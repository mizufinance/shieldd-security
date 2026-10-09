//! Closed circuit catalogue; templates supply shape only and contain no setup randomness.
use crate::{
    audit, authorization, compliance, disclosure, encryption, group::Point, hash::Parameters,
    map::Generators, note, proof::Family, recovery, registry, reshape, routing, scalar, seizure,
    self_action, transfer, tree::Path, volume, withdrawal,
};
use anyhow::Result;
use commonware_cryptography::{
    bls12381::primitives::group::Scalar,
    zk::{
        circuit::{self, Context, ValuedCircuit, Var},
        pari::{InputLayout, Relation},
    },
};
use commonware_math::algebra::Additive;

pub enum Witness {
    Transfer(Box<transfer::Witness>),
    Reshape(Box<reshape::Witness>),
    Withdrawal(Box<withdrawal::Witness>),
    Seizure(Box<seizure::Witness>),
    Disclosure(Box<disclosure::Witness>),
    DisclosureOne(Box<disclosure::Witness<1>>),
}
impl Witness {
    pub fn family(&self) -> Family {
        match self {
            Self::Transfer(_) => Family::Transfer,
            Self::Reshape(w) => match &w.notes {
                reshape::Notes::Split { .. } => Family::ReshapeOneToEight,
                reshape::Notes::Merge { .. } => Family::ReshapeEightToOne,
            },
            Self::Withdrawal(_) => Family::Withdrawal,
            Self::Seizure(_) => Family::Seizure,
            Self::Disclosure(_) => Family::Disclosure,
            Self::DisclosureOne(_) => Family::DisclosureOne,
        }
    }
    pub fn digest(&self, p: &Parameters, g: &Generators) -> Result<Scalar> {
        Ok(match self {
            Self::Transfer(w) => p.native(
                transfer::STATEMENT_DOMAIN,
                &transfer::statement(p, g, w)?.fields(),
            ),
            Self::Reshape(w) => w.statement(g).digest(p),
            Self::Withdrawal(w) => w.statement(g).digest(p),
            Self::Seizure(w) => w.statement.digest(p),
            Self::Disclosure(w) => w.statement.digest(p),
            Self::DisclosureOne(w) => w.statement.digest(p),
        })
    }
    pub fn constrain<'a>(
        &self,
        ctx: Context<'a, Scalar>,
        p: &Parameters,
        g: &Generators,
        digest: &Scalar,
    ) -> Vec<Var<'a, Scalar>> {
        match self {
            Self::Transfer(w) => transfer::constrain(ctx, p, g, w, digest),
            Self::Reshape(w) => reshape::constrain(ctx, p, g, w, digest),
            Self::Withdrawal(w) => withdrawal::constrain(ctx, p, g, w, digest),
            Self::Seizure(w) => seizure::constrain(ctx, p, w, digest),
            Self::Disclosure(w) => disclosure::constrain(ctx, p, w, digest),
            Self::DisclosureOne(w) => disclosure::constrain(ctx, p, w, digest),
        }
    }
}
pub struct Compiled {
    pub family: Family,
    pub relation: Relation,
    pub layout: InputLayout,
}
pub fn compile(family: Family) -> Result<Compiled> {
    let p = Parameters::load()?;
    let g = Generators::derive(&p);
    let w = template(family);
    let (c, selected) = circuit::build(|ctx| w.constrain(ctx, &p, &g, &Scalar::zero()));
    let layout = InputLayout::new(vec![selected[0]], vec![vec![selected[1]]])?;
    let relation = Relation::compile(&c, &layout)?;
    Ok(Compiled {
        family,
        relation,
        layout,
    })
}

#[cfg(feature = "formal-observer")]
pub struct BalanceInspection {
    pub compiled: Compiled,
    pub handles: Vec<(&'static str, Vec<circuit::CircuitIdx>, Vec<circuit::CircuitIdx>)>,
    pub selected: Vec<circuit::CircuitIdx>,
    /// Pre-outline linear combinations; constant_copy and its final equality row
    /// must be used for correspondence to the final stored rows.
    pub expressions: Vec<Vec<(u32, Scalar)>>,
    pub constant_copy: u32,
    pub nodes: Vec<(u32, bool, circuit::CircuitIdx, circuit::CircuitIdx)>,
}

#[cfg(feature = "formal-observer")]
pub fn inspect_transfer_balance() -> Result<BalanceInspection> {
    use circuit::CircuitIdx;
    use std::collections::BTreeSet;
    let _capture = crate::balance::inspection::begin()?;
    let p = Parameters::load()?;
    let g = Generators::derive(&p);
    let w = template(Family::Transfer);
    let (c, returned) = circuit::build(|ctx| w.constrain(ctx, &p, &g, &Scalar::zero()));
    anyhow::ensure!(returned.len() == 2, "Transfer return roles changed");
    let layout = InputLayout::new(vec![returned[0]], vec![vec![returned[1]]])?;
    let handles = crate::balance::inspection::take();
    anyhow::ensure!(handles.len() == 5 && handles[..4].iter().all(|(role, values, bits)|
        *role == "amount" && values.len() == 1 && bits.len() == 128)
        && handles[4].0 == "signed" && handles[4].1.len() == 4 && handles[4].2.len() == 129,
        "balance observation shape changed");
    let roots: BTreeSet<_> = handles[..4].iter().map(|(_, values, _)| values[0])
        .chain([handles[4].1[1], handles[4].1[2]]).collect();
    let mut pending = vec![handles[4].1[0], handles[4].1[3]];
    let mut visited = BTreeSet::new();
    let mut nodes = Vec::new();
    while let Some(index) = pending.pop() {
        if !visited.insert(index) || roots.contains(&index) { continue; }
        anyhow::ensure!(visited.len() <= 128, "balance source closure exceeds bound");
        if let CircuitIdx::Node(node) = index {
            let (multiply, left, right) = c.inspect_node(node).ok_or_else(|| anyhow::anyhow!("invalid source node"))?;
            nodes.push((node, multiply, left, right));
            pending.extend([left, right]);
        } else if matches!(index, CircuitIdx::Witness(_)) {
            anyhow::bail!("unexpected witness in bounded balance source closure");
        }
    }
    nodes.sort_by_key(|node| node.0);
    let mut selected: Vec<_> = handles.iter().flat_map(|(_, values, bits)| values.iter().chain(bits)).copied().collect();
    selected.extend(visited);
    selected.sort();
    selected.dedup();
    let (relation, expressions, constant_copy) = Relation::compile_inspected(&c, &layout, &selected)?;
    Ok(BalanceInspection { compiled: Compiled { family: Family::Transfer, relation, layout },
        handles, selected, expressions, constant_copy, nodes })
}
#[cfg(feature = "formal-observer")]
pub struct CanonicalBalanceInspection {
    pub compiled: Compiled,
    pub value: circuit::CircuitIdx,
    pub bits: Vec<circuit::CircuitIdx>,
    pub endpoint: circuit::CircuitIdx,
    pub steps: Vec<[crate::scalar::inspection::Observed;6]>,
    pub selected: Vec<circuit::CircuitIdx>,
    pub expressions: Vec<Vec<(u32, Scalar)>>,
    pub constant_copy: u32,
    pub nodes: Vec<(u32, bool, circuit::CircuitIdx, circuit::CircuitIdx)>,
}

#[cfg(feature = "formal-observer")]
pub fn inspect_transfer_canonical_balance() -> Result<CanonicalBalanceInspection> {
    use circuit::CircuitIdx;
    use std::collections::BTreeSet;
    let _capture = crate::scalar::inspection::begin()?;
    let p = Parameters::load()?;
    let g = Generators::derive(&p);
    let w = template(Family::Transfer);
    let (c, returned) = circuit::build(|ctx| w.constrain(ctx, &p, &g, &Scalar::zero()));
    anyhow::ensure!(returned.len() == 2, "Transfer return roles changed");
    let layout = InputLayout::new(vec![returned[0]], vec![vec![returned[1]]])?;
    let (value, bits, endpoint, steps) = crate::scalar::inspection::take()?;
    anyhow::ensure!(value == returned[1] && bits.len() == 252,
        "canonical balance is not the actual committed return handle");
    let roots: BTreeSet<_> = bits.iter().copied().chain([value]).collect();
    let mut pending = vec![endpoint];
    let mut visited = BTreeSet::new();
    let mut nodes = Vec::new();
    while let Some(index) = pending.pop() {
        if !visited.insert(index) || roots.contains(&index) { continue; }
        anyhow::ensure!(visited.len() <= 6144, "canonical source closure exceeds bound");
        if let CircuitIdx::Node(node) = index {
            let (multiply, left, right) = c.inspect_node(node)
                .ok_or_else(|| anyhow::anyhow!("invalid canonical source node"))?;
            nodes.push((node, multiply, left, right));
            pending.extend([left, right]);
        } else if matches!(index, CircuitIdx::Witness(_)) {
            anyhow::bail!("unexpected witness in canonical comparison closure");
        }
    }
    nodes.sort_by_key(|node| node.0);
    let mut selected: Vec<_> = roots.into_iter().chain(steps.iter().flatten().filter_map(|v| match v { crate::scalar::inspection::Observed::Source(index) => Some(*index), _ => None })).chain([endpoint]).collect();
    selected.sort(); selected.dedup();
    anyhow::ensure!(selected.len() <= 4096, "canonical selected expressions exceed bound");
    let (relation, expressions, constant_copy) = Relation::compile_inspected(&c, &layout, &selected)?;
    Ok(CanonicalBalanceInspection { compiled: Compiled { family: Family::Transfer, relation, layout },
        value, bits, endpoint, steps, selected, expressions, constant_copy, nodes })
}

/// One current Transfer IVK hash cone. Source nodes are bounded separately from
/// the selected linear expressions; deferred-square selections fail closed.
#[cfg(feature = "formal-observer")]
pub struct IvkInspection {
    pub compiled: Compiled,
    /// nk, ak.x, ak.y, full-field IVK hash (before scalar reduction).
    pub handles: [circuit::CircuitIdx; 4],
    pub selected: Vec<circuit::CircuitIdx>,
    pub expressions: Vec<Vec<(u32, Scalar)>>,
    pub constant_copy: u32,
    pub nodes: Vec<(u32, bool, circuit::CircuitIdx, circuit::CircuitIdx)>,
}

#[cfg(feature = "formal-observer")]
pub fn inspect_transfer_ivk() -> Result<IvkInspection> {
    use circuit::CircuitIdx;
    use std::collections::BTreeSet;
    let _capture = authorization::inspection::begin()?;
    let p = Parameters::load()?;
    let g = Generators::derive(&p);
    let w = template(Family::Transfer);
    let (c, returned) = circuit::build(|ctx| w.constrain(ctx, &p, &g, &Scalar::zero()));
    anyhow::ensure!(returned.len() == 2, "Transfer return roles changed");
    let layout = InputLayout::new(vec![returned[0]], vec![vec![returned[1]]])?;
    let handles = authorization::inspection::take()?;
    let roots: BTreeSet<_> = handles[..3].iter().copied().collect();
    anyhow::ensure!(roots.len() == 3, "IVK input roles alias");
    let mut pending = vec![handles[3]];
    let mut visited = BTreeSet::new();
    let mut selected: BTreeSet<_> = handles.into_iter().collect();
    let mut nodes = Vec::new();
    while let Some(index) = pending.pop() {
        if !visited.insert(index) || roots.contains(&index) { continue; }
        anyhow::ensure!(visited.len() <= 16384, "IVK source cone exceeds 16384");
        match index {
            CircuitIdx::Node(node) => {
                let (multiply, left, right) = c.inspect_node(node)
                    .ok_or_else(|| anyhow::anyhow!("invalid IVK source node"))?;
                nodes.push((node, multiply, left, right));
                // Addition expressions follow symbolically from the DAG. Each
                // multiplication and both operands have observed compiler LCs.
                if multiply && !matches!(left, CircuitIdx::Constant(_))
                    && !matches!(right, CircuitIdx::Constant(_)) { selected.extend([index, left, right]); }
                pending.extend([left, right]);
            }
            CircuitIdx::Constant(_) => { selected.insert(index); }
            CircuitIdx::Witness(_) => anyhow::bail!("unexpected witness in IVK source cone"),
        }
    }
    nodes.sort_by_key(|node| node.0);
    let selected: Vec<_> = selected.into_iter().collect();
    anyhow::ensure!(selected.len() <= 4096, "IVK linear selection exceeds 4096");
    let (relation, expressions, constant_copy) = Relation::compile_inspected(&c, &layout, &selected)?;
    Ok(IvkInspection { compiled: Compiled { family: Family::Transfer, relation, layout },
        handles, selected, expressions, constant_copy, nodes })
}

/// One of two RNK permutations, or its small commitment permutation.
/// Hash inputs and absorbed states are distinct observed boundaries.
#[cfg(feature = "formal-observer")]
pub struct RnkHashInspection {
    pub compiled: Compiled,
    pub block: usize,
    pub hashes: Vec<crate::hash::inspection::Report>,
    pub rnk: crate::group::ownership_inspection::RnkBindings,
    pub ivk_handles: [circuit::CircuitIdx;4],
    pub selected: Vec<circuit::CircuitIdx>,
    pub expressions: Vec<Vec<(u32,Scalar)>>,
    pub constant_copy: u32,
    pub nodes: Vec<(u32,bool,circuit::CircuitIdx,circuit::CircuitIdx)>,
}

#[cfg(feature = "formal-observer")]
pub fn inspect_transfer_rnk_hash(block: usize) -> Result<RnkHashInspection> {
    use circuit::CircuitIdx;
    use crate::scalar::inspection::Observed;
    use std::collections::BTreeSet;
    anyhow::ensure!(block<3,"RNK hash block must be 0, 1 or 2");
    let _hash_capture=crate::hash::inspection::begin()?;
    let _rnk_capture=crate::group::ownership_inspection::begin_rnk_dh()?;
    let _ivk_capture=authorization::inspection::begin()?;
    let p=Parameters::load()?;let g=Generators::derive(&p);let w=template(Family::Transfer);
    let (c,returned)=circuit::build(|ctx| w.constrain(ctx,&p,&g,&Scalar::zero()));
    anyhow::ensure!(returned.len()==2,"Transfer return roles changed");
    let layout=InputLayout::new(vec![returned[0]],vec![vec![returned[1]]])?;
    let report=crate::group::ownership_inspection::take()?;
    let hashes=crate::hash::inspection::take()?;
    let ivk_handles=authorization::inspection::take()?;
    let rnk=report.rnk.ok_or_else(||anyhow::anyhow!("missing RNK boundary roles"))?;
    anyhow::ensure!(hashes[0].inputs.as_slice()==rnk.inputs && hashes[0].output==rnk.hash
        && hashes[1].inputs==vec![rnk.hash.clone()] && hashes[1].output==rnk.commitment,
        "RNK and commitment source roles differ");
    anyhow::ensure!(hashes[0].output==hashes[0].blocks[1].after[1] &&
        hashes[1].output==hashes[1].blocks[0].after[1],"hash output lane changed");
    let (call,offset)=if block<2 {(0,block)} else {(1,0)};
    let permutation=&hashes[call].blocks[offset];
    let roots:BTreeSet<_>=permutation.before.iter().filter_map(|value| match value {
        Observed::Source(index)=>Some(*index),Observed::Native(_)=>None,
    }).collect();
    let mut selected=roots.clone();
    // NK is a non-hash source boundary for the effective-NK selector.
    selected.insert(ivk_handles[0]);
    for value in hashes.iter().flat_map(|hash|hash.inputs.iter().chain(std::iter::once(&hash.output))
        .chain(hash.blocks.iter().flat_map(|block|block.before.iter().chain(block.after.iter()))))
        .chain([&rnk.regulated,&rnk.registered,&rnk.effective_nk]) {
        if let Observed::Source(index)=value {selected.insert(*index);}
    }
    let mut pending:Vec<_>=permutation.after.iter().filter_map(|value| match value {
        Observed::Source(index)=>Some(*index),Observed::Native(_)=>None,
    }).collect();
    let mut visited=BTreeSet::new();let mut nodes=Vec::new();
    while let Some(index)=pending.pop() {
        if !visited.insert(index) || roots.contains(&index) {continue;}
        anyhow::ensure!(visited.len()<=16384,"RNK permutation cone exceeds 16384");
        match index {
            CircuitIdx::Node(node)=>{
                let (multiply,left,right)=c.inspect_node(node)
                    .ok_or_else(||anyhow::anyhow!("invalid RNK permutation node"))?;
                nodes.push((node,multiply,left,right));
                if multiply && !matches!(left,CircuitIdx::Constant(_)) &&
                    !matches!(right,CircuitIdx::Constant(_)) {selected.extend([index,left,right]);}
                pending.extend([left,right]);
            }
            CircuitIdx::Constant(_)=>{selected.insert(index);}
            CircuitIdx::Witness(_)=>anyhow::bail!("unexpected RNK permutation witness"),
        }
    }
    nodes.sort_by_key(|node|node.0);
    let selected:Vec<_>=selected.into_iter().collect();
    anyhow::ensure!(selected.len()<=4096,"RNK permutation LC selection exceeds 4096");
    let (relation,expressions,constant_copy)=Relation::compile_inspected(&c,&layout,&selected)?;
    Ok(RnkHashInspection {compiled:Compiled {family:Family::Transfer,relation,layout},
        block,hashes,rnk,ivk_handles,selected,expressions,constant_copy,nodes})
}

#[cfg(feature = "formal-observer")]
pub struct IvkReductionInspection {
    pub compiled: Compiled,
    pub ivk_hash_handles: [circuit::CircuitIdx;4],
    pub report: scalar::reduction_inspection::Report,
    pub selected: Vec<circuit::CircuitIdx>,
    pub expressions: Vec<Vec<(u32,Scalar)>>,
    pub constant_copy: u32,
    pub nodes: Vec<(u32,bool,circuit::CircuitIdx,circuit::CircuitIdx)>,
}

#[cfg(feature = "formal-observer")]
pub struct TransferRoleInspection {
    pub compiled: Compiled,
    pub report: transfer::inspection::Report,
    pub rnk: crate::group::ownership_inspection::RnkBindings,
    pub ivk_handles: [circuit::CircuitIdx; 4],
    pub selected: Vec<circuit::CircuitIdx>,
    pub expressions: Vec<Vec<(u32, Scalar)>>,
    pub constant_copy: u32,
}

#[cfg(feature = "formal-observer")]
pub fn inspect_transfer_roles() -> Result<TransferRoleInspection> {
    use crate::scalar::inspection::Observed;
    use std::collections::BTreeSet;
    let _roles = transfer::inspection::begin()?;
    let _rnk = crate::group::ownership_inspection::begin_rnk_dh()?;
    let _ivk = authorization::inspection::begin()?;
    let p = Parameters::load()?;
    let g = Generators::derive(&p);
    let w = template(Family::Transfer);
    let (c, returned) = circuit::build(|ctx| w.constrain(ctx, &p, &g, &Scalar::zero()));
    anyhow::ensure!(returned.len() == 2, "Transfer return roles changed");
    let layout = InputLayout::new(vec![returned[0]], vec![vec![returned[1]]])?;
    let report = transfer::inspection::take()?;
    let rnk_report = crate::group::ownership_inspection::take()?;
    let ivk_handles = authorization::inspection::take()?;
    let rnk = rnk_report.rnk.ok_or_else(|| anyhow::anyhow!("missing RNK bindings"))?;
    let a = &report.caller;
    anyhow::ensure!(a.nk == Observed::Source(ivk_handles[0]) &&
        a.ak == [Observed::Source(ivk_handles[1]), Observed::Source(ivk_handles[2])],
        "caller IVK input roles differ");
    anyhow::ensure!(a.address.as_slice() == &rnk.inputs[2..6] && a.asset == rnk.inputs[6] &&
        a.selected_ring.as_slice() == &rnk.inputs[7..9] && a.regulated == rnk.regulated &&
        a.registered_rnk == rnk.registered && a.effective_nk == rnk.effective_nk &&
        a.rnk_dh == rnk_report.base && rnk_report.output.as_slice() == &rnk.inputs[..2],
        "caller RNK input roles differ");
    let mut selected = BTreeSet::from(ivk_handles);
    selected.extend(report.spend.bits.iter().copied());
    for value in [&a.regulated, &a.asset, &a.registered_rnk, &a.nk, &a.effective_nk,
                  &report.spend.randomizer]
        .into_iter().chain(a.leaf_ring.iter()).chain(a.fixed_ring.iter())
        .chain(a.selected_ring.iter()).chain(a.address.iter()).chain(a.rnk_dh.iter())
        .chain(a.ak.iter()).chain(report.spend.generator.iter()).chain(report.spend.contribution.iter())
        .chain(report.spend.computed.iter()).chain(report.spend.rk.iter())
        .chain(rnk.inputs.iter()).chain([&rnk.hash, &rnk.commitment]) {
        if let Observed::Source(index) = value { selected.insert(*index); }
    }
    let selected: Vec<_> = selected.into_iter().collect();
    anyhow::ensure!(selected.len() <= 512, "transfer role LC bound exceeded");
    let (relation, expressions, constant_copy) = Relation::compile_inspected(&c, &layout, &selected)?;
    Ok(TransferRoleInspection { compiled: Compiled { family: Family::Transfer, relation, layout },
        report, rnk, ivk_handles, selected, expressions, constant_copy })
}

/// Bounded ascending spend-fixed windows; no transitive source DAG is retained.
#[cfg(feature = "formal-observer")]
pub struct FixedSpendInspection {
    pub compiled: Compiled,
    pub report: crate::group::fixed_inspection::Report,
    pub canonical_endpoint: circuit::CircuitIdx,
    pub canonical_steps: Vec<[scalar::inspection::Observed; 6]>,
    pub selected: Vec<circuit::CircuitIdx>,
    pub expressions: Vec<Vec<(u32, Scalar)>>,
    pub constant_copy: u32,
}

#[cfg(feature = "formal-observer")]
pub fn inspect_transfer_fixed_spend(start: usize, count: usize) -> Result<FixedSpendInspection> {
    use scalar::inspection::Observed;
    use std::collections::BTreeSet;
    let _capture = crate::group::fixed_inspection::begin(start, count)?;
    let _canonical = scalar::inspection::begin_spend()?;
    let p = Parameters::load()?;
    let g = Generators::derive(&p);
    let w = template(Family::Transfer);
    let (c, returned) = circuit::build(|ctx| w.constrain(ctx, &p, &g, &Scalar::zero()));
    anyhow::ensure!(returned.len() == 2, "Transfer return roles changed");
    let layout = InputLayout::new(vec![returned[0]], vec![vec![returned[1]]])?;
    let report = crate::group::fixed_inspection::take()?;
    let (canonical_value, canonical_bits, canonical_endpoint, canonical_steps) = scalar::inspection::take()?;
    anyhow::ensure!(report.randomizer == Observed::Source(canonical_value) &&
        report.bits == canonical_bits && canonical_steps.len() == 252,
        "fixed/canonical randomizer role mismatch");
    let mut selected: BTreeSet<_> = report.bits.iter().copied().collect();
    selected.insert(canonical_endpoint);
    for value in [&report.randomizer].into_iter().chain(report.generator.iter())
        .chain(report.output.iter()).chain(report.windows.iter().flat_map(|window|
            window.table.iter().flatten().chain(window.points.iter().flatten())
                .chain(window.arithmetic.iter()).chain(window.quotient.iter())))
        .chain(canonical_steps.iter().flatten()) {
        if let Observed::Source(index) = value { selected.insert(*index); }
    }
    let selected: Vec<_> = selected.into_iter().collect();
    anyhow::ensure!(selected.len() <= 4096, "fixed spend LC selection exceeds bound");
    let (relation, expressions, constant_copy) = Relation::compile_inspected(&c, &layout, &selected)?;
    Ok(FixedSpendInspection { compiled: Compiled { family: Family::Transfer, relation, layout },
        report, canonical_endpoint, canonical_steps, selected, expressions, constant_copy })
}

#[cfg(feature = "formal-observer")]
pub fn inspect_transfer_ivk_reduction() -> Result<IvkReductionInspection> {
    use circuit::CircuitIdx;
    use scalar::inspection::Observed;
    use std::collections::BTreeSet;
    let _hash_capture=authorization::inspection::begin()?;
    let _reduction_capture=scalar::reduction_inspection::begin()?;
    let p=Parameters::load()?;
    let g=Generators::derive(&p);
    let w=template(Family::Transfer);
    let (c,returned)=circuit::build(|ctx|w.constrain(ctx,&p,&g,&Scalar::zero()));
    anyhow::ensure!(returned.len()==2,"Transfer return roles changed");
    let layout=InputLayout::new(vec![returned[0]],vec![vec![returned[1]]])?;
    let ivk_hash_handles=authorization::inspection::take()?;
    let report=scalar::reduction_inspection::take()?;
    anyhow::ensure!(report.value==ivk_hash_handles[3] && report.quotient_bits.len()==4
        && report.remainder_bits.len()==252,"IVK reduction input/bit shape changed");
    let (consumer,inverse)=report.consumer.ok_or_else(||anyhow::anyhow!("missing IVK consumer"))?;
    let roots:BTreeSet<_>=report.quotient_bits.iter().chain(&report.remainder_bits).copied()
        .chain([report.value,report.quotient,report.remainder,inverse]).collect();
    let endpoints=[&report.quotient_end,&report.remainder_end,&report.terminal_end];
    let mut selected:BTreeSet<_>=roots.iter().copied().chain([consumer,inverse,report.equation,report.terminal_gate]).collect();
    for value in report.steps.iter().flatten().flatten().chain(endpoints) {
        if let Observed::Source(index)=value {selected.insert(*index);}
    }
    let mut pending:Vec<_>=selected.iter().copied().collect();
    let mut visited=BTreeSet::new();
    let mut nodes=Vec::new();
    while let Some(index)=pending.pop() {
        if !visited.insert(index) || roots.contains(&index) {continue;}
        anyhow::ensure!(visited.len()<=16384,"IVK reduction source closure exceeds bound");
        match index {
            CircuitIdx::Node(node)=>{
                let (multiply,left,right)=c.inspect_node(node).ok_or_else(||anyhow::anyhow!("invalid reduction source node"))?;
                nodes.push((node,multiply,left,right));pending.extend([left,right]);
            }
            CircuitIdx::Constant(_)=>{}, // topology only; literal meanings are checked in recorded step LCs
            CircuitIdx::Witness(_)=>anyhow::bail!("unexpected witness in reduction source closure"),
        }
    }
    nodes.sort_by_key(|node|node.0);
    let selected:Vec<_>=selected.into_iter().collect();
    anyhow::ensure!(selected.len()<=4096,"IVK reduction LC selection exceeds bound: {}",selected.len());
    let (relation,expressions,constant_copy)=Relation::compile_inspected(&c,&layout,&selected)?;
    Ok(IvkReductionInspection {compiled:Compiled {family:Family::Transfer,relation,layout},
        ivk_hash_handles,report,selected,expressions,constant_copy,nodes})
}

#[cfg(feature = "formal-observer")]
pub struct AkSubgroupInspection {
    pub compiled: Compiled,
    pub report: crate::group::inspection::Report,
    pub ivk_handles: [circuit::CircuitIdx; 4],
    pub selected: Vec<circuit::CircuitIdx>,
    pub expressions: Vec<Vec<(u32, Scalar)>>,
    pub constant_copy: u32,
    pub nodes: Vec<(u32, bool, circuit::CircuitIdx, circuit::CircuitIdx)>,
}

#[cfg(feature = "formal-observer")]
pub fn inspect_transfer_ak_subgroup() -> Result<AkSubgroupInspection> {
    use circuit::CircuitIdx;
    use std::collections::BTreeSet;
    let _capture = crate::group::inspection::begin()?;
    let _ivk_capture = authorization::inspection::begin()?;
    let p = Parameters::load()?;
    let g = Generators::derive(&p);
    let w = template(Family::Transfer);
    let (c, returned) = circuit::build(|ctx| w.constrain(ctx, &p, &g, &Scalar::zero()));
    anyhow::ensure!(returned.len() == 2, "Transfer return roles changed");
    let layout = InputLayout::new(vec![returned[0]], vec![vec![returned[1]]])?;
    let report = crate::group::inspection::take()?;
    let ivk_handles = authorization::inspection::take()?;
    anyhow::ensure!(report.inputs[..2] == ivk_handles[1..3], "AK does not feed the IVK hash");
    let mut selected: BTreeSet<_> = report.inputs.into_iter().chain(report.curve)
        .chain(report.nonidentity).chain(report.doubles.iter().flatten().copied()).collect();
    // Inverse witnesses are graph leaves. Include the bounded existing add spans
    // so denominator and inverse-assertion products cannot disappear from closure.
    for [start, end] in &report.spans {
        for node in *start..*end { selected.insert(CircuitIdx::Node(u32::try_from(node)?)); }
    }
    let CircuitIdx::Node(nonidentity_node) = report.nonidentity_product else {
        anyhow::bail!("nonidentity product must be a source node");
    };
    anyhow::ensure!(c.inspect_node(nonidentity_node) == Some((true, report.nonidentity[1], report.nonidentity[0])),
        "AK nonidentity product source boundary changed");
    selected.insert(report.nonidentity_product);
    let mut pending: Vec<_> = selected.iter().copied().collect();
    let mut visited = BTreeSet::new();
    let mut nodes = Vec::new();
    while let Some(index) = pending.pop() {
        if !visited.insert(index) { continue; }
        anyhow::ensure!(visited.len() <= 2048, "AK source cone exceeds 2048");
        match index {
            CircuitIdx::Node(node) => {
                let (multiply, left, right) = c.inspect_node(node)
                    .ok_or_else(|| anyhow::anyhow!("invalid subgroup source node"))?;
                nodes.push((node, multiply, left, right));
                if multiply && !matches!(left, CircuitIdx::Constant(_))
                    && !matches!(right, CircuitIdx::Constant(_)) {
                    selected.extend([index, left, right]);
                }
                pending.extend([left, right]);
            }
            CircuitIdx::Constant(_) | CircuitIdx::Witness(_) => { selected.insert(index); }
        }
    }
    nodes.sort_by_key(|node| node.0);
    let selected: Vec<_> = selected.into_iter().collect();
    anyhow::ensure!(selected.len() <= 1024, "AK selection exceeds 1024");
    let (relation, expressions, constant_copy) = Relation::compile_inspected(&c, &layout, &selected)?;
    Ok(AkSubgroupInspection { compiled: Compiled { family: Family::Transfer, relation, layout },
        report, ivk_handles, selected, expressions, constant_copy, nodes })
}

#[cfg(feature = "formal-observer")]
pub struct OwnershipInspection {
    pub compiled: Compiled,
    pub report: crate::group::ownership_inspection::Report,
    pub reduction: crate::scalar::reduction_inspection::Report,
    pub ivk_handles: [circuit::CircuitIdx; 4],
    pub selected: Vec<circuit::CircuitIdx>,
    pub expressions: Vec<Vec<(u32, Scalar)>>,
    pub constant_copy: u32,
    pub nodes: Vec<(u32, bool, circuit::CircuitIdx, circuit::CircuitIdx)>,
    pub window_start: usize,
    pub window_count: usize,
}

#[cfg(feature = "formal-observer")]
pub fn inspect_transfer_ownership(window_start: usize, window_count: usize) -> Result<OwnershipInspection> {
    inspect_transfer_variable_loop(window_start, window_count, false)
}

#[cfg(feature = "formal-observer")]
pub fn inspect_transfer_rnk_dh(window_start: usize, window_count: usize) -> Result<OwnershipInspection> {
    inspect_transfer_variable_loop(window_start, window_count, true)
}

#[cfg(feature = "formal-observer")]
fn inspect_transfer_variable_loop(window_start: usize, window_count: usize, rnk_dh: bool) -> Result<OwnershipInspection> {
    use circuit::CircuitIdx;
    use crate::scalar::inspection::Observed;
    use std::collections::BTreeSet;
    anyhow::ensure!(window_count > 0 && window_count <= 16 && window_start < 126 &&
        window_start.checked_add(window_count).is_some_and(|end| end <= 126),
        "ownership chunk must select 1..16 windows within 0..126");
    let window_end = window_start + window_count;
    let _capture = if rnk_dh { crate::group::ownership_inspection::begin_rnk_dh()? }
        else { crate::group::ownership_inspection::begin()? };
    let _reduction = crate::scalar::reduction_inspection::begin()?;
    let _ivk = authorization::inspection::begin()?;
    let p = Parameters::load()?;
    let g = Generators::derive(&p);
    let w = template(Family::Transfer);
    let (c, returned) = circuit::build(|ctx| w.constrain(ctx, &p, &g, &Scalar::zero()));
    anyhow::ensure!(returned.len() == 2, "Transfer return roles changed");
    let layout = InputLayout::new(vec![returned[0]], vec![vec![returned[1]]])?;
    let report = crate::group::ownership_inspection::take()?;
    let reduction = crate::scalar::reduction_inspection::take()?;
    let ivk_handles = authorization::inspection::take()?;
    anyhow::ensure!(report.bits == reduction.remainder_bits,
        "ownership bits differ from the canonical IVK remainder bits");
    anyhow::ensure!(reduction.value == ivk_handles[3], "ownership reduction hash role changed");
    let observed = report.base.iter().chain(report.twice.iter()).chain(report.triple.iter())
        .chain(report.output.iter()).chain(report.target.iter().flatten())
        .chain(report.nonidentity_inverse.iter())
        .chain(report.windows[window_start..window_end].iter().flatten().flatten())
        .chain(report.quotients[..2].iter().flatten())
        .chain(report.quotients[2 + 3 * window_start..2 + 3 * window_end].iter().flatten());
    let mut selected: BTreeSet<_> = report.bits.iter().copied().collect();
    for value in observed {
        if let Observed::Source(index) = value { selected.insert(*index); }
    }
    let mut pending: Vec<_> = selected.iter().copied().collect();
    let mut visited = BTreeSet::new();
    let mut nodes = Vec::new();
    while let Some(index) = pending.pop() {
        if !visited.insert(index) { continue; }
        anyhow::ensure!(visited.len() <= 8192, "ownership source cone exceeds 8192");
        match index {
            CircuitIdx::Node(node) => {
                let (multiply, left, right) = c.inspect_node(node)
                    .ok_or_else(|| anyhow::anyhow!("invalid ownership source node"))?;
                nodes.push((node, multiply, left, right));
                if multiply && !matches!(left, CircuitIdx::Constant(_)) &&
                    !matches!(right, CircuitIdx::Constant(_)) { selected.extend([index, left, right]); }
                pending.extend([left, right]);
            }
            CircuitIdx::Constant(_) | CircuitIdx::Witness(_) => { selected.insert(index); }
        }
    }
    nodes.sort_by_key(|node| node.0);
    let selected: Vec<_> = selected.into_iter().collect();
    anyhow::ensure!(selected.len() <= 4096, "ownership LC selection exceeds 4096: {}", selected.len());
    let (relation, expressions, constant_copy) = Relation::compile_inspected(&c, &layout, &selected)?;
    Ok(OwnershipInspection { compiled: Compiled { family: Family::Transfer, relation, layout },
        report, reduction, ivk_handles, selected, expressions, constant_copy, nodes,
        window_start, window_count })
}

pub fn evaluate(witness: &Witness) -> Result<ValuedCircuit<Scalar>> {
    let p = Parameters::load()?;
    let g = Generators::derive(&p);
    let digest = witness.digest(&p, &g)?;
    Ok(circuit::build_with_values(|ctx| witness.constrain(ctx, &p, &g, &digest)).0)
}

fn zero() -> Scalar {
    Scalar::zero()
}
fn point() -> Point<Scalar> {
    Point::identity()
}
fn address() -> encryption::Address<Scalar> {
    encryption::Address {
        diversified: point(),
        transmission: point(),
    }
}
fn path<const D: usize>() -> Path<Scalar, D> {
    Path {
        position: zero(),
        siblings: std::array::from_fn(|_| std::array::from_fn(|_| zero())),
    }
}
fn note() -> note::Note<Scalar> {
    note::Note {
        blinding: zero(),
        amount: zero(),
        recovery: zero(),
    }
}
fn capsule() -> recovery::Capsule<Scalar> {
    recovery::Capsule {
        commitment: zero(),
        epk: point(),
        c2: zero(),
        salt: zero(),
        confirmation: zero(),
        encrypted_amount: zero(),
        encrypted_blinding: zero(),
    }
}
fn output() -> note::OutputWitness {
    note::OutputWitness {
        note: note(),
        commitment: zero(),
        capsule: recovery::Witness {
            capsule: capsule(),
            seed: zero(),
            randomizer: zero(),
        },
    }
}
fn spend() -> note::SpendWitness {
    note::SpendWitness {
        note: note(),
        path: path(),
        nullifier: zero(),
    }
}
fn optional() -> note::OptionalWitness {
    note::OptionalWitness {
        is_dummy: false,
        seed: zero(),
    }
}
fn auth() -> authorization::Witness {
    authorization::Witness {
        ak: point(),
        ak_preimage: point(),
        nk: zero(),
        ivk: scalar::Reduction {
            remainder: zero(),
            quotient: 0,
        },
    }
}
fn audit() -> audit::Keys<Scalar> {
    audit::Keys {
        epoch: zero(),
        payload: point(),
        checking: point(),
    }
}
fn registry() -> registry::Witness {
    registry::Witness {
        path: path(),
        leaf: registry::Leaf {
            value: zero(),
            next_index: zero(),
            next_value: zero(),
            dk: point(),
            daily_limit: zero(),
            route_policy: zero(),
            ring: point(),
            ring_id: zero(),
            policy_id: zero(),
            permission: zero(),
            resource: zero(),
            audit: audit(),
        },
    }
}
fn owner() -> compliance::Witness {
    compliance::Witness {
        path: path(),
        leaf: compliance::Leaf {
            address: address(),
            rnk_dh: point(),
            rnk_commitment: zero(),
            lifecycle: zero(),
        },
    }
}
fn volume() -> volume::Witness {
    volume::Witness {
        nullifier: zero(),
        commitment: zero(),
        day_start: zero(),
        proof_context: 1,
        use_real: false,
        starts_new_day: false,
        timestamp_day_index: 0,
        timestamp_second: 0,
        subject: zero(),
        prior_volume: 0,
        prior_blinding: zero(),
        prior_commitment: zero(),
        prior_path: path(),
        successor_volume: 0,
        successor_blinding: zero(),
    }
}
fn self_action() -> self_action::Witness {
    self_action::Witness {
        spend_auth: note::SpendAuthorization {
            randomizer: zero(),
            rk: point(),
        },
        anchor: zero(),
        asset_anchor: zero(),
        compliance_anchor: zero(),
        asset: zero(),
        regulated: false,
        balance_blinding: zero(),
        routing_nonce: zero(),
        routing: routing::SingleWitness {
            regulated_precision: 0,
            unregulated_precision: 0,
            as_of_height: zero(),
            parameter_set: zero(),
            tag: zero(),
        },
        auth: auth(),
        registry: registry(),
        sender: owner(),
    }
}
fn predicate() -> disclosure::Predicate<Scalar> {
    disclosure::Predicate {
        op: zero(),
        lower: zero(),
        upper: zero(),
        result: zero(),
    }
}
fn disclosure_template<const N: usize>() -> disclosure::Witness<N> {
    disclosure::Witness {
        statement: disclosure::Statement {
            context: [zero(), zero()],
            context_hash: zero(),
            slots: std::array::from_fn(|_| disclosure::Slot {
                active: zero(),
                commitment: zero(),
                reveal_amount: zero(),
                reveal_asset: zero(),
                reveal_recipient: zero(),
                amount: zero(),
                asset: zero(),
                address: address(),
                predicate: predicate(),
            }),
            total_enabled: zero(),
            total_reveal: zero(),
            total_amount: zero(),
            total_asset: zero(),
            total_predicate: predicate(),
        },
        notes: std::array::from_fn(|_| disclosure::Opening {
            note: note(),
            asset: zero(),
            address: address(),
        }),
    }
}

fn template(family: Family) -> Witness {
    match family {
        Family::Transfer => {
            let core = || encryption::Core {
                epk: point(),
                c2: zero(),
                confirmation: zero(),
                ciphertext: zero(),
            };
            let extended = || encryption::Extended {
                epk: point(),
                c2: zero(),
                ciphertext: std::array::from_fn(|_| zero()),
            };
            Witness::Transfer(Box::new(transfer::Witness {
                spend_auth: note::SpendAuthorization {
                    randomizer: zero(),
                    rk: point(),
                },
                anchor: zero(),
                asset_anchor: zero(),
                compliance_anchor: zero(),
                asset: zero(),
                regulated: false,
                timestamp: zero(),
                nonce_root: zero(),
                balance_blinding: zero(),
                auth: auth(),
                registry: registry(),
                sender: owner(),
                receiver: owner(),
                spends: [spend(), spend()],
                optional: optional(),
                outputs: [output(), output()],
                volume: volume(),
                encryption: encryption::Witness {
                    ephemeral: std::array::from_fn(|_| zero()),
                    ownership_randomness: std::array::from_fn(|_| zero()),
                    published: encryption::Published {
                        detection: std::array::from_fn(|_| zero()),
                        sender_core: core(),
                        sender_ext: extended(),
                        output_core: core(),
                        output_ext: extended(),
                        metadata: encryption::Metadata {
                            policy: encryption::Policy {
                                ring_id: zero(),
                                policy_id: zero(),
                                resource: zero(),
                                permission: zero(),
                                timestamp: zero(),
                            },
                            audit_epoch: zero(),
                            salts: std::array::from_fn(|_| zero()),
                        },
                        ownership: std::array::from_fn(|_| audit::Ciphertext {
                            r: point(),
                            c: point(),
                        }),
                    },
                },
                routing: routing::Witness {
                    regulated_precision: 0,
                    unregulated_precision: 0,
                    as_of_height: zero(),
                    parameter_set: zero(),
                    tags: [zero(), zero()],
                },
            }))
        }
        Family::ReshapeOneToEight => Witness::Reshape(Box::new(reshape::Witness {
            owner: self_action(),
            notes: reshape::Notes::Split {
                input: spend(),
                outputs: std::array::from_fn(|_| output()),
            },
        })),
        Family::ReshapeEightToOne => Witness::Reshape(Box::new(reshape::Witness {
            owner: self_action(),
            notes: reshape::Notes::Merge {
                inputs: std::array::from_fn(|_| reshape::MergeInput {
                    spend: spend(),
                    padding: optional(),
                }),
                output: output(),
            },
        })),
        Family::Withdrawal => Witness::Withdrawal(Box::new(withdrawal::Witness {
            owner: self_action(),
            timestamp: zero(),
            amount: zero(),
            effect_hash: std::array::from_fn(|_| zero()),
            spends: [spend(), spend()],
            optional: optional(),
            change: output(),
            volume: volume(),
            volume_seed: zero(),
            encryption: withdrawal::EncryptionWitness {
                ciphertext: withdrawal::Ciphertext {
                    epk: point(),
                    c2: zero(),
                    confirmation: zero(),
                    address: std::array::from_fn(|_| zero()),
                },
                randomizer: zero(),
                seed: zero(),
            },
        })),
        Family::Seizure => Witness::Seizure(Box::new(seizure::Witness {
            statement: seizure::Statement {
                anchor: zero(),
                commitment: zero(),
                nullifier: zero(),
                address: address(),
                asset: zero(),
                amount: zero(),
                recovery: capsule(),
                seed: zero(),
                rnk_commitment: zero(),
                authorization: zero(),
            },
            blinding: zero(),
            rnk: zero(),
            path: path(),
        })),
        Family::Disclosure => Witness::Disclosure(Box::new(disclosure_template::<32>())),
        Family::DisclosureOne => Witness::DisclosureOne(Box::new(disclosure_template::<1>())),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fixtures;
    use commonware_math::algebra::Ring;
    #[test]
    fn catalogue_relations_match_all_seven_real_witness_shapes() {
        let p = Parameters::load().unwrap();
        let g = Generators::derive(&p);
        let witnesses = [
            Witness::Transfer(Box::new(
                fixtures::build(&p, &g, &fixtures::load().unwrap()[0]).unwrap(),
            )),
            Witness::Reshape(Box::new(fixtures::reshape(&p, &g, true, None).unwrap())),
            Witness::Reshape(Box::new(fixtures::reshape(&p, &g, true, Some(2)).unwrap())),
            Witness::Withdrawal(Box::new(fixtures::withdrawal(&p, &g, 0).unwrap())),
            Witness::Seizure(Box::new(seizure::tests::fixture(&p))),
            Witness::Disclosure(Box::new(disclosure::tests::fixture(&p, 2, Scalar::one()))),
            Witness::DisclosureOne(Box::new(disclosure::tests::fixture_for_capacity::<1>(
                &p,
                1,
                Scalar::one(),
            ))),
        ];
        let mut digests = std::collections::BTreeSet::new();
        for w in witnesses {
            let family = w.family();
            let compiled = compile(family).unwrap();
            let digest = w.digest(&p, &g).unwrap();
            let (c, selected) = circuit::build(|ctx| w.constrain(ctx, &p, &g, &digest));
            let layout = InputLayout::new(vec![selected[0]], vec![vec![selected[1]]]).unwrap();
            let actual = Relation::compile(&c, &layout).unwrap();
            assert_eq!(
                actual.digest(),
                compiled.relation.digest(),
                "{}",
                family.label()
            );
            assert!(digests.insert(*actual.digest()));
            assert!(evaluate(&w).unwrap().is_satisfied());
            let wrong_digest = digest + &Scalar::one();
            let (invalid, _) =
                circuit::build_with_values(|ctx| w.constrain(ctx, &p, &g, &wrong_digest));
            assert!(!invalid.is_satisfied(), "{} digest binding", family.label());
        }
    }
}

/// The same Transfer build and ordinary compiler entry point as compile().
/// The callback only reads the already-built source program. No witness values,
/// satisfying assignment, setup material, or changed compiler lowering is used.
#[cfg(feature = "formal-observer")]
pub fn inspect_transfer_program<Consume>(mut consume: Consume) -> Result<Compiled>
where
    Consume: FnMut(&circuit::Circuit<Scalar>, &InputLayout) -> Result<()>,
{
    let p = Parameters::load()?;
    let g = Generators::derive(&p);
    let w = template(Family::Transfer);
    let (c, selected) = circuit::build(|ctx| w.constrain(ctx, &p, &g, &Scalar::zero()));
    anyhow::ensure!(selected.len() == 2, "complete Transfer program return roles changed");
    let layout = InputLayout::new(vec![selected[0]], vec![vec![selected[1]]])?;
    consume(&c, &layout)?;
    let relation = Relation::compile(&c, &layout)?;
    Ok(Compiled { family: Family::Transfer, relation, layout })
}
