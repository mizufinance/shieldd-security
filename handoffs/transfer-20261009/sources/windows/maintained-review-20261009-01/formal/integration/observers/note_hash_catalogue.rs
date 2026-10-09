// Include inside catalogue.rs in a NEW diagnostic stage only.
#[cfg(feature = "formal-observer")]
pub struct NoteHashInspection {
    pub compiled: Compiled,
    pub spends: crate::note::spend_inspection::Report,
    pub hash: crate::hash::note_inspection::Report,
    pub selected: Vec<circuit::CircuitIdx>,
    pub expressions: Vec<Vec<(u32, Scalar)>>,
    pub constant_copy: u32,
    pub nodes: Vec<(u32, bool, circuit::CircuitIdx, circuit::CircuitIdx)>,
}
#[cfg(feature = "formal-observer")]
pub fn inspect_transfer_note_hash(
    slot: usize,
    role: crate::hash::note_inspection::Role,
    block: usize,
) -> Result<NoteHashInspection> {
    let _hash_capture = crate::hash::note_inspection::begin(slot, role, block)?;
    let _spend_capture = crate::note::spend_inspection::begin()?;
    let p = Parameters::load()?;
    let g = Generators::derive(&p);
    let w = template(Family::Transfer);
    let (c, returned) = circuit::build(|ctx| w.constrain(ctx, &p, &g, &Scalar::zero()));
    anyhow::ensure!(returned.len() == 2, "Transfer return roles changed");
    let layout = InputLayout::new(vec![returned[0]], vec![vec![returned[1]]])?;
    let spends = crate::note::spend_inspection::take()?;
    let hash = crate::hash::note_inspection::take()?;
    validate_note_hash_roles(&spends, &hash)?;
    let (selected, nodes) = note_hash_page_cone(&c, &spends, &hash)?;
    let (relation, expressions, constant_copy) =
        Relation::compile_inspected(&c, &layout, &selected)?;
    Ok(NoteHashInspection {
        compiled: Compiled {
            family: Family::Transfer,
            relation,
            layout,
        },
        spends,
        hash,
        selected,
        expressions,
        constant_copy,
        nodes,
    })
}

#[cfg(feature = "formal-observer")]
fn validate_note_hash_roles(
    spends: &crate::note::spend_inspection::Report,
    hash: &crate::hash::note_inspection::Report,
) -> Result<()> {
    use crate::{hash::note_inspection::Role, scalar::inspection::Observed};
    let slot = hash.slot;
    let role = hash.role;
    let spend = &spends.spends[slot];
    match role {
        Role::Commitment => anyhow::ensure!(
            hash.inputs.as_slice() == spend.note && hash.output == spend.commitment,
            "note commitment source roles changed"
        ),
        Role::Nullifier => anyhow::ensure!(
            hash.inputs
                == vec![
                    spend.shared.nk.clone(),
                    spend.commitment.clone(),
                    spend.position.clone()
                ]
                && hash.output == spend.real_nullifier,
            "note real-nullifier source roles changed"
        ),
        Role::Dummy => {
            let optional = spend
                .optional
                .as_ref()
                .ok_or_else(|| anyhow::anyhow!("missing optional spend"))?;
            anyhow::ensure!(
                hash.inputs
                    == vec![
                        optional.seed.clone(),
                        spend.shared.randomizer.clone(),
                        Observed::Native(Scalar::from(1u64))
                    ]
                    && hash.output == optional.synthetic,
                "note dummy-nullifier source roles changed"
            );
        }
        Role::StateLevel(level) => {
            anyhow::ensure!(
                hash.inputs[0] == Observed::Native(Scalar::from(level as u64 + 1)),
                "state level domain prefix changed"
            );
            if level == 23 {
                anyhow::ensure!(
                    hash.output == spend.computed_anchor,
                    "final input-note tree output source changed"
                );
            }
        }
    }
    Ok(())
}
#[cfg(feature = "formal-observer")]
fn note_hash_page_cone(
    c: &circuit::Circuit<Scalar>,
    spends: &crate::note::spend_inspection::Report,
    hash: &crate::hash::note_inspection::Report,
) -> Result<(
    Vec<circuit::CircuitIdx>,
    Vec<(u32, bool, circuit::CircuitIdx, circuit::CircuitIdx)>,
)> {
    use crate::scalar::inspection::Observed;
    use circuit::CircuitIdx;
    use std::collections::BTreeSet;
    let block = hash.block;
    let permutation = &hash.blocks[block];
    let roots: BTreeSet<_> = permutation
        .before
        .iter()
        .filter_map(|value| match value {
            Observed::Source(index) => Some(*index),
            Observed::Native(_) => None,
        })
        .collect();
    let mut selected: BTreeSet<_> = spends.selected().into_iter().collect();
    selected.extend(&roots);
    for value in hash
        .inputs
        .iter()
        .chain(std::iter::once(&hash.output))
        .chain(
            hash.blocks
                .iter()
                .flat_map(|b| b.before.iter().chain(b.after.iter())),
        )
    {
        if let Observed::Source(index) = value {
            selected.insert(*index);
        }
    }
    let mut pending: Vec<_> = permutation
        .after
        .iter()
        .filter_map(|value| match value {
            Observed::Source(index) => Some(*index),
            Observed::Native(_) => None,
        })
        .collect();
    let mut visited = BTreeSet::new();
    let mut nodes = Vec::new();
    while let Some(index) = pending.pop() {
        if !visited.insert(index) || roots.contains(&index) {
            continue;
        }
        anyhow::ensure!(
            visited.len() <= 16384,
            "note permutation cone exceeds 16384"
        );
        match index {
            CircuitIdx::Node(node) => {
                let (multiply, left, right) = c
                    .inspect_node(node)
                    .ok_or_else(|| anyhow::anyhow!("invalid note permutation node"))?;
                nodes.push((node, multiply, left, right));
                if multiply
                    && !matches!(left, CircuitIdx::Constant(_))
                    && !matches!(right, CircuitIdx::Constant(_))
                {
                    selected.extend([index, left, right]);
                }
                pending.extend([left, right]);
            }
            CircuitIdx::Constant(_) => {
                selected.insert(index);
            }
            CircuitIdx::Witness(_) => anyhow::bail!("undeclared note permutation witness"),
        }
    }
    nodes.sort_by_key(|node| node.0);
    let selected: Vec<_> = selected.into_iter().collect();
    anyhow::ensure!(
        selected.len() <= 4096,
        "note permutation LC selection exceeds 4096"
    );
    Ok((selected, nodes))
}
