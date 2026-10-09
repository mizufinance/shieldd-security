//! Ordinary baseline or one bounded native legal-branch replay. No setup/proof.
use commonware_codec::Encode;
use commonware_cryptography::{
    bls12381::primitives::group::Scalar,
    zk::{circuit, pari},
};
use commonware_math::algebra::Additive;
use serde_json::{json, Value};
// Reuse the exact native fixture constructor through the same checkout as the
// SDK dependency. Its `crate::` module paths resolve to these SDK reexports.
// This does not copy or modify runtime fixture source or export a runtime API.
pub use shieldd_sdk_circuits::*;
// Fresh SDK example stage only:
// cargo rustc -p shieldd-sdk-circuits --locked --profile ci --features formal-observer
//   --example transfer-baseline -- --cfg shieldd_formal_example
//   --check-cfg 'cfg(shieldd_formal_example)'
// The cfg applies to this example target only, preserving dependency builds.
#[cfg(shieldd_formal_example)]
#[path = "../src/fixtures.rs"]
mod fixtures;
#[cfg(not(shieldd_formal_example))]
#[path = "../../../.work/shieldd-current/crates/crypto/circuits/src/fixtures.rs"]
mod fixtures;

const PIN: &str = "844389ee069e1fb2e576708842d0b389b4d9a44a";
const RELATION: &str = "16e7b009b763be55ca21f423f4f97e8c132b40b6adbcd06f6a3be17f2d0ef236";

struct BranchCase {
    name: String,
    facts: fixtures::Facts,
    canonical_fee: bool,
}

fn branch_cases() -> anyhow::Result<Vec<BranchCase>> {
    let ordinary = fixtures::load()?;
    anyhow::ensure!(
        ordinary.len() == 6,
        "native fixture scenario catalogue changed"
    );
    let mut cases = ordinary
        .iter()
        .cloned()
        .map(|facts| BranchCase {
            name: facts.scenario.clone(),
            facts,
            canonical_fee: false,
        })
        .collect::<Vec<_>>();
    let mut add = |name: &str, mut facts: fixtures::Facts, canonical_fee| {
        facts.scenario = name.to_string();
        cases.push(BranchCase {
            name: name.to_string(),
            facts,
            canonical_fee,
        });
    };
    let mut real_second = ordinary[0].clone();
    real_second.inputs = ["60".into(), "40".into()];
    real_second.optional_dummy = false;
    real_second.spend_positions = [0, 1];
    add("real-second-input", real_second, false);

    let mut regulated_self = ordinary[0].clone();
    regulated_self.same_affine_address = true;
    regulated_self.receiver_position = regulated_self.sender_position;
    regulated_self.volume.use_real = false;
    regulated_self.volume.successor = "0".into();
    add("regulated-self-transfer", regulated_self.clone(), false);
    let mut unregulated_self = ordinary[1].clone();
    unregulated_self.same_affine_address = true;
    unregulated_self.receiver_position = unregulated_self.sender_position;
    add("unregulated-self-transfer", unregulated_self, false);
    let mut fee = regulated_self;
    fee.volume.context = "2".into();
    fee.volume.day_start = "0".into();
    fee.volume.starts_new_day = false;
    fee.volume.prior = "0".into();
    fee.volume.successor = "0".into();
    add("fee-funding-self-transfer", fee, true);

    let mut zero_change = ordinary[0].clone();
    zero_change.outputs = ["100".into(), "0".into()];
    zero_change.registry.daily_limit = "100".into();
    zero_change.volume.successor = "100".into();
    add("regulated-zero-change", zero_change, false);
    let mut zero_change = ordinary[1].clone();
    zero_change.outputs = ["100".into(), "0".into()];
    add("unregulated-zero-change", zero_change, false);

    let mut continuation = ordinary[5].clone();
    continuation.volume.prior = "11".into();
    continuation.volume.successor = "36".into();
    continuation.registry.daily_limit = "36".into();
    add("nonzero-volume-continuation", continuation, false);

    let mut minimum = ordinary[1].clone();
    minimum.outputs = ["1".into(), "99".into()];
    add("receiver-amount-one", minimum, false);
    let mut maximum = ordinary[1].clone();
    maximum.inputs = [u128::MAX.to_string(), "0".into()];
    maximum.outputs = [u128::MAX.to_string(), "0".into()];
    maximum.registry.daily_limit = u128::MAX.to_string();
    add("receiver-amount-u128-max", maximum.clone(), false);
    maximum.inputs = [u128::MAX.to_string(), u128::MAX.to_string()];
    maximum.outputs = [u128::MAX.to_string(), u128::MAX.to_string()];
    maximum.optional_dummy = false;
    maximum.spend_positions = [0, 1];
    add("two-real-inputs-u128-max", maximum, false);

    for (name, regulated, unregulated) in [
        ("routing-zero-bits", 0, 0),
        ("routing-full-32-bits", 32, 32),
        ("routing-mixed-zero-32-bits", 0, 32),
    ] {
        let mut routing = ordinary[0].clone();
        routing.regulated_precision = regulated;
        routing.unregulated_precision = unregulated;
        add(name, routing, false);
    }
    Ok(cases)
}

fn facts_summary(case: &BranchCase) -> Value {
    let f = &case.facts;
    json!({
        "name": case.name, "seed": hex::encode(f.seed), "asset": f.asset,
        "regulated": f.regulated, "inputs": f.inputs, "outputs": f.outputs,
        "optional_dummy": f.optional_dummy, "same_affine_address": f.same_affine_address,
        "spend_positions": f.spend_positions, "sender_position": f.sender_position,
        "receiver_position": f.receiver_position, "timestamp": f.timestamp,
        "regulated_precision": f.regulated_precision, "unregulated_precision": f.unregulated_precision,
        "routing_height": f.routing_height, "daily_limit": f.registry.daily_limit,
        "volume": {"use_real": f.volume.use_real, "starts_new_day": f.volume.starts_new_day,
          "day_start": f.volume.day_start, "context": f.volume.context, "prior": f.volume.prior,
          "successor": f.volume.successor, "position": f.volume.position},
        "canonical_fee_adapter": case.canonical_fee
    })
}

fn build_case(
    p: &hash::Parameters,
    g: &map::Generators,
    case: &BranchCase,
) -> anyhow::Result<transfer::Witness> {
    let mut witness = fixtures::build(p, g, &case.facts)?;
    if case.canonical_fee {
        anyhow::ensure!(
            case.facts.same_affine_address
                && !case.facts.volume.use_real
                && witness.volume.proof_context == 2
                && witness.volume.day_start == Scalar::zero(),
            "canonical fee adapter requires a disabled self-transfer fee slot"
        );
        // Pinned native VolumeAccumulatorPayload::canonical_fee_funding at
        // crates/core/component/shielded-pool/src/volume_accumulator.rs:175:
        // nullifier=0, commitment=0, day_start=0, encrypted_state all zero.
        // The 64-field circuit statement contains the first three of these;
        // native payload encryption/state reachability is outside this replay.
        // fixtures::build already rebuilt notes, recovery, audit encryption,
        // routing and all trees natively for the self-transfer and zero day.
        witness.volume.nullifier = Scalar::zero();
        witness.volume.commitment = Scalar::zero();
    }
    Ok(witness)
}

#[cfg(feature = "formal-observer")]
fn run_branch(case: &BranchCase) -> anyhow::Result<()> {
    let compiled = catalogue::compile(proof::Family::Transfer)?;
    anyhow::ensure!(
        hex::encode(compiled.relation.digest()) == RELATION,
        "baseline does not match exact selected relation"
    );
    anyhow::ensure!(
        compiled.relation.public_inputs() == 1
            && compiled.relation.blocks() == [1]
            && compiled.layout.public().len() == 1
            && compiled.layout.blocks().len() == 1
            && compiled.layout.blocks()[0].len() == 1
            && compiled.relation.inspect_committed_start() == 2,
        "Transfer public/committed layout changed"
    );
    let p = hash::Parameters::load()?;
    let g = map::Generators::derive(&p);
    let witness = build_case(&p, &g, case)?;
    let fields = transfer::statement(&p, &g, &witness)?.fields();
    anyhow::ensure!(
        fields.len() == 64 && transfer::STATEMENT_FIELDS == 64,
        "complete Transfer statement must contain exactly 64 fields"
    );
    let digest = p.native(transfer::STATEMENT_DOMAIN, &fields);
    let (valued, selected_values) =
        circuit::build_with_values(|ctx| transfer::constrain(ctx, &p, &g, &witness, &digest));
    anyhow::ensure!(
        valued.is_satisfied(),
        "native legal branch is unsatisfied: {}",
        case.name
    );
    anyhow::ensure!(
        selected_values.len() == 2,
        "Transfer selected arity changed"
    );
    anyhow::ensure!(
        valued[selected_values[0]] == digest
            && valued[selected_values[1]] == witness.balance_blinding,
        "statement/committed native values differ from selected source roles"
    );
    let (source, selected) =
        circuit::build(|ctx| transfer::constrain(ctx, &p, &g, &witness, &digest));
    anyhow::ensure!(
        selected == selected_values,
        "valued/source selected role handles changed"
    );
    let layout = pari::InputLayout::new(vec![selected[0]], vec![vec![selected[1]]])?;
    let branch_relation = pari::Relation::compile(&source, &layout)?;
    drop(source);
    anyhow::ensure!(
        layout == compiled.layout
            && branch_relation.digest() == compiled.relation.digest()
            && branch_relation.domain_size() == compiled.relation.domain_size()
            && branch_relation.public_inputs() == compiled.relation.public_inputs()
            && branch_relation.blocks() == compiled.relation.blocks()
            && branch_relation.inspect_committed_start()
                == compiled.relation.inspect_committed_start()
            && branch_relation.inspect_rows().len() == compiled.relation.inspect_rows().len(),
        "legal branch changed relation/layout identity"
    );
    for (row, (branch, ordinary)) in branch_relation
        .inspect_rows()
        .zip(compiled.relation.inspect_rows())
        .enumerate()
    {
        anyhow::ensure!(
            branch == ordinary,
            "full ordered relation row mismatch at {row}"
        );
    }
    // Exercises exact upstream source-fingerprint/layout validation. The zero
    // opening is diagnostic only; no setup, commitment, or proof is generated.
    let _assignment = compiled.relation.witness(
        &valued,
        &compiled.layout,
        vec![pari::Opening::new(Scalar::zero())],
    )?;
    let index = |value: &circuit::CircuitIdx| match value {
        circuit::CircuitIdx::Constant(i) => json!([0, i]),
        circuit::CircuitIdx::Witness(i) => json!([1, i]),
        circuit::CircuitIdx::Node(i) => json!([2, i]),
    };
    println!(
        "{}",
        json!({
            "schema": "shieldd-transfer-legal-branch-replay-v1", "case": facts_summary(case),
            "target_shieldd_pin": PIN, "relation_digest": RELATION,
            "domain_size": compiled.relation.domain_size(), "stored_rows": compiled.relation.inspect_rows().len(),
            "public_inputs": 1, "committed_blocks": [1], "committed_columns": [[2]],
            "source_public": compiled.layout.public().iter().map(index).collect::<Vec<_>>(),
            "source_blocks": compiled.layout.blocks().iter().map(|b| b.iter().map(index).collect::<Vec<_>>()).collect::<Vec<_>>(),
            "statement_fields": fields.iter().map(|v| hex::encode(v.encode())).collect::<Vec<_>>(),
            "public_values": [hex::encode(digest.encode())],
            "committed_values": [[hex::encode(witness.balance_blinding.encode())]],
            "native_witness_satisfied": true, "full_ordered_relation_rows_equal": true,
            "source_fingerprint_witness_compilation": true,
            "scope": "runtime circuit legal-branch testing only; full formal completeness and transaction/state reachability open"
        })
    );
    Ok(())
}

fn main() -> anyhow::Result<()> {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    if args == ["branch-list"] {
        println!(
            "{}",
            json!({"schema": "shieldd-transfer-legal-branch-catalogue-v1",
            "cases": branch_cases()?.iter().map(facts_summary).collect::<Vec<_>>(),
            "scope": "construction plan only; no runtime satisfaction or reachability result"})
        );
        return Ok(());
    }
    if args.len() == 2 && args[0] == "branches" {
        let cases = branch_cases()?;
        let case = cases
            .iter()
            .find(|case| case.name == args[1])
            .ok_or_else(|| anyhow::anyhow!("unknown branch case; inspect branch-list"))?;
        #[cfg(feature = "formal-observer")]
        return run_branch(case);
        #[cfg(not(feature = "formal-observer"))]
        anyhow::bail!("branches mode requires matching formal-observer SDK/Commonware source");
    }
    anyhow::ensure!(
        args.is_empty(),
        "expected no arguments, branch-list, or branches <exact-case>"
    );
    let compiled = catalogue::compile(proof::Family::Transfer)?;
    println!(
        "{}",
        json!({
            "relation_digest": hex::encode(compiled.relation.digest()),
            "domain_size": compiled.relation.domain_size(),
            "public_inputs": compiled.relation.public_inputs(),
            "committed_blocks": compiled.relation.blocks(),
            "layout": format!("{:?}", compiled.layout),
        })
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn matrix_has_distinct_typed_constructions_and_fee_is_self_disabled() {
        let cases = branch_cases().unwrap();
        let names = cases
            .iter()
            .map(|case| &case.name)
            .collect::<std::collections::BTreeSet<_>>();
        assert_eq!(names.len(), cases.len());
        let fee = cases.iter().find(|case| case.canonical_fee).unwrap();
        assert!(fee.facts.same_affine_address);
        assert!(!fee.facts.volume.use_real);
        assert_eq!(fee.facts.volume.context, "2");
        assert_eq!(fee.facts.volume.day_start, "0");
        for case in &cases {
            let f = &case.facts;
            assert!(
                f.regulated_precision <= f.unregulated_precision && f.unregulated_precision <= 32
            );
            assert_ne!(f.outputs[0].parse::<u128>().unwrap(), 0);
            if !f.optional_dummy {
                assert_ne!(f.spend_positions[0], f.spend_positions[1]);
            }
            if f.volume.use_real {
                assert!(f.regulated && !f.same_affine_address);
                let prior = f.volume.prior.parse::<u128>().unwrap();
                let outbound = f.outputs[0].parse::<u128>().unwrap();
                let successor = f.volume.successor.parse::<u128>().unwrap();
                assert_eq!(prior.checked_add(outbound), Some(successor));
                assert!(successor <= f.registry.daily_limit.parse::<u128>().unwrap());
            }
        }
        let continuation = cases
            .iter()
            .find(|case| case.name == "nonzero-volume-continuation")
            .unwrap();
        assert!(!continuation.facts.volume.starts_new_day);
        assert_ne!(continuation.facts.volume.prior, "0");
        assert_ne!(
            continuation.facts.volume.position,
            continuation.facts.spend_positions[0]
        );
    }
}
