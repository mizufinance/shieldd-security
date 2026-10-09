//! Deferred native Transfer branch tests: one genuine proof per invocation.
//! Supplements the pinned six fixtures without changing them or wallet code.
use anyhow::{bail, ensure, Context, Result};
use commonware_codec::Encode;
use commonware_cryptography::bls12381::primitives::group::Scalar;
use commonware_parallel::Sequential;
use shieldd_sdk_circuits::{catalogue, fixtures, hash::Parameters, map::Generators,
    proof::{Envelope, Family}, routing, transfer};
use shieldd_sdk_proof_params::pari::Registry;

const CASES: [&str; 17] = [
    "real_second", "self_transfer", "fee_funding", "zero_change",
    "nonzero_continuation", "outbound_one", "amount_max", "routing_zero",
    "routing_full", "routing_mixed_unregulated", "permutation_zero",
    "permutation_one", "day_first", "day_last_second", "day_next", "position_max",
    "amount_sum_max",
];

fn facts(name: &str) -> Result<fixtures::Facts> {
    ensure!(CASES.contains(&name), "unknown branch case");
    let all = fixtures::load()?;
    let mut f = all[0].clone();
    f.scenario = format!("formal_branch_{name}");
    match name {
        "real_second" | "position_max" => {
            f.optional_dummy = false;
            f.inputs = ["100".into(), "40".into()];
            f.outputs = ["25".into(), "115".into()];
            f.spend_positions = [0, 1];
            if name == "position_max" {
                f.spend_positions = [(1u64 << 48) - 2, (1u64 << 48) - 1];
                f.volume.position = f.spend_positions[0]; // unused path is still native/valid
                f.sender_position = (1u64 << 32) - 2;
                f.receiver_position = (1u64 << 32) - 1;
                f.registry.position = (1u64 << 32) - 1;
            }
        }
        "self_transfer" | "fee_funding" => {
            f.same_affine_address = true;
            f.volume.use_real = false;
            f.volume.successor = "0".into();
            if name == "fee_funding" { f.volume.context = "2".into(); }
        }
        "zero_change" => {
            f.outputs = ["100".into(), "0".into()];
            f.volume.successor = "100".into();
            f.registry.daily_limit = "100".into();
        }
        "nonzero_continuation" => {
            f.volume.starts_new_day = false;
            f.volume.position = 2;
            f.volume.prior = "5".into();
            f.volume.successor = "30".into();
            f.registry.daily_limit = "30".into();
        }
        "outbound_one" => {
            f.outputs = ["1".into(), "99".into()];
            f.volume.successor = "1".into();
            f.registry.daily_limit = "1".into();
        }
        "amount_max" | "routing_mixed_unregulated" => {
            // Preserve the native unregulated registry interval/selected generators.
            f = all[1].clone();
            f.scenario = format!("formal_branch_{name}");
            let total = if name == "amount_max" { u128::MAX } else { 100 };
            f.inputs = [total.to_string(), "0".into()];
            f.outputs = [total.to_string(), "0".into()];
            if name == "routing_mixed_unregulated" {
                f.regulated_precision = 0;
                f.unregulated_precision = 32;
            }
        }
        "amount_sum_max" => {
            f = all[1].clone();
            f.scenario = format!("formal_branch_{name}");
            f.optional_dummy = false;
            f.spend_positions = [0, 1];
            f.inputs = [u128::MAX.to_string(), u128::MAX.to_string()];
            f.outputs = f.inputs.clone();
        }
        "routing_zero" => { f.regulated_precision = 0; f.unregulated_precision = 0; }
        "routing_full" => { f.regulated_precision = 32; f.unregulated_precision = 32; }
        "permutation_zero" | "permutation_one" => {}
        "day_first" => { f.timestamp = "1".into(); f.volume.day_start = "0".into(); }
        "day_last_second" => { f.timestamp = "86399".into(); f.volume.day_start = "0".into(); }
        "day_next" => { f.timestamp = "86400".into(); f.volume.day_start = "86400".into(); }
        _ => bail!("unknown branch case"),
    }
    Ok(f)
}

fn permutation(p: &Parameters, w: &transfer::Witness) -> bool {
    let word = p.native(shieldd_sdk_crypto::domains::ROUTE_PERMUTATION,
        &[w.nonce_root.clone()]).encode();
    word[31] & 1 == 1
}

fn witness(name: &str, p: &Parameters, g: &Generators)
    -> Result<(fixtures::Facts, transfer::Witness)> {
    let mut f = facts(name)?;
    let wanted = match name { "permutation_zero" => Some(false),
        "permutation_one" => Some(true), _ => None };
    for seed in 0..32u8 {
        // A finite native search, never a manually supplied swap flag.
        if wanted.is_some() { f.seed = [seed; 32]; }
        let mut w = fixtures::build(p, g, &f).context("native fixture construction")?;
        if name == "fee_funding" {
            // The pinned fixture computes Ordinary volume regardless of context.
            // Native selected_payload(FeeFunding) returns canonical_fee_funding():
            // NF=0, commitment=0, day=0; encrypted-state bytes are App-level only.
            ensure!(w.volume.proof_context == 2 && !w.volume.use_real
                && f.same_affine_address, "FeeFunding native preconditions");
            w.volume.nullifier = Scalar::from(0);
            w.volume.commitment = Scalar::from(0);
            w.volume.day_start = Scalar::from(0);
        }
        if wanted.is_none_or(|v| permutation(p, &w) == v) { return Ok((f, w)); }
    }
    bail!("bounded native permutation search exhausted; no coverage result")
}

fn main() -> Result<()> {
    let arguments = std::env::args().skip(1).collect::<Vec<_>>();
    ensure!(arguments.len() == 2,
        "usage: transfer_branch_matrix COMPLETE_REGISTRY05 EXACT_CASE");
    let name = arguments[1].as_str();
    ensure!(CASES.contains(&name), "unknown branch case");
    let p = Parameters::load()?;
    let g = Generators::derive(&p);
    let (f, w) = witness(name, &p, &g)?;
    let outbound = transfer::amount(&w.outputs[0].note.amount)?;
    let change = transfer::amount(&w.outputs[1].note.amount)?;
    let input0 = transfer::amount(&w.spends[0].note.amount)?;
    let input1 = transfer::amount(&w.spends[1].note.amount)?;
    // Compare full129-bit sums independently: low word plus the carry bit.
    // Two native128-bit notes can sum above u128MAX without field wrap.
    let input_sum = input0.overflowing_add(input1);
    let output_sum = outbound.overflowing_add(change);
    ensure!(input_sum == output_sum,
        "independent native amount sum mismatch");
    ensure!(outbound > 0 && (w.optional.is_dummy == f.optional_dummy), "native branch mismatch");
    if !w.optional.is_dummy {
        ensure!(input1 > 0 && w.spends[0].path.position != w.spends[1].path.position
            && w.spends[0].nullifier != w.spends[1].nullifier, "real second spend collapsed");
    }
    let same = transfer::address_fields(&w.sender.leaf.address)
        == transfer::address_fields(&w.receiver.leaf.address);
    ensure!(same == f.same_affine_address, "native address branch mismatch");
    let ordinary = w.volume.proof_context == 1;
    let eligible = ordinary && w.regulated && !same;
    ensure!(!w.volume.use_real || eligible, "ineligible native real volume");
    if w.volume.use_real {
        ensure!(w.volume.prior_volume.checked_add(outbound) == Some(w.volume.successor_volume),
            "native accumulator successor mismatch");
    }
    let timestamp = f.timestamp.parse::<u64>()?;
    ensure!(w.volume.timestamp_day_index == timestamp / 86400
        && w.volume.timestamp_second == timestamp % 86400, "native timestamp mismatch");
    ensure!(w.volume.day_start == Scalar::from(if ordinary { timestamp / 86400 * 86400 } else { 0 }),
        "native selected day mismatch");
    if !ordinary {
        ensure!(w.volume.nullifier == Scalar::from(0)
            && w.volume.commitment == Scalar::from(0), "native FeeFunding volume is not canonical");
    }
    let routed = routing::build_tags(&p, w.regulated, change != 0,
        &w.sender.leaf.address.transmission, &w.receiver.leaf.address.transmission,
        &w.nonce_root, f.regulated_precision, f.unregulated_precision,
        Scalar::from(f.routing_height))?;
    ensure!(routed.tags == w.routing.tags && routed.parameter_set == w.routing.parameter_set,
        "native routing construction mismatch");
    // Independent native API boundary controls; these are not rejected proof controls.
    for (rp, up) in [(33, 33), (8, 7)] {
        let error = routing::build_tags(&p, w.regulated, change != 0,
            &w.sender.leaf.address.transmission, &w.receiver.leaf.address.transmission,
            &w.nonce_root, rp, up, Scalar::from(1)).err()
            .context("invalid native routing precision unexpectedly accepted")?;
        ensure!(error.to_string().contains("routing precision"), "wrong native boundary error: {error:#}");
    }
    let error = transfer::amount(&Scalar::from_limbs([0, 0, 1, 0])).err()
        .context("2^128 native amount unexpectedly accepted")?;
    ensure!(error.to_string().contains("amount exceeds u128"), "wrong native amount error: {error:#}");
    let observed = serde_json::json!({
        "case": name, "optional_dummy": w.optional.is_dummy, "same_address": same,
        "regulated": w.regulated, "proof_context": w.volume.proof_context,
        "eligible": eligible, "flagged": eligible && !w.volume.use_real,
        "use_real": w.volume.use_real, "starts_new_day": w.volume.starts_new_day,
        "prior": w.volume.prior_volume.to_string(), "successor": w.volume.successor_volume.to_string(),
        "input0": input0.to_string(), "input1": input1.to_string(), "outbound": outbound.to_string(),
        "input_sum_low": input_sum.0.to_string(), "input_sum_carry": input_sum.1,
        "output_sum_low": output_sum.0.to_string(), "output_sum_carry": output_sum.1,
        "change": change.to_string(), "sender_meaningful": w.regulated || change != 0,
        "permutation": permutation(&p, &w), "regulated_precision": f.regulated_precision,
        "unregulated_precision": f.unregulated_precision, "timestamp": timestamp,
        "day_index": w.volume.timestamp_day_index, "second": w.volume.timestamp_second,
        "selected_day": transfer::amount(&w.volume.day_start)?.to_string(),
        "spend_positions": [transfer::amount(&w.spends[0].path.position)?.to_string(),
            transfer::amount(&w.spends[1].path.position)?.to_string()],
        "sender_position": transfer::amount(&w.sender.path.position)?.to_string(),
        "receiver_position": transfer::amount(&w.receiver.path.position)?.to_string(),
        "registry_position": transfer::amount(&w.registry.path.position)?.to_string(),
        "prior_position": transfer::amount(&w.volume.prior_path.position)?.to_string(),
        "volume_nullifier_zero": w.volume.nullifier == Scalar::from(0),
        "volume_commitment_zero": w.volume.commitment == Scalar::from(0),
        "statement_fields": transfer::statement(&p, &g, &w)?.fields().len(),
    });
    let native = catalogue::Witness::Transfer(Box::new(w));
    let digest = native.digest(&p, &g)?;
    // Loader success is not PK validation: this genuine prove also decodes/checks
    // the current complete Transfer PK and its embedded VK through the native API.
    let registry = Registry::load(&arguments[0]).context("complete registry load")?;
    let envelope = registry.prove(&native, &Sequential).context("genuine native Transfer prove")?;
    let decoded = Envelope::from_bytes(&envelope.to_bytes()).context("native envelope roundtrip")?;
    registry.verify(Family::Transfer, &digest, &decoded).context("genuine native Transfer verify")?;
    println!("BRANCH_GENUINE_PASS {observed}");
    Ok(())
}
