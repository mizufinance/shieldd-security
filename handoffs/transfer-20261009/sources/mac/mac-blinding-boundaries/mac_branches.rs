// Independent temporary test module for the pinned circuits crate.
// This file is installed only in a disposable source copy, never the runtime snapshot.
use crate::{catalogue, fixtures, hash::Parameters, map::Generators, proof::Family, transfer};
use commonware_cryptography::{bls12381::primitives::group::Scalar,
    zk::{circuit::{build_with_values, ValuedCircuit}, pari::Opening}};
use commonware_math::algebra::{Additive, Ring};

#[derive(Clone, Copy, Debug)]
struct Case { regulated: bool, external: bool, dummy: bool, change: bool,
    fee: bool, mode: u8 }
// mode: 0 padding; 1 origin; 2 continuation prior 0; 3 continuation prior 5.
fn legal(c: Case) -> bool {
    (!c.fee || !c.external) &&
      (c.mode == 0 || (!c.fee && c.regulated && c.external))
}
fn build_case(p: &Parameters, g: &Generators, c: Case) -> transfer::Witness {
    let mut f = fixtures::load().unwrap()[usize::from(!c.regulated)].clone();
    f.scenario = format!("mac_{c:?}");
    f.same_affine_address = !c.external;
    f.optional_dummy = c.dummy;
    f.inputs = ["100".into(), if c.dummy {"0"} else {"20"}.into()];
    f.outputs = ["25".into(), if c.change {"75"} else {"0"}.into()];
    // The baseline builder still looks up the dummy's inactive path. Reuse the
    // required spend's position; a live second note uses its own distinct slot.
    f.spend_positions = [0, if c.dummy {0} else {1}];
    f.volume.position = 2;
    // Position 0 is needed for padding's unused path lookup by the baseline builder.
    if c.mode <= 1 { f.volume.position = 0; }
    f.volume.use_real = c.mode != 0;
    f.volume.starts_new_day = c.mode <= 1;
    f.volume.prior = if c.mode == 3 {"5"} else {"0"}.into();
    f.volume.successor = match c.mode {0 => "0", 3 => "30", _ => "25"}.into();
    f.registry.daily_limit = "30".into();
    f.volume.context = if c.fee {"2"} else {"1"}.into();
    f.volume.day_start = if c.fee {"0"} else {"86400"}.into();
    let mut w = fixtures::build(p, g, &f).unwrap();
    // The original native fixture builder has no fee branch and emits padding
    // hashes even for context 2. Apply the runtime's canonical fee selection.
    if c.fee {
        w.volume.nullifier = Scalar::zero();
        w.volume.commitment = Scalar::zero();
    }
    w
}
fn evaluate(p: &Parameters, g: &Generators, w: &transfer::Witness) -> ValuedCircuit<Scalar> {
    let statement = transfer::statement(p, g, w).unwrap();
    let digest = p.native(transfer::STATEMENT_DOMAIN, &statement.fields());
    build_with_values(|ctx| transfer::constrain(ctx, p, g, w, &digest)).0
}
fn accepts(p: &Parameters, g: &Generators, w: &transfer::Witness) -> bool {
    evaluate(p, g, w).is_satisfied()
}

#[test]
fn mac_expanded_branch_positive_matrix() {
    let p = Parameters::load().unwrap();
    let g = Generators::derive(&p);
    let compiled = catalogue::compile(Family::Transfer).unwrap();
    let mut count = 0;
    for regulated in [false, true] { for external in [false, true] {
      for dummy in [false, true] { for change in [false, true] {
        for fee in [false, true] { for mode in 0..4 {
          let c = Case {regulated, external, dummy, change, fee, mode};
          if !legal(c) {continue;}
          let w = build_case(&p, &g, c);
          let values = evaluate(&p, &g, &w);
          assert!(values.is_satisfied(), "positive native circuit case {c:?}");
          compiled.relation.witness(&values, &compiled.layout,
              vec![Opening::new(Scalar::one())]).expect("exact canonical Transfer relation/layout");
          println!("MAC_POSITIVE regulated={regulated} external={external} dummy={dummy} change={change} fee={fee} mode={mode}");
          count += 1;
        }}
      }}
    }}
    assert_eq!(count, 36, "complete discrete core matrix census");
}

#[test]
fn mac_expanded_branch_semantic_rejection_controls() {
    let p = Parameters::load().unwrap();
    let g = Generators::derive(&p);
    let base = Case {regulated: false, external: false, dummy: true,
        change: false, fee: true, mode: 0};
    assert!(accepts(&p, &g, &build_case(&p, &g, base)), "positive fee baseline");
    // Unregulated avoids independently flagged encryption when constructing an
    // illegal external fee; all canonical fee payload auxiliaries remain valid.
    assert!(!accepts(&p, &g, &build_case(&p, &g, Case {external: true, ..base})), "external fee gate");
    println!("MAC_NEGATIVE fee_external");
    let ordinary = Case {regulated: true, external: true, dummy: true,
        change: true, fee: false, mode: 0};
    let padding = build_case(&p, &g, ordinary);
    assert!(accepts(&p, &g, &padding), "positive disclosure baseline");
    let mut bad = padding.clone();
    bad.spends[1].note.amount = Scalar::one();
    assert!(!accepts(&p, &g, &bad), "dummy spend must have zero amount");
    println!("MAC_NEGATIVE dummy_nonzero");
    let real = build_case(&p, &g, Case {dummy: false, mode: 3, ..ordinary});
    assert!(accepts(&p, &g, &real), "positive real-input continuation baseline");
    let mut bad = real.clone();
    bad.spends[1].path.siblings[0][0] += &Scalar::one();
    assert!(!accepts(&p, &g, &bad), "real optional spend must authenticate anchor");
    println!("MAC_NEGATIVE real_second_wrong_path");
    let mut bad = real.clone();
    bad.volume.successor_volume += 1;
    assert!(!accepts(&p, &g, &bad), "real accumulator binds exact addition");
    println!("MAC_NEGATIVE real_successor_changed");
    let mut bad = real;
    bad.volume.prior_path.siblings[0][0] += &Scalar::one();
    assert!(!accepts(&p, &g, &bad), "real continuation must authenticate prior anchor");
    println!("MAC_NEGATIVE continuation_wrong_path");
}

#[path = "mac_rows.rs"]
mod row_replay;
