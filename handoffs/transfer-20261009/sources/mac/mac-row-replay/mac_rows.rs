// Diagnostic finite compiled-assignment evidence, never a backend proof.
use super::{Case, legal, build_case, evaluate};
use crate::{catalogue, hash::Parameters, map::Generators, proof::Family, transfer};
use commonware_cryptography::{bls12381::primitives::group::Scalar, zk::pari::Opening};
use commonware_math::algebra::{Additive, Ring};

#[test]
fn mac_actual_pari_transfer_rows_and_assignment_controls() {
    let p = Parameters::load().unwrap();
    let g = Generators::derive(&p);
    let compiled = catalogue::compile(Family::Transfer).unwrap();
    assert_eq!(compiled.relation.public_inputs(), 1);
    assert_eq!(compiled.relation.blocks(), &[1]);
    assert_eq!(compiled.layout.public().len(), 1);
    assert_eq!(compiled.layout.blocks().len(), 1);
    assert_eq!(compiled.layout.blocks()[0].len(), 1);
    let digest = *compiled.relation.digest();
    let mut count = 0;
    for regulated in [false, true] { for external in [false, true] {
      for dummy in [false, true] { for change in [false, true] {
        for fee in [false, true] { for mode in 0..4 {
          let c = Case {regulated, external, dummy, change, fee, mode};
          if !legal(c) {continue;}
          let w = build_case(&p, &g, c);
          let values = evaluate(&p, &g, &w);
          assert!(values.is_satisfied(), "native positive {c:?}");
          let witness = compiled.relation.witness(&values, &compiled.layout,
              vec![Opening::new(Scalar::one())]).expect("exact compiled relation/layout");
          let (assignment, committed_start, assignment_digest, rows, auxiliary) =
              compiled.relation.mac_diagnostic_values(&witness);
          assert_eq!(assignment_digest, digest);
          assert_eq!(assignment.len(), compiled.relation.domain_size());
          assert_eq!(assignment[0], Scalar::one());
          let statement = transfer::statement(&p, &g, &w).unwrap();
          assert_eq!(assignment[1], p.native(transfer::STATEMENT_DOMAIN, &statement.fields()));
          assert_eq!(assignment[committed_start], w.balance_blinding);
          assert!(compiled.relation.mac_diagnostic_replay(&witness, None, false, false),
              "actual PARI rows positive {c:?}");
          for (role, index) in [("constant", 0), ("public_digest", 1),
              ("committed_blinding", committed_start), ("auxiliary", auxiliary)] {
            assert!(!compiled.relation.mac_diagnostic_replay(&witness,
                Some((index, Scalar::one())), false, false), "assignment mutation {role} {c:?}");
            println!("MAC_ROW_REJECT case={count} role={role} index={index}");
          }
          assert!(!compiled.relation.mac_diagnostic_replay(&witness, None, false, true));
          println!("MAC_ROW_REJECT case={count} role=relation_digest");
          // This row-only predicate has no explicit leading-one check. The
          // homogeneous all-zero vector satisfies square rows; it is not a
          // canonical compiler witness or an accepted PARI transaction.
          if count == 0 {
            assert!(compiled.relation.mac_diagnostic_replay(&witness, None, true, false));
            println!("MAC_ROW_SCOPE all_zero_row_vector_accepted constant_one_role_violated");
          }
          assert!(compiled.relation.mac_diagnostic_replay(&witness, None, false, false),
              "diagnostic mutation must not change original witness {c:?}");
          println!("MAC_ROW_POSITIVE case={count} regulated={regulated} external={external} dummy={dummy} change={change} fee={fee} mode={mode} rows={rows} domain={} committed_start={committed_start} auxiliary={auxiliary}", assignment.len());
          count += 1;
        }}
      }}
    }}
    assert_eq!(count, 36);
}

#[test]
fn mac_actual_pari_source_mutations() {
    let p = Parameters::load().unwrap();
    let g = Generators::derive(&p);
    let compiled = catalogue::compile(Family::Transfer).unwrap();
    let fee_case = Case {regulated: false, external: false, dummy: true,
        change: false, fee: true, mode: 0};
    let fee = build_case(&p, &g, fee_case);
    let external_fee = build_case(&p, &g, Case {external: true, ..fee_case});
    let ordinary = Case {regulated: true, external: true, dummy: true,
        change: true, fee: false, mode: 0};
    let padding = build_case(&p, &g, ordinary);
    let mut dummy_bad = padding.clone();
    dummy_bad.spends[1].note.amount = Scalar::one();
    let real = build_case(&p, &g, Case {dummy: false, mode: 3, ..ordinary});
    let mut spend_path_bad = real.clone();
    spend_path_bad.spends[1].path.siblings[0][0] += &Scalar::one();
    let mut successor_bad = real.clone();
    successor_bad.volume.successor_volume += 1;
    let mut predecessor_bad = real.clone();
    predecessor_bad.volume.prior_path.siblings[0][0] += &Scalar::one();
    let cases = [("external_fee", fee, external_fee),
        ("dummy_nonzero", padding, dummy_bad),
        ("optional_real_wrong_path", real.clone(), spend_path_bad),
        ("successor_changed", real.clone(), successor_bad),
        ("predecessor_wrong_path", real, predecessor_bad)];
    for (label, base, bad) in cases {
        let values = evaluate(&p, &g, &base);
        assert!(values.is_satisfied(), "positive native source {label}");
        let witness = compiled.relation.witness(&values, &compiled.layout,
            vec![Opening::new(Scalar::one())]).expect("positive exact relation/layout");
        assert!(compiled.relation.mac_diagnostic_replay(&witness, None, false, false));
        println!("MAC_ROW_SOURCE_POSITIVE {label}");
        let values = evaluate(&p, &g, &bad);
        assert!(!values.is_satisfied(), "negative native source {label}");
        let witness = compiled.relation.witness(&values, &compiled.layout,
            vec![Opening::new(Scalar::one())]).expect("negative exact same relation/layout");
        let (assignment, _, assignment_digest, _, _) =
            compiled.relation.mac_diagnostic_values(&witness);
        assert_eq!(assignment_digest, *compiled.relation.digest());
        assert_eq!(assignment[0], Scalar::one());
        assert!(!compiled.relation.mac_diagnostic_replay(&witness, None, false, false),
            "actual compiled square rows reject native source mutation {label}");
        println!("MAC_ROW_SOURCE_REJECT {label}");
    }
}
