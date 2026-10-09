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

#[test]
fn mac_committed_blinding_subgroup_boundaries() {
    use crate::scalar;
    use commonware_codec::Encode;
    use commonware_cryptography::zk::circuit::build_with_values;
    let p = Parameters::load().unwrap();
    let g = Generators::derive(&p);
    let compiled = catalogue::compile(Family::Transfer).unwrap();
    let order = Scalar::from_limbs(scalar::ORDER);
    assert_eq!(hex::encode(order.encode()), "0e7db4ea6533afa906673b0101343b00a6682093ccc81082d0970e5ed6f72cb7");
    assert_eq!(hex::encode((order.clone() + &Scalar::one()).encode()), "0e7db4ea6533afa906673b0101343b00a6682093ccc81082d0970e5ed6f72cb8");
    assert_eq!(hex::encode((-Scalar::one()).encode()), "73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000000");
    let contexts = [
        ("fee_self_padding", Case {regulated:false,external:false,dummy:true,change:false,fee:true,mode:0}),
        ("ordinary_external_padding", Case {regulated:true,external:true,dummy:true,change:false,fee:false,mode:0}),
        ("ordinary_external_continuation", Case {regulated:true,external:true,dummy:false,change:true,fee:false,mode:3})];
    let legal_values = [("zero",Scalar::zero()),("one",Scalar::one()),("order_minus_one",order.clone()-&Scalar::one())];
    let bad_values = [("order",order.clone()),("order_plus_one",order.clone()+&Scalar::one()),("field_minus_one",-Scalar::one())];
    let mut positives=0;let mut raw_controls=0;let mut column_controls=0;
    for (context, case) in contexts {
        for (name, blinding) in &legal_values {
            assert!(*blinding < order);
            let mut w=build_case(&p,&g,case);w.balance_blinding=blinding.clone();
            let statement=transfer::statement(&p,&g,&w).expect("legal native statement");
            let digest=p.native(transfer::STATEMENT_DOMAIN,&statement.fields());
            let values=evaluate(&p,&g,&w);assert!(values.is_satisfied());
            let witness=compiled.relation.witness(&values,&compiled.layout,vec![Opening::new(Scalar::one())]).unwrap();
            let (assignment, committed, assignment_digest, _, _)=compiled.relation.mac_diagnostic_values(&witness);
            assert_eq!(committed,2);assert_eq!(assignment[0],Scalar::one());
            assert_eq!(assignment[1],digest);assert_eq!(assignment[2],*blinding);
            assert_eq!(assignment_digest,*compiled.relation.digest());
            assert!(compiled.relation.mac_diagnostic_replay(&witness,None,false,false));
            println!("MAC_BLIND_POSITIVE context={context} value={name} encoded={}",hex::encode(blinding.encode()));positives+=1;
            for index in [2,9] {
                let (source,touched,failing)=compiled.relation.mac_diagnostic_column_rows(&witness,index,&Scalar::one());
                assert!(!failing.is_empty());assert!(!compiled.relation.mac_diagnostic_replay(&witness,Some((index,Scalar::one())),false,false));
                println!("MAC_BLIND_COLUMN_REJECT context={context} value={name} index={index} source={source} touched={touched:?} failing={failing:?}");column_controls+=1;
            }
        }
        let mut baseline=build_case(&p,&g,case);baseline.balance_blinding=Scalar::one();
        assert!(evaluate(&p,&g,&baseline).is_satisfied());
        let good=compiled.relation.witness(&evaluate(&p,&g,&baseline),&compiled.layout,vec![Opening::new(Scalar::one())]).unwrap();
        assert!(compiled.relation.mac_diagnostic_replay(&good,None,false,false));
        for (name,blinding) in &bad_values {
            assert!(*blinding >= order,"raw circuit-field value is representably out of subgroup range");
            let mut bad=baseline.clone();bad.balance_blinding=blinding.clone();
            assert!(transfer::statement(&p,&g,&bad).is_err(),"native rejects raw noncanonical blinding");
            // A legal reduced witness supplies a concrete public claim. The bad
            // raw circuit-field value remains un-reduced in the constrained witness.
            let mut reference=bad.clone();reference.balance_blinding=scalar::reduce(blinding).remainder;
            let statement=transfer::statement(&p,&g,&reference).unwrap();
            let claimed=p.native(transfer::STATEMENT_DOMAIN,&statement.fields());
            let values=build_with_values(|ctx|transfer::constrain(ctx,&p,&g,&bad,&claimed)).0;
            assert!(!values.is_satisfied());
            let witness=compiled.relation.witness(&values,&compiled.layout,vec![Opening::new(Scalar::one())]).expect("same full relation/layout");
            let (assignment,committed,assignment_digest,_,_)=compiled.relation.mac_diagnostic_values(&witness);
            assert_eq!(assignment[0],Scalar::one());assert_eq!(assignment[1],claimed);assert_eq!(assignment[committed],*blinding);assert_eq!(assignment_digest,*compiled.relation.digest());
            assert!(!compiled.relation.mac_diagnostic_replay(&witness,None,false,false));
            println!("MAC_BLIND_RAW_REJECT context={context} value={name} encoded={}",hex::encode(blinding.encode()));raw_controls+=1;
        }
    }
    assert_eq!((positives,raw_controls,column_controls),(9,9,18));
}
