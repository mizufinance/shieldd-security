use commonware_codec::Encode;
use commonware_cryptography::{
    bls12381::primitives::group::Scalar,
    zk::{
        circuit::{CircuitIdx, build},
        pari::{InputLayout, Relation},
    },
};
use commonware_math::algebra::{Additive, Ring};
use serde_json::json;
use shieldd_sdk_circuits::{catalogue, hash::Parameters, map::Generators, proof::Family, transfer};
use std::collections::BTreeSet;

fn main() {
    let catalogue::Witness::Transfer(witness) = catalogue::template(Family::Transfer) else {
        unreachable!()
    };
    let parameters = Parameters::load().unwrap();
    let generators = Generators::derive(&parameters);
    let (circuit, selected) = build(|ctx| {
        let (mut public, observation) =
            transfer::constrain_observed(ctx, &parameters, &generators, &witness, &Scalar::zero());
        let arithmetic = observation.arithmetic;
        assert_eq!(
            observation.output_amount, arithmetic.outbound,
            "actual note/volume caller differs"
        );
        public.extend([
            arithmetic.prior,
            arithmetic.successor,
            arithmetic.outbound,
            arithmetic.limit,
            arithmetic.use_real.into_var(),
            arithmetic.comparison.borrow.into_var(),
            arithmetic.comparison.difference,
        ]);
        for bits in [
            observation.output_amount_bits,
            arithmetic.prior_bits,
            arithmetic.successor_bits,
            arithmetic.candidate_bits,
            arithmetic.limit_bits,
            arithmetic.comparison.difference_bits,
        ] {
            assert_eq!(bits.len(), 128);
            public.extend(bits.into_iter().map(|bit| bit.into_var()));
        }
        public
    });
    // Retained handles are NOT selected as inputs: selection affects compiler fusion.
    let layout = InputLayout::new(vec![selected[0]], vec![vec![selected[1]]]).unwrap();
    let relation = Relation::compile(&circuit, &layout).unwrap();
    let column = |index: CircuitIdx| match index {
        CircuitIdx::Witness(i) => relation
            .witness_column(i)
            .expect("retained original witness"),
        _ => panic!("this observation must be an original witness, not an inlined expression"),
    };
    let columns: Vec<_> = selected[2..].iter().copied().map(column).collect();
    let observed: BTreeSet<u32> = columns.iter().map(|i| *i as u32).collect();
    // Keep relevant exact rows plus zero assertions on their product auxiliaries.
    // The kernel checks emitted arithmetic templates and their implication.
    // Membership in the full runtime relation remains this exporter's trust boundary.
    let mut auxiliaries = BTreeSet::new();
    for (a, b) in relation.constraints() {
        if a.iter().chain(b).any(|(i, _)| observed.contains(i)) {
            auxiliaries.extend(b.iter().map(|(i, _)| *i));
        }
    }
    let rows: Vec<_> = relation
        .constraints()
        .enumerate()
        .filter_map(|(index, (a, b))| {
            let relevant = a
                .iter()
                .chain(b)
                .any(|(i, _)| observed.contains(i) || *i == 0)
                || (b.is_empty() && a.len() == 1 && auxiliaries.contains(&a[0].0));
            if !relevant {
                return None;
            }
            let terms = |xs: &[(u32, Scalar)]| {
                xs.iter()
                    .map(|(i, c)| json!([i, hex::encode(c.encode())]))
                    .collect::<Vec<_>>()
            };
            Some(json!({"index":index,"a":terms(a),"b":terms(b)}))
        })
        .collect();
    println!("{}", serde_json::to_string_pretty(&json!({
        "subject":"actual Transfer amount/volume arithmetic row subset",
        "scalar_encoding":"canonical-big-endian-32", "modulus_minus_one":hex::encode((-Scalar::one()).encode()),
        "relation_digest":hex::encode(relation.digest()), "domain_size":relation.domain_size(),
        "public_inputs":relation.public_inputs(), "committed_blocks":relation.blocks(),
        "row_count":relation.constraints().len(), "layout":format!("{:?}",layout),
        "variables":columns[..7], "bit_columns":columns[7..].chunks(128).collect::<Vec<_>>(), "rows":rows,
    })).unwrap());
}
