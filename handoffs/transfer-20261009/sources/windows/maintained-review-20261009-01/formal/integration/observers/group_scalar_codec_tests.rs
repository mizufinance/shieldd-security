//! Test-only source included beneath the pinned SDK `group` module in a fresh
//! diagnostic stage. No production function or frozen stage is changed here.
use super::*;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{BigInteger, PrimeField};

#[test]
fn native_encoded_reader_boundaries_match_independent_group() {
    let powers = [7usize, 8, 63, 64, 251, 254];
    let mut values = vec![
        Scalar::zero(),
        Scalar::one(),
        Scalar::from_limbs(crate::scalar::ORDER) - &Scalar::one(),
        -Scalar::one(),
    ];
    for bit in powers {
        let mut limbs = [0u64; 4];
        limbs[bit / 64] = 1u64 << (bit % 64);
        values.push(Scalar::from_limbs(limbs));
    }
    let coordinate = |value: &Scalar| {
        ark_ed_on_bls12_381::Fq::from_be_bytes_mod_order(value.encode().as_ref())
    };
    let native_base = generator();
    let reference = ark_ed_on_bls12_381::EdwardsAffine::new_unchecked(
        coordinate(&native_base.x),
        coordinate(&native_base.y),
    );
    assert!(reference.is_on_curve());
    assert!(reference.is_in_correct_subgroup_assuming_on_curve());
    for value in values {
        let bytes = value.encode();
        assert_eq!(bytes.len(), 32);
        let integer = coordinate(&value).into_bigint();
        assert!(!integer.get_bit(255));
        for index in 0..255usize {
            let source_bit = bytes[31 - index / 8] >> (index % 8) & 1 == 1;
            assert_eq!(source_bit, integer.get_bit(index), "bit {index}");
        }
        let scalar = ark_ed_on_bls12_381::Fr::from_be_bytes_mod_order(bytes.as_ref());
        let expected = reference.mul_bigint(scalar.into_bigint()).into_affine();
        let actual = native_base.multiply(&value);
        assert_eq!(coordinate(&actual.x), expected.x);
        assert_eq!(coordinate(&actual.y), expected.y);
    }
}
