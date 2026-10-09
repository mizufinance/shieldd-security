// Appended to the exact pinned fee/gas.rs in a fresh diagnostic successor.
// These controls identify native arithmetic behavior; they provide no genuine
// Transfer-proof, transaction-conservation, rollback, or runtime-certification result.
#[cfg(test)]
mod fv_transfer_fee_arithmetic_controls {
    use super::*;

    fn overflow_message(payload: Box<dyn std::any::Any + Send>, operation: &str) {
        let message = payload
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| payload.downcast_ref::<&str>().copied())
            .expect("pricing failure must carry the intended overflow message");
        assert!(message.contains(operation), "unrelated native panic: {message}");
    }

    #[test]
    fn valid_native_price_width_does_not_bound_transfer_product() {
        let params = crate::FeeParameters {
            fixed_gas_prices: GasPrices {
                verification_price: u64::MAX,
                ..GasPrices::default()
            },
        };
        // The real native protobuf decoder calls validate_base_asset_only.
        let decoded = crate::FeeParameters::try_from(pb::FeeParameters::from(params))
            .expect("max-width base-asset price passes the actual native parameter API");
        let gas = Gas {
            // Native transfer_gas_cost = 2 spends + 2 outputs, each verification=1000.
            verification: 4_000,
            ..Gas::zero()
        };
        let exact_product = u128::from(u64::MAX) * u128::from(gas.verification);
        assert!(exact_product > u128::from(u64::MAX));
        match std::panic::catch_unwind(|| decoded.fixed_gas_prices.fee(&gas)) {
            Ok(fee) => {
                let expected = u64::MAX.wrapping_mul(gas.verification) / 1_000;
                assert_eq!(fee.amount().value(), u128::from(expected));
                assert_ne!(fee.amount().value(), exact_product / 1_000);
                eprintln!("native fee pricing mode: wrapped u64 product; mathematical product differs");
            }
            Err(payload) => {
                overflow_message(payload, "attempt to multiply with overflow");
                eprintln!("native fee pricing mode: checked u64 product panic");
            }
        }
    }

    #[test]
    fn native_amount_accumulator_addition_boundary() {
        let maximum = Amount::from(u128::MAX);
        let increment = Amount::from(1u64);
        match std::panic::catch_unwind(|| maximum + increment) {
            Ok(result) => {
                assert_eq!(result.value(), 0);
                eprintln!("native Amount addition mode: wrapped u128 sum");
            }
            Err(payload) => {
                overflow_message(payload, "attempt to add with overflow");
                eprintln!("native Amount addition mode: checked u128 sum panic");
            }
        }
    }
}
