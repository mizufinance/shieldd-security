
#[cfg(test)]
mod formal_parameter_loader_controls {
    use super::*;

    fn artifact() -> serde_json::Value {
        serde_json::from_str(include_str!("../params/poseidon381-wide.json")).unwrap()
    }

    fn rejected(value: serde_json::Value, reason: &str) {
        let encoded = serde_json::to_string(&value).unwrap();
        let error = Permutation::<6>::load(&encoded).err()
            .expect("expected semantic loader rejection");
        assert_eq!(error.to_string(), reason);
    }

    fn native_values<const N: usize>(value: &serde_json::Value) {
        let loaded = Permutation::<N>::load(&serde_json::to_string(value).unwrap())
            .ok().expect("valid source recipe");
        assert_eq!(loaded.ark.len(), 65);
        for round in 0..65 {
            for column in 0..N {
                assert_eq!(loaded.ark[round][column], field(value["ark"][round][column]
                    .as_str().unwrap()).unwrap());
            }
        }
        for row in 0..N {
            for column in 0..N {
                assert_eq!(loaded.mds[row][column], field(value["mds"][row][column]
                    .as_str().unwrap()).unwrap());
            }
        }
    }

    #[test]
    fn field_hex_length_and_canonicality() {
        assert!(field("zz").is_err());
        for count in [31, 33] {
            let error = field(&"00".repeat(count)).err().unwrap();
            assert_eq!(error.to_string(), "Poseidon field length");
        }
        assert_eq!(field(&"00".repeat(32)).unwrap(), Fq::ZERO);
        let error = field("ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff")
            .err().unwrap();
        assert_eq!(error.to_string(), "noncanonical field element");
    }

    #[test]
    fn exact_row_widths() {
        let zero = "00".repeat(32);
        assert_eq!(row::<3>(&vec![zero.clone(); 3]).unwrap(), [Fq::ZERO; 3]);
        assert_eq!(row::<6>(&vec![zero.clone(); 6]).unwrap(), [Fq::ZERO; 6]);
        for width in [2, 4] {
            assert_eq!(row::<3>(&vec![zero.clone(); width]).err().unwrap().to_string(),
                "Poseidon row width");
        }
        for width in [5, 7] {
            assert_eq!(row::<6>(&vec![zero.clone(); width]).err().unwrap().to_string(),
                "Poseidon row width");
        }
    }

    #[test]
    fn schema_and_json_are_checked() {
        assert!(Permutation::<6>::load("{").is_err());
        let mut value = artifact();
        value["schema"] = "shieldd.poseidon381.v0".into();
        rejected(value, "invalid Poseidon parameter recipe");
        let mut missing = artifact();
        missing.as_object_mut().unwrap().remove("schema");
        assert!(Permutation::<6>::load(&serde_json::to_string(&missing).unwrap()).is_err());
    }

    #[test]
    fn recipe_header_fields_are_checked() {
        for (name, wrong) in [
            ("modulus", serde_json::json!("0")),
            ("alpha", serde_json::json!(3)),
            ("full_rounds", serde_json::json!(7)),
            ("partial_rounds", serde_json::json!(56)),
            ("skip_matrices", serde_json::json!(1)),
        ] {
            let mut value = artifact();
            value[name] = wrong;
            rejected(value, "invalid Poseidon parameter recipe");
        }
    }

    #[test]
    fn ark_height_is_checked() {
        let mut short = artifact();
        short["ark"].as_array_mut().unwrap().pop();
        rejected(short, "invalid Poseidon parameter recipe");
        let mut long = artifact();
        let first = long["ark"][0].clone();
        long["ark"].as_array_mut().unwrap().push(first);
        rejected(long, "invalid Poseidon parameter recipe");
    }

    #[test]
    fn mds_height_is_checked() {
        let mut short = artifact();
        short["mds"].as_array_mut().unwrap().pop();
        rejected(short, "Poseidon MDS height");
        let mut long = artifact();
        let first = long["mds"][0].clone();
        long["mds"].as_array_mut().unwrap().push(first);
        rejected(long, "Poseidon MDS height");
    }

    #[test]
    fn native_collection_preserves_values_order_and_errors() {
        let value = artifact();
        native_values::<6>(&value);
        native_values::<3>(&serde_json::from_str(include_str!("../params/poseidon381.json")).unwrap());
        for table in ["ark", "mds"] {
            let mut noncanonical = artifact();
            noncanonical[table][0][0] = "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff".into();
            rejected(noncanonical, "noncanonical field element");
            let mut narrow = artifact();
            narrow[table][0].as_array_mut().unwrap().pop();
            rejected(narrow, "Poseidon row width");
        }
    }
}
