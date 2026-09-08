module CanonicalEncodingProofs
#set-options "--fuel 4 --ifuel 2 --z3rlimit 100"
open Core_models
module C = Shieldd_sdk_proof_aggregation.Canonical_encoding

let accepted_bytes_are_canonical (input encoded:t_Slice u8)
  : Lemma
    (requires C.canonical_encoding_matches input encoded)
    (ensures input == encoded)
= ()

let different_bytes_are_rejected (input encoded:t_Slice u8)
  : Lemma
    (requires input <> encoded)
    (ensures not (C.canonical_encoding_matches input encoded))
= ()

let canonical_bytes_are_accepted (encoded:t_Slice u8)
  : Lemma (C.canonical_encoding_matches encoded encoded)
= ()
