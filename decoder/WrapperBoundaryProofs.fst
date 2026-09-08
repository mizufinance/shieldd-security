module WrapperBoundaryProofs
#set-options "--fuel 16 --ifuel 2 --z3rlimit 200"
open Core_models
module W = Shieldd_sdk_proof_aggregation.Aggregate_proof_wrapper
module Seq = FStar.Seq

let truncated_header_is_rejected
    (bytes:t_Slice u8) (digest:t_Array u8 (mk_usize 32))
  : Lemma
    (requires Seq.length bytes < 73)
    (ensures W.decode_wrapped_aggregate_proof_inner_range bytes digest
      (Core_models.Option.Option_None <: Core_models.Option.t_Option usize)
      == Core_models.Result.Result_Err W.AggregateProofBytesError_MalformedProofBytes)
= WrapperProofs.lemma_wrapper_domain_len ()

let unsupported_domain_is_rejected
    (bytes:t_Slice u8) (digest:t_Array u8 (mk_usize 32))
  : Lemma
    (requires Seq.length bytes >= 73 /\
      not (Core_models.Slice.impl__starts_with #u8 bytes W.v_AGGREGATE_PROOF_WRAPPER_DOMAIN))
    (ensures W.decode_wrapped_aggregate_proof_inner_range bytes digest
      (Core_models.Option.Option_None <: Core_models.Option.t_Option usize)
      == Core_models.Result.Result_Err W.AggregateProofBytesError_BadVersion)
= WrapperProofs.lemma_wrapper_domain_len ()
