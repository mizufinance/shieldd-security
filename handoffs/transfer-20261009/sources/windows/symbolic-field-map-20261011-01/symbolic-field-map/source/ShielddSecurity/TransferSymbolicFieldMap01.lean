import ShielddSecurity.TransferScalarCanonicalKey01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferSymbolicFieldMap01
/-! Small polymorphic list-map contracts for the live typed pending-field
codec. Keep encoder and projection symbolic while checking the mapping proof,
then instantiate with the proved source-derived Scalar field constructor.
No concrete field operations unfold in this proof; no native credit. -/

theorem mapped_field_projection_equals_pointwise_reference {Key Field Value : Type}
    (encode : Key → Field) (project : Field → Value) (reference : Key → Value)
    (keys : List Key) (pointwise : ∀ key ∈ keys, project (encode key) = reference key) :
    (keys.map encode).map project = keys.map reference := by
  rw [List.map_map]
  exact List.map_congr_left pointwise

theorem finite_field_list_roundtrip_follows_from_symbolic_pointwise_inverse {Key Field : Type}
    (encode : Key → Field) (project : Field → Key) (keys : List Key)
    (pointwise : ∀ key ∈ keys, project (encode key) = key) :
    (keys.map encode).map project = keys :=
  (mapped_field_projection_equals_pointwise_reference encode project id keys pointwise).trans (List.map_id keys)

set_option pp.all true in
#check @mapped_field_projection_equals_pointwise_reference
#print axioms mapped_field_projection_equals_pointwise_reference
set_option pp.all true in
#check @finite_field_list_roundtrip_follows_from_symbolic_pointwise_inverse
#print axioms finite_field_list_roundtrip_follows_from_symbolic_pointwise_inverse
end ShielddSecurity.TransferSymbolicFieldMap01
