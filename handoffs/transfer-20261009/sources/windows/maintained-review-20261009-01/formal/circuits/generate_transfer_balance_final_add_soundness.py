"""Arbitrary-assignment soundness of the genuine captured shared-inverse final add."""
from . import generate_transfer_balance_final_add_completion as completion
from . import transfer_relation as relation
from .generate_hash_round import _signature_audits


def _finish(namespace, source):
    end = 'end ShielddSecurity.' + namespace + '\n'
    if (source.count(end) != 1 or not source.endswith(end) or
            'private theorem endpoint ' not in source or
            'private theorem signed_full ' not in source):
        raise relation.RelationError('final soundness shared-inverse algebraic proof anchors')
    proof = '''
/-- Both row orientations are checked against the actual physical relation.
The copied constant is normalized only after its actual assertion is proved. -/
theorem reverse_rows_checked : expectedRows.all (fun row =>
    Compiler.checkRow modulus (Compiler.unoutlineRows 200692 rawRows) row ||
    Compiler.checkRow modulus (Compiler.unoutlineRows 200692 rawRows)
      ⟨scaleLinear (-1) row.a,row.b⟩) = true := by decide

theorem expected_rows_from_actual {F : Type} [Field F] [CharP F modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    Satisfies rho expectedRows := by
  have normalized := Compiler.unoutline_rows_sound rho 200692 rawRows satisfied (by decide)
  intro row member
  have checked := List.all_eq_true.mp reverse_rows_checked row member
  rcases Bool.or_eq_true.mp checked with direct | reversed
  · exact Compiler.checked_row_sound rho _ row normalized direct
  · have truth := Compiler.checked_row_sound rho _
      ⟨scaleLinear (-1) row.a,row.b⟩ normalized reversed
    simpa only [eval_scale,Int.cast_neg,Int.cast_one,neg_one_mul,
      Square,neg_mul_neg] using truth

/-- No constructed assignment, quotient legality or desired endpoint is a
premise. The equations come from the captured rows of this same assignment. -/
theorem actual_rows_sound {F : Type} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rawRows)
    (sign : Bool) (signValue : eval rho negative = if sign then 1 else 0) :
    outputPoint rho = Group.affineAdd (d : F)
      (GroupSignedPoint.signed sign (unsignedPoint rho)) (blindedPoint rho) := by
  have expected := expected_rows_from_actual rho satisfied
  have result := endpoint rho one expected
  rw [signed_full rho expected sign signValue] at result
  exact result

#print axioms reverse_rows_checked
#print axioms expected_rows_from_actual
#print axioms actual_rows_sound
'''
    return namespace, _signature_audits(source[:-len(end)] + proof + end)


def generate_from_joint(variable_parent, variable_pages, blinding_parent, blinding_pages,
                        caller_parent, caller_page, accepted_roles, signed_value,
                        asset_base, blinding_base, joint):
    if not isinstance(joint, dict) or joint.get('final_add', {}).get('lowering') != 'point_shared_inverse':
        raise relation.RelationError('final soundness requires actual shared-inverse source lowering')
    namespace, source = completion.generate_from_joint(
        variable_parent, variable_pages, blinding_parent, blinding_pages,
        caller_parent, caller_page, accepted_roles, signed_value, asset_base,
        blinding_base, joint, namespace='RuntimeTransferBalanceFinalAddSoundness')
    return _finish(namespace, source)


def render_plan(plan):
    """Neutral renderer for rechecked plans; actual callers must use genuine joint ingress."""
    if not isinstance(plan, dict) or plan.get('lowering') != 'point_shared_inverse':
        raise relation.RelationError('final soundness shared-inverse plan required')
    namespace, source = completion.render_plan(
        plan, namespace='RuntimeTransferBalanceFinalAddSoundness')
    return _finish(namespace, source)
