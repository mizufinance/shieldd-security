"""Actual Boolean/low-bit parity rows from independently computed native seeds.

This is three original assertions only. QR/rational/cofactor assertions and the
native sqrt/codec implementation joins are explicit remaining obligations.
"""
from . import transfer_asset_map as maps,transfer_asset_map_completion as completion
from . import transfer_asset_map_native_seed_completion as seeds
from . import transfer_relation as relation
from .transfer_balance_rows import canonical,combine


def plan(data,extracted,accepted_roles):
    result=seeds.plan(data,extracted,accepted_roles);recipe=result['recipe']
    choice=result['other']['choice'];zero=result['other']['zero'];bit=result['bits'][0]
    expected=[(((choice,1),),((choice,1),)),(((zero,1),),((zero,1),)),
              (combine(((bit,1),),((choice,1),),-1),())]
    indices=[]
    for left,right in expected:
        matches=[index for index,(a,b) in recipe['normalized'].items()
                 if b==right and a in (left,canonical((c,-n) for c,n in left))]
        if len(matches)!=1:raise relation.RelationError('native seed assertion exact original row match')
        indices.append(matches[0])
    if len(set(indices))!=3 or set(indices)&set(recipe['material_rows']):
        raise relation.RelationError('native seed assertions original allocation separation')
    return dict(seeds=result,expected=expected,indices=indices,
                raw={i:recipe['raw'][i] for i in indices})


def construct(data,extracted,accepted_roles,base,sqrt):
    result=plan(data,extracted,accepted_roles)
    built=completion.construct(data,extracted,accepted_roles,base,sqrt)
    rho=built['assignment']
    value=lambda lc:sum(rho.get(c,0)*n for c,n in lc)%maps.P
    if any(value(a)**2%maps.P!=value(b) for a,b in result['raw'].values()):
        raise relation.RelationError('native seed Boolean/parity original assertion failed')
    return dict(assignment=rho,plan=result,proof=False,
                scope='three actual Boolean/parity assertions only; full map/Transfer open')


def generate(data,extracted,accepted_roles):
    from .generate_hash_round import linear,_signature_audits
    result=plan(data,extracted,accepted_roles);seed=result['seeds'];recipe=seed['recipe']
    choice=seed['other']['choice'];zero=seed['other']['zero'];start=seed['bits'][0]
    copy=recipe['checked']['metadata']['constant_copy'];name='RuntimeTransferAssetMapSeedAssertions'
    native='RuntimeTransferAssetMapNativeSeeds';numeric='RuntimeTransferAssetMapNumericConstruction'
    bits='RuntimeTransferAssetMapNativeBits'
    source=f'''import ShielddSecurity.{native}
import ShielddSecurity.CompilerSignedCompletion
set_option maxHeartbeats 250000
set_option maxRecDepth 2048
namespace ShielddSecurity.{name}
-- Exact actual metadata SHA256 {recipe['checked']['metadata_sha256']}.
-- Three native Boolean/parity assertions; no desired satisfaction/value premise.
abbrev modulus := {native}.modulus
def originalRowIndices : List Nat := {result['indices']}
def rawRows : List Row := [
'''+',\n'.join('⟨'+linear(a)+','+linear(b)+'⟩' for a,b in result['raw'].values())+''']
def expectedRows : List Row := [
'''+',\n'.join('⟨'+linear(a)+','+linear(b)+'⟩' for a,b in result['expected'])+f''']
variable {{F : Type}} [Field F] [CharP F modulus] [DecidableEq F]

theorem bit0_value (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) :
    {native}.completeAssignment codec api rho {start} =
      if codec.decode ({native}.nativeY codec api rho) % 2 = 1 then 1 else 0 := by
  unfold {native}.completeAssignment
  rw [{numeric}.seed_values _ {start} (by decide)]
  unfold {native}.seedAssignment {bits}.completeAssignment
  have inside : {start} ≤ {start} ∧ {start} < {start} +
      (encodeBits 255 (codec.decode ({native}.nativeY codec api rho))).length := by
    simp only [encodeBits_length]
    omega
  rw [writeBits,if_pos inside]
  change (if decide (codec.decode ({native}.nativeY codec api rho) % 2 = 1) then (1 : F) else 0) = _
  simp only [decide_eq_true_eq]

theorem choice_boolean (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) :
    Square ({native}.completeAssignment codec api rho {choice})
      ({native}.completeAssignment codec api rho {choice}) := by
  rw [{native}.final_choice_value]
  cases option : {native}.nativeChoice api rho <;> simp only [option,Bool.false_eq_true,if_true,if_false,Square,one_mul,zero_mul]

theorem zero_boolean (codec : TransferReduction.CanonicalField F)
    (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) :
    Square ({native}.completeAssignment codec api rho {zero})
      ({native}.completeAssignment codec api rho {zero}) := by
  rw [{native}.final_zero_value]
  by_cases exceptional : {native}.nativeRationalDenominator codec api rho = 0
  · simp only [if_pos exceptional,Square,one_mul]
  · simp only [if_neg exceptional,Square,zero_mul]

theorem parity_value [Fintype F] (cardinality : Fintype.card F = modulus)
    (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) :
    {native}.completeAssignment codec api rho {start} =
      {native}.completeAssignment codec api rho {choice} := by
  rw [bit0_value,{native}.final_choice_value]
  have parity := ({native}.selected_square_parity cardinality codec api rho).2
  rw [parity]
  cases option : {native}.nativeChoice api rho <;> simp only [option,Bool.false_eq_true,if_false,if_true,Nat.zero_ne_one]

theorem expected_complete [Fintype F] (cardinality : Fintype.card F = modulus)
    (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F) :
    Satisfies ({native}.completeAssignment codec api rho) expectedRows := by
  intro row member
  simp only [expectedRows,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · simpa only [eval,Int.cast_one,one_mul,add_zero] using choice_boolean codec api rho
  · simpa only [eval,Int.cast_one,one_mul,add_zero] using zero_boolean codec api rho
  · have parity := parity_value cardinality codec api rho
    simp only [eval,Int.cast_one,Int.cast_neg,one_mul,neg_one_mul,add_zero,Square,parity]
    ring

theorem coverage_checked : rawRows.all (fun actual => expectedRows.any (fun expected => decide (
    (Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a ∨
     Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus (scaleLinear (-1) expected.a)) ∧
    Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b))) = true := by decide

theorem coverage : ∀ actual ∈ rawRows, ∃ expected ∈ expectedRows,
    (Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a ∨
     Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus (scaleLinear (-1) expected.a)) ∧
    Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b := by
  intro actual member
  obtain ⟨expected,present,equations⟩ := List.any_eq_true.mp (List.all_eq_true.mp coverage_checked actual member)
  exact ⟨expected,present,of_decide_eq_true equations⟩

theorem complete_rows [Fintype F] (cardinality : Fintype.card F = modulus)
    (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F) (rho : Nat → F)
    (linked : rho {copy} = rho 0) : Satisfies ({native}.completeAssignment codec api rho) rawRows := by
  have finalLink : {native}.completeAssignment codec api rho {copy} = {native}.completeAssignment codec api rho 0 := by
    unfold {native}.completeAssignment
    rw [{numeric}.preserves _ {copy} (by decide),{numeric}.preserves _ 0 (by decide),
      {native}.preserves codec api rho {copy} (by decide) (by decide) (by decide),
      {native}.preserves codec api rho 0 (by decide) (by decide) (by decide),linked]
  exact CompilerSignedCompletion.original_rows ({native}.completeAssignment codec api rho)
    expectedRows rawRows {copy} finalLink (expected_complete cardinality codec api rho) coverage
'''
    exports=['bit0_value','choice_boolean','zero_boolean','parity_value','expected_complete',
             'coverage_checked','coverage','complete_rows']
    source+=''.join('#print axioms '+export+'\n' for export in exports)
    return name,_signature_audits(source+'end ShielddSecurity.'+name+'\n')
