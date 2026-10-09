"""Derive fixed126 endpoint meaning from arbitrary actual canonical rows."""
from . import transfer_epk_fixed_program as full, transfer_fixed_spend as fixed
from . import transfer_relation as relation
from .generate_hash_round import _signature_audits, signed


def generate_modules(parent, pages, capsules, roles, extracted, scope_id, page):
    accepted = full.plan(parent, pages, capsules, roles, extracted, scope_id)
    if scope_id != 0 or len(accepted['loop']['programs']) != 126 or len(accepted['chunks']) != 8:
        raise relation.RelationError('canonical soundness exact scope0/eight-page126 source')
    if accepted['scalar']['bit_start'] != 4931 or accepted['scalar']['value'] != 4930:
        raise relation.RelationError('canonical soundness exact source scalar and bit columns')
    if accepted['bounds']['constant_copy'] != 200692:
        raise relation.RelationError('canonical soundness exact captured copy column')
    if type(page) is not int or not 0 <= page < 8:
        raise relation.RelationError('canonical soundness bounded page required')
    canonical = 'RuntimeTransferEpk0Canonical'
    reflection = 'TransferEpkCanonicalReflection'
    trace = f'RuntimeTransferEpk0FixedTemplatePage{page:02d}Trace'
    ns = f'RuntimeTransferEpk0FixedTemplatePage{page:02d}CanonicalSoundBits'
    decoded = f'binary ({canonical}.decodedBits rho)'
    start, end = max(1, 16 * page), min(126, 16 * (page + 1))
    source = f'''import ShielddSecurity.{reflection}
import ShielddSecurity.{trace}
namespace ShielddSecurity.{ns}
set_option maxHeartbeats 500000
set_option maxRecDepth 4096

theorem actual_bit_meanings {{F : Type}} [Field F] [CharP F {relation.MODULUS}]
    (rho : Nat → F) (satisfied : Satisfies rho {canonical}.originalRows) :
    ∀ window ∈ {trace}.windows ({decoded}),
      eval rho window.program.low = (if window.program.lowBit then 1 else 0) ∧
      eval rho window.program.high = (if window.program.highBit then 1 else 0) := by
  intro window member
  simp only [{trace}.windows,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with {' | '.join('rfl' for _ in range(start, end))}
'''
    for index in range(start, end):
        source += f'''  · change eval rho [(4931+{2*index},1)] =
        (if (encodeBits 252 ({decoded}))[{2*index}]?.getD false then 1 else 0) ∧
        eval rho [(4931+{2*index+1},1)] =
        (if (encodeBits 252 ({decoded}))[{2*index+1}]?.getD false then 1 else 0)
    exact ⟨{reflection}.source_bit_value rho satisfied {2*index} (by decide),
      {reflection}.source_bit_value rho satisfied {2*index+1} (by decide)⟩
'''
    source += f'''#print axioms actual_bit_meanings
end ShielddSecurity.{ns}
'''
    modules = [(ns, _signature_audits(source))]
    if page != 0:
        return modules
    ns = 'RuntimeTransferEpk0FixedTemplateCanonicalSoundness'
    ordinary = 'RuntimeTransferEpk0FixedTemplateOrdinaryTrace'
    sound = 'RuntimeTransferEpk0FixedTemplateScalarSoundness'
    first = 'RuntimeTransferEpk0FixedWindow000'
    d = signed(fixed.D)
    imports = '\n'.join(f'import ShielddSecurity.RuntimeTransferEpk0FixedTemplatePage{i:02d}CanonicalSoundBits' for i in range(8))
    source = f'''{imports}
import ShielddSecurity.{sound}
namespace ShielddSecurity.{ns}
set_option maxHeartbeats 500000
set_option maxRecDepth 4096

theorem ordinary_bit_meanings {{F : Type}} [Field F] [CharP F {relation.MODULUS}]
    (rho : Nat → F) (satisfied : Satisfies rho {canonical}.originalRows) :
    ∀ window ∈ {ordinary}.windows ({decoded}),
      eval rho window.program.low = (if window.program.lowBit then 1 else 0) ∧
      eval rho window.program.high = (if window.program.highBit then 1 else 0) := by
  intro window member
  obtain ⟨page,present,windowMember⟩ := List.mem_flatten.mp member
  simp only [{ordinary}.pages,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with {' | '.join('rfl' for _ in range(8))}
'''
    for index in range(8):
        source += f'  · exact RuntimeTransferEpk0FixedTemplatePage{index:02d}CanonicalSoundBits.actual_bit_meanings rho satisfied window windowMember\n'
    source += f'''
theorem actual_canonical_and_fixed126_sound {{F : Type}} [Field F] [CharP F {relation.MODULUS}]
    {{J : Type}} [AddCommGroup J] (model : Group.StandardCurveModel J (({d} : Int) : F))
    (rho : Nat → F) (generator : J) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (imaginary : F) (nonSquare : Group.NoUnitSquare (({d} : Int) : F))
    (imaginarySquare : imaginary*imaginary = -1)
    (baseMeaning : ({first}.base : Group.Point F) = model.coordinates generator)
    (satisfied : Satisfies rho ({canonical}.originalRows ++ {sound}.rows ({decoded}))) :
    let n := {decoded}
    n < Scalar.order ∧ (n : F) = eval rho {canonical}.privateValue ∧
      GroupFixedCircuitCompletion.point rho
        (GroupFixedTemplateTrace.endpoint {ordinary}.input ({ordinary}.windows n)) =
        model.coordinates (n • generator) := by
  have canonicalRows : Satisfies rho {canonical}.originalRows := by
    intro row member
    exact satisfied row (List.mem_append_left _ member)
  have fixedRows : Satisfies rho ({sound}.rows ({decoded})) := by
    intro row member
    exact satisfied row (List.mem_append_right _ member)
  have scalar := {canonical}.actual_randomizer_bits rho one four canonicalRows
  have width : {decoded} < 2^252 := Nat.lt_of_lt_of_le scalar.1 (by decide)
  exact ⟨scalar.1,scalar.2,{sound}.actual_native_sound model rho ({decoded}) generator width
    one four imaginary nonSquare imaginarySquare baseMeaning fixedRows
    ({reflection}.source_bit_value rho canonicalRows 0 (by decide))
    ({reflection}.source_bit_value rho canonicalRows 1 (by decide))
    (ordinary_bit_meanings rho canonicalRows)⟩
#print axioms ordinary_bit_meanings
#print axioms actual_canonical_and_fixed126_sound
end ShielddSecurity.{ns}
'''
    modules.append((ns, _signature_audits(source)))
    return modules
