"""Reflect canonical ingress into the actual 126-window scalar constructor.

Each narrow page proves only its actual bit meanings. The endpoint constructor
uses those proofs and preserves the explicit common read frame. Preservation
of canonical rows through the later constructors remains a separate join.
"""
from . import transfer_epk_fixed_program as full, transfer_fixed_spend as fixed
from . import transfer_relation as relation
from .generate_hash_round import _signature_audits, signed


def generate_modules(parent, pages, capsules, roles, extracted, scope_id, page):
    accepted = full.plan(parent, pages, capsules, roles, extracted, scope_id)
    if scope_id != 0 or len(accepted['loop']['programs']) != 126 or len(accepted['chunks']) != 8:
        raise relation.RelationError('canonical ingress exact current scope0/eight-page126 source')
    if accepted['scalar']['bit_start'] != 4931 or accepted['bounds']['constant_copy'] != 200692:
        raise relation.RelationError('canonical ingress exact qualified source0 columns')
    if type(page) is not int or not 0 <= page < 8:
        raise relation.RelationError('canonical ingress bounded page required')
    canonical = 'RuntimeTransferEpk0CanonicalCompletion'
    trace = f'RuntimeTransferEpk0FixedTemplatePage{page:02d}Trace'
    ns = f'RuntimeTransferEpk0FixedTemplatePage{page:02d}CanonicalBits'
    start, end = max(1, 16*page), min(126, 16*(page+1))
    source = f'''import ShielddSecurity.{canonical}
import ShielddSecurity.{trace}
namespace ShielddSecurity.{ns}
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
theorem actual_bit_meanings {{F : Type}} [Field F] (base : Nat → F) (n : Nat) :
    ∀ window ∈ {trace}.windows n,
      eval ({canonical}.construct base n) window.program.low = (if window.program.lowBit then 1 else 0) ∧
      eval ({canonical}.construct base n) window.program.high = (if window.program.highBit then 1 else 0) := by
  intro window member
  simp only [{trace}.windows,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with {' | '.join('rfl' for _ in range(start,end))}
'''
    for index in range(start, end):
        source += f'''  · change eval ({canonical}.construct base n) [(4931+{2*index},1)] =
        (if (encodeBits 252 n)[{2*index}]?.getD false then 1 else 0) ∧
        eval ({canonical}.construct base n) [(4931+{2*index+1},1)] =
        (if (encodeBits 252 n)[{2*index+1}]?.getD false then 1 else 0)
    exact ⟨{canonical}.bit_reflection base n {2*index} (by decide),
      {canonical}.bit_reflection base n {2*index+1} (by decide)⟩
'''
    source += f'''#print axioms actual_bit_meanings
end ShielddSecurity.{ns}
'''
    modules = [(ns, _signature_audits(source))]
    if page != 0:
        return modules
    ns = 'RuntimeTransferEpk0FixedTemplateCanonicalIngress'
    ordinary = 'RuntimeTransferEpk0FixedTemplateOrdinaryTrace'
    complete = 'RuntimeTransferEpk0FixedTemplateScalarCompletion'
    prefix = 'RuntimeTransferEpk0FixedWindow000TemplatePrefix'
    first = 'RuntimeTransferEpk0FixedWindow000'
    low, high = '(encodeBits 252 n)[0]?.getD false', '(encodeBits 252 n)[1]?.getD false'
    d = signed(fixed.D)
    imports = '\n'.join(f'import ShielddSecurity.RuntimeTransferEpk0FixedTemplatePage{i:02d}CanonicalBits' for i in range(8))
    kept0 = '(List.mem_append_left _ (by decide))'
    kept_copy = '(by decide)'
    for _ in range(16):
        kept_copy = f'(List.mem_append_right _ {kept_copy})'
    # Preserve the existing bounded append tree, rather than normalizing its
    # thousands of caller columns for each membership proof.
    kept_tree = 'RuntimeTransferEpk0CanonicalOrder.keptPart016'
    for i in reversed(range(16)):
        kept_tree = f'(RuntimeTransferEpk0CanonicalOrder.keptPart{i:03d} ++ {kept_tree})'
    source = f'''{imports}
import ShielddSecurity.{complete}
namespace ShielddSecurity.{ns}
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
theorem ordinary_bit_meanings {{F : Type}} [Field F] (base : Nat → F) (n : Nat) :
    ∀ program ∈ ({ordinary}.windows n).map GroupFixedTemplateTrace.Window.program,
      eval ({canonical}.construct base n) program.low = (if program.lowBit then 1 else 0) ∧
      eval ({canonical}.construct base n) program.high = (if program.highBit then 1 else 0) := by
  intro program member
  obtain ⟨window,inside,rfl⟩ := List.mem_map.mp member
  obtain ⟨page,present,windowMember⟩ := List.mem_flatten.mp inside
  simp only [{ordinary}.pages,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with {' | '.join('rfl' for _ in range(8))}
'''
    for i in range(8):
        source += f'  · exact RuntimeTransferEpk0FixedTemplatePage{i:02d}CanonicalBits.actual_bit_meanings base n window windowMember\n'
    source += f'''
theorem actual_native_scalar_from_canonical {{F : Type}} [Field F] [CharP F {relation.MODULUS}]
    {{J : Type}} [AddCommGroup J] (model : Group.StandardCurveModel J (({d} : Int) : F))
    (rho : Nat → F) (n : Nat) (generator : J) (canonical : n < Scalar.order)
    (meaning : rho 4930 = (n : F)) (one : rho 0 = 1) (linked : rho 200692 = rho 0) (four : (4 : F) ≠ 0)
    (imaginary : F) (nonSquare : Group.NoUnitSquare (({d} : Int) : F))
    (imaginarySquare : imaginary*imaginary = -1)
    (baseMeaning : ({first}.base : Group.Point F) = model.coordinates generator) :
    let ingress := {canonical}.construct rho n
    let firstAssignment := ({prefix}.program ({low}) ({high})).build ingress
    let completed := GroupFixedCircuitCompletion.run firstAssignment
      (({ordinary}.windows n).map GroupFixedTemplateTrace.Window.program)
    Satisfies completed ({first}.rawRows ++ GroupFixedCircuitCompletion.rows
      (({ordinary}.windows n).map GroupFixedTemplateTrace.Window.program)) ∧
    (∀ column, column ∈ {prefix}.kept → column ∈ {ordinary}.kept → completed column = ingress column) ∧
    GroupFixedCircuitCompletion.point completed
      (GroupFixedTemplateTrace.endpoint {ordinary}.input ({ordinary}.windows n)) =
      model.coordinates (n • generator) := by
  have ingress := {canonical}.constructs rho n canonical meaning one four
  have preserve0 := ingress.2.2.2 0 (by change 0 ∈ {kept_tree}; exact {kept0})
  have preserveCopy := ingress.2.2.2 200692 (by change 200692 ∈ {kept_tree}; exact {kept_copy})
  have oneIngress : {canonical}.construct rho n 0 = 1 := preserve0.trans one
  have linkedIngress : {canonical}.construct rho n 200692 = {canonical}.construct rho n 0 :=
    preserveCopy.trans (linked.trans preserve0.symm)
  have width : n < 2^252 := Nat.lt_of_lt_of_le canonical (by decide)
  exact {complete}.actual_native_scalar_complete model ({canonical}.construct rho n) n generator width
    oneIngress linkedIngress four imaginary nonSquare imaginarySquare baseMeaning
    ({canonical}.bit_reflection rho n 0 (by decide))
    ({canonical}.bit_reflection rho n 1 (by decide)) (ordinary_bit_meanings rho n)
#print axioms ordinary_bit_meanings
#print axioms actual_native_scalar_from_canonical
end ShielddSecurity.{ns}
'''
    modules.append((ns, _signature_audits(source)))
    return modules
