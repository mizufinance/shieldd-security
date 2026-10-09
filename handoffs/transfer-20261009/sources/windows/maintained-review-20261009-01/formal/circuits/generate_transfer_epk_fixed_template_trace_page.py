"""Actual ordinary EPK page certificates and constructive native trace joins.

The full retained fixed/canonical union is independently reaccepted before any
source emits. Folded window zero, canonical scalar construction, the eight-page
join and six native caller instances remain separate proof obligations.
"""
from . import generate_transfer_epk_fixed_completion as ingress
from . import generate_transfer_epk_fixed_template as template
from . import transfer_epk_fixed_program as full
from . import transfer_relation as relation, transfer_fixed_spend as fixed
from .generate_hash_round import linear, signed, _signature_audits


def generate_modules(parent, pages, capsules, roles, extracted, scope_id, page_index=0):
    accepted = full.plan(parent, pages, capsules, roles, extracted, scope_id)
    first = 1 if page_index == 0 else 0
    checked, raw, normal, _, _, plan, _ = ingress._selection(
        parent, pages, capsules, roles, extracted['fixed'], scope_id, page_index, first, ())
    bounds = accepted['bounds']
    data = [template._layout(checked, raw, normal, plan, offset)
            for offset, window in enumerate(plan['windows']) if window['index'] != 0]
    if not 1 <= len(data) <= 16:
        raise relation.RelationError('EPK trace bounded ordinary page')
    # Ordinary window one consumes the folded prefix output; later pages
    # consume the preceding page output. Preserve those incoming coordinates
    # as well as the original caller columns, and reject every write alias.
    incoming = {column for lc in data[0]['before'] for column, _ in lc}
    kept = sorted(set(plan['kept']) | incoming)
    for item in data:
        if item['copy'] != bounds['constant_copy']:
            raise relation.RelationError('EPK trace exact whole/page constant copy')
        frame = bounds['frames'][item['index']]
        if frame['index'] != item['index']:
            raise relation.RelationError('EPK trace exact original allocation frame')
        for stage in item['stages']:
            writes = ({stage['output'], stage['auxiliary']} if stage['kind'] == 'product'
                      else {stage['quotient'], stage['product'], stage['auxiliary']})
            if writes.intersection(kept):
                raise relation.RelationError('EPK trace original writes alias page incoming/caller bits')
    for previous, current in zip(data, data[1:]):
        if previous['after'] != current['before'] or previous['table'][3] != current['table'][0]:
            raise relation.RelationError('EPK trace exact source point and weighted-table adjacency')
    stem = f'RuntimeTransferEpk{scope_id}Fixed'
    result = []
    for item in data:
        name = stem + f'Window{item["index"]:03d}TemplateTrace'
        result.append((name, _window(item, bounds['frames'][item['index']], bounds, kept, stem)))
    name = stem + f'TemplatePage{page_index:02d}Trace'
    result.append((name, _page(data, bounds, kept, stem, name)))
    return result


def _window(item, frame, bounds, kept, stem):
    name = stem + f'Window{item["index"]:03d}'
    local, program, ns = name+'TemplateCompletion', name+'TemplateProgram', name+'TemplateTrace'
    copy, high = bounds['constant_copy'], bounds['high_start']
    x, y = item['table'][3]
    source = f'''import ShielddSecurity.{program}
import ShielddSecurity.GroupFixedTemplateTrace
import ShielddSecurity.GroupFixedCircuitBounds
namespace ShielddSecurity.{ns}
set_option maxHeartbeats 400000
set_option maxRecDepth 4096

def kept : List Nat := {kept}
def before : GroupFixedCircuitBounds.Frame := ⟨{frame['before']['low']},{frame['before']['high']}⟩
def after : GroupFixedCircuitBounds.Frame := ⟨{frame['after']['low']},{frame['after']['high']}⟩
def window (low high : Bool) : GroupFixedTemplateTrace.Window where
  program := {program}.program low high
  layout := {local}.layout
  products := {local}.products
  x := {local}.x
  y := {local}.y
  nextBase := ⟨{signed(x)},{signed(y)}⟩

theorem checked_rows (low high : Bool) :
    (window low high).Checked {relation.MODULUS} {copy} {signed(fixed.D)} := by
  change (window false false).Checked {relation.MODULUS} {copy} {signed(fixed.D)}
  unfold GroupFixedTemplateTrace.Window.Checked
  decide

theorem checked_table (low high : Bool) :
    (window low high).TableChecked {relation.MODULUS} := by
  change (window false false).TableChecked {relation.MODULUS}
  unfold GroupFixedTemplateTrace.Window.TableChecked
    GroupFixedTableTemplate.xCertificate GroupFixedTableTemplate.yCertificate
  decide

theorem checked_bounds (low high : Bool) :
    (before.low ≤ after.low ∧ before.high ≤ after.high) ∧
      GroupFixedCircuitBounds.RowsCovered {high} {copy} after (window low high).program.rows ∧
      GroupFixedCircuitBounds.WritesOutside {high} {copy} before (window low high).program :=
  GroupFixedCircuitBounds.checked_local {high} {copy} before after (window low high).program (by
    change GroupFixedCircuitBounds.checkLocal {high} {copy} before after (window false false).program = true
    decide)

theorem caller_protected (low high : Bool) :
    GroupFixedCircuitCompletion.Protected kept (window low high).program := by
  have checked : (window false false).program.stages.all
      (fun stage => GroupCircuitOrder.checkOutside kept stage.writes) = true := by decide
  intro stage member column present written
  exact (of_decide_eq_true
    (List.all_eq_true.mp (List.all_eq_true.mp checked stage member) column written)) present

#print axioms checked_rows
#print axioms checked_table
#print axioms checked_bounds
#print axioms caller_protected
end ShielddSecurity.{ns}
'''
    return _signature_audits(source)


def _page(data, bounds, kept, stem, ns):
    names = [stem+f'Window{item["index"]:03d}' for item in data]
    adapters = [name+'TemplateTrace' for name in names]
    copy, high = bounds['constant_copy'], bounds['high_start']
    bit = lambda i: f'(encodeBits 252 n)[{i}]?.getD false'
    win = lambda offset: f'({adapters[offset]}.window ({bit(2*data[offset]["index"])}) ({bit(2*data[offset]["index"]+1)}))'
    input_lcs = data[0]['before']
    base = data[0]['table'][0]
    out = [''.join(f'import ShielddSecurity.{name}\n' for name in adapters),
           f'namespace ShielddSecurity.{ns}\n',
           'set_option maxHeartbeats 500000\nset_option maxRecDepth 4096\n',
           f'def kept : List Nat := {kept}\n',
           f'def input : Linear × Linear := ({linear(input_lcs[0])},{linear(input_lcs[1])})\n',
           f'def base : Group.Point Int := ⟨{signed(base[0])},{signed(base[1])}⟩\n',
           'def windows (n : Nat) : List GroupFixedTemplateTrace.Window := ['+
           ','.join(win(i) for i in range(len(data)))+']\n',
           'def segments (n : Nat) : List (GroupFixedCircuitCompletion.Program × GroupFixedCircuitBounds.Frame) := ['+
           ','.join(f'({win(i)}.program,{adapters[i]}.after)' for i in range(len(data)))+']\n',
           f'''theorem certified_bounds (n : Nat) :
    GroupFixedCircuitBounds.Certified {high} {copy} {adapters[0]}.before (segments n) := by
  unfold segments
''']
    for i, adapter in enumerate(adapters):
        index = data[i]['index']
        out.append(f'  have bounds{i} := {adapter}.checked_bounds ({bit(2*index)}) ({bit(2*index+1)})\n')
        out.append(f'  refine ⟨bounds{i}.1,bounds{i}.2.1,bounds{i}.2.2,?_⟩\n')
    out.append('  trivial\n#print axioms certified_bounds\n')
    out.append(f'''theorem fresh (n : Nat) :
    GroupFixedCircuitCompletion.Fresh [] ((windows n).map GroupFixedTemplateTrace.Window.program) := by
  have result := GroupFixedCircuitBounds.bounded_fresh {high} {copy} {adapters[0]}.before
    [] (segments n) (by intro row member; cases member) (certified_bounds n)
  simpa only [segments,windows,List.map_cons,List.map_nil,Prod.fst] using result
#print axioms fresh

theorem source_aligned (n : Nat) :
    GroupFixedTemplateTrace.Aligned input base (windows n) ∧
    GroupFixedCircuitCompletion.Aligned input ((windows n).map GroupFixedTemplateTrace.Window.program) := by
  constructor <;> repeat constructor
#print axioms source_aligned

theorem checked (n : Nat) : ∀ window ∈ windows n,
    window.Checked {relation.MODULUS} {copy} {signed(fixed.D)} ∧
      window.TableChecked {relation.MODULUS} := by
  intro window member
  simp only [windows,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with {' | '.join('rfl' for _ in data)}
''')
    for item, adapter in zip(data, adapters):
        low, highbit = bit(2*item['index']), bit(2*item['index']+1)
        out.append(f'  · exact ⟨{adapter}.checked_rows ({low}) ({highbit}),{adapter}.checked_table ({low}) ({highbit})⟩\n')
    out.append('#print axioms checked\n')
    out.append(f'''theorem constructors {{F : Type}} [Field F] [CharP F {relation.MODULUS}]
    (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (({signed(fixed.D)} : Int) : F))
    (imaginarySquare : imaginary*imaginary = -1) (n : Nat) :
    ∀ window ∈ windows n,
      GroupFixedCircuitCompletion.LocalConstruct (({signed(fixed.D)} : Int) : F) {copy} window.program := by
  intro window member
  simp only [windows,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with {' | '.join('rfl' for _ in data)}
''')
    for item, name in zip(data, names):
        out.append(f'  · simpa only [{name}TemplateCompletion.layout] using\n'
                   f'      ({name}TemplateProgram.local_constructor four imaginary\n'
                   f'        (by simpa only [{name}TemplateCompletion.layout] using nonSquare)\n'
                   f'        imaginarySquare ({bit(2*item["index"])}) ({bit(2*item["index"]+1)}))\n')
    out.append('#print axioms constructors\n')
    out.append(f'''theorem actual_native_complete {{F : Type}} [Field F] [CharP F {relation.MODULUS}]
    {{J : Type}} [AddCommGroup J] (model : Group.StandardCurveModel J (({signed(fixed.D)} : Int) : F))
    (rho : Nat → F) (n : Nat) (acc generator : J)
    (one : rho 0 = 1) (linked : rho {copy} = rho 0) (four : (4 : F) ≠ 0)
    (imaginary : F) (nonSquare : Group.NoUnitSquare (({signed(fixed.D)} : Int) : F))
    (imaginarySquare : imaginary*imaginary = -1)
    (inputMeaning : GroupFixedCircuitCompletion.point rho input = model.coordinates acc)
    (baseMeaning : GroupFixedWindowTemplate.castPoint base = model.coordinates generator)
    (bits : ∀ program ∈ (windows n).map GroupFixedTemplateTrace.Window.program,
      eval rho program.low = (if program.lowBit then 1 else 0) ∧
      eval rho program.high = (if program.highBit then 1 else 0)) :
    let completed := GroupFixedCircuitCompletion.run rho
      ((windows n).map GroupFixedTemplateTrace.Window.program)
    Satisfies completed (GroupFixedCircuitCompletion.rows
      ((windows n).map GroupFixedTemplateTrace.Window.program)) ∧
    (∀ column ∈ kept, completed column = rho column) ∧
    GroupFixedCircuitCompletion.point completed (GroupFixedTemplateTrace.endpoint input (windows n)) =
      model.coordinates (acc + TransferWindows.digitsValue
        (((windows n).map (fun window => window.witness completed)).map GroupFixedWindows.fixedDigit) • generator) := by
  have protection : ∀ program ∈ (windows n).map GroupFixedTemplateTrace.Window.program,
      GroupFixedCircuitCompletion.Protected kept program := by
    intro program member
    simp only [windows,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with {' | '.join('rfl' for _ in data)}
''')
    for item, adapter in zip(data, adapters):
        out.append(f'    · exact {adapter}.caller_protected ({bit(2*item["index"])}) ({bit(2*item["index"]+1)})\n')
    out.append('''  have inputSupports : ∀ term ∈ input.1 ++ input.2, term.1 ∈ kept := by
    have checked : (input.1 ++ input.2).all (fun term => decide (term.1 ∈ kept)) = true := by decide
    intro term member
    exact of_decide_eq_true (List.all_eq_true.mp checked term member)
  have bitSupports : ∀ program ∈ (windows n).map GroupFixedTemplateTrace.Window.program,
      ∀ term ∈ program.low ++ program.high, term.1 ∈ kept := by
    have checked : ((windows n).map GroupFixedTemplateTrace.Window.program).all
        (fun program => (program.low ++ program.high).all (fun term => decide (term.1 ∈ kept))) = true := by
      change ((windows 0).map GroupFixedTemplateTrace.Window.program).all
        (fun program => (program.low ++ program.high).all (fun term => decide (term.1 ∈ kept))) = true
      decide
    intro program member term present
    exact of_decide_eq_true
      (List.all_eq_true.mp (List.all_eq_true.mp checked program member) term present)
''')
    out.append(f'''  exact GroupFixedTemplateTrace.constructs_native {copy} {signed(fixed.D)} model rho
    (windows n) input base kept acc generator one linked four imaginary nonSquare imaginarySquare
    inputMeaning baseMeaning (constructors four imaginary nonSquare imaginarySquare n)
    protection inputSupports bitSupports (fresh n) (source_aligned n).2 (source_aligned n).1
    (by decide) (by decide) (checked n) bits
#print axioms actual_native_complete
end ShielddSecurity.{ns}
''')
    return _signature_audits(''.join(out))
