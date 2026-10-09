"""Bounded page certificates for the common full ordinary EPK read frame.

The already emitted native page keeps its own incoming coordinates. Full-loop
composition additionally keeps the first ordinary input and the other five
scopes' scalar/point roles on every later page. Numeric interval checks are
split into blocks of at most128 read columns and one window's writes.
Only exact retained source data reaches this renderer; no row truth is assumed.
"""
from . import generate_transfer_epk_fixed_completion as ingress
from . import generate_transfer_epk_fixed_template as template
from . import transfer_epk_fixed_program as full, transfer_relation as relation
from .generate_hash_round import _signature_audits


def generate(parent, pages, capsules, roles, extracted, scope_id, page_index):
    accepted = full.plan(parent, pages, capsules, roles, extracted, scope_id)
    first, raw_first, normal_first, _, _, first_plan, _ = ingress._selection(
        parent, pages, capsules, roles, extracted['fixed'], scope_id, 0, 1, ())
    initial = template._layout(first, raw_first, normal_first, first_plan, 1)['before']
    incoming = sorted({column for lc in initial for column, _ in lc})
    common = sorted(set(accepted['loop']['kept']))
    checked, raw, normal, _, _, plan, _ = ingress._selection(
        parent, pages, capsules, roles, extracted['fixed'], scope_id,
        page_index, 1 if page_index == 0 else 0, ())
    data = [template._layout(checked, raw, normal, plan, offset)
            for offset, window in enumerate(plan['windows']) if window['index'] != 0]
    if not 1 <= len(data) <= 16:
        raise relation.RelationError('EPK join bounded ordinary page')
    common_blocks = [common[i:i+128] for i in range(0, len(common), 128)]
    if not common_blocks or len(common_blocks) > 32:
        raise relation.RelationError('EPK join bounded common source read frame')
    for item in data:
        for stage in item['stages']:
            writes = ({stage['output'], stage['auxiliary']} if stage['kind'] == 'product'
                      else {stage['quotient'], stage['product'], stage['auxiliary']})
            if writes.intersection(common + incoming):
                raise relation.RelationError('EPK join actual writes alias common or initial input')
    writes = sorted({column for item in data for stage in item['stages']
                     for column in ({stage['output'], stage['auxiliary']} if stage['kind'] == 'product'
                                    else {stage['quotient'], stage['product'], stage['auxiliary']})})
    high_start = accepted['bounds']['high_start']
    low = [c for c in writes if c < high_start]
    high = [c for c in writes if c >= high_start]
    if not low or not high:
        raise relation.RelationError('EPK join exact low and high write regions')
    regions = (min(low), max(low), min(high), max(high))
    outside = lambda c: (c < regions[0] or regions[1] < c) and (c < regions[2] or regions[3] < c)
    if not all(outside(c) for c in common + incoming):
        raise relation.RelationError('EPK join read column crosses actual write region')
    stem = f'RuntimeTransferEpk{scope_id}Fixed'
    page = stem + f'TemplatePage{page_index:02d}Trace'
    ns = stem + f'TemplatePage{page_index:02d}Join'
    bit = lambda i: f'(encodeBits 252 n)[{i}]?.getD false'
    source = f'''import ShielddSecurity.{page}
import ShielddSecurity.GroupFixedReadIntervals
namespace ShielddSecurity.{ns}
set_option maxHeartbeats 400000
set_option maxRecDepth 4096

def regions : GroupFixedReadIntervals.Regions := ⟨{','.join(map(str,regions))}⟩
'''
    for i, block in enumerate(common_blocks):
        source += f'def commonBlock{i} : List Nat := {block}\n'
    source += 'def commonParts : List (List Nat) := [' + ','.join(f'commonBlock{i}' for i in range(len(common_blocks))) + ']\n'
    source += f'''def commonKept : List Nat := commonParts.flatten
def incomingKept : List Nat := {incoming}
def kept : List Nat := commonKept ++ incomingKept

'''
    for i in range(len(common_blocks)):
        source += f'''private theorem common_part{i} : ∀ column ∈ commonBlock{i},
    GroupFixedReadIntervals.Outside regions column := by
  have checked : commonBlock{i}.all
      (fun column => decide (GroupFixedReadIntervals.Outside regions column)) = true := by decide
  intro column member
  exact of_decide_eq_true (List.all_eq_true.mp checked column member)

'''
    source += f'''theorem common_outside : ∀ column ∈ commonKept,
    GroupFixedReadIntervals.Outside regions column := by
  intro column member
  obtain ⟨part,inside,present⟩ := List.mem_flatten.mp member
  simp only [commonParts,List.mem_cons,List.not_mem_nil,or_false] at inside
  rcases inside with {' | '.join('rfl' for _ in common_blocks)}
'''
    for i in range(len(common_blocks)):
        source += f'  · exact common_part{i} column present\n'
    for item in data:
        index=item['index']
        adapter=stem+f'Window{index:03d}TemplateTrace'
        source += f'''
private theorem writes_{index} (low high : Bool) :
    ∀ stage ∈ ({adapter}.window low high).program.stages,
      ∀ column ∈ stage.writes, GroupFixedReadIntervals.Inside regions column := by
  have checked : ({adapter}.window low high).program.stages.all
      (fun stage => stage.writes.all
        (fun column => decide (GroupFixedReadIntervals.Inside regions column))) = true := by
    change ({adapter}.window false false).program.stages.all
      (fun stage => stage.writes.all
        (fun column => decide (GroupFixedReadIntervals.Inside regions column))) = true
    decide
  intro stage present column written
  exact of_decide_eq_true
    (List.all_eq_true.mp (List.all_eq_true.mp checked stage present) column written)
'''
    source += f'''
private theorem program_writes (n : Nat) :
    ∀ program ∈ ({page}.windows n).map GroupFixedTemplateTrace.Window.program,
      ∀ stage ∈ program.stages, ∀ column ∈ stage.writes,
        GroupFixedReadIntervals.Inside regions column := by
  intro program member
  simp only [{page}.windows,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with {' | '.join('rfl' for _ in data)}
'''
    for item in data:
        i=item['index']
        source+=f'  · exact writes_{i} ({bit(2*i)}) ({bit(2*i+1)})\n'
    source += f'''
private theorem incoming_outside : ∀ column ∈ incomingKept,
    GroupFixedReadIntervals.Outside regions column := by
  have checked : incomingKept.all
      (fun column => decide (GroupFixedReadIntervals.Outside regions column)) = true := by decide
  intro column member
  exact of_decide_eq_true (List.all_eq_true.mp checked column member)

theorem incoming_protected (n : Nat) :
    ∀ program ∈ ({page}.windows n).map GroupFixedTemplateTrace.Window.program,
      GroupFixedCircuitCompletion.Protected incomingKept program := by
  intro program member
  exact GroupFixedReadIntervals.protected_reads regions incomingKept program
    incoming_outside (program_writes n program member)

theorem caller_protected (n : Nat) :
    ∀ program ∈ ({page}.windows n).map GroupFixedTemplateTrace.Window.program,
      GroupFixedCircuitCompletion.Protected kept program := by
  intro program member
  apply GroupFixedReadIntervals.protected_reads regions kept program
  · intro column included
    rcases List.mem_append.mp included with common | incoming
    · exact common_outside column common
    · exact incoming_outside column incoming
  · exact program_writes n program member
'''
    for item in data:
        i=item['index'];adapter=stem+f'Window{i:03d}TemplateTrace'
        indices = sorted({j for lc in item['bits'] for c,_ in lc
                          for j,b in enumerate(common_blocks) if c in b})
        if not indices or any(not any(c in common_blocks[j] for j in indices) for lc in item['bits'] for c,_ in lc):
            raise relation.RelationError('EPK join actual bit read missing common frame')
        if len(indices)>2:
            raise relation.RelationError('EPK join bounded actual bit support blocks')
        small=' ++ '.join(f'commonBlock{j}' for j in indices)
        source+=f'''
private theorem bit_support_{i} (low high : Bool) :
    ∀ term ∈ ({adapter}.window low high).program.low ++ ({adapter}.window low high).program.high,
      term.1 ∈ commonKept := by
  have checked : (({adapter}.window low high).program.low ++ ({adapter}.window low high).program.high).all
      (fun term => decide (term.1 ∈ ({small}))) = true := by
    change (({adapter}.window false false).program.low ++ ({adapter}.window false false).program.high).all
      (fun term => decide (term.1 ∈ ({small}))) = true
    decide
  intro term present
  have member := of_decide_eq_true (List.all_eq_true.mp checked term present)
'''
        if len(indices)==2:source+='  rcases List.mem_append.mp member with left | right\n'
        for pos,j in enumerate(indices):
            member='member' if len(indices)==1 else ('left' if pos==0 else 'right')
            prefix='  ' if len(indices)==1 else '  · '
            proof='List.mem_cons_self'
            for _ in range(j):proof='List.mem_cons_of_mem _ ('+proof+')'
            source+=prefix+f'exact List.mem_flatten.mpr ⟨commonBlock{j}, {proof}, {member}⟩\n'
    source+=f'''
theorem bit_supports (n : Nat) :
    ∀ program ∈ ({page}.windows n).map GroupFixedTemplateTrace.Window.program,
      ∀ term ∈ program.low ++ program.high, term.1 ∈ kept := by
  intro program member term present
  apply List.mem_append_left incomingKept
  simp only [{page}.windows,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with {' | '.join('rfl' for _ in data)}
'''
    for item in data:
        i=item['index'];source+=f'  · exact bit_support_{i} ({bit(2*i)}) ({bit(2*i+1)}) term present\n'
    source+=''.join(f'#print axioms {e}\n' for e in ('common_outside','incoming_protected','caller_protected','bit_supports'))
    source+=f'end ShielddSecurity.{ns}\n'
    return ns, _signature_audits(source)
