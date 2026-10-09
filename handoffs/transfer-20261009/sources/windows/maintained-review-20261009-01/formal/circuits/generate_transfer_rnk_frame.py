"""Bounded support candidates on existing RNK Data declarations.

This consumes maintained Data source after its independent actual row replay.
Hashes bind dependencies only; every support theorem checks the actual imported
row expressions. No source acceptance, row satisfaction or evidence is emitted.
"""
import hashlib
import re
from .transfer_relation import RelationError


def generate_hash_data_coverage(data_module, data_source, *, origin, copy, frame, chunk_size=5):
    if (not isinstance(data_module,str) or not re.fullmatch(r'(RuntimeRnkHash[0-2]|RuntimeIvkHash)_Data',data_module) or
            not isinstance(data_source,bytes) or len(data_source)>10*2**20):
        raise RelationError('bounded existing RNK Data source required')
    if (type(origin) is not int or type(copy) is not int or not 0<origin<copy or
            not isinstance(frame,(tuple,list)) or len(frame)!=2 or
            any(type(c) is not int or not 0<c<copy for c in frame) or
            not 0<frame[0]<=origin<frame[1] or type(chunk_size) is not int or not 1<=chunk_size<=5):
        raise RelationError('RNK frame/source chunk bounds')
    try:text=data_source.decode('utf8')
    except UnicodeError as error:raise RelationError('RNK Data encoding') from error
    namespaces=re.findall(r'^namespace ShielddSecurity\.([A-Za-z0-9_]+)\s*$',text,re.MULTILINE)
    expected=('RuntimeHashBlock_authorization_ivk_0' if data_module=='RuntimeIvkHash_Data' else
        'RuntimeHashBlock_authorization_rnk_permutation'+data_module[len('RuntimeRnkHash')]+'_0')
    if namespaces!=[expected] or not text.rstrip().endswith('end ShielddSecurity.'+expected):
        raise RelationError('exact existing RNK Data namespace')
    declarations='def rawRoundRows : Nat → List Row := fun index => match index with'
    whole='def rawRows : List Row := (List.range 65).flatMap rawRoundRows'
    if text.count(declarations)!=1 or text.count(whole)!=1:
        raise RelationError('existing RNK round/whole Data declarations')
    section=text.split(declarations,1)[1].split(whole,1)[0]
    cases=[int(x) for x in re.findall(r'^\s*\| ([0-9]+) =>',section,re.MULTILINE)]
    if cases!=list(range(65)) or section.count('| _ => []')!=1:
        raise RelationError('complete ordered65 RNK round declarations')
    prefix=data_module.removesuffix('_Data')+'_Frame'
    groups=[list(range(start,min(start+chunk_size,65))) for start in range(0,65,chunk_size)]
    modules={};digest=hashlib.sha256(data_source).hexdigest()
    header=lambda name:f'''import ShielddSecurity.CompilerFrameCoverage
import ShielddSecurity.{data_module}
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
-- Existing maintained Data dependency SHA256: {digest}
-- Support only; actual replay and Rust/source interpretation are separate.
def frame : GroupFixedCircuitBounds.Frame := ⟨{frame[0]},{frame[1]}⟩
'''
    audit=lambda name:f'''set_option pp.all true in
#check @{name}
#print axioms {name}
'''
    for number,group in enumerate(groups):
        name=prefix+f'{number:02d}'
        source=header(name)
        source+=f'def indices : List Nat := {group}\ndef rows : List Row := indices.flatMap Data.rawRoundRows\n'
        for index in group:
            source+=f'''private theorem round{index:02d} : GroupFixedCircuitBounds.RowsCovered {origin} {copy} frame
    (Data.rawRoundRows {index}) := CompilerFrameCoverage.checked_rows {origin} {copy} frame _ (by decide)
'''
        source+=f'''theorem rows_covered : GroupFixedCircuitBounds.RowsCovered {origin} {copy} frame rows := by
  apply CompilerFrameCoverage.flat_map_rows
  intro index member
  simp only [indices,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at member
  rcases member with '''+' | '.join('rfl' for _ in group)+'\n'
        source+=''.join(f'  · exact round{index:02d}\n' for index in group)
        modules[name]=(source+audit('rows_covered')+'end ShielddSecurity.'+name+'\n').replace('Data.',expected+'.')
    name=prefix+'All'
    source=''.join('import ShielddSecurity.'+prefix+f'{i:02d}\n' for i in range(len(groups)))+header(name)
    source+=f'def groups : List (List Nat) := {groups}\n'
    source+=f'''theorem all_rows_covered : GroupFixedCircuitBounds.RowsCovered {origin} {copy} frame Data.rawRows := by
  have joined : List.range 65 = groups.foldr List.append [] := by decide
  rw [Data.rawRows,joined,CompilerFrameCoverage.grouped_flat_map]
  apply CompilerFrameCoverage.flat_map_rows
  intro part member
  simp only [groups,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at member
  rcases member with '''+' | '.join('rfl' for _ in groups)+'\n'
    for i in range(len(groups)):
        source+=f'  · exact {prefix}{i:02d}.rows_covered\n'
    modules[name]=(source+audit('all_rows_covered')+'end ShielddSecurity.'+name+'\n').replace('Data.',expected+'.')
    return modules


def generate_ownership_window_coverage(data_module,data_source,*,origin,copy,frame):
    """Check the imported actual window rawRows, including first-table cones.

    The enclosing replay/freeze retains that module's actual extraction and
    qualified proof dependencies separately. This certificate uses no assumed
    row values and does not reconstruct or qualify the source module.
    """
    if (not isinstance(data_module,str) or not re.fullmatch(r'RuntimeOwnershipWindow[0-9]{3}',data_module)
            or int(data_module[-3:])>=126 or not isinstance(data_source,bytes) or len(data_source)>2**20):
        raise RelationError('bounded existing ownership window source required')
    if (type(origin) is not int or type(copy) is not int or not 0<origin<copy or
            not isinstance(frame,(tuple,list)) or len(frame)!=2 or
            any(type(c) is not int or not 0<c<copy for c in frame) or not 0<frame[0]<=origin<frame[1]):
        raise RelationError('ownership frame bounds')
    try:text=data_source.decode('utf8')
    except UnicodeError as error:raise RelationError('ownership source encoding') from error
    start='namespace ShielddSecurity.'+data_module+'\n'
    end='end ShielddSecurity.'+data_module+'\n'
    if text.count(start)!=1 or text.count(end)!=1:
        raise RelationError('exact ownership main namespace')
    body=text.split(start,1)[1].split(end,1)[0]
    if body.count('def rawRows : List Row :=')!=1:
        raise RelationError('exact ownership main rawRows declaration')
    name=data_module+'_Frame'
    source=f'''import ShielddSecurity.CompilerFrameCoverage
import ShielddSecurity.{data_module}
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
-- Existing actual-row module dependency SHA256: {hashlib.sha256(data_source).hexdigest()}
-- Pointwise support only; actual replay/dependency kernel qualification separate.
def frame : GroupFixedCircuitBounds.Frame := ⟨{frame[0]},{frame[1]}⟩
theorem rows_covered : GroupFixedCircuitBounds.RowsCovered {origin} {copy} frame {data_module}.rawRows :=
  CompilerFrameCoverage.checked_rows {origin} {copy} frame _ (by decide)
set_option pp.all true in
#check @rows_covered
#print axioms rows_covered
end ShielddSecurity.{name}
'''
    return {name:source}


def generate_declared_rows_coverage(data_module,data_source,*,declarations,origin,copy,frame):
    """Small named original-row blocks from the retained IVK reduction modules."""
    allowed={'RuntimeTransferQuotient','RuntimeTransferRemainderData','RuntimeTransferTerminalData'}
    if (not isinstance(data_module,str) or data_module not in allowed or not isinstance(data_source,bytes) or len(data_source)>2**20 or
            not isinstance(declarations,list) or not 1<=len(declarations)<=32 or
            any(not isinstance(name,str) or not re.fullmatch(r'originalRows|c[0-9]+Raw',name) for name in declarations)
            or len(set(declarations))!=len(declarations)):
        raise RelationError('bounded original IVK row declarations required')
    if (type(origin) is not int or type(copy) is not int or not 0<origin<copy or
            not isinstance(frame,(tuple,list)) or len(frame)!=2 or
            any(type(c) is not int or not 0<c<copy for c in frame) or not 0<frame[0]<=origin<frame[1]):
        raise RelationError('IVK original-row frame bounds')
    try:text=data_source.decode('utf8')
    except UnicodeError as error:raise RelationError('IVK row source encoding') from error
    if (re.findall(r'^namespace ShielddSecurity\.([A-Za-z0-9_]+)\s*$',text,re.MULTILINE)!=[data_module]
            or not text.rstrip().endswith('end ShielddSecurity.'+data_module)):
        raise RelationError('IVK original-row namespace')
    modules={}
    for declaration in declarations:
        if text.count('def '+declaration+' : List Row :=')!=1:
            raise RelationError('IVK original row declaration absent or ambiguous')
        name=data_module+'_Frame_'+declaration
        modules[name]=f'''import ShielddSecurity.CompilerFrameCoverage
import ShielddSecurity.{data_module}
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
-- Existing actual-row Data dependency SHA256: {hashlib.sha256(data_source).hexdigest()}
def frame : GroupFixedCircuitBounds.Frame := ⟨{frame[0]},{frame[1]}⟩
theorem rows_covered : GroupFixedCircuitBounds.RowsCovered {origin} {copy} frame {data_module}.{declaration} :=
  CompilerFrameCoverage.checked_rows {origin} {copy} frame _ (by decide)
set_option pp.all true in
#check @rows_covered
#print axioms rows_covered
end ShielddSecurity.{name}
'''
    return modules


def generate_aggregate_coverage(specifications,*,origin,copy,frame):
    """Package checked imported row blocks without a wide row membership walk."""
    if (not isinstance(specifications,list) or not 1<=len(specifications)<=256 or
            type(origin) is not int or type(copy) is not int or not 0<origin<copy or
            not isinstance(frame,(tuple,list)) or len(frame)!=2 or
            any(type(c) is not int or not 0<c<copy for c in frame) or not 0<frame[0]<=origin<frame[1]):
        raise RelationError('bounded actual prior-row aggregate')
    required={'proof_module','rows','proof'}
    for spec in specifications:
        if not isinstance(spec,dict) or set(spec)!=required or any(not isinstance(value,str) or
                not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*(\.[A-Za-z][A-Za-z0-9_]*)*',value) for value in spec.values()):
            raise RelationError('typed imported row/proof names')
        if not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',spec['proof_module']):
            raise RelationError('one exact imported proof module')
    name='RuntimeTransferRkEarlierRows'
    imports=sorted({spec['proof_module'] for spec in specifications})
    source='import ShielddSecurity.CompilerFrameCoverage\n'+''.join(
        'import ShielddSecurity.'+module+'\n' for module in imports)
    source+=f'''set_option maxHeartbeats 300000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
def frame : GroupFixedCircuitBounds.Frame := ⟨{frame[0]},{frame[1]}⟩
def blocks : List (CompilerFrameCoverage.CoveredBlock {origin} {copy} frame) := [
'''+',\n'.join('  ⟨'+spec['rows']+','+spec['proof']+'⟩' for spec in specifications)+']\n'
    source+=f'''def rows : List Row := blocks.flatMap (fun block => block.rows)
theorem rows_covered : GroupFixedCircuitBounds.RowsCovered {origin} {copy} frame rows :=
  CompilerFrameCoverage.flat_map_rows {origin} {copy} frame blocks (fun block => block.rows)
    (by intro block member; exact block.covered)
set_option pp.all true in
#check @rows_covered
#print axioms rows_covered
end ShielddSecurity.{name}
'''
    return {name:source}


def extend_rk_support(base_source,*,prior_frame=(4271,64440)):
    """Two prior-row exports on top of the frozen six actual exclusion exports."""
    end='end ShielddSecurity.RuntimeTransferRkSupport\n'
    if not isinstance(base_source,str) or not base_source.endswith(end) or base_source.count('#check @')!=6:
        raise RelationError('exact six-export RK support source required')
    normalized=re.sub(r'\s+','',base_source)
    if any(guard not in normalized for guard in (
            'deffixedFrame:GroupFixedCircuitBounds.Frame:=⟨4271,64440⟩',
            'defadditionFrame:GroupFixedCircuitBounds.Frame:=⟨4272,64462⟩',
            'GroupFixedCircuitBounds.covers22738200692')):
        raise RelationError('exact broader actual RK support fence')
    if (not isinstance(prior_frame,(tuple,list)) or len(prior_frame)!=2 or
            any(type(column) is not int for column in prior_frame) or
            not 0<prior_frame[0]<=4271 or not 22738<prior_frame[1]<=64440):
        raise RelationError('prior row frame must independently widen into the fixed frame')
    proof=('  RuntimeTransferRkEarlierRows.rows_covered\n' if tuple(prior_frame)==(4271,64440) else '''by
  intro row member term present
  rcases RuntimeTransferRkEarlierRows.rows_covered row member term present with low | high | copied
  · exact Or.inl (Nat.lt_of_lt_of_le low (by decide))
  · exact Or.inr (Or.inl ⟨high.1,Nat.lt_of_lt_of_le high.2 (by decide)⟩)
  · exact Or.inr (Or.inr copied)
''')
    extra='''def earlierRows : List Row := RuntimeTransferRkEarlierRows.rows
theorem earlier_rows_covered : GroupFixedCircuitBounds.RowsCovered 22738 200692 fixedFrame earlierRows :=
'''+proof+'''
theorem earlier_addition_preserves_support {F : Type} [Field F] (base : Nat → F)
    (row : Row) (member : row ∈ earlierRows) (term : Nat × Int) (present : term ∈ row.a ++ row.b) :
    RuntimeTransferRkAdditionCompletion.completeAssignment base term.1 = base term.1 :=
  addition_preserves_support base earlierRows earlier_rows_covered row member term present
set_option pp.all true in
#check @earlier_rows_covered
#print axioms earlier_rows_covered
set_option pp.all true in
#check @earlier_addition_preserves_support
#print axioms earlier_addition_preserves_support
'''
    return 'import ShielddSecurity.RuntimeTransferRkEarlierRows\n'+base_source.removesuffix(end)+extra+end
