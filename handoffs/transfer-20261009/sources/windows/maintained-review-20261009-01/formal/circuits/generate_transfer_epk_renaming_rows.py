"""Bounded row equality instances for the existing exact EPK renaming.

The strict actual matcher supplies the column/physical-row map. This adapter
does not accept runtime metadata or a desired row truth. It splits only the
wide canonical basis; ordinary window/inverse/binding output stays unchanged.
"""
from collections import Counter
from . import generate_transfer_epk_fixed_renaming as renderer
from . import transfer_relation as relation
from .generate_hash_round import linear,_signature_audits


def generate_block(scope_id,ordinal,block,pair,source_raw,target_raw,*,maximum_rows=128):
    if (type(scope_id)is not int or not 1<=scope_id<6 or type(ordinal)is not int or
            not 0<=ordinal<129 or type(maximum_rows)is not int or not 1<=maximum_rows<=128):
        raise relation.RelationError('EPK renaming exact bounded row selector')
    indices=block['indices']
    if (not isinstance(indices,list) or not indices or
            any(type(index)is not int or index<0 for index in indices)):
        raise relation.RelationError('EPK renaming ordered physical basis required')
    repeats={index:count for index,count in Counter(indices).items() if count!=1}
    if repeats:
        # Window.rawRows is the exact concatenation of local rows and quotient
        # rows. Both include the SAME original copylink. Do not deduplicate it.
        from .transfer_fixed_spend import canonical
        copylink=(canonical([(0,1),(200692,-1)]),())
        if (ordinal>=126 or block['module']!=f'RuntimeTransferEpk0FixedWindow{ordinal:03d}'
                or block['definition']!='rawRows' or len(repeats)!=1
                or next(iter(repeats.values()))!=2
                or source_raw.get(next(iter(repeats)))!=copylink):
            raise relation.RelationError('only exact retained window copylink repeat allowed')
    if len(indices)<=maximum_rows:
        return [renderer._row_source(scope_id,ordinal,block,pair,source_raw,target_raw)]
    if (ordinal!=126 or block['module']!='RuntimeTransferEpk0Canonical' or
            block['definition']!='originalRows'):
        raise relation.RelationError('EPK unsupported wide original basis')
    # Reuse the unchanged strict coefficient/shape checker before publishing
    # any part. Its wide result is validation-only, never a generated artifact.
    renderer._row_source(scope_id,ordinal,block,pair,source_raw,target_raw)
    row_map=dict(pair['original_row_map'])
    namespace=f'RuntimeTransferEpk{scope_id}RenamingRows{ordinal:03d}'
    map_ns=f'ShielddSecurity.RuntimeTransferEpk{scope_id}RenamingMap'
    original='ShielddSecurity.RuntimeTransferEpk0Canonical.originalRows'
    chunks=[indices[start:start+maximum_rows] for start in range(0,len(indices),maximum_rows)]
    modules=[];names=[];tails=[];tail=original
    for index,chunk in enumerate(chunks):
        name=namespace+f'Part{index:03d}';names.append(name);tails.append(tail)
        source=tail if index==len(chunks)-1 else f'({tail}).take {maximum_rows}'
        actual=[target_raw[row_map[physical]] for physical in chunk]
        source_text=f'''import ShielddSecurity.RowCompletionRenaming
import ShielddSecurity.RuntimeTransferEpk0Canonical
import {map_ns}
namespace ShielddSecurity.{name}
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
def physicalRows : List Nat := {[row_map[physical] for physical in chunk]}
def sourceRows : List Row := {source}
def rawRows : List Row := ['''+',\n'.join('⟨'+renderer._raw_linear(a)+','+renderer._raw_linear(b)+'⟩' for a,b in actual)+f''']
theorem exact_rows : rawRows = sourceRows.map (RowRenaming.row {map_ns}.columns) := by decide
#print axioms exact_rows
end ShielddSecurity.{name}
'''
        modules.append((name,_signature_audits(source_text)))
        tail=f'({tail}).drop {maximum_rows}'
    full_names=['ShielddSecurity.'+name for name in names]
    concatenation=full_names[-1]+'.rawRows'
    for name in reversed(full_names[:-1]):concatenation=f'({name}.rawRows ++ {concatenation})'
    text=''.join('import '+name+'\n' for name in full_names)
    text+=f'''namespace ShielddSecurity.{namespace}
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
def physicalRows : List Nat := {[row_map[physical] for physical in indices]}
def rawRows : List Row := {concatenation}
private theorem mapped_cut (rows : List Row) (transform : Row → Row) :
    (rows.take {maximum_rows}).map transform ++ (rows.drop {maximum_rows}).map transform = rows.map transform := by
  rw [← List.map_append,List.take_append_drop]
theorem exact_rows : rawRows = {original}.map (RowRenaming.row {map_ns}.columns) := by
  have suffix{len(names)-1:03d} : {full_names[-1]}.rawRows =
      ({tails[-1]}).map (RowRenaming.row {map_ns}.columns) := {full_names[-1]}.exact_rows
'''
    suffix=full_names[-1]+'.rawRows'
    for index in range(len(names)-2,-1,-1):
        suffix=f'({full_names[index]}.rawRows ++ {suffix})'
        text+=f'''  have suffix{index:03d} : {suffix} =
      ({tails[index]}).map (RowRenaming.row {map_ns}.columns) :=
    (congrArg₂ (fun left right : List Row => left ++ right)
      {full_names[index]}.exact_rows suffix{index+1:03d}).trans
        (mapped_cut ({tails[index]}) (RowRenaming.row {map_ns}.columns))
'''
    text+=f'''  exact suffix000
#print axioms exact_rows
end ShielddSecurity.{namespace}
'''
    modules.append((namespace,_signature_audits(text)))
    return modules
