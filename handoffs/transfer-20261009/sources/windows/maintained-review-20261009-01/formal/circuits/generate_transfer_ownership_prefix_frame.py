"""Bounded support certificates for the already constructed IVK prefix.

The caller supplies only reaccepted typed derivatives retained by prefix replay.
Each imported original row block is checked separately against the entire
precompute footprint and the actual first variable-window allocation frame.
No ordinary scan, compiler-origin assumption or preceding row truth is added.
"""
from . import generate_transfer_prefix_hash_completion as hashes
from . import transfer_ivk_reduction_completion as reduction
from . import generate_transfer_ivk_reduction_join as joins
from . import generate_transfer_ownership_precompute_frame as precompute
from .generate_hash_round import _signature_audits


def _stage_writes(stage):
    if stage['kind'] in ('square','linear'):return [stage['output']]
    if stage['kind']=='product':return [stage['output'],stage['auxiliary']]
    if stage['kind']=='quotient':return [stage['quotient'],stage['product'],stage['auxiliary']]
    if stage['kind'] in ('equal','square_equal'):return []
    raise reduction.relation.RelationError('ownership exact precompute write stage')


def _bounded(name, rows, frame_name, copy, before, writes):
    low,high=before
    if not rows or len(rows)>128:
        raise reduction.relation.RelationError('bounded IVK original support block')
    for row in rows:
        for terms in row:
            for column,_ in terms:
                if column in writes or not (column<low or 22738<=column<high or column==copy):
                    raise reduction.relation.RelationError('actual IVK/precompute support collision '+name)
    output=name+'OwnershipFrame'
    source=f'''import ShielddSecurity.{name}
import ShielddSecurity.{frame_name}
import ShielddSecurity.CompilerWriteExclusion
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
namespace ShielddSecurity.{output}
def beforeFrame : GroupFixedCircuitBounds.Frame := ⟨{low},{high}⟩
theorem outside : CompilerWriteExclusion.RowsOutside {frame_name}.writes {name}.rawRows := by
  apply CompilerWriteExclusion.checked_rows
  decide
theorem covered : GroupFixedCircuitBounds.RowsCovered 22738 {copy} beforeFrame {name}.rawRows := by
  apply CompilerFrameCoverage.checked_rows
  decide
#print axioms outside
#print axioms covered
end ShielddSecurity.{output}
'''
    return output,_signature_audits(source)


def generate(checked,extracted,ivk_data,ivk_export,reduction_data,reduction_export,
             parameter_root,expected_relation,readonly_lcs=()):
    frame_name,_=precompute.generate(checked,extracted,readonly_lcs)
    selected,hash_metadata,protected=hashes.select_ivk(ivk_data,ivk_export,parameter_root,expected_relation,readonly_lcs)
    accepted=hashes.ivk.inspect_metadata(ivk_data,parameter_root,expected_relation)
    plan=reduction.plan(reduction_data,accepted,reduction_export,expected_relation,readonly_lcs)
    metadata=checked['metadata'];copy=metadata['constant_copy']
    if metadata['relation_digest']!=expected_relation or copy!=accepted['metadata']['constant_copy']:
        raise reduction.relation.RelationError('ownership prefix exact same relation/copy')
    owned=precompute.tables.completion.window_plan(checked,extracted,0,True,readonly_lcs)
    if len(owned['point_groups'])<2:
        raise reduction.relation.RelationError('ownership prefix actual two precompute operations')
    groups=owned['point_groups'][:2]
    if [group['index'] for group in groups]!=[0,1]:
        raise reduction.relation.RelationError('ownership prefix actual precompute source order')
    cones=precompute.tables.completion.owner.cone_certificates(checked,extracted,0,True)
    formula=next(cone for cone in cones['cones'] if cone['role']=='formula0')
    source=[cones['observations'][identity][1][0][0] for identity in formula['inputs']]
    writes=set(source)
    for stage in owned['stages'][:groups[-1]['stage_end']]:writes.update(_stage_writes(stage))
    window=precompute.tables.completion.window_plan(checked,extracted,0,False,readonly_lcs)
    low=[c for c in window['writes'] if c<22738];high=[c for c in window['writes'] if 22738<=c<copy]
    if not low or not high or min(low)<2257:
        raise reduction.relation.RelationError('ownership prefix actual first-window frame')
    before=(min(low),min(high));blocks=[]
    context=(selected,dict(metadata=hash_metadata),None)
    for index,start in enumerate(range(0,65,5)):
        chunk=hashes.blocks._chunk_plan(context,start,start+5,readonly_lcs=protected)
        blocks.append((f'RuntimeTransferIvkHashOwnedCompletionChunk{index}',list(chunk['raw'].values())))
    for phase in plan['phases']:
        for start in range(0,phase['width'],16):
            stop=min(start+16,phase['width'])
            indices=[plan['roles'][f'{phase["key"]}.boolean.{i}'] for i in range(start,stop)]
            indices += [row for i in range(max(1,start),stop) for row in phase['stages'][i-1]['rows']]
            blocks.append((f'RuntimeTransferIvkComparison{phase["phase"]}OriginalChunk{start//16}',
                           [plan['raw'][i] for i in sorted(set(indices))]))
    blocks.append(('RuntimeTransferIvkGateProductOriginal',[plan['raw'][i] for i in plan['gate_stage']['rows']]))
    tail=['quotient.reconstruction','remainder.reconstruction','quotient_end.assertion',
          'remainder_end.assertion','hash-equation','terminal-gate','constant-copy']
    blocks.append(('RuntimeTransferIvkReductionTailCompletion',[plan['raw'][plan['roles'][key]] for key in tail]))
    blocks.append(('RuntimeTransferIvkInverseOwnedCompletion',[plan['raw'][i] for i in plan['inverse']['rows']]))
    if len(blocks)!=49:
        raise reduction.relation.RelationError('ownership prefix exact49 bounded original blocks')
    for name,rows in blocks:yield _bounded(name,rows,frame_name,copy,before,writes)
    names=[name for name,_ in blocks]
    yield _composition(names,frame_name,copy,before)


def _composition(names,frame_name,copy,before):
    if len(names)!=49 or len(set(names))!=49:
        raise reduction.relation.RelationError('ownership prefix exact bounded certificate inventory')
    name='RuntimeOwnershipIvkPrefixFrame'
    h='RuntimeTransferIvkHashOwnedCompletion';r='RuntimeTransferIvkReductionOriginalRows'
    i='RuntimeTransferIvkInverseOwnedCompletion';p='RuntimeTransferIvkInversePrefixJoin'
    hashparts=names[:13];parts=names[13:-2];tail=names[-2]
    source=''.join(f'import ShielddSecurity.{part}OwnershipFrame\n' for part in names)
    source+=f'''import ShielddSecurity.{p}
set_option maxHeartbeats 150000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
def beforeFrame : GroupFixedCircuitBounds.Frame := ⟨{before[0]},{before[1]}⟩
'''
    for export,property_name,helper in (
            ('outside','CompilerWriteExclusion.RowsOutside','CompilerWriteExclusion'),
            ('covered','GroupFixedCircuitBounds.RowsCovered','CompilerFrameCoverage')):
        args=f'{frame_name}.writes' if export=='outside' else f'22738 {copy} beforeFrame'
        def fact(block):return f'{block}OwnershipFrame.{export}'
        combined=fact(hashparts[0])
        for block in hashparts[1:]:combined=f'{helper}.append_rows {args} _ _ ({combined}) ({fact(block)})'
        # All13 round blocks remain opaque; no sparse row expression is unfolded.
        source+=f'''theorem {export} : {property_name} {args} {p}.originalRows := by
  have hashRows : {property_name} {args} {h}.rawRows := by
    change {property_name} {args} ({' ++ '.join(part+'.rawRows' for part in hashparts)})
    exact {combined}
  have comparisonRows : {property_name} {args} ({r}.parts.flatMap id) := by
    apply {helper}.flat_map_rows {args} {r}.parts id
    intro part member
    simp only [{r}.parts,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at member
    rcases member with '''+' | '.join('rfl' for _ in parts)+'\n'
        source+=''.join(f'    · exact {fact(part)}\n' for part in parts)
        source+=f'''  have reductionRows : {property_name} {args} {r}.originalRows :=
    {helper}.append_rows {args} _ _ comparisonRows ({fact(tail)})
  change {property_name} {args} (({h}.rawRows ++ {r}.originalRows) ++ {i}.rawRows)
  exact {helper}.append_rows {args} _ _
    ({helper}.append_rows {args} _ _ hashRows reductionRows) ({fact(i)})
#print axioms {export}
'''
    return name,_signature_audits(source+f'end ShielddSecurity.{name}\n')
