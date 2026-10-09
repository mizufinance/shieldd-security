"""Symbolic bounded ordering/initialization for all actual reduction products.

Independent source helpers construct q/r from the computed hash codec, write
both actual bit blocks once, and carry small product bounds symbolically. This
candidate does not presume any quotient, remainder, endpoint or assertion row.
"""
from . import transfer_ivk_reduction_completion as reduction
from .generate_hash_round import linear,_signature_audits


def generate(data,accepted_ivk,extracted,expected_relation,readonly_lcs=()):
    plan=reduction.plan(data,accepted_ivk,extracted,expected_relation,readonly_lcs)
    meta=plan['checked']['metadata'];q,r=plan['phases'][:2]
    if any(len(phase['value'])!=1 or phase['value'][0][1]!=1 for phase in (q,r)):
        raise reduction.relation.RelationError('IVK reduction exact q/r seed unit columns')
    qcol,rcol=q['value'][0][0],r['value'][0][0];qs,rs=q['start'],r['start']
    stages=[*q['stages'],*r['stages'],*plan['phases'][2]['stages'],plan['gate_stage']]
    chunks=[]
    for phase in plan['phases']:
        chunks.extend(phase['stages'][start:start+16] for start in range(0,len(phase['stages']),16))
    chunks.append([plan['gate_stage']])
    first=stages[0]['output'];lower=first
    for stage in stages:
        if not (lower<=stage['output']<stage['auxiliary'] and
                all(c<stage['output'] for key in ('left','right','remainder') for c,_ in stage[key])):
            raise reduction.relation.RelationError('IVK reduction captured product allocation bound')
        lower=stage['auxiliary']+1
    if not (qcol<first and rcol<first and qs+4<=first and rs+252<=first):
        raise reduction.relation.RelationError('IVK initial support exceeds first actual product')
    bitcols=[*q['columns'],*r['columns']]
    kept=sorted(set(plan['readonly'])|set(bitcols))
    if set(bitcols)&set(plan['readonly']):
        raise reduction.relation.RelationError('IVK bit write aliases readonly actual roles')
    name='RuntimeTransferIvkReductionProductOrder'
    hash_value=plan['checked']['expressions'][reduction.source_index(meta['value'])]
    source=f'''import ShielddSecurity.ScalarReductionSeed
import ShielddSecurity.ScalarBitFootprint
import ShielddSecurity.PoseidonCompletion
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
def hashValue : Linear := {linear(hash_value)}
def kept : List Nat := {kept}
def initialRows : List Row := ScalarReductionSeed.initialRows {qcol} {rcol} {qs} {rs}
def prefix000 : List CompilerCompletion.Step := []
def prior000 : List Row := initialRows ++ CompilerCompletion.emitted prefix000
theorem prior_bound000 : ScalarRandomizerBounds.RowsBelow {first} prior000 := by
  exact ScalarRandomizerBounds.rows_append {first}
    (ScalarComparatorCompletion.initialRows {qcol} {qs} 4)
    (ScalarComparatorCompletion.initialRows {rcol} {rs} 252)
    (ScalarBitFootprint.initial_rows_below {qcol} {qs} 4 {first} (by decide) (by decide))
    (ScalarBitFootprint.initial_rows_below {rcol} {rs} 252 {first} (by decide) (by decide))
theorem prefix_order000 : CompilerCompletion.Topological kept initialRows prefix000 := True.intro
theorem prefix_products000 : ScalarRandomizerCompletion.Products prefix000 := True.intro
'''
    lower=first
    for index,chunk in enumerate(chunks):
        current,next_=f'{index:03d}',f'{index+1:03d}';upper=chunk[-1]['auxiliary']+1
        body=','.join(f'.product {linear(s["left"])} {linear(s["right"])} {linear(s["remainder"])} '
            f'{s["output"]} {s["auxiliary"]}' for s in chunk)
        source+=f'''def chunk{current} : List CompilerCompletion.Step := [{body}]
def prefix{next_} : List CompilerCompletion.Step := prefix{current} ++ chunk{current}
def prior{next_} : List Row := initialRows ++ CompilerCompletion.emitted prefix{next_}
theorem checked_bound{current} : ScalarRandomizerBounds.checkBounded {lower} {upper} chunk{current} = true := by decide
theorem checked_protected{current} : ScalarRandomizerBounds.checkProtected kept chunk{current} = true := by decide
theorem chunk_order{current} : CompilerCompletion.Topological kept prior{current} chunk{current} :=
  ScalarRandomizerBounds.bounded_ordered {lower} {upper} chunk{current} kept prior{current}
    checked_bound{current} prior_bound{current}
    (ScalarRandomizerBounds.protected_certificate kept chunk{current} checked_protected{current})
theorem prefix_order{next_} : CompilerCompletion.Topological kept initialRows prefix{next_} :=
  ScalarRandomizerCompletion.ordered_append kept initialRows prefix{current} chunk{current}
    prefix_order{current} chunk_order{current}
theorem prior_bound{next_} : ScalarRandomizerBounds.RowsBelow {upper} prior{next_} := by
  simpa only [prior{next_},prefix{next_},prior{current},ScalarRandomizerBounds.emitted_append,List.append_assoc] using
    (ScalarRandomizerBounds.rows_append {upper} prior{current} (CompilerCompletion.emitted chunk{current})
      (ScalarRandomizerBounds.rows_mono {lower} {upper} prior{current} prior_bound{current} (by decide))
      (ScalarRandomizerBounds.bounded_rows {lower} {upper} chunk{current} checked_bound{current}))
theorem prefix_products{next_} : ScalarRandomizerCompletion.Products prefix{next_} :=
  ScalarRandomizerCompletion.products_append prefix{current} chunk{current} prefix_products{current} (by trivial)
'''
        lower=upper
    end=f'{len(chunks):03d}'
    source+=f'''def allStages : List CompilerCompletion.Step := prefix{end}
def rows : List Row := initialRows ++ CompilerCompletion.emitted allStages
theorem ordered : CompilerCompletion.Topological kept initialRows allStages := prefix_order{end}
theorem products : ScalarRandomizerCompletion.Products allStages := prefix_products{end}
theorem row_support : ScalarRandomizerBounds.RowsBelow {lower} rows := prior_bound{end}
def construct {{F : Type}} [Field F] (codec : TransferReduction.CanonicalField F) (base : Nat → F) : Nat → F :=
  CompilerCompletion.run (ScalarReductionSeed.bitBase base codec (eval base hashValue) {qcol} {rcol} {qs} {rs}) allStages
theorem constructs {{F : Type}} [Field F] (codec : TransferReduction.CanonicalField F) (base : Nat → F) :
    Satisfies (construct codec base) rows :=
  ScalarReductionSeed.products_constructed base codec (eval base hashValue) {qcol} {rcol} {qs} {rs} allStages kept
    (by decide) (by decide) (by decide) (by decide)
    (by
      have checked : (ScalarComparatorCompletion.initialRows {qcol} {qs} 4).all
        (fun row => (row.a ++ row.b).all (fun term => decide (term.1 < {rs} ∨ {rs+252} ≤ term.1))) = true := by decide
      intro row member term present
      exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checked row member) term present))
    ordered products
'''
    for export in ('ordered','products','row_support','constructs'):source+='#print axioms '+export+'\n'
    return name,_signature_audits(source+f'end ShielddSecurity.{name}\n')
