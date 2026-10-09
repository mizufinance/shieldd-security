"""Committed input shadow from the exact owned Compiler::link_inputs row.

No source-handle equality is assumed. The same joint ordinary replay must find
the real target2/shadow9 assertion at its production lowering position.
"""
from . import transfer_relation as relation
from .transfer_balance_rows import canonical,source_index
from .generate_hash_round import linear,_signature_audits

TARGET=2
SHADOW=9
ROW=200768
EXPECTED=(canonical([(TARGET,1),(SHADOW,-1)]),())


def public_witness_shadows(identity):
    """Compiler witness offset from the real production source-input header.

    Source descriptors are witness indices, not physical LC columns. This
    protects the public shadow; it does not prove its emitted copy/output rows.
    """
    if (not isinstance(identity,dict) or identity.get('source_public')!=[[1,22734]] or
            identity.get('source_blocks')!=[[[1,6]]] or identity.get('stored_rows')!=200770 or
            identity.get('domain_size')!=262144 or identity.get('relation_digest')!=
            '16e7b009b763be55ca21f423f4f97e8c132b40b6adbcd06f6a3be17f2d0ef236'):
        raise relation.RelationError('actual production source-input layout required')
    offset=1+len(identity['source_public'])+sum(map(len,identity['source_blocks']))
    return tuple(offset+index for tag,index in identity['source_public'])


def same_original_identity(previous,current):
    """Older signed extraction identity plus the joint parser's exact header.

    Every old field must match, including raw stream identity. Added header
    fields are checked separately and are never attributed to the old packet.
    Semantic row and source-role correspondence still require their checkers.
    """
    core={'schema','domain_size','stored_rows','relation_digest','raw_sha256','scope'}
    extra={'source_public','source_blocks'}
    if (not isinstance(previous,dict) or not isinstance(current,dict) or
            set(previous) not in (core,core|extra) or set(current)!=core|extra):
        return False
    try:public_witness_shadows(current)
    except relation.RelationError:return False
    if previous.keys()>=extra:
        try:public_witness_shadows(previous)
        except relation.RelationError:return False
    if current['schema']!='shieldd-transfer-relation-v1':return False
    if (not isinstance(current['raw_sha256'],str) or len(current['raw_sha256'])!=64 or
            any(c not in '0123456789abcdef' for c in current['raw_sha256'])):return False
    return all(type(value) is type(current[key]) and value==current[key]
               for key,value in previous.items())

def source_role(ref,terms):
    if not isinstance(ref,dict) or set(ref)!={'source'} or source_index(ref['source'])!=(1,6) or terms!=((SHADOW,1),):
        raise relation.RelationError('balance exact committed Witness6 source shadow9 required')
    return dict(source=[1,6],shadow=SHADOW,target=TARGET)

def requirements():return {EXPECTED:['committed-shadow']},[],[]

def selected(combined):
    identity=combined['identity']
    if (identity.get('source_blocks')!=[[[1,6]]] or identity.get('source_public')!=[[1,22734]] or
        identity.get('stored_rows')!=200770 or identity.get('domain_size')!=262144):
        raise relation.RelationError('balance exact production committed/public source layout')
    matches=[item for item in combined['templates'] if item['roles']==['layout.committed-shadow']]
    if len(matches)!=1 or matches[0]['row']!=ROW:
        raise relation.RelationError('balance committed link_inputs actual original row position')
    records=[record for record in combined['selected_rows'] if record['row']==ROW]
    if len(records)!=1:raise relation.RelationError('balance committed shadow original row missing')
    raw=records[0]
    actual=tuple(tuple((c,int(v,16)) for c,v in raw[key]) for key in ('a','b'))
    if actual not in (EXPECTED,(canonical((c,-v) for c,v in EXPECTED[0]),())):
        raise relation.RelationError('balance committed shadow actual polynomial mismatch')
    return dict(identity=identity,selected_rows=records,writes=[SHADOW],source=[1,6],target=TARGET,shadow=SHADOW,
        scope='Exact original committed input assertion; constructor writes only source shadow9 from target2')

def render(plan):
    if (not isinstance(plan,dict) or plan.get('writes')!=[SHADOW] or plan.get('source')!=[1,6] or
        (plan.get('target'),plan.get('shadow'))!=(TARGET,SHADOW) or
        len(plan.get('selected_rows',[]))!=1):raise relation.RelationError('exact committed shadow retained plan required')
    record=plan['selected_rows'][0]
    raw=tuple(tuple((c,int(v,16)) for c,v in record[key]) for key in ('a','b'))
    if record['row']!=ROW or raw not in (EXPECTED,(canonical((c,-v) for c,v in EXPECTED[0]),())):
        raise relation.RelationError('exact committed shadow original row transport required')
    left,right=(2,9) if raw==EXPECTED else (9,2)
    name='RuntimeBalanceInputLayout'
    source=f'''import ShielddSecurity.CompilerLinearCompletion
import ShielddSecurity.CompilerSignedCompletion
import ShielddSecurity.Scalar
namespace ShielddSecurity.{name}
set_option maxHeartbeats 100000
def rawRows : List Row := [⟨{linear(raw[0])}, []⟩]
def expectedRows : List Row := CompilerLinearCompletion.rows [(2,1)] [] 9
def construct {{F : Type}} [Field F] (base : Nat → F) : Nat → F :=
  CompilerLinearCompletion.extend base [(2,1)] [] 9
variable {{F : Type}} [Field F] [CharP F Scalar.modulus]
theorem outside (base : Nat → F) (column : Nat) (excluded : column ≠ 9) :
    construct base column = base column :=
  CompilerLinearCompletion.preserves base [(2,1)] [] 9 column excluded
theorem value (base : Nat → F) : construct base 9 = base 2 := by
  simp [construct,CompilerLinearCompletion.extend,patchAssignment,eval]
theorem canonical_complete (base : Nat → F) : Satisfies (construct base) expectedRows := by
  apply CompilerLinearCompletion.constructs
  intro term member
  simp only [List.append_nil,List.mem_singleton] at member
  subst term
  decide
theorem raw_checked : Compiler.checkRow Scalar.modulus rawRows
    ⟨Compiler.subtract [({left},1)] [({right},1)],[]⟩ = true := by decide
theorem constructs (base : Nat → F) : Satisfies (construct base) rawRows := by
  intro row member
  simp only [rawRows,List.mem_singleton] at member
  subst row
  apply CompilerSignedCompletion.signed_row (p := Scalar.modulus)
    (construct base) _ ⟨Compiler.subtract [(9,1)] [(2,1)],[]⟩
  · decide
  · decide
  · exact canonical_complete base _ (by simp [expectedRows,CompilerLinearCompletion.rows])
theorem binding (rho : Nat → F) (satisfied : Satisfies rho rawRows) : rho 9 = rho 2 := by
  have equal := Compiler.checked_assertion_sound rho rawRows [({left},1)] [({right},1)] satisfied raw_checked
  simp only [eval,Int.cast_one,one_mul,add_zero] at equal
  exact {'equal.symm' if left==2 else 'equal'}
'''
    for export in ['outside','value','canonical_complete','raw_checked','constructs','binding']:
        source+='#print axioms '+export+'\n'
    return name,_signature_audits(source+f'end ShielddSecurity.{name}\n')
