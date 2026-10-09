from pathlib import Path
import hashlib,json,os
local=Path('C:/src/shieldd-transfer-handoffs')
repo=Path('C:/src/shieldd-transfer-windows-publication-20261009')
candidate=repo/'handoffs/transfer-20261009/sources/parent/weierstrass-order-inputs01/candidate.json'
digest=hashlib.sha256(candidate.read_bytes()).hexdigest()
assert digest=='028924209b34a15720e93083253a54b4fe2f759bd19e93e43fdf2707c576096c'
data=json.loads(candidate.read_text());p=data['p'];A=40962;B=-40964
assert data['runtime_sha']=='844389ee069e1fb2e576708842d0b389b4d9a44a'
bx,by=data['base'];ix,iy=data['steps'][1]['after'];step=data['steps'][2]
assert step['prefix']==7 and data['steps'][1]['prefix']==3
assert step['doubling']['case']=='double' and step['addition']['case']=='add'
double=step['doubling'];addition=step['addition']
dx,dy=double['after'];ds=double['slope'];ax,ay=addition['after'];ss=addition['slope']
target=repo/'circuits/ShielddSecurity/ConcretePointOperationPilot02.lean';assert not target.exists()
body="""import ShielddSecurity.ConcretePointOperationPilot01
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointOperationPilot02
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

"""
constants={'baseX':bx,'baseY':by,'inputX':ix,'inputY':iy,'doubleX':dx,'doubleY':dy,'doubleSlope':ds,'addX':ax,'addY':ay,'addSlope':ss}
for name,value in constants.items():body+=f'def {name} : F := {value}\n'
body+='\n'
records={}
def integer(value):return f'({value} : Int)'
def check(name,left_expression,right_expression,left_value,right_value):
 difference=left_value-right_value
 assert difference%p==0
 q=difference//p
 records[name]={'multiple':q,'integer_difference':difference,'kernel_status':'UNRUN; no proof credit'}
 return f'    have integer : {left_expression} =\n        {right_expression} + {integer(q)} * (Scalar.modulus : Int) := by decide +kernel\n'
simps='[Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, '+', '.join(constants)+']'
phase='double'
def field_row(name,goal,lhs,rhs,left_value,right_value):
 result=f'  have {name} : {goal} := by\n'
 result+=check(phase+'_'+name,lhs,rhs,left_value,right_value)
 result+='    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer\n'
 result+=f'    simpa only {simps} using equal\n'
 return result
body+='theorem next_double : ∃ output : curve.Equation doubleX doubleY,\n    ((3 : Nat) • base) + ((3 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by\n'
body+='  obtain ⟨inputValid, inputImage⟩ := ConcretePointOperationPilot01.prefix_three\n'
body+='  have valid : curve.Equation inputX inputY := inputValid\n'
den=2*iy;inv=double['denominator_inverse']
body+='  have nonzero : (2 : F) * inputY ≠ 0 := by\n'
body+=check('double_inverse',f'({integer(2)} * {integer(iy)}) * {integer(inv)}','(1 : Int)',den*inv,1)
body+='    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer\n'
body+=f'    simpa only {simps} using equal\n'
body+=field_row('slopeRow','doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B',
 f'{integer(ds)} * ({integer(2)} * {integer(iy)})',
 f'{integer(3)} * {integer(ix)} ^ 2 + {integer(2)} * ({integer(A)} * {integer(B)}) * {integer(ix)} + {integer(B)} * {integer(B)}',
 ds*den,3*ix*ix+2*A*B*ix+B*B)
body+=field_row('xRow','doubleX = doubleSlope ^ 2 - A * B - inputX - inputX',integer(dx),
 f'{integer(ds)} ^ 2 - {integer(A)} * {integer(B)} - {integer(ix)} - {integer(ix)}',dx,ds*ds-A*B-2*ix)
body+=field_row('yRow','doubleY = doubleSlope * (inputX - doubleX) - inputY',integer(dy),
 f'{integer(ds)} * ({integer(ix)} - {integer(dx)}) - {integer(iy)}',dy,ds*(ix-dx)-iy)
body+='  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow\n'
body+='  refine ⟨output, ?_⟩\n  rw [inputImage]\n  exact doubled\n\n'
body+='theorem next_add : ∃ output : curve.Equation addX addY,\n    (((3 : Nat) • base) + ((3 : Nat) • base)) + base = WeierstrassCurve.Affine.Point.mk output := by\n'
body+='  obtain ⟨doubleValid, doubled⟩ := next_double\n'
phase='add';den=dx-bx;inv=(-addition['denominator_inverse'])%p
body+='  have different : doubleX ≠ baseX := by\n    apply sub_ne_zero.mp\n'
body+=check('add_inverse',f'({integer(dx)} - {integer(bx)}) * {integer(inv)}','(1 : Int)',den*inv,1)
body+='    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer\n'
body+=f'    simpa only {simps} using equal\n'
body+=field_row('slopeRow','addSlope * (doubleX - baseX) = doubleY - baseY',
 f'{integer(ss)} * ({integer(dx)} - {integer(bx)})',f'{integer(dy)} - {integer(by)}',ss*(dx-bx),dy-by)
body+=field_row('xRow','addX = addSlope ^ 2 - A * B - doubleX - baseX',integer(ax),
 f'{integer(ss)} ^ 2 - {integer(A)} * {integer(B)} - {integer(dx)} - {integer(bx)}',ax,ss*ss-A*B-dx-bx)
body+=field_row('yRow','addY = addSlope * (doubleX - addX) - doubleY',integer(ay),
 f'{integer(ss)} * ({integer(dx)} - {integer(ax)}) - {integer(dy)}',ay,ss*(dx-ax)-dy)
body+='  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow\n'
body+='  refine ⟨output, ?_⟩\n  rw [doubled]\n  exact added\n\n'
body+='theorem prefix_seven : ∃ output : curve.Equation addX addY,\n    (7 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by\n'
body+='  simpa only [show (7 : Nat) = 3 + 3 + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using next_add\n\n'
body+='end ShielddSecurity.ConcretePointOperationPilot02\n'
assert len(records)==8
pending=target.with_suffix('.lean.pending-20261009-03');assert not pending.exists()
pending.write_bytes(body.encode());os.replace(pending,target)
record=local/'point-operation-pilot-generation-20261009-03.json';assert not record.exists()
record.write_text(json.dumps({'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'source_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'candidate_sha256':digest,
 'runtime_sha':data['runtime_sha'],'selected_step_index':2,'prior_prefix':3,'selected_prefix':7,
 'addition_inverse_orientation':'negated canonical inverse because consumer denominator is doubleX-baseX',
 'selected_operations':['double','add'],'integer_certificates':records,'kernel_status':'UNRUN; zero proof credit','full_transfer':'OPEN'},indent=2)+'\n')
print(json.dumps({'source_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'candidate_sha256':digest,'kernel_run':False,'certificates':len(records),'prefix':7,'full_transfer':'OPEN'}))
