from pathlib import Path
import argparse, hashlib, json, os

parser = argparse.ArgumentParser()
parser.add_argument('--start', type=int, required=True)
parser.add_argument('--end', type=int, required=True)
parser.add_argument('--candidate', required=True)
parser.add_argument('--output-root', required=True)
parser.add_argument('--records-root', required=True)
args = parser.parse_args()
assert 3 <= args.start <= args.end < 252
local = Path(args.records_root).resolve()
repo = Path(args.output_root).resolve()
candidate = Path(args.candidate).resolve()
assert not local.exists() and not repo.exists(), 'fresh separate output and records roots required'
assert local != repo and local not in repo.parents and repo not in local.parents
local.mkdir(parents=True)
(repo/'circuits/ShielddSecurity').mkdir(parents=True)
digest = hashlib.sha256(candidate.read_bytes()).hexdigest()
assert digest == '028924209b34a15720e93083253a54b4fe2f759bd19e93e43fdf2707c576096c'
data = json.loads(candidate.read_text())
assert data['runtime_sha'] == '844389ee069e1fb2e576708842d0b389b4d9a44a'
assert len(data['steps']) == 252
p, A, B = data['p'], data['A'], -40964
assert (B % p) == data['B'] and data['a2'] == (A * B) % p and data['a4'] == (B * B) % p
bx, by = data['base']
outputs = []

def generate(index):
    step, prior = data['steps'][index], data['steps'][index-1]
    n, result_n = prior['prefix'], step['prefix']
    assert result_n == n + n + step['bit']
    ix, iy = prior['after']
    double, addition = step['doubling'], step['addition']
    assert double['case'] == 'double'
    dx, dy = double['after']; ds = double['slope']
    final = addition is not None and addition['case'] == 'inverse'
    assert not final or index == 251
    assert (addition is not None) == (step['bit'] == 1)
    assert addition is None or addition['case'] in ['add', 'inverse']
    previous = 'ConcretePointOperationPilot02' if index == 3 else f'ConcretePointTraceStep{index-1:03d}'
    previous_theorem = 'prefix_seven' if index == 3 else 'prefix_image'
    module = f'ConcretePointTraceStep{index:03d}'
    target = repo/'circuits/ShielddSecurity'/f'{module}.lean'
    assert not target.exists()
    records = {}
    constants = {'baseX':bx, 'baseY':by, 'inputX':ix, 'inputY':iy,
                 'doubleX':dx, 'doubleY':dy, 'doubleSlope':ds}
    if addition is not None and not final:
        ax, ay = addition['after']; ss = addition['slope']
        constants.update(addX=ax, addY=ay, addSlope=ss)
    if not final:
        ox, oy = step['after']; constants.update(outX=ox, outY=oy)
    body = f'''import ShielddSecurity.{previous}
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.{module}
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

'''
    body += ''.join(f'def {name} : F := {value}\n' for name,value in constants.items()) + '\n'
    simps = '[Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, '+', '.join(constants)+']'
    def integer(value): return f'({value} : Int)'
    def check(name, lhs, rhs, left_value, right_value):
        difference = left_value - right_value
        assert difference % p == 0, (index, name)
        q = difference // p
        assert name not in records
        records[name] = {'multiple':q, 'integer_difference':difference, 'kernel_status':'UNRUN; zero proof credit'}
        return f'    have integer : {lhs} =\n        {rhs} + {integer(q)} * (Scalar.modulus : Int) := by decide +kernel\n'
    def field_row(name, goal, lhs, rhs, left_value, right_value):
        return (f'  have {name.split("_")[-1]} : {goal} := by\n'
                +check(name,lhs,rhs,left_value,right_value)
                +'    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer\n'
                +f'    simpa only {simps} using equal\n')
    left_point = f'(({n} : Nat) • base)'
    doubled_point = f'{left_point} + {left_point}'
    body += f'theorem next_double : ∃ output : curve.Equation doubleX doubleY,\n    {doubled_point} = WeierstrassCurve.Affine.Point.mk output := by\n'
    body += f'  obtain ⟨inputValid, inputImage⟩ := {previous}.{previous_theorem}\n'
    body += '  have valid : curve.Equation inputX inputY := inputValid\n'
    den, inv = 2*iy, double['denominator_inverse']
    body += '  have nonzero : (2 : F) * inputY ≠ 0 := by\n'
    body += check('double_inverse',f'({integer(2)} * {integer(iy)}) * {integer(inv)}','(1 : Int)',den*inv,1)
    body += '    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer\n'
    body += f'    simpa only {simps} using equal\n'
    body += field_row('double_slopeRow','doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B',
                     f'{integer(ds)} * ({integer(2)} * {integer(iy)})',
                     f'{integer(3)} * {integer(ix)} ^ 2 + {integer(2)} * ({integer(A)} * {integer(B)}) * {integer(ix)} + {integer(B)} * {integer(B)}',
                     ds*den,3*ix*ix+2*A*B*ix+B*B)
    body += field_row('double_xRow','doubleX = doubleSlope ^ 2 - A * B - inputX - inputX',integer(dx),
                     f'{integer(ds)} ^ 2 - {integer(A)} * {integer(B)} - {integer(ix)} - {integer(ix)}',dx,ds*ds-A*B-2*ix)
    body += field_row('double_yRow','doubleY = doubleSlope * (inputX - doubleX) - inputY',integer(dy),
                     f'{integer(ds)} * ({integer(ix)} - {integer(dx)}) - {integer(iy)}',dy,ds*(ix-dx)-iy)
    body += '  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow\n'
    body += '  refine ⟨output, ?_⟩\n  rw [inputImage]\n  exact doubled\n\n'
    if final:
        body += f'theorem final_add : ({doubled_point}) + base = 0 := by\n'
        body += '  obtain ⟨doubleValid, doubled⟩ := next_double\n  have same : doubleX = baseX := rfl\n'
        body += field_row('inverse_opposite','doubleY = -baseY',integer(dy),f'-{integer(by)}',dy,-by)
        body += '  rw [doubled]\n  exact ConcretePointOperationRows01.vertical_addition doubleValid ConcretePointOperationPilot01.base_valid same opposite\n\n'
        body += f'theorem scalar_zero : ({result_n} : Nat) • base = 0 := by\n'
        body += f'  simpa only [show ({result_n} : Nat) = {n} + {n} + 1 by rfl, ConcretePointScalarRecurrence01.odd_prefix] using final_add\n\n'
    else:
        operation = 'next_double'
        if addition is not None:
            body += f'theorem next_add : ∃ output : curve.Equation addX addY,\n    ({doubled_point}) + base = WeierstrassCurve.Affine.Point.mk output := by\n'
            body += '  obtain ⟨doubleValid, doubled⟩ := next_double\n'
            # The canonical candidate stores inverse(baseX-doubleX).
            den, inv = dx-bx, (-addition['denominator_inverse']) % p
            body += '  have different : doubleX ≠ baseX := by\n    apply sub_ne_zero.mp\n'
            body += check('add_inverse',f'({integer(dx)} - {integer(bx)}) * {integer(inv)}','(1 : Int)',den*inv,1)
            body += '    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer\n'
            body += f'    simpa only {simps} using equal\n'
            body += field_row('add_slopeRow','addSlope * (doubleX - baseX) = doubleY - baseY',
                             f'{integer(ss)} * ({integer(dx)} - {integer(bx)})',f'{integer(dy)} - {integer(by)}',ss*(dx-bx),dy-by)
            body += field_row('add_xRow','addX = addSlope ^ 2 - A * B - doubleX - baseX',integer(ax),
                             f'{integer(ss)} ^ 2 - {integer(A)} * {integer(B)} - {integer(dx)} - {integer(bx)}',ax,ss*ss-A*B-dx-bx)
            body += field_row('add_yRow','addY = addSlope * (doubleX - addX) - doubleY',integer(ay),
                             f'{integer(ss)} * ({integer(dx)} - {integer(ax)}) - {integer(dy)}',ay,ss*(dx-ax)-dy)
            body += '  obtain ⟨output, added⟩ := ConcretePointOperationRows01.secant_rows doubleValid ConcretePointOperationPilot01.base_valid different slopeRow xRow yRow\n'
            body += '  refine ⟨output, ?_⟩\n  rw [doubled]\n  exact added\n\n'
            operation = 'next_add'
        recurrence = 'odd_prefix' if step['bit'] else 'even_prefix'
        expression = f'{n} + {n}' + (' + 1' if step['bit'] else '')
        body += f'theorem prefix_image : ∃ output : curve.Equation outX outY,\n    ({result_n} : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by\n'
        body += f'  simpa only [outX, outY, '+ ('addX, addY, ' if addition else 'doubleX, doubleY, ') +f'show ({result_n} : Nat) = {expression} by rfl, ConcretePointScalarRecurrence01.{recurrence}] using {operation}\n\n'
    body += f'end ShielddSecurity.{module}\n'
    pending = target.with_suffix('.lean.pending-trace-20261009-01')
    assert not pending.exists()
    pending.write_bytes(body.encode()); os.replace(pending,target)
    return {'step_index':index, 'module':module, 'source_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),
            'prior_prefix':n, 'prefix':result_n, 'operation_cases':['double']+([addition['case']] if addition else []),
            'integer_certificates':records, 'kernel_status':'UNRUN; zero proof credit'}

for index in range(args.start,args.end+1): outputs.append(generate(index))
record = local/f'point-trace-generation-20261009-01-{args.start:03d}-{args.end:03d}.json'
assert not record.exists()
record.write_text(json.dumps({'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'candidate_sha256':digest, 'runtime_sha':data['runtime_sha'], 'steps':outputs,
    'addition_inverse_orientation':'negated canonical inverse for doubleX-baseX consumer denominator',
    'kernel_status':'UNRUN; zero proof credit', 'full_transfer':'OPEN'},indent=2)+'\n')
print(json.dumps({'marker':'TRANSFER_POINT_TRACE_GENERATION_UNRUN','start':args.start,'end':args.end,
    'modules':len(outputs),'operations':sum(len(x['operation_cases']) for x in outputs),'candidate_sha256':digest,
    'record_sha256':hashlib.sha256(record.read_bytes()).hexdigest(),'full_transfer':'OPEN'}))
