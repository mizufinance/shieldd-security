"""Generate small integer certificates from untrusted proposals; Lean decides validity."""
import hashlib
import json
import os
from pathlib import Path
import re
ROOT = Path(__file__).resolve().parent
PROPOSAL = ROOT / 'inputs/proposals.json'
assert hashlib.sha256(PROPOSAL.read_bytes()).hexdigest() == '0d7894fcb68a2b32e5976add363a5df303988d86271d320c43fdc1e29eb7fbbb'
data = json.loads(PROPOSAL.read_text())
points = data['double_chain']; assert len(points) == 4 and points[-1] == data['sdk_point']
P = data['p']; D = data['d']
names = ['preimage', 'twice', 'four', 'sdkBase']
lines = ['import ShielddSecurity.ConcreteIntegerCertificates01', 'import ShielddSecurity.Group', '',
         'set_option autoImplicit false', 'set_option maxHeartbeats 300000', 'set_option maxRecDepth 4096', '',
         'namespace ShielddSecurity.SDKSpendAuthCertificates01', 'open ConcreteJubjubField01', '',
         '/-- Generated proposals are accepted only by the Lean kernel. This source',
         'proves mathematical coordinates, bytes and an eight-preimage, not native',
         'Rust field, decoder or source-code representation correspondence. -/']
int_casts = 'Int.cast_add, Int.cast_mul, Int.cast_sub, Int.cast_one, Int.cast_ofNat'
def integer(value): return '(' + str(value) + ' : Int)'
def certificate(left_expr, right_expr, left, right, conclusion, reductions):
    assert (left-right) % P == 0
    quotient = (left-right)//P
    return ['  have integer : ' + left_expr + ' = ' + right_expr + ' + ' + integer(quotient) + ' * (Scalar.modulus : Int) := by decide +kernel',
            '  have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer',
            '  simpa only [' + int_casts + ', ' + reductions + '] using equal']
for name,(u,v) in zip(names,points):
    lines += ['', 'def ' + name + ' : Group.Point F := ⟨' + str(u) + ', ' + str(v) + '⟩']
    left_expr = integer(v) + ' * ' + integer(v) + ' - ' + integer(u) + ' * ' + integer(u)
    right_expr = '(1 : Int) + ' + integer(D) + ' * ' + integer(u) + ' * ' + integer(u) + ' * ' + integer(v) + ' * ' + integer(v)
    lines += ['', 'theorem ' + name + '_on_curve : Group.OnCurve coefficient ' + name + ' := by']
    lines += certificate(left_expr,right_expr,v*v-u*u,1+D*u*u*v*v,'',
                         'Group.OnCurve, ' + name + ', coefficient, coefficientNat')
for index,(name,next_name) in enumerate(zip(names,names[1:])):
    u,v = points[index]; outX,outY = points[index+1]
    delta = integer(D) + ' * ' + integer(u) + ' * ' + integer(u) + ' * ' + integer(v) + ' * ' + integer(v)
    for axis,out,sign,right_expr,right in [('x',outX,'+',integer(u)+' * '+integer(v)+' + '+integer(v)+' * '+integer(u),u*v+v*u),
                                          ('y',outY,'-',integer(v)+' * '+integer(v)+' + '+integer(u)+' * '+integer(u),v*v+u*u)]:
        row_name = name + '_' + axis + '_row'
        numerator = 'Group.cross' if axis == 'x' else 'Group.diagonal'
        conclusion = next_name + '.' + axis + ' * (1 ' + sign + ' Group.delta coefficient ' + name + ' ' + name + ') = ' + numerator + ' ' + name + ' ' + name
        left_expr = integer(out) + ' * ((1 : Int) ' + sign + ' ' + delta + ')'
        left = out*(1+D*u*u*v*v) if sign == '+' else out*(1-D*u*u*v*v)
        lines += ['', 'theorem ' + row_name + ' : ' + conclusion + ' := by']
        lines += certificate(left_expr,right_expr,left,right,conclusion,
                             'Group.delta, ' + numerator + ', ' + name + ', ' + next_name + ', coefficient, coefficientNat')
    lines += ['', 'theorem ' + name + '_double : ' + next_name + ' = Group.affineAdd coefficient ' + name + ' ' + name + ' :=',
              '  Group.affine_rows_sound coefficient imaginary coefficient_no_unit_square imaginary_square',
              '    ' + name + ' ' + name + ' ' + next_name + ' ' + name + '_on_curve ' + name + '_on_curve',
              '    ' + name + '_x_row ' + name + '_y_row']
u,v = points[-1]
lines += ['', 'def sdkX : Nat := ' + str(u), 'def sdkY : Nat := ' + str(v),
          'def sdkBytes : List Nat := ' + repr(data['sdk_bytes']),
          'def maskedYBytes : List Nat := ' + repr(data['masked_y_bytes']),
          'def littleEndianValue (bytes : List Nat) : Nat := bytes.foldr (fun byte acc => byte + 256 * acc) 0',
          '', 'theorem sdk_x_bound : sdkX < Scalar.modulus := by decide +kernel',
          'theorem sdk_y_bound : sdkY < Scalar.modulus := by decide +kernel',
          'theorem sdk_x_odd : sdkX % 2 = 1 := by decide +kernel',
          'theorem masked_y_value : littleEndianValue maskedYBytes = sdkY := by',
          '  norm_num [littleEndianValue, maskedYBytes, List.foldr, sdkY]',
          'theorem compressed_sign_byte : sdkBytes = maskedYBytes.take 31 ++ [87 + 128] := by decide +kernel',
          'theorem sdk_base_coordinates : sdkBase = ⟨(sdkX : F), (sdkY : F)⟩ := rfl',
          '', 'end ShielddSecurity.SDKSpendAuthCertificates01', '']
body = '\n'.join(lines)
audit_names = re.findall(r'^(?:theorem|def) ([A-Za-z0-9_]+)',body,re.M)
assert len(audit_names) == len(set(audit_names))
body += '\n'.join('set_option pp.all true in\n#check @ShielddSecurity.SDKSpendAuthCertificates01.'+name+'\n#print axioms ShielddSecurity.SDKSpendAuthCertificates01.'+name for name in audit_names)+'\n'
out = ROOT / 'generated/SDKSpendAuthCertificates01.lean'
out.parent.mkdir(exist_ok=False)
pending = out.with_suffix('.lean.pending'); pending.write_text(body,encoding='utf-8',newline='\n'); os.replace(pending,out)
def pin(path): return {'path':str(path),'bytes':path.stat().st_size,'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
review = {'generator':pin(Path(__file__)),'proposal':pin(PROPOSAL),'generated_source':pin(out),
          'audits':len(audit_names),'kind':'GENERATED_INTEGER_CERTIFICATE_PROPOSALS',
          'proof_credit':0,'certification':False,'scope':'Generation establishes identity only; Lean validation is required. No generated source may be hand edited.'}
(ROOT / 'generation-review.json').write_text(json.dumps(review,indent=2)+'\n')
print(json.dumps(review))
