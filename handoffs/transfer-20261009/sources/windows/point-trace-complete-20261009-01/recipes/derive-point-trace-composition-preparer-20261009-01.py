from pathlib import Path
import hashlib, json

local = Path('C:/src/shieldd-transfer-handoffs')
old = local / 'prepare-point-trace-007-251-20261009-01.py'
new = local / 'prepare-point-trace-composition-20261009-01.py'
assert not new.exists()
body = old.read_text()
body = body.replace('point-trace-007-251', 'point-trace-composition')
body = body.replace('ConcretePointTraceStep251', 'ConcretePointTraceComposition01')
needle = '"for namespace in [\'windows-point-trace-003-006-20261009-01\''
assert body.count(needle) == 1
body = body.replace(needle, '"for namespace in [\'windows-point-trace-007-251-20261009-01\',\'windows-point-trace-003-006-20261009-01\'', 1)
old_scope = "scope='357 further actual Mathlib Point operations"
assert body.count(old_scope) == 1
start = body.index(old_scope)
end = body.index('\n', start)
scope = ('Fresh initial-infinity doubling/addition and initial prefix; actual Point base nonidentity; '
         'exact Scalar.order annihilation and initial/final endpoint conjunction, importing the '
         'completed 007-251 trace with audited symbolic recurrences and operation witnesses. '
         'Two new handwritten modules, six declaration audits, unchanged finite 300000 heartbeats/'
         '4096 recursion/1536MiB/240s per module and qualified external disk closure <=2GiB. '
         'Exact point order, cardinality, native generator correspondence and full Transfer OPEN.')
body = body[:start] + 'scope=' + repr(scope) + body[end:]
new.write_bytes(body.encode())
print(json.dumps({'preparer': str(new), 'sha256': hashlib.sha256(new.read_bytes()).hexdigest(),
                  'kernel_run': False, 'requires_completed_chain': True}))
