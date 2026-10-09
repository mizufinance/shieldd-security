from pathlib import Path
import hashlib, json

local = Path('C:/src/shieldd-transfer-handoffs')
old = local / 'prepare-point-trace-composition-20261009-01.py'
new = local / 'prepare-point-order-20261009-01.py'
assert not new.exists()
body = old.read_text().replace('point-trace-composition', 'point-order')
body = body.replace('ConcretePointTraceComposition01', 'ConcretePointOrder01')
needle = '"for namespace in [\'windows-point-trace-007-251-20261009-01\''
assert body.count(needle) == 1
body = body.replace(needle, '"for namespace in [\'windows-point-trace-composition-20261009-01\',\'windows-point-trace-007-251-20261009-01\'', 1)
start = body.index("scope='Fresh initial-infinity")
end = body.index('\n', start)
scope = ('Exact additive order of the concrete actual Mathlib Point base, consuming qualified '
         'annihilation and nonidentity plus freshly replayed canonical Lucas subgroup prime '
         'nodes and SubgroupOrderPrime06; shared field certificates and actual Point trace '
         'imports reused by exact qualified identities. Finite 300000 heartbeats in new '
         'nodes/order root, 4096 recursion, 1536MiB, 240s per module, one verifier, <=2GiB '
         'qualified external disk closure. Cardinality, native generator correspondence '
         'and full Transfer OPEN. No Hasse launch.')
body = body[:start] + 'scope=' + repr(scope) + body[end:]
new.write_bytes(body.encode())
print(json.dumps({'preparer': str(new), 'sha256': hashlib.sha256(new.read_bytes()).hexdigest(),
                  'kernel_run': False, 'requires_completed_composition': True}))
