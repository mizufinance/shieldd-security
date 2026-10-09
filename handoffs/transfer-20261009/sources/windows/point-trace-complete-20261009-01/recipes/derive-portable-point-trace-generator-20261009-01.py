from pathlib import Path
import hashlib, json

local = Path('C:/src/shieldd-transfer-handoffs')
old = local / 'generate-concrete-point-trace-20261009-01.py'
new = local / 'generate-concrete-point-trace-portable-20261009-01.py'
assert not new.exists()
body = old.read_text()
proposal = json.loads((local / 'point-trace-generation-20261009-01-007-251.json').read_text())
assert hashlib.sha256(old.read_bytes()).hexdigest() == proposal['producer_sha256']
anchor = "args = parser.parse_args()"
assert body.count(anchor) == 1
body = body.replace(anchor, "parser.add_argument('--candidate', required=True)\nparser.add_argument('--output-root', required=True)\nparser.add_argument('--records-root', required=True)\n" + anchor, 1)
bindings = "local = Path('C:/src/shieldd-transfer-handoffs')\nrepo = Path('C:/src/shieldd-transfer-windows-publication-20261009')\ncandidate = repo/'handoffs/transfer-20261009/sources/parent/weierstrass-order-inputs01/candidate.json'"
assert body.count(bindings) == 1
body = body.replace(bindings, "local = Path(args.records_root).resolve()\nrepo = Path(args.output_root).resolve()\ncandidate = Path(args.candidate).resolve()\nassert not local.exists() and not repo.exists(), 'fresh separate output and records roots required'\nassert local != repo and local not in repo.parents and repo not in local.parents\nlocal.mkdir(parents=True)\n(repo/'circuits/ShielddSecurity').mkdir(parents=True)", 1)
new.write_bytes(body.encode())
print(json.dumps({'portable_generator': str(new), 'sha256': hashlib.sha256(new.read_bytes()).hexdigest(),
                  'original_template_producer_sha256': proposal['producer_sha256'],
                  'changes': 'Required explicit input/output arguments and fresh path bindings only; identical Lean generation template',
                  'kernel_run': False, 'new_kernel_credit': 0}))
