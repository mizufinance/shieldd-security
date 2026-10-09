from pathlib import Path
import ast,hashlib,json
local=Path('C:/src/shieldd-transfer-handoffs');diag=Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002');rows={}
for label in ['01','02','03']:
 producer=local/('prepare-point-smoke-20261009-'+label+'.py');tree=ast.parse(producer.read_text())
 call=next(n for n in ast.walk(tree) if isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute) and n.func.attr=='write_text' and n.args and isinstance(n.args[0],ast.Constant) and 'stage=Path(sys.argv[1])' in str(n.args[0].value))
 raw=call.args[0].value.replace('\n','\r\n').encode();recovered=local/('compose-point-smoke-cache-20261009-'+label+'-recovered.py')
 assert recovered.read_bytes()==raw
 digest=hashlib.sha256(raw).hexdigest();overlay=json.loads((diag/('windows-point-smoke-20261009-'+label+'-kernel/external-overlay.json')).read_text())
 assert digest==overlay['producer_sha256']
 rows[label]={'recovered_path':str(recovered),'sha256':digest,'actual_overlay_producer_match':True,'original_producer_sha256':hashlib.sha256(producer.read_bytes()).hexdigest()}
assert hashlib.sha256((local/'compose-point-smoke-cache-20261009-01.py').read_bytes()).hexdigest()==rows['03']['sha256']
report={'kind':'Append-only recipe-path disposition; no new proof credit','history':rows,'reason':'Smoke successors retained composer filename01 while changing stage namespace. Failed smoke01/02 composer bytes were overwritten, but exact bytes are recovered from frozen producer literals including Windows newline translation and match actual overlay hashes. Successful smoke03 producer remains exact. Point04 rejected mismatched stage before any Lean job. No original inspection, compiled object or successful audit changed.','proof_credit':0,'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
out=local/'point-composer-path-disposition-20261009-02.json';assert not out.exists();out.write_bytes((json.dumps(report,indent=2)+'\n').encode());print(hashlib.sha256(out.read_bytes()).hexdigest())
