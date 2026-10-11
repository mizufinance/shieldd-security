from pathlib import Path
import hashlib,json,sys
S=Path(__file__).resolve().parent
if not (sys.flags.isolated and sys.flags.dont_write_bytecode and sys.flags.no_site and not sys.flags.optimize):raise ValueError('isolated flags')
b=(S/'template.lean').read_bytes();p=S/'source-root/ShielddSecurity/CompilerIndexedRecipe38.lean';p.parent.mkdir(parents=True,exist_ok=True)
with p.open('xb') as f:f.write(b)
with (S/'generation01.json').open('x') as f:json.dump({'source_sha256':hashlib.sha256(b).hexdigest(),'template_sha256':hashlib.sha256(b).hexdigest()},f,sort_keys=True)
