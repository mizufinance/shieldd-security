from pathlib import Path
import json,hashlib,sys
S=Path(__file__).resolve().parent
if not (sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize):raise ValueError('isolated flags')
if (S/'producer-manifest01.json').exists():raise ValueError('sealed refresh')
b=(S/'template.lean').read_bytes();p=S/'source-root/ShielddSecurity/CompilerArithmeticBlock44.lean';p.parent.mkdir(parents=True,exist_ok=True)
with p.open('xb') as f:f.write(b)
with (S/'generation01.json').open('x') as f:json.dump(dict(source_sha256=hashlib.sha256(b).hexdigest(),template_sha256=hashlib.sha256(b).hexdigest()),f)
