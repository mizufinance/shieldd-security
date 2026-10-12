"""Regenerate the selected group source closure from existing repository sources."""
from pathlib import Path
import argparse,hashlib,json,os,re
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--repository',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();repo=a.repository.resolve();out=a.output.resolve();assert not out.exists();tmp=out.with_name(out.name+'.pending');tmp.mkdir()
manifest=json.loads((root/'selection.json').read_bytes());generated={}
for name,row in manifest['selected'].items():
    source=repo/row['repository_path'];assert source.is_file() and repo in source.resolve().parents
    data=source.read_bytes().replace(b'\r\n',b'\n');assert hashlib.sha256(data).hexdigest()==row['lf_sha256'],name
    if 'directive_adaptation' in row:
        lines=[x for x in data.decode().splitlines() if not x.startswith(('set_option','#'))]
        assert hashlib.sha256(('\n'.join(lines)+'\n').encode()).hexdigest()==row['proof_lines_sha256']
        result=[]
        for item in row['directive_adaptation']:
            if 'directive' in item:
                line=item['directive']
                assert re.fullmatch(r'(?:set_option (?:autoImplicit false|maxHeartbeats [1-9][0-9]*|maxRecDepth [1-9][0-9]*|pp.all true in|linter.dupNamespace false)|#check @[A-Za-z0-9_.]+|#print axioms [A-Za-z0-9_.]+)',line),line
                result.append(line)
            else:result.append(lines[item['source_line']])
        data=('\n'.join(result)+'\n').encode()
    if row['newline']=='CRLF':data=data.replace(b'\n',b'\r\n')
    assert len(data)==row['source_bytes'] and hashlib.sha256(data).hexdigest()==row['selected_source_sha256'],name
    target=tmp/'source/ShielddSecurity'/(name+'.lean');target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
    generated[name]=dict(bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
(tmp/'generation.json').write_text(json.dumps(dict(runtime_sha=manifest['runtime_sha'],mathlib=manifest['mathlib'],sources=generated,proof_credit=0,certification=False),sort_keys=True)+'\n')
os.replace(tmp,out);print(json.dumps(dict(source_modules=len(generated),generation='exact reproduced sources; no independent proof credit')))

