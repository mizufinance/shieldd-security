"""Apply captured unified diffs to exact pinned text, checking contexts and retained hashes."""
import hashlib,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parent; P=ROOT/'packet01'; R=ROOT.parent.parent/'runtime-snapshot'; OUT=ROOT/'reconstructed-overlay01'
cap=json.loads((P/'overlay-review/capture.json').read_bytes())
OUT.mkdir(exist_ok=True)
count=0; unresolved=[]
for x in cap['differences']:
 name=x['path']; f=R/name
 old=f.read_bytes().decode().splitlines(keepends=True) if f.exists() else []
 lines=(P/'overlay-review/diffs'/Path(name+'.diff')).read_text().splitlines(keepends=True)
 assert lines[0].rstrip()=='--- clean/'+name and lines[1].rstrip()=='+++ overlay/'+name
 pos=0; out=[]; i=2
 while i<len(lines):
  match=re.fullmatch(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@.*\n?',lines[i])
  assert match,(name,lines[i])
  start=int(match[1]);old_count=int(match[2] or 1); new_count=int(match[4] or 1)
  offset=start-1 if old_count else start
  assert offset>=pos
  out.extend(old[pos:offset]);pos=offset;i+=1;removed=added=0
  while i<len(lines) and not lines[i].startswith('@@'):
   line=lines[i];i+=1
   assert line[0] in ' +-'
   if line[0] in ' -':
    assert pos<len(old) and old[pos].replace('\r\n','\n')==line[1:],(name,pos)
    pos+=1;removed+=1
   if line[0]==' ':out.append(old[pos-1]);added+=1
   if line[0]=='+':out.append(line[1:]);added+=1
  assert removed==old_count and added==new_count,(name,removed,added)
 out.extend(old[pos:])
 text=''.join(out)
 normalized=text.replace('\r\n','\n')
 variants=[text,normalized,normalized.replace('\n','\r\n')]
 candidates=[v.encode() for v in variants]+[v.rstrip('\r\n').encode() for v in variants]
 matches=[b for b in candidates if hashlib.sha256(b).hexdigest()==x['overlay_sha256']]
 if not matches:
  unresolved.append(name);continue
 raw=matches[0]
 target=OUT/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(raw);count+=1
(ROOT/'source-diff-reconstruction01.json').write_text(json.dumps(dict(exact_reconstructed_paths=count,unresolved_text_diff_paths=unresolved,runtime_sha='844389ee069e1fb2e576708842d0b389b4d9a44a',scope='Exact source contexts and retained hashes; no build/refinement'),indent=2)+'\n')
print(dict(exact_paths=count,unresolved=unresolved))

