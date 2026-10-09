from pathlib import Path
import json,re,hashlib
package_root=Path('C:/src/shieldd-formal/circuits/.lake/packages')
cache=Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002/windows-jubjub-isolated-05/modules')
roots=[p for p in package_root.iterdir() if p.is_dir()]
def strip(s):
    result=[];index=0;depth=0;quoted=False
    while index<len(s):
        if depth:
            if s[index:index+2]=='/-':depth+=1;index+=2
            elif s[index:index+2]=='-/':depth-=1;index+=2
            else:
                if s[index]=='\n':result.append('\n')
                index+=1
        elif quoted:
            result.append(s[index])
            if s[index]=='\\' and index+1<len(s):index+=1;result.append(s[index])
            elif s[index]=='"':quoted=False
            index+=1
        elif s[index:index+2]=='/-':depth=1;index+=2
        elif s[index:index+2]=='--':
            stop=s.find('\n',index);index=len(s) if stop<0 else stop
        else:
            result.append(s[index]);quoted=s[index]=='"'
            index+=1
    assert depth==0
    return ''.join(result)
seen=set();sources={};files=[];missing=[]
def walk(name):
    if name in seen:return
    seen.add(name)
    if name.startswith(('Init.','Lean.','Std.','Lake.')) or name in ['Init','Lean','Std','Lake']:return
    if name.startswith('ShielddSecurity.'):
        short=name.split('.',1)[1]
        choices=[Path('C:/src/shieldd-transfer-windows-publication-20261009/circuits/ShielddSecurity')/(short+'.lean'),
                 Path('C:/src/shieldd-transfer-handoffs/field-certificate-tree-20261009-01/ShielddSecurity')/(short+'.lean'),
                 Path('C:/src/shieldd-formal/circuits/ShielddSecurity')/(short+'.lean')]
        matches=[next(p for p in choices if p.exists())]
    else:
        matches=[p/Path(name.replace('.','/')).with_suffix('.lean') for p in roots]
    matches=[p for p in matches if p.exists()]
    assert len(matches)==1,(name,matches)
    p=matches[0];sources[name]={'source':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
    for line in strip(p.read_text()).splitlines():
        line=line.strip()
        if not line or line in ['module','prelude']:continue
        m=re.fullmatch(r'(?:(?:public|meta)\s+)*import\s+(.+)',line)
        if not m:break
        for dep in m[1].split():
            if dep!='all':walk(dep)
    if name=='Mathlib.NumberTheory.LucasPrimality' or name.startswith('ShielddSecurity.'):return
    for suffix in ['.olean','.olean.private','.olean.server','.ir']:
        object_path=cache/(name.replace('.','/')+suffix)
        if object_path.exists():files.append({'path':str(object_path),'bytes':object_path.stat().st_size})
        else:missing.append(str(object_path))
for name in ['ShielddSecurity.ConcreteStandardCurveModel01']:
    walk(name)
out=Path('C:/src/shieldd-transfer-handoffs/standard-curve-model-closure-inspection-20261009-01.json')
result={'sources':sources,'files':files,'missing':missing,'bytes':sum(x['bytes'] for x in files),'proof_credit':0}
assert not out.exists()
out.write_bytes((json.dumps(result,indent=2)+'\n').encode())
print(json.dumps({'modules':len(sources),'files':len(files),'bytes':result['bytes'],'missing':missing[:10]}))
