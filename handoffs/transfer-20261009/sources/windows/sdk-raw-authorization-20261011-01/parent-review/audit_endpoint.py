"""Independently verify structured audits against their exact original output hashes."""
from pathlib import Path
import json,hashlib,re,itertools
J=Path(__file__).resolve().parent;P=J/'packet01';M=json.loads((P/'manifest.json').read_bytes())
def check(v,m):
 if not v:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
for r in M['files']:
 b=(P/r['path']).read_bytes();check(len(b)==r['bytes']and sha(b)==r['sha256'],r['path'])
summaries=[]
for spec in M['modules']:
 name=spec['module'];record=json.loads((P/'proof-audits'/(name+'.json')).read_bytes());receipt=record['receipt']
 check(receipt['status']=='passed'and record['captured_stdout']==receipt['stdout'],name+' qualification')
 source=P/(spec['source_class']+'-source/ShielddSecurity')/(name+'.lean')
 check(sha(source.read_bytes())==spec['source_sha256'],name+' source')
 names=re.findall(r'(?m)^#check @([\w.]+)\s*$',source.read_text());audits=record['audits']
 check(names==[x['declaration']for x in audits]and set(names)==set(receipt['audits'])and len(set(names))==len(names),name+' exact census')
 check(len(names)==spec['audit_pairs'],name+' manifest count')
 # Lean's MessageData.ofList formats axiom lists either flat or with all
 # comma separators broken under its grouped, one-column bracket indentation.
 # Recover only those two permitted layouts, then demand the full original
 # stdout byte count AND SHA256. This also detects omitted diagnostics/gaps.
 variants=[]
 for a in audits:
  declaration=a['declaration'];signature=a['full_type'];axioms=a['axioms'];registered=receipt['audits'][declaration]
  check(sha(signature.encode())==a['full_type_sha256']==registered['full_type_sha256'],declaration+' full type')
  check(axioms==registered['axioms']and set(axioms)<={'propext','Classical.choice','Quot.sound'},declaration+' axioms')
  check(all(not line.strip()or line[0].isspace()for line in signature.splitlines()[1:]),declaration+' complete type')
  prefix=signature+"\n'"+declaration+"' "
  if axioms:
   lines=[prefix+'depends on axioms: ['+', '.join(axioms)+']\n']
   if len(axioms)>1:lines.append(prefix+'depends on axioms: ['+',\n '.join(axioms)+']\n')
  else:lines=[prefix+'does not depend on any axioms\n']
  variants.append(lines)
 check(len(variants)<=128,name+' bounded reconstruction')
 expected=record['captured_stdout'];matches=[]
 suffix_min=[0]*(len(variants)+1);suffix_max=[0]*(len(variants)+1)
 for i in range(len(variants)-1,-1,-1):
  lengths=[len(v.encode()) for v in variants[i]]
  suffix_min[i]=suffix_min[i+1]+min(lengths);suffix_max[i]=suffix_max[i+1]+max(lengths)
 explored=[0]
 def recover(i,parts,size):
  if size+suffix_min[i]>expected['bytes']or size+suffix_max[i]<expected['bytes']:return
  if i==len(variants):
   explored[0]+=1;check(explored[0]<=65536,name+' bounded candidate search')
   b=''.join(parts).encode()
   if sha(b)==expected['sha256']:matches.append(b)
   return
  for v in variants[i]:recover(i+1,parts+[v],size+len(v.encode()))
 recover(0,[],0)
 check(len(matches)==1,name+' exact complete original stdout')
 raw=matches[0].decode();check(not re.search(r'\b(?:error|warning|info|trace):|sorryAx',raw),name+' diagnostics')
 reports=re.findall(r"(?m)^'([^']+)' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",raw)
 check(reports==names,name+' complete original reports')
 summaries.append(dict(module=name,source_sha256=spec['source_sha256'],audits=audits,original_stdout=expected,receipt=receipt))
check(sum(len(x['audits'])for x in summaries)==M['type_axiom_pairs']==172,'aggregate audits')
result=dict(kind='parent exact source/manifest/structured type and axiom audit; full original diagnostic bytes reconstructed and checksum matched, no Lean replay',modules=summaries,manifest_files_rehashed=len(M['files']),declarations=172,full_transfer='OPEN',native_correspondence='OPEN',reconstruction='Lean MessageData.ofList flat or grouped line breaks; complete original byte counts/SHA256 require exact diagnostic identity')
with(J/'audit-result01.json').open('x')as f:json.dump(result,f,indent=2);f.write('\n')
print(json.dumps(dict(modules=len(summaries),declarations=172,files_rehashed=len(M['files']),original_outputs_exact=True)))
