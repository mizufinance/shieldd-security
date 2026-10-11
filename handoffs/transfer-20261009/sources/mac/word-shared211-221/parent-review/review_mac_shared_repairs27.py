from pathlib import Path
import json,re,hashlib,difflib
J=Path(__file__).resolve().parent;W=J.parent

def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
for label,packet,module in [('word211-213','mac-word211-213-kernel-result01','CapturedWordRoot213'),('shared-word-flags220','mac-shared-word-flags220-kernel-result01','SharedWordFlags220'),('shared-word-witness221','mac-shared-word-witness221-kernel-result01','SharedWordWitness221')]:
 D=J/(label+'-review01');h=json.loads((D/'source-history-review01.json').read_text());prior=[r for r in h['rejected']if r['module']==module];assert len(prior)==1;q=prior[0];p=Path(q['source']['path']);before=p.read_text();entry=next(e for e in json.loads((W/packet/'source-object-receipt01.json').read_text())if e['module']==module);current=Path(entry['source']['path']);final=current.read_text();repaired=before
 if label=='word211-213':
  needle='simp only [words,List.forall_mem_cons,List.forall_mem_nil,and_true]';assert repaired.count(needle)==5;repaired=repaired.replace(needle,'simp only [words,List.forall_mem_cons]')
  for suffix in ['checked','bits_checked','positions','originals','sound rho satisfied']:
   old='CapturedWordSlots211B016.W65.'+suffix;assert repaired.count(old)==1;repaired=repaired.replace(old,'⟨'+old+',by intro entry member;cases member⟩')
  reason='Five empty-list membership proof cases retained explicitly; definitions and theorem statements unchanged.'
 elif label=='shared-word-flags220':
  old='     simp only [chosen,if_pos rfl]';assert repaired.count(old)==1;repaired=repaired.replace(old,'     change (if head.1=head.1 then head.2 else chosen rest fallback head.1)=head.2\n     exact if_pos rfl');reason='Definitional equality of selected head; definitions and theorem statements unchanged.'
 else:
  for name in ['unselected_input','links']:
   old='theorem '+name;assert repaired.count(old)==1;repaired=repaired.replace(old,'omit [CharP F p] in\n'+old)
  reason='Unused characteristic section instance omitted in two declarations; mathematical statements, definitions and proof terms unchanged.'
 assert repaired==final
 r=dict(status='PASSED',kind='Exact retained failed source repair comparison, no requalification',failed_original=q,selected_source=pin(current),reason=reason,exact_delta=''.join(difflib.unified_diff(before.splitlines(True),final.splitlines(True))),full_transfer='OPEN');out=D/'precise-source-repair-review01.json';out.write_text(json.dumps(r,indent=2)+'\n');sem=D/'source-semantic-review01.json';s=json.loads(sem.read_text());s['precise_original_repair_review']=pin(out);sem.write_text(json.dumps(s,indent=2)+'\n');print(json.dumps(dict(label=label,status='PASSED',failed_originals=1)))
