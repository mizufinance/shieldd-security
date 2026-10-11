from pathlib import Path
import json,zlib,ast,re,hashlib
J=Path(__file__).parent;W=J.parent.parent;P=W/'mac-boolean208-209-kernel-result01';data=json.loads((W/'mac-boolean-slots208-source01/selected-data01.json').read_text());q=json.loads(Path(data['qualification']['path']).read_text());groups=[];excluded=[];selected=[]
for chunk in q['chunks']:
 p=Path(chunk['data']['path']);raw=p.read_bytes();assert len(raw)==chunk['data']['bytes']and hashlib.sha256(raw).hexdigest()==chunk['data']['sha256'];d=zlib.decompressobj();b=d.decompress(raw,1048577);assert d.eof and not d.unused_data and not d.unconsumed_tail and len(b)==chunk['decoded_bytes']<=1048576 and hashlib.sha256(b).hexdigest()==chunk['decoded_sha256'];block=json.loads(b);slots=[]
 for r in block['records']:
  x=r.get('x',[])
  if r.get('constructor')=='squareLinear'and x==r['y']and len(x)==1 and x[0][1]==0:
   c=x[0][0];assert r['actual']==[x,x]and r['index']==177954+r['assertion']
   if 3<=c<22738:
    assert r['left'][0]==2 and r['right'][0]==1;slots.append([r['assertion'],c]);selected.append([r['assertion'],c])
   else:excluded.append(dict(position=r['index'],column=c,left=r['left'],right=r['right']))
 if slots:groups.append(dict(block=chunk['index'],count=len(slots),slots=slots))
assert groups==data['groups']and excluded==data['excluded']and len(selected)==10783 and len({p for p,c in selected})==len({c for p,c in selected})==10783
mods=json.loads((P/'source-object-receipt01.json').read_text());leafs={}
for e in mods:
 if e['module']=='CapturedBooleanRoot209':continue
 s=Path(e['source']['path']).read_text();m=re.search(r'^def slots : List \(Nat × Nat\) := (.*)$',s,re.M);pairs=ast.literal_eval(m.group(1));leafs[e['module']]=[list(p)for p in pairs]
assert leafs=={'CapturedBooleanSlots208B'+str(g['block']).zfill(4):g['slots']for g in groups}
root=W/'mac-boolean-root209-source02/source-root/ShielddSecurity/CapturedBooleanRoot209.lean';s=root.read_text();assert re.findall(r'^import ShielddSecurity.(\w+)',s,re.M)==list(leafs);assert all(v in s for v in ['CapturedFullRelation58.candidate (seeded base bits)','candidate_arithmetic (seeded base bits)','(outside : 3+input∉columns)','seeded_outside base bits columns (3+input) outside']);assert [0,10]in selected
report=dict(status='PASSED',kind='Independent actual Boolean DATA census, selected exact source literals and shared assignment contract review',modules=59,reports=421,positions=10783,distinct_original_columns=10783,all_selected_lists_exact=True,raw_coeff_shape='Equal one-coefficient operands; Square/Linear coefficient references vary. Per-leaf checked captured wireRecipe proves exact normalized Boolean semantics; raw indices are not assumed to be coefficient values.',excluded_actual_fresh_boolean=excluded,scope='One shared Boolean-seeded candidate satisfies all arithmetic and10783actual original-column Boolean positions. Selected bits intentionally seeded, incloriginal flag10; only unselected original inputs preserved. Seed fixes public/committed/zero/copy; candidate preserves first3 coordinates and reconstructs verifier copy from zero according to original candidate semantics. Total compatible legal private/hint/alias seed, word consistency/other assertion truths/fresh comparatorBoolean180208/concrete canonical/hash/native/full Transfer remain owned OPEN. Historical1467constructor assertions remain separate; coverage union not silently added',full_transfer='OPEN');(J/'source-semantic-review01.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(status='PASSED',positions=10783,excluded=len(excluded))))
