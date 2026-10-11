from pathlib import Path
import json,zlib,hashlib,re
J=Path(__file__).resolve().parent;W=J.parent

def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def read(z):
 p=Path(z['path']);b=p.read_bytes();assert len(b)==z['bytes']and hashlib.sha256(b).hexdigest()==z['sha256'];return b
selection=json.loads((W/'mac-word-slots211-source01/selected-data01.json').read_bytes());q=json.loads(read(selection['qualification']));assert q['runtime']=='844389ee069e1fb2e576708842d0b389b4d9a44a';coeff=[]
for k in ['old_coefficients','extra_coefficients']:
 c=json.loads(read(q[k]));assert k!='extra_coefficients'or c['first_index']==len(coeff);coeff.extend(c['coefficients'])
records=[]
for z in q['chunks']:
 b=read(z['data']);d=zlib.decompressobj();raw=d.decompress(b,1048577);assert d.eof and not d.unused_data and not d.unconsumed_tail and len(raw)==z['decoded_bytes']<=1048576 and hashlib.sha256(raw).hexdigest()==z['decoded_sha256'];chunk=json.loads(raw);assert chunk['start']==z['start']and chunk['count']==z['count']==len(chunk['records']);records.extend(chunk['records'])
assert len(records)==22816 and [r['index']for r in records]==list(range(177954,200770));bits={}
for r in records:
 if r.get('constructor')=='squareLinear'and r['x']==r['y']and len(r['x'])==1:
  col,coef=r['x'][0]
  if coeff[coef]==1 and 3<=col<22738:assert col not in bits;bits[col]=r['assertion']
assert len(bits)==10783
selected=[];excluded=[]
for r in records:
 if r.get('constructor')!='linear'or len(r['y'])!=1 or not r['x']:continue
 value,ycoef=r['y'][0]
 if coeff[ycoef]!=1:continue
 pairs=[(column,coeff[coefficient])for column,coefficient in r['x']];start=pairs[0][0];width=len(pairs)
 if not(3<=start and start+width<=22738 and 3<=value<22738):continue
 if any(column!=start+offset or coefficient!=1<<offset for offset,(column,coefficient)in enumerate(pairs)):continue
 missing=[column for column,_ in pairs if column not in bits]
 if missing:excluded.append(dict(position=r['assertion'],start=start,width=width,value=value,reason='one or more columns lack wire-Boolean recipe'));continue
 first=bits[start];assert [bits[c]for c,_ in pairs]==list(range(first,first+width));assert first+width<=22816 and(value<start or start+width<=value)
 selected.append(dict(position=r['assertion'],start=start,width=width,value=value,first=first,index=r['index'],outlined_recipe_x=r['x'],outlined_recipe_y=r['y'],actual=r['actual']))
assert selected==selection['selected']and excluded==selection['excluded']and len(selected)==66 and len(excluded)==21
mods=json.loads((W/'mac-word211-213-kernel-result01/source-object-receipt01.json').read_text());literal=[];providers=[]
for e in mods:
 if e['module']=='CapturedWordRoot213':continue
 providers.append(e['module']);s=read(e['source']).decode();rows=re.findall(r'^def slot : Slot := ⟨(\d+),(\d+),(\d+),(\d+)⟩\ndef first : Nat := (\d+)$',s,re.M);literal.extend(tuple(map(int,row))for row in rows)
assert len(providers)==17 and literal==[(r['position'],r['start'],r['width'],r['value'],r['first'])for r in selected]
root=W/'mac-word-root213-source02/source-root/ShielddSecurity/CapturedWordRoot213.lean';s=root.read_text();assert re.findall(r'^import ShielddSecurity.(CapturedWordSlots\w+)',s,re.M)==providers;line=next(l for l in s.splitlines()if l.startswith('def words :'));references=re.findall(r'\((CapturedWordSlots211B\d{3}\.W\d{2})\.slot,\1\.first\)',line);assert references==[providers[i//4]+'.W'+str(i).zfill(2)for i in range(66)];positions={r['position']for r in selected};assert len(positions)==66 and not positions.intersection(bits.values());word_columns={c for r in selected for c in range(r['start'],r['start']+r['width'])};assert word_columns.issubset(bits)
scopes={
'word211-213':'Exact66 selected weighted word-reconstruction positions across17 providers plus captured root. Full captured SAT derives each bounded natural word meaning through actual checked Boolean and weighted rows. Per-word constructors are separate; shared constructor assumes one supplied bit map, natural bounds, seeded value meanings and encoded-bit agreement.21 other weighted recipe candidates excluded for missing Boolean recipes. Total compatible legal seed/remaining assertions/native/full Transfer owned OPEN.',
'shared-word-flags220':'A single chosen bit map agrees with every encoded word under explicit pairwise duplicate-column coherence. Bits outside the assignment list retain fallback. Coherence is an owned legal-input obligation, not proved universally; no claim that arbitrary overlapping words agree. Native/full Transfer OPEN.',
'shared-word-witness221':'One candidate assignment simultaneously satisfies177954 arithmetic rows,10783 selected original Boolean assertions and66 distinct selected word-reconstruction assertions under explicit duplicate-column coherence, natural bounds and seeded value meanings.10783distinct selected original bit columns, word-bit columns already within Boolean set. Selected inputs intentionally seeded; only unselected original inputs preserved. Seed fixes first3/copy; candidate rebuilds verifier copy from zero and existing links. Full compatible legal private/hint/alias encoding, fresh Boolean/21 excluded word candidates/other assertions/concrete canonical/hash/native/full Transfer remain owned OPEN. Historical1467constructor assignment not silently unioned.'}
for label,modules,reports in [('word211-213',18,602),('shared-word-flags220',1,8),('shared-word-witness221',1,15)]:
 D=J/(label+'-review01');audit=json.loads((D/'audit-result01.json').read_text());assert len(audit['modules'])==modules and audit['declarations']==reports
 r=dict(status='PASSED',kind='Independent full captured DATA classification, exact provider/root literals and shared assignment contract review',modules=modules,reports=reports,actual_word_records=66,excluded_weighted_candidates=21,selected_boolean_positions=10783,distinct_selected_assertions=10849,word_bit_columns=len(word_columns),distinct_selected_bit_columns=10783,actual_data=selection['qualification'],all_selected_lists_exact=True,scope=scopes[label],full_transfer='OPEN');(D/'source-semantic-review01.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(dict(label=label,status='PASSED',modules=modules,reports=reports,selected_assertions=10849)))
