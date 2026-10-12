"""Independent typed Open numeric refinement and retained failed proof histories."""
from pathlib import Path
import json,hashlib,re,ast,difflib
J=Path(__file__).resolve().parent;D=J/'windows-word-stage-numeric-refinement-review01';P=D/'packet01';M='TransferWordStageNumericRefinement01';S=P/'source/ShielddSecurity'/(M+'.lean');final=S.read_text()
def read(p):return json.loads(p.read_text())
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
plan=read(P/'qualified/plan.json');t=plan['targets'][0]['source'];assert len(S.read_bytes())==t['bytes']and hashlib.sha256(S.read_bytes()).hexdigest()==t['sha256'];assert any(z['path'].replace('\\','/').endswith('/handwritten/'+M+'.lean')and z['bytes']==t['bytes']and z['sha256']==t['sha256']for z in plan['pins']);assert re.findall(r'^(?:def|theorem) ([A-Za-z0-9_]+)',final,re.M)==re.findall(r'^#check @([^\n]+)',final,re.M)and final.count('#check @')==6
old=(P/'rejected-numeric-attempt02/handwritten'/(M+'.lean')).read_text();source=old
# Interpret only proof-source string replacements in the exact maintained repair.
def replacement(n):
 if isinstance(n,ast.Name):assert n.id=='source';return source
 assert isinstance(n,ast.Call)and isinstance(n.func,ast.Attribute)and n.func.attr=='replace'and not n.keywords
 return replacement(n.func.value).replace(*(ast.literal_eval(v)for v in n.args))
changes=0
for n in ast.parse((P/'qualified/prepare_recipe.py').read_text()).body:
 if isinstance(n,ast.Assign)and len(n.targets)==1 and isinstance(n.targets[0],ast.Name)and n.targets[0].id=='source'and isinstance(n.value,ast.Call)and isinstance(n.value.func,ast.Attribute)and n.value.func.attr=='replace':source=replacement(n.value);changes+=1
assert changes==3 and source==final
records=[]
for index in [1,2]:
 q=P/('rejected-numeric-attempt'+str(index).zfill(2));original=(q/'handwritten'/(M+'.lean')).read_text();assert original==old==(q/'project/ShielddSecurity'/(M+'.lean')).read_text();ev=[json.loads(l)for l in(q/'events.jsonl').read_text().splitlines()];assert len(ev)==2;r=ev[-1]['result'];assert r['status']=='failed'and r['seconds']<240;assert(q/'execute_bounded.py').read_bytes()==(P/'qualified/execute_bounded.py').read_bytes();assert read(q/'plan.json')['pressure_limits']==plan['pressure_limits'];logs=list(q.glob('runs/*/stdout.txt'))
 if index==1:assert r['reason']=='Physical memory pressure'and not logs
 else:assert r['reason']=='Lean exit 1'and len(logs)==1 and 'error:'in logs[0].read_text()
 records.append({'result':r,'source':pin(q/'handwritten'/(M+'.lean')),'events':pin(q/'events.jsonl'),'stdout':pin(logs[0])if logs else None,'exact_delta':''.join(difflib.unified_diff(original.splitlines(True),final.splitlines(True))),'scope':'Entire original failed attempt retained, including any placeholder/partial reports; no accepted evidence','all_definitions_and_theorem_contracts_unchanged':True})
assert '{backend with pending := fun _ => restore (decodeWordPending (.opened ordered members))}'in final
assert 'match contains gate lookup'in final and 'zipUnspent keys flags'in final and 'source_ord_membership_is_exact_mapped_key_membership'in final
assert 'typed_open_stage_has_exact_numeric_inspection_result_and_original_field_write'in final and 'inspection_success_order'in final and 'inspection_success_capacity_and_all_inputs'in final
scope='Explicit typed Open prior object with original ordered/member canonical fields is projected into the existing numeric pending backend. Constructed durable reader uses existing modeled contains/zipUnspent and fallible gate/lookup interfaces. Entire staging result agrees with numeric inspection for every refusal and exact original-field append, without caller codec inverse/admission/desired object/getter-success premises. Returned success derives exact numeric pending append and lookup-unspent/pending-freshness observations. Previous typed Open and canonical input-type invariants are an explicit model domain, not arbitrary native Any reachability. Real authenticated reader/Scalar/Ord/collections/usize/compiler/async/delta/ownership/full source trace remains owned OPEN. Original startup pressure and failed proof-search diagnostics retained, all definitions/contracts unchanged; selected full types/axioms must independently pass. No native execution or control claim; full Transfer/combined replay OPEN.'
r={'status':'PASSED_SOURCE_HISTORY','source':pin(S),'fresh_reports':6,'kind':'Exact maintained proof-only repair and modeled reader/refinement scope; no verifier','rejected':records,'scope':scope,'full_transfer':'OPEN','native_execution':'UNRUN'};(D/'semantic-source-review01.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'status':r['status'],'reports':6,'original_failed_attempts':2,'proof_only_repair':True}))
