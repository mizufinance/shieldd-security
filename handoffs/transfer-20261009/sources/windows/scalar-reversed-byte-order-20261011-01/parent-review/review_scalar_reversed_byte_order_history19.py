from pathlib import Path
import ast,json,hashlib,re,difflib
J=Path(__file__).resolve().parent;D=J/'windows-scalar-reversed-byte-order-review01';P=D/'packet01';M='TransferScalarReversedByteOrder01';S=P/'source/ShielddSecurity'/(M+'.lean');final=S.read_text()
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def regenerate(p,expected):
 t=ast.parse(p.read_text());n=next(n for n in t.body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name)and x.id=='source' for x in n.targets));source=ast.literal_eval(n.value);assert isinstance(source,str);names=re.findall(r'^(?:def|theorem) ([A-Za-z0-9_]+)',source,re.M);assert len(names)==8
 for name in names:source+='set_option pp.all true in\n#check @'+name+'\n#print axioms '+name+'\n'
 source+='end ShielddSecurity.TransferScalarReversedByteOrder01\n';assert source==expected
regenerate(P/'qualified/recipe_source.py',final);records=[]
for number,before in [('01','    | nil => rfl'),('02','    | nil => cases compare lastLeft.toNat lastRight.toNat <;> rfl')]:
 q=P/'rejected-kernel'/number;old=(q/'handwritten'/(M+'.lean')).read_text();assert old==(q/'project/ShielddSecurity'/(M+'.lean')).read_text();regenerate(q/('prepare_recipe.py' if number=='01' else 'recipe_source.py'),old)
 after='    | nil => simp only [List.nil_append, compareHighFirst]; cases compare lastLeft.toNat lastRight.toNat <;> rfl';marker='theorem equal_width_lexical_append_compares_suffix_only_after_equal_prefix';a=old.index(marker);b=old.index('theorem reversed_typed_byte_lexical_comparison',a);section=old[a:b];assert section.count(before)==1;assert old[:a]+section.replace(before,after)+old[b:]==final
 events=[json.loads(x) for x in(q/'events.jsonl').read_text().splitlines()];assert len(events)==2;failed=events[-1]['result'];assert failed['status']=='failed' and failed['reason']=='Lean exit 1' and 0<failed['seconds']<240
 assert json.loads((q/'plan.json').read_bytes())['pressure_limits']==json.loads((P/'qualified/plan.json').read_bytes())['pressure_limits'];assert(q/'execute_bounded.py').read_bytes()==(P/'qualified/execute_bounded.py').read_bytes()
 diagnostics=[x for x in(q/'runs'/('01-'+M)/'stdout.txt').read_text().splitlines() if 'error:' in x];assert diagnostics
 records.append(dict(kind='Original failed proof-only empty-list reduction',result=failed,source=pin(q/'handwritten'/(M+'.lean')),diagnostics=diagnostics,all_definitions_and_theorem_contracts_unchanged=True,exact_delta=''.join(difflib.unified_diff(old.splitlines(True),final.splitlines(True)))))
scope='Equal-width typed UInt8 lists reversed high-byte-first lexical comparison derives exact decodeLE mathematical comparison. Exact four-word source serializer derives Montgomery mathematical ordering; canonical raw domain additionally equates compare Eq with raw word equality. No caller ordering hypothesis. Actual Rust iterator cmp/u8 primitives, Scalar invariant, Ord trait, collections, compiler/cache and full execution binding remain owned OPEN.'
out=D/'semantic-source-review01.json';out.write_text(json.dumps(dict(status='PASSED',kind='Independent literal source regeneration and complete original failed-attempt review',source=pin(S),fresh_reports=8,rejected=records,scope=scope,full_transfer='OPEN',native_execution='UNRUN'),indent=2)+'\n');kpath=D/'endpoint-audit-review01.json';k=json.loads(kpath.read_text());assert k['status']=='PASSED' and k['fresh_reports']==8;k.update(rejected=records,semantic_scope=scope,precise_repair_review=pin(out));kpath.write_text(json.dumps(k,indent=2)+'\n');print(json.dumps(dict(status='PASSED',reports=8,failed_originals=2)))
