from pathlib import Path
import json,hashlib,argparse,re
parser=argparse.ArgumentParser();parser.add_argument('--plan',required=True);parser.add_argument('--semantic-source',required=True);parser.add_argument('--output',required=True);args=parser.parse_args()
plan_path=Path(args.plan);plan=json.loads(plan_path.read_text());semantic=Path(args.semantic_source)
assert hashlib.sha256(semantic.read_bytes()).hexdigest()==plan['semantic_source_sha256']
fields=plan['fields'];assert len(fields)==64 and [x['index'] for x in fields]==list(range(64))
assert [(x['index'],x['column']) for x in fields if x['role']=='computed_node']==[(7,195230),(8,195234)]
assert len({x['column'] for x in fields})==64
stored=[x for x in fields if x['role']=='witness_input'];assert len(stored)==62
out=Path(args.output);out.mkdir(parents=True,exist_ok=False);root=out/'source-root/ShielddSecurity';root.mkdir(parents=True)
header='/- GENERATED from the maintained public-statement binding generator. Edit the generator, then regenerate. -/\n'
opts='set_option autoImplicit false\nset_option maxHeartbeats 900000\nset_option maxRecDepth 8192\nnoncomputable section\n'
def save(module,body,audits):
 text=header+body+'\n'
 for name in audits:
  qualified='ShielddSecurity.'+module+'.'+name
  text+='\nset_option pp.all true in\n#check @'+qualified+'\n#print axioms '+qualified+'\n'
 (root/(module+'.lean')).write_text(text)
 return {'module':module,'sha256':hashlib.sha256(text.encode()).hexdigest(),'audits':audits}
module='PublicStatementLayout979';columns='['+','.join(str(x['column']) for x in stored)+']'
body='import ShielddSecurity.RegistryNaturalSeed298\n'+opts+'namespace ShielddSecurity.'+module+'\n'
body+='def columns : List Nat := '+columns+'\n'
body+='def inputColumns : List Nat := ['+','.join(str(x['column']) for x in fields)+']\n'
body+='theorem input_count : inputColumns.length=64 := rfl\n'
body+='theorem stored_count : columns.length=62 := rfl\n'
body+='theorem zero_outside : 0∉columns := by decide +kernel\n'
body+='theorem net_x_outside : 195230∉columns := by decide +kernel\n'
body+='theorem net_y_outside : 195234∉columns := by decide +kernel\n'
body+='theorem claimed_outside : 22737∉columns := by decide +kernel\n'
body+='theorem bounds (column : Nat) (member : column∈columns) : 3≤column ∧ column≤19849 := by\n  simp only [columns,List.mem_cons,List.not_mem_nil,or_false] at member\n  omega\n'
body+='end ShielddSecurity.'+module+'\n';manifest=[save(module,body,['input_count','stored_count','zero_outside','net_x_outside','net_y_outside','claimed_outside','bounds'])]
module='PublicStatementSeed980'
body='import ShielddSecurity.PublicStatementLayout979\nimport ShielddSecurity.TransferSem\n'+opts+'namespace ShielddSecurity.'+module+'\nopen ConcreteJubjubField01\n'
body+='def value (w : TransferSem.Witness) : Nat → F\n'
def expression(s):
 for alias,target in [('senderCore','(w.encryption.tiers 0)'),('senderExt','(w.encryption.tiers 1)'),('outputCore','(w.encryption.tiers 2)'),('outputExt','(w.encryption.tiers 3)')]:s=s.replace(alias+'.',target+'.')
 s=re.sub(r'\be\.', 'w.encryption.', s);return s
for x in stored: body+='  | '+str(x['column'])+' => ('+expression(x['semantic_expression'])+':F)\n'
body+='  | _ => 0\n'
body+='def seed (original : Nat → F) (w : TransferSem.Witness) (column : Nat) : F :=\n  if column∈PublicStatementLayout979.columns then value w column else original column\n'
audits=[]
for x in stored:
 i=x['index'];col=x['column'];name='field'+str(i)
 body+='theorem '+name+' (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :\n    seed original w '+str(col)+'=(((TransferSem.publicFields c w)['+str(i)+']?.getD 0:Nat):F) := by rfl\n';audits.append(name)
body+='theorem outside (original : Nat → F) (w : TransferSem.Witness) (column : Nat)\n    (separate : column∉PublicStatementLayout979.columns) : seed original w column=original column := by\n  exact if_neg separate\n'
body+='theorem zero (original : Nat → F) (w : TransferSem.Witness) : seed original w 0=original 0 :=\n  outside original w 0 PublicStatementLayout979.zero_outside\n'
body+='theorem net_x (original : Nat → F) (w : TransferSem.Witness) : seed original w 195230=original 195230 :=\n  outside original w 195230 PublicStatementLayout979.net_x_outside\n'
body+='theorem net_y (original : Nat → F) (w : TransferSem.Witness) : seed original w 195234=original 195234 :=\n  outside original w 195234 PublicStatementLayout979.net_y_outside\n'
body+='end ShielddSecurity.'+module+'\n';audits+=['outside','zero','net_x','net_y'];manifest.append(save(module,body,audits))
report={'status':'generated_UNRUN','plan_sha256':hashlib.sha256(plan_path.read_bytes()).hexdigest(),'semantic_sha256':plan['semantic_source_sha256'],'modules':manifest,'audit_count':sum(len(x['audits']) for x in manifest),'scope':'Initial seed only. Preservation by the full assignment, computed balance coordinates, claimed hash, and final circuit assertion remain unproved.','certification':False,'native_credit':0}
(out/'manifest.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='modules'}))
