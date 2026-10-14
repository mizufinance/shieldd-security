from pathlib import Path
import json,argparse,hashlib,os
root=Path(__file__).resolve().parent;ap=argparse.ArgumentParser();ap.add_argument('output',type=Path);a=ap.parse_args();assert not a.output.exists();tmp=a.output.with_name(a.output.name+'.pending');tmp.mkdir();out=tmp/'source-root/ShielddSecurity';out.mkdir(parents=True);inventory={}
def lc(t):return '['+','.join(f'({c},{v})' for c,v in t)+']'
def rows(rs):return '['+','.join('⟨'+lc(x)+','+lc(y)+'⟩' for x,y in rs)+']'
def op(e):return '⟨'+str(e['isAdd']).lower()+',['+','.join(map(lc,e['ports']))+'],'+str(e['arithmeticStart'])+','+rows(e['arithmeticRows'])+','+str(e['assertionStart'])+','+rows(e['assertionRows'])+'⟩'
def selector(e):return '⟨['+','.join(map(lc,e['ports']))+'],'+str(e['arithmeticStart'])+','+rows(e['arithmeticRows'])+','+lc(e['outputX'])+','+lc(e['outputY'])+'⟩'
def emit(name,imports,body,audits):
 text='-- GENERATED from families.json by generate.py. Do not hand edit.\n'+''.join('import ShielddSecurity.'+n+'\n' for n in imports)+'set_option autoImplicit false\nset_option maxHeartbeats 900000\nset_option maxRecDepth 8192\nnoncomputable section\nnamespace ShielddSecurity.'+name+'\nopen Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableFamilyLayout562\n'+body+'\nend ShielddSecurity.'+name+'\n'
 for n in audits:text+='\nset_option pp.all true in\n#check @ShielddSecurity.'+name+'.'+n+'\n#print axioms ShielddSecurity.'+name+'.'+n+'\n'
 text=text.replace('\ndef ', '\nnoncomputable def ')
 p=out/(name+'.lean');p.write_text(text);inventory[name]=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),audits=['ShielddSecurity.'+name+'.'+n for n in audits])
for f in json.loads((root/'families.json').read_text()):
 family='TierCapture610F'+str(f['family']).zfill(2);layout='⟨'+lc(f['base'][0])+','+lc(f['base'][1])+','+','.join(map(str,[f['bits'],f['points'],f['assertions']]))+'⟩';leaves=[]
 for k,start in enumerate(range(1,126)):
  name=family+'B'+str(k).zfill(2);leaves.append(name);part=f['entries'][start:start+1]
  body='def layout : Family := '+layout+'\ndef entries : List (Nat × VariableWindowJoin443.Entry) := [\n'
  body+=',\n'.join('⟨'+str(e['window'])+',⟨'+','.join(op(o) for o in e['operations'])+','+selector(e['selector'])+'⟩⟩' for e in part)+']\n'
  body+='theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by decide +kernel\n'
  body+='theorem schedule : entries.map (fun e => e.1)=List.range\' '+str(start)+' '+str(len(part))+' := by rfl\n'
  emit(name,['VariableFamilyLayout562'],body,['checked','schedule'])
 def aggregate(name,parts,first,count):
  body='def layout : Family := '+layout+'\ndef entries : List (Nat × VariableWindowJoin443.Entry) := '+'++'.join(n+'.entries' for n in parts)+'\n'
  body+='theorem checked : entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := by\n'
  for i,n in enumerate(parts):body+='  have h'+str(i)+' : '+n+'.entries.all (fun e => checkComplete ⟨layout,e.1,e.2⟩)=true := '+n+'.checked\n'
  body+='  simp only [entries,List.all_append,'+','.join('h'+str(i) for i in range(len(parts)))+',Bool.true_and]\n'
  body+='theorem schedule : entries.map (fun e => e.1)=List.range\' '+str(first)+' '+str(count)+' := by\n  simp only [entries,List.map_append,'+','.join(n+'.schedule' for n in parts)+']\n  rfl\n'
  emit(name,parts,body,['checked','schedule'])
 groups=[]
 for offset in range(0,len(leaves),8):
  name=family+'G'+str(offset//8).zfill(2);groups.append(name)
  part=leaves[offset:offset+8];aggregate(name,part,offset+1,len(part))
 aggregate(family,groups,1,125)
(tmp/'generation.json').write_text(json.dumps(inventory,indent=2)+'\n');os.replace(tmp,a.output);print(json.dumps(dict(modules=len(inventory),scope='Generated positive variable windows; kernel checks pending, no proof credit')))
