from pathlib import Path
import argparse,json,hashlib,os
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('output',type=Path);a=ap.parse_args();assert not a.output.exists();out=a.output.with_name(a.output.name+'.pending');out.mkdir();sources=out/'source-root/ShielddSecurity';sources.mkdir(parents=True);inventory={}
families=json.loads((root/'families.json').read_text())
def lc(t):return '['+','.join(f'({k},{v})' for k,v in t)+']'
def rows(rs):return '['+','.join('⟨'+lc(x)+','+lc(y)+'⟩' for x,y in rs)+']'
def op(e):return '⟨true,['+','.join(map(lc,e['ports']))+'],'+str(e['arithmeticStart'])+','+rows(e['arithmeticRows'])+','+str(e['assertionStart'])+','+rows(e['assertionRows'])+'⟩'
def sel(e):
 px=e['arithmeticRows'][1][1][0][0];py=e['arithmeticRows'][3][1][0][0]
 return '⟨'+','.join(map(str,[e['low'],e['high'],*e['base'],*e['twice'],*e['triple'],px,py,e['arithmeticStart']]))+','+rows(e['arithmeticRows'])+','+lc(e['selected'][0])+','+lc(e['selected'][1])+'⟩'
def emit(n,imports,body,audits):
 s='-- GENERATED from families.json by generate.py. Do not hand edit.\n'+''.join('import ShielddSecurity.'+i+'\n' for i in imports)+'set_option autoImplicit false\nset_option maxHeartbeats 900000\nset_option maxRecDepth 8192\nnoncomputable section\nnamespace ShielddSecurity.'+n+'\nopen FixedFamilyJoin543\n'+body+'\nend ShielddSecurity.'+n+'\n'
 for t in audits:s+='set_option pp.all true in\n#check @ShielddSecurity.'+n+'.'+t+'\n#print axioms ShielddSecurity.'+n+'.'+t+'\n'
 s=s.replace('\ndef ', '\nnoncomputable def ')
 p=sources/(n+'.lean');p.write_text(s);inventory[n]=dict(source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),audits=audits)
for f in families:
 prefix='FixedFamilies544F'+str(f['family']).zfill(2);layout='⟨'+','.join(str(f['layout'][k]) for k in ['bits','points','assertions'])+'⟩';leaves=[]
 for b,start in enumerate(range(0,125,2)):
  part=f['entries'][start:start+2];n=prefix+'B'+str(b).zfill(2);leaves.append(n);body='def layout : Layout := '+layout+'\n';audits=[]
  for j,e in enumerate(part):
   body+=f'def entry{j} : Entry := ⟨{e["index"]},'+op(e['operation'])+','+sel(e['selector'])+'⟩\n'
   body+=f'theorem operation{j} : VariableOperationAdapter434.check entry{j}.operation=true := by decide +kernel\n'
   body+=f'theorem selector{j} : FixedSelectorAdapter480.check entry{j}.selector=true := by decide +kernel\n'
   body+=f'theorem checked{j} : check layout entry{j}=true := by\n  have valid : Valid layout entry{j} := ⟨operation{j},selector{j},by decide +kernel⟩\n  simp only [check,valid,decide_true]\n'
   body+=f'theorem matched{j} : FixedWindowMeaning491.check entry{j}=true := by decide +kernel\n'
   audits += [f'operation{j}',f'selector{j}',f'checked{j}',f'matched{j}']
  body+='def entries : List Entry := ['+','.join('entry'+str(j) for j in range(len(part)))+']\n'
  body+='theorem checked : entries.all (check layout)=true := by\n  simp only [entries,List.all_cons,List.all_nil,'+','.join('checked'+str(j) for j in range(len(part)))+',Bool.true_and]\n'
  body+='theorem matched : entries.all FixedWindowMeaning491.check=true := by\n  simp only [entries,List.all_cons,List.all_nil,'+','.join('matched'+str(j) for j in range(len(part)))+',Bool.true_and]\n'
  body+='theorem schedule : entries.map (fun e => e.index)='+str([e['index'] for e in part]).replace(' ','')+' := rfl\n'
  emit(n,['FixedFamilyJoin543'],body,audits+['checked','matched','schedule'])
 n=prefix;body='def layout : Layout := '+layout+'\ndef entries : List Entry := '+'++'.join(x+'.entries' for x in leaves)+'\n'
 body+='theorem checked : entries.all (check layout)=true := by\n'
 for i,x in enumerate(leaves):body+=f'  have h{i} : {x}.entries.all (check layout)=true := {x}.checked\n'
 body+='  simp only [entries,List.all_append,'+','.join('h'+str(i) for i in range(len(leaves)))+',Bool.true_and]\n'
 body+='theorem matched : entries.all FixedWindowMeaning491.check=true := by\n  simp only [entries,List.all_append,'+','.join(x+'.matched' for x in leaves)+',Bool.true_and]\n'
 body+='theorem schedule : entries.map (fun e => e.index)=List.range\' 1 125 := by\n  simp only [entries,List.map_append,'+','.join(x+'.schedule' for x in leaves)+']\n  rfl\n'
 emit(n,leaves,body,['checked','matched','schedule'])
(out/'generation.json').write_text(json.dumps(inventory,indent=2)+'\n');os.replace(out,a.output);print(json.dumps(dict(modules=len(inventory),families=len(families),scope='kernel checks not yet run')))
