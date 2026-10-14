from pathlib import Path
import argparse,json,hashlib,os
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();assert not a.output.exists();out=a.output.with_name(a.output.name+'.pending');out.mkdir();sources=out/'source-root/ShielddSecurity';sources.mkdir(parents=True)
items=json.loads((root/'table.json').read_text());assert len(items)==126
inventory={}
def lc(ts):return '['+','.join('('+str(c)+','+str(v)+')' for c,v in ts)+']'
def rows(rs):return '['+','.join('⟨'+lc(x)+','+lc(y)+'⟩' for x,y in rs)+']'
def entry(e):
 px=e['arithmeticRows'][1][1][0][0];py=e['arithmeticRows'][3][1][0][0]
 return '⟨'+','.join(map(str,[e['low'],e['high'],*e['base'],*e['twice'],*e['triple'],px,py,e['arithmeticStart']]))+','+rows(e['arithmeticRows'])+','+lc(e['selected'][0])+','+lc(e['selected'][1])+'⟩'
def emit(n,imports,body,names):
 s='-- GENERATED from table.json by generate.py. Do not hand edit.\n'+''.join('import ShielddSecurity.'+x+'\n' for x in imports)+'''set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.'''+n+'''
open Compiler CompilerArithmeticTransport41 FixedSelectorAdapter480 ConcreteJubjubField01
'''+body+'\nend ShielddSecurity.'+n+'\n'
 names=['ShielddSecurity.'+n+'.'+x for x in names]
 for k in names:s+='\nset_option pp.all true in\n#check @'+k+'\n#print axioms '+k+'\n'
 s=s.replace('\ndef ', '\nnoncomputable def ')
 p=sources/(n+'.lean');p.write_text(s);inventory[n]=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),audits=names)
leaves=[]
for i,start in enumerate(range(0,len(items),2)):
 n='BalanceBlindingSelectors672B'+str(i).zfill(3);leaves.append(n);part=items[start:start+2]
 body='def tables : List (Entry × Group.Point F) := ['+','.join('('+entry(e)+',⟨'+','.join(map(str,e['next']))+'⟩)' for e in part)+']\n'
 body+='def entries : List Entry := tables.map Prod.fst\n'
 body+='theorem checked : entries.all check=true := by decide +kernel\n'
 body+='theorem geometry_checked : tables.all (fun item => decide (FixedTableGeometry482.Equations (CapturedFirstSubgroup81.d:F) (base item.1) (twice item.1) (triple item.1) item.2))=true := by decide +kernel\n'
 emit(n,['FixedTableGeometry482','ConcreteJubjubField01'],body,['tables','entries','checked','geometry_checked'])
groups=[]
for i,start in enumerate(range(0,len(leaves),8)):
 part=leaves[start:start+8];n='BalanceBlindingSelectors672G'+str(i).zfill(2);groups.append(n)
 body='def tables : List (Entry × Group.Point F) := '+'++'.join(x+'.tables' for x in part)+'\n'
 body+='def entries : List Entry := '+'++'.join(x+'.entries' for x in part)+'\n'
 body+='theorem checked : entries.all check=true := by\n  simp only [entries,List.all_append,'+','.join(x+'.checked' for x in part)+',Bool.true_and]\n'
 body+='theorem geometry_checked : tables.all (fun item => decide (FixedTableGeometry482.Equations (CapturedFirstSubgroup81.d:F) (base item.1) (twice item.1) (triple item.1) item.2))=true := by\n  simp only [tables,List.all_append,'+','.join(x+'.geometry_checked' for x in part)+',Bool.true_and]\n'
 body+='theorem count : entries.length='+str(len(part)*2)+' := by rfl\n'
 emit(n,part,body,['tables','entries','checked','geometry_checked','count'])
body='def tables : List (Entry × Group.Point F) := '+'++'.join(x+'.tables' for x in groups)+'\n'
body+='def entries : List Entry := '+'++'.join(x+'.entries' for x in groups)+'\n'
body+='theorem checked : entries.all check=true := by\n  simp only [entries,List.all_append,'+','.join(x+'.checked' for x in groups)+',Bool.true_and]\n'
body+='theorem geometry_checked : tables.all (fun item => decide (FixedTableGeometry482.Equations (CapturedFirstSubgroup81.d:F) (base item.1) (twice item.1) (triple item.1) item.2))=true := by\n  simp only [tables,List.all_append,'+','.join(x+'.geometry_checked' for x in groups)+',Bool.true_and]\n'
body+='theorem count : entries.length=126 := by\n  simp only [entries,List.length_append,'+','.join(x+'.count' for x in groups)+']\n'
emit('BalanceBlindingSelectors672',groups,body,['tables','entries','checked','geometry_checked','count'])
(out/'generation.json').write_text(json.dumps(inventory,indent=2,sort_keys=True)+'\n');os.replace(out,a.output);print(json.dumps(dict(modules=len(inventory),selectors=len(items))))
