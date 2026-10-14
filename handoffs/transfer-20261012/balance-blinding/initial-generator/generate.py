from pathlib import Path
import json,argparse,hashlib,os
root=Path(__file__).resolve().parent;ap=argparse.ArgumentParser();ap.add_argument('output',type=Path);a=ap.parse_args();assert not a.output.exists();out=a.output.with_name(a.output.name+'.pending');out.mkdir();dest=out/'source-root/ShielddSecurity';dest.mkdir(parents=True);inventory={}
def lc(t):return '['+','.join(f'({k},{v})' for k,v in t)+']'
def rows(rs):return '['+','.join('⟨'+lc(x)+','+lc(y)+'⟩' for x,y in rs)+']'
def selector(e):
 px=e['arithmeticRows'][1][1][0][0];py=e['arithmeticRows'][3][1][0][0]
 return '⟨'+','.join(map(str,[e['low'],e['high'],*e['base'],*e['twice'],*e['triple'],px,py,e['arithmeticStart']]))+','+rows(e['arithmeticRows'])+','+lc(e['selected'][0])+','+lc(e['selected'][1])+'⟩'
for f in json.loads((root/'families.json').read_text()):
 n='BalanceBlindingInitial684F'+str(f['family']).zfill(2);start=f['layout']['points'];bits=f['layout']['bits'];pos=f['layout']['assertions']-2;e=f['initial']
 terms=[[[start,1]],[[start+1,1]],*e['selected']]
 body='noncomputable def entry : PointEqualityAdapter440.Entry := ⟨'+','.join(map(lc,terms))+','+str(pos)+','+rows(f['initialRows'])+'⟩\n'
 body+='theorem checked : PointEqualityAdapter440.check entry=true := by decide +kernel\n'
 body+='noncomputable def selector : FixedSelectorAdapter480.Entry := '+selector(e)+'\n'
 body+='theorem selector_checked : FixedSelectorAdapter480.check selector=true := by decide +kernel\n'
 body+=f'''theorem rows_iff {{F : Type}} [Field F] [CharP F p] (rho : Nat → F)
    (one : rho copy=1) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+{pos}+i)) 2 ↔
      columnPoint rho {start}=Group.windowPoint (rho {bits}) (rho {bits+1})
        (FixedSelectorAdapter480.base selector) (FixedSelectorAdapter480.twice selector)
        (FixedSelectorAdapter480.triple selector) := by
  have equivalence := PointEqualityAdapter440.equality_iff entry checked rho
  have x : canonical p entry.expectedX=canonical p selector.outputX := by decide +kernel
  have y : canonical p entry.expectedY=canonical p selector.outputY := by decide +kernel
  rw [canonical_equal rho _ _ x,canonical_equal rho _ _ y] at equivalence
  have outputX : entry.outputX=[({start},1)] := rfl
  have outputY : entry.outputY=[({start+1},1)] := rfl
  rw [outputX,outputY] at equivalence
  simp only [eval,Int.cast_one,one_mul,add_zero] at equivalence
  rw [FixedSelectorAdapter480.coordinates selector selector_checked rho one arithmetic] at equivalence
  exact equivalence

theorem table_points :
    (FixedSelectorAdapter480.base selector : Group.Point ConcreteJubjubField01.F)=FixedSelectorAdapter480.base (BalanceBlindingTables673.table 0).1 ∧
    (FixedSelectorAdapter480.twice selector : Group.Point ConcreteJubjubField01.F)=FixedSelectorAdapter480.twice (BalanceBlindingTables673.table 0).1 ∧
    (FixedSelectorAdapter480.triple selector : Group.Point ConcreteJubjubField01.F)=FixedSelectorAdapter480.triple (BalanceBlindingTables673.table 0).1 := by
  exact ⟨rfl,rfl,rfl⟩
'''
 s='-- GENERATED from families.json by generate.py. Do not hand edit.\nimport ShielddSecurity.PointEqualityAdapter440\nimport ShielddSecurity.VariableWindowColumns449\nimport ShielddSecurity.BalanceBlindingTables673\nset_option autoImplicit false\nset_option maxHeartbeats 900000\nset_option maxRecDepth 8192\nnoncomputable section\nnamespace ShielddSecurity.'+n+'\nopen Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableWindowColumns449\n'+body+'\nend ShielddSecurity.'+n+'\n'
 names=['checked','selector_checked','rows_iff','table_points']
 for t in names:s+='set_option pp.all true in\n#check @ShielddSecurity.'+n+'.'+t+'\n#print axioms ShielddSecurity.'+n+'.'+t+'\n'
 p=dest/(n+'.lean');p.write_text(s);inventory[n]=dict(source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),positions=[pos,pos+1],audits=names)
(out/'generation.json').write_text(json.dumps(inventory,indent=2)+'\n');os.replace(out,a.output);print('Generated1 exact balance-blinding initial row adapters; kernel checks pending')
