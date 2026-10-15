from pathlib import Path
import json,argparse,hashlib,re,os
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();assert not a.output.exists();pending=a.output.with_name(a.output.name+'.pending');assert not pending.exists();dst=pending/'source-root/ShielddSecurity';dst.mkdir(parents=True)
D=json.loads((root/'data.json').read_text());assert [(d['user'],d['level']) for d in D['levels']]==[(u,i) for u in ['S','R'] for i in range(16)]
lc=lambda xs:'['+','.join(f'({c},{v})' for c,v in xs)+']'
row=lambda r:'⟨'+lc(r[0])+','+lc(r[1])+'⟩'
def entry(d):return '⟨'+str(d['source_node'])+',false,'+','.join(lc(d[k]) for k in ['left','right','output','auxiliary'])+','+str(d['start'])+',['+','.join(row(r) for r in d['rows'])+']⟩'
modules={}
for data in D['levels']:
 level=data['level'];ci=data['call'];user=data['user'];name=f'UserPathSelector964{user}L{level:02d}';prev=f'UserPathHash958C{ci-1}';cur=f'UserPathHash958C{ci}';node=prev+'.result';nv='eval rho '+node;low=(1579 if user=='S' else 1817)+2*level;high=low+1;sib=(1531 if user=='S' else 1769)+3*level;cols=[e['output'][0][0] for e in data['entries']];l,r=cols[:2]
 shapes={
 'leftSwap':(lc([[low,1]]),lc([[sib,1]])+'++scaleLinear (-1) '+node,f'rho {low}',f'rho {sib}-{nv}'),
 'rightSwap':(lc([[low,1]]),lc([[sib+2,1]])+'++scaleLinear (-1) '+node,f'rho {low}',f'rho {sib+2}-{nv}'),
 'select0':(lc([[high,1]]),lc([[sib,1],[l,-1]])+'++scaleLinear (-1) '+node,f'rho {high}',f'rho {sib}-rho {l}-{nv}'),
 'select1':(lc([[high,1]]),lc([[sib+1,1],[sib,-1],[l,1]]),f'rho {high}',f'rho {sib+1}-rho {sib}+rho {l}'),
 'select2':(lc([[high,1]]),node+'++'+lc([[r,1],[sib+1,-1]]),f'rho {high}',f'{nv}+rho {r}-rho {sib+1}'),
 'select3':(lc([[high,1]]),lc([[r,-1]]),f'rho {high}',f'-rho {r}')}
 s=f'''-- GENERATED from exact captured path selector products; do not edit.
import ShielddSecurity.MapArithmeticAdapter704
import ShielddSecurity.QuaternarySelector944
import ShielddSecurity.{prev}
import ShielddSecurity.{cur}
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.{name}
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 MapArithmeticAdapter704
variable {{F : Type}} [Field F] [CharP F p]
attribute [local irreducible] SatisfiesAt
''';names=[]
 for e in data['entries']:
  n=e['name'];out=e['output'][0][0];left,right,lv,rv=shapes[n];s+=f'noncomputable def {n}Entry : Entry := '+entry(e)+'\n'
  s+=f'''theorem {n}_checked : check {n}Entry=true := by decide +kernel
theorem {n}_left : canonical p {n}Entry.left=canonical p ({left}) := by decide +kernel
theorem {n}_right : canonical p {n}Entry.right=canonical p ({right}) := by decide +kernel
theorem {n}_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho {out}=({lv})*({rv}) := by
  have result := MapArithmeticAdapter704.equation {n}Entry {n}_checked rho arithmetic
  have output : eval rho {n}Entry.output=rho {out} := by simp [{n}Entry,eval]
  have square : {n}Entry.square=false := rfl
  rw [output,square] at result
  simp only [Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ {n}_left,canonical_equal rho _ _ {n}_right] at result
  simpa only [eval_append,eval_scale,eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_one_mul,neg_mul,sub_eq_add_neg,add_assoc] using result
''';names += [n+'_checked',n+'_left',n+'_right',n+'_value']
 children=[node+'++'+lc([[l,1],[cols[2],1]]),lc([[sib,1],[l,-1],[cols[3],1]]),lc([[sib+1,1],[cols[4],1]]),lc([[sib+2,1],[cols[5],1]])]
 for i,terms in enumerate(data['children']):
  s+=f'noncomputable def child{i} : Linear := {lc(terms)}\ntheorem child{i}_shape : canonical p child{i}=canonical p ({children[i]}) := by decide +kernel\n';names.append(f'child{i}_shape')
 s+=f'''theorem inputs_shape : {cur}.inputs=[[(0,{level+1})],child0,child1,child2,child3] := by decide +kernel

theorem input_values (rho : Nat → F) (one : rho 0=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) (lo hi : Bool)
    (low : rho {low}=BooleanHints207.bitValue lo) (high : rho {high}=BooleanHints207.bitValue hi) :
    {cur}.inputs.map (eval rho)=[({level+1}:F)]++QuaternarySelector944.children
      (if hi then (if lo then 3 else 2) else (if lo then 1 else 0)) ({nv}) (rho {sib}) (rho {sib+1}) (rho {sib+2}) := by
  rw [inputs_shape]
  simp only [List.map_cons,List.map_nil,List.singleton_append]
  have first : eval rho [(0,{level+1})]=({level+1}:F) := by norm_num [eval,one]
  rw [first]
  apply congrArg (fun tail : List F => ({level+1}:F)::tail)
  rw [canonical_equal rho _ _ child0_shape,canonical_equal rho _ _ child1_shape,
    canonical_equal rho _ _ child2_shape,canonical_equal rho _ _ child3_shape]
  have singleton (column : Nat) : eval rho [(column,1)]=rho column := by simp [eval]
  have pair (a b : Nat) : eval rho [(a,1),(b,1)]=rho a+rho b := by simp [eval]
  have triple (a b c : Nat) : eval rho [(a,1),(b,-1),(c,1)]=rho a-rho b+rho c := by simp [eval];ring
  simp only [eval_append,pair,triple]
  rw [select0_value rho arithmetic,select1_value rho arithmetic,select2_value rho arithmetic,select3_value rho arithmetic,
    leftSwap_value rho arithmetic,rightSwap_value rho arithmetic,low,high]
  have selected := QuaternarySelector944.select lo hi ({nv}) (rho {sib}) (rho {sib+1}) (rho {sib+2})
  dsimp only at selected
  ring_nf at selected ⊢ <;> exact selected
end ShielddSecurity.{name}
''';names += ['inputs_shape','input_values']
 # No unused helper under the strict warning audit.
 s=s.replace('  have singleton (column : Nat) : eval rho [(column,1)]=rho column := by simp [eval]\n','')
 for n in names:s+=f'\nset_option pp.all true in\n#check @ShielddSecurity.{name}.{n}\n#print axioms ShielddSecurity.{name}.{n}\n'
 f=dst/(name+'.lean');f.write_text(s);modules[name]=dict(sha256=hashlib.sha256(f.read_bytes()).hexdigest(),audits=names)
name='UserPathSelectors964';s=''.join('import ShielddSecurity.'+m+'\n' for m in modules)+f'namespace ShielddSecurity.{name}\ndef levelCount : Nat := 32\nend ShielddSecurity.{name}\nset_option pp.all true in\n#check @ShielddSecurity.{name}.levelCount\n#print axioms ShielddSecurity.{name}.levelCount\n';f=dst/(name+'.lean');f.write_text(s);modules[name]=dict(sha256=hashlib.sha256(f.read_bytes()).hexdigest(),audits=['levelCount'])
(pending/'generation.json').write_text(json.dumps(modules,indent=2,sort_keys=True)+'\n');os.replace(pending,a.output);print(json.dumps(dict(modules=len(modules),audits=sum(len(v['audits']) for v in modules.values()))))
