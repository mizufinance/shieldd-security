from pathlib import Path
import argparse,json,hashlib,os
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();out=a.output.resolve();assert not out.exists();tmp=out.with_name(out.name+'.pending');tmp.mkdir()
leaves=json.loads((root/'leaves.json').read_bytes());assert len(leaves)==58;sources=tmp/'source-root/ShielddSecurity';sources.mkdir(parents=True);outputs={}
def emit(name,imports,body,names):
 text=''.join('import '+n+'\n' for n in imports)+'set_option autoImplicit false\nset_option maxHeartbeats 900000\nset_option maxRecDepth 8192\nnoncomputable section\nnamespace ShielddSecurity.'+name+'\n'+body+'\nend ShielddSecurity.'+name+'\n'
 names=['ShielddSecurity.'+name+'.'+n for n in names];text+=''.join('\nset_option pp.all true in\n#check @'+n+'\n#print axioms '+n+'\n' for n in names);p=sources/(name+'.lean');p.write_text(text);outputs[name]=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),audits=names)
proofs=[]
for i,leaf in enumerate(leaves):
 name='ZeroHintBooleanShape304B'+str(i).zfill(2);proofs.append(name)
 emit(name,['ShielddSecurity.'+leaf],'theorem checked : '+leaf+'.slots.all (fun pair => decide\n    (113 ≤ pair.2 → pair.2 < 135 → pair.2 % 2 = 1)) = true := by decide +kernel',['checked'])
body='theorem checked : CapturedBooleanRoot209.columns.all (fun column => decide\n    (113 ≤ column → column < 135 → column % 2 = 1)) = true := by\n  simp only [CapturedBooleanRoot209.columns, CapturedBooleanRoot209.slots, List.map_append, List.all_append, List.all_map, Function.comp_def, '+', '.join(n+'.checked' for n in proofs)+', Bool.true_and]\n'
body+='''theorem boolean_odd (column : Nat) (member : column ∈ CapturedBooleanRoot209.columns)
    (lower : 113 ≤ column) (upper : column < 135) : column % 2 = 1 :=
  (of_decide_eq_true ((List.all_eq_true.mp checked) column member)) lower upper

theorem selected_odd (column : Nat) (member : column ∈ SharedWordWitness221.seedColumns)
    (lower : 113 ≤ column) (upper : column < 135) : column % 2 = 1 := by
  rcases List.mem_append.mp member with boolean | word
  · exact boolean_odd column boolean lower upper
  · obtain ⟨slot, known, inside⟩ := List.mem_flatMap.mp word
    obtain ⟨entry, entryKnown, equal⟩ := List.mem_map.mp known
    subst slot
    exact False.elim (ZeroHintWordFrame303.outside_window entry entryKnown column lower upper inside)
'''
emit('ZeroHintBooleanShape304',['ShielddSecurity.ZeroHintWordFrame303']+['ShielddSecurity.'+n for n in proofs],body,['checked','boolean_odd','selected_odd'])
(tmp/'generation.json').write_text(json.dumps(outputs,sort_keys=True)+'\n');os.replace(tmp,out);print(json.dumps(dict(modules=len(outputs),scope='Zero-hint Boolean write-set parity only.')))

