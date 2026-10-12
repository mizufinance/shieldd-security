"""Small upper-bound certificates and a balanced Boolean seed frame."""
from pathlib import Path
import json,hashlib
root=Path(__file__).resolve().parent
import argparse,os
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();out=a.output.resolve();assert not out.exists();pending=out.with_name(out.name+'.pending');pending.mkdir();leaves=json.loads((root/'leaves.json').read_bytes());assert len(leaves)==58
sources=pending/'source-root/ShielddSecurity';sources.mkdir(parents=True,exist_ok=True);outputs={}
def emit(name,imports,body,names):
    text=''.join('import '+n+'\n' for n in imports)+'set_option autoImplicit false\nset_option maxHeartbeats 900000\nset_option maxRecDepth 8192\nnoncomputable section\nnamespace ShielddSecurity.'+name+'\n'+body+'\nend ShielddSecurity.'+name+'\n'
    qualified=['ShielddSecurity.'+name+'.'+n for n in names]
    text+=''.join('\nset_option pp.all true in\n#check @'+n+'\n#print axioms '+n+'\n' for n in qualified)
    p=sources/(name+'.lean');p.write_text(text);outputs[name]=dict(source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),audits=qualified)
pairs=[]
for i,leaf in enumerate(leaves):
    name='SharedPublicBooleanFrame301B'+str(i).zfill(2)
    emit(name,['ShielddSecurity.'+leaf], 'theorem checked : '+leaf+'.slots.all (fun pair => decide (pair.2 < 22737)) = true := by decide +kernel',['checked'])
    pairs.append((leaf,name))
body='theorem boolean_checked : CapturedBooleanRoot209.columns.all (fun column => decide (column < 22737)) = true := by\n  simp only [CapturedBooleanRoot209.columns, CapturedBooleanRoot209.slots, List.map_append, List.all_append, List.all_map, Function.comp_def, '+', '.join(n+'.checked' for l,n in pairs)+', Bool.true_and]\n'
body+='''theorem boolean_outside : (22737 : Nat) ∉ CapturedBooleanRoot209.columns := by
  intro member
  have before := of_decide_eq_true ((List.all_eq_true.mp boolean_checked) 22737 member)
  omega

theorem word_checked : CapturedWordRoot213.words.all
    (fun entry => decide (entry.1.start + entry.1.width ≤ 22737)) = true := by decide +kernel

theorem word_outside (entry : WordHints210.Slot × Nat)
    (member : entry ∈ CapturedWordRoot213.words) : (22737 : Nat) ∉ WordHints210.columns entry.1 := by
  intro inside
  have before := of_decide_eq_true ((List.all_eq_true.mp word_checked) entry member)
  obtain ⟨offset, bounded, equal⟩ := List.mem_range'.mp inside
  simp only [Nat.one_mul] at equal
  omega

theorem seed_outside : (22737 : Nat) ∉ SharedWordWitness221.seedColumns := by
  intro member
  rcases List.mem_append.mp member with boolean | word
  · exact boolean_outside boolean
  · obtain ⟨slot, selected, inside⟩ := List.mem_flatMap.mp word
    obtain ⟨entry, known, equal⟩ := List.mem_map.mp selected
    subst slot
    exact word_outside entry known inside

variable {F : Type} [Field F]
theorem seeded_public (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool) :
    SharedWordWitness221.seeded base numbers fallback 22737 = base 22737 :=
  BooleanHints207.seeded_outside base _ _ 22737 seed_outside

theorem completed_public_input (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool) :
    SharedWordWitness221.completed base numbers fallback 22737 = base 22737 := by
  exact (CapturedFullRelation58.candidate_inputs _ 22734 (by decide)).trans
    (seeded_public base numbers fallback)

variable [CharP F CompilerArithmeticTransport41.p]
theorem completed_declared_public (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool) :
    SharedWordWitness221.completed base numbers fallback 1 = base 22737 :=
  (CapturedFullRelation58.candidate_links _).1.trans (completed_public_input base numbers fallback)
'''
emit('SharedPublicFrame301',['ShielddSecurity.SharedWordWitness221']+['ShielddSecurity.'+n for l,n in pairs],body,['boolean_checked','boolean_outside','word_checked','word_outside','seed_outside','seeded_public','completed_public_input','completed_declared_public'])
(pending/'generation.json').write_text(json.dumps(dict(outputs=outputs,leaf_count=len(leaves)),sort_keys=True)+'\n')
os.replace(pending,out)
print(json.dumps(dict(modules=len(outputs),leaf_count=len(leaves),scope='Public-input frame only; no full assertion truth.')))

