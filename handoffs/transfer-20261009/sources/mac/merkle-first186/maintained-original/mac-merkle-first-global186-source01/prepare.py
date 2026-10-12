from pathlib import Path
import json,hashlib,sys,shutil
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work')
def require(v,m):
 if not v:raise ValueError(m)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated')
roots=[W/'mac-merkle-first-global186-source01',W/'mac-merkle-path-global187-source01']
require(all(not p.exists()for p in roots),'fresh source stages')
require(shutil.disk_usage(W).free>=2147483648+2097152,'source reserve')
g=(W/'mac-indexed-slices183-source01/generate.py').read_text()
header='set_option autoImplicit false\nset_option maxHeartbeats 900000\nset_option maxRecDepth 8192\nnoncomputable section\n'
mods={};leafnames=[]
for block,offset in enumerate(range(0,412,16)):
 n='CapturedMerkleFirstGlobal186B'+f'{block:02d}';leafnames.append(n);size=min(16,412-offset)
 b='import ShielddSecurity.MerkleHash27Whole\nimport ShielddSecurity.CompilerIndexedCopyStream171\nimport ShielddSecurity.CapturedFullRelation58\n'+header+'namespace ShielddSecurity.'+n+'\n'+'''open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
'''+f'''def rows : List Row := MerkleHash27Whole.selectedRows.drop {offset} |>.take {size}
def indices : List Nat := List.range' {2734+offset} {size}
def productionCheck : Bool := CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices rows
theorem checked : productionCheck=true := by decide +kernel
theorem count : rows.length={size} := by decide +kernel
variable {{F : Type}} [Field F] [CharP F p]
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) : Satisfies rho rows :=
 CompilerIndexedCopyStream171.sound copy CapturedFullRelation58.rowAt 200770 indices rows checked rho
 ((CapturedFullRelation58.verifier_links rho satisfied).2.2) satisfied
end ShielddSecurity.{n}
'''
 mods[n]=dict(body=b,names=['rows','indices','productionCheck','checked','count','sound'])
n='CapturedMerkleFirstSelection186'
b='import ShielddSecurity.MerkleSelection26Proof\nimport ShielddSecurity.CompilerIndexedCopyStream171\nimport ShielddSecurity.CapturedFullRelation58\n'+header+'namespace ShielddSecurity.'+n+'\n'+'''open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
def indices : List Nat := List.range' 2722 12++[200769]
def productionCheck : Bool := CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices MerkleSelection26Data.originalRows
theorem checked : productionCheck=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 Satisfies rho MerkleSelection26Data.originalRows :=
 CompilerIndexedCopyStream171.sound copy CapturedFullRelation58.rowAt 200770 indices MerkleSelection26Data.originalRows checked rho
 ((CapturedFullRelation58.verifier_links rho satisfied).2.2) satisfied
end ShielddSecurity.CapturedMerkleFirstSelection186
'''
mods[n]=dict(body=b,names=['indices','productionCheck','checked','sound'])
n='CapturedMerkleFirstGlobal186';widths='['+','.join(map(str,[16]*25+[12]))+']'
b=''.join('import ShielddSecurity.'+x+'\n'for x in leafnames)+'''import ShielddSecurity.CompilerIndexedSlices183
import ShielddSecurity.CapturedMerkleFirstSelection186
import ShielddSecurity.CapturedRegistryGlobalSound176
'''+header+'namespace ShielddSecurity.'+n+'\n'+'''open Compiler CompilerAssertionBlock51 CompilerSelectedChunks172 CompilerIndexedSlices183
open CapturedInitial73419Generic01 (p copy)
'''+f'''def chunks : List (List Row) := slicesAt MerkleHash27Whole.selectedRows 0 {widths}
theorem partition : chunks.flatten=MerkleHash27Whole.selectedRows.take 412 := by
 rw [chunks,slicesAt_eq,List.drop_zero,slices_flatten]
 rfl
def copyCheck : Bool := CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 [200769] (MerkleHash27Whole.selectedRows.drop 412)
theorem copy_checked : copyCheck=true := by decide +kernel
variable {{F : Type}} [Field F] [CharP F p]
theorem arithmetic_sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 Satisfies rho (MerkleHash27Whole.selectedRows.take 412) := by
 rw [←partition]
 apply flatten_sound
 change AllSatisfied rho [{','.join(x+'.rows'for x in leafnames)}]
 exact {''.join('⟨'+x+'.sound rho satisfied,'for x in leafnames)+'True.intro'+'⟩'*len(leafnames)}
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 Satisfies rho MerkleHash27Whole.selectedRows := by
 have copying := CompilerIndexedCopyStream171.sound copy CapturedFullRelation58.rowAt 200770 [200769]
   (MerkleHash27Whole.selectedRows.drop 412) copy_checked rho
   ((CapturedFullRelation58.verifier_links rho satisfied).2.2) satisfied
 intro row member
 rw [←List.take_append_drop 412 MerkleHash27Whole.selectedRows] at member
 rcases List.mem_append.mp member with member|member
 · exact arithmetic_sound rho satisfied row member
 · exact copying row member
theorem prior_sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 Satisfies rho MerkleHash27Whole.priorRows := by
 have families := CapturedRegistryGlobalSound176.row_families rho satisfied
 intro row member
 simp only [MerkleHash27Whole.priorRows,List.mem_append] at member
 rcases member with ((member|member)|member)|member
 · exact families.1 row member
 · exact families.2.1 row member
 · exact families.2.2 row member
 · exact CapturedMerkleFirstSelection186.sound rho satisfied row member
end ShielddSecurity.{n}
'''
mods[n]=dict(body=b,names=['chunks','partition','copyCheck','copy_checked','arithmetic_sound','sound','prior_sound'])
n='CapturedMerklePathGlobal187'
b='''import ShielddSecurity.CapturedMerkleGlobalLevels185
import ShielddSecurity.CapturedMerkleFirstGlobal186
import ShielddSecurity.MerklePath33Meaning
import ShielddSecurity.CapturedAnchorRowSound165
'''+header+'namespace ShielddSecurity.'+n+'\n'+'''open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
variable {F : Type} [Field F] [CharP F p]
theorem rest_sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 Satisfies rho (MerklePath33.rows (F:=F)) := by
 change Satisfies rho (CompilerSegmentChain33.rows copy (MerklePath33.piece (F:=F)) 15)
 apply CompilerIndexedSlices183.chain_sound
 intro i less
 change Satisfies rho (MerkleFamily32Whole.rows (F:=F) ⟨i%15,Nat.mod_lt i (by decide)⟩)
 exact CapturedMerkleGlobalLevels185.sound rho satisfied _
theorem output (rho : Nat → F) (one : rho 0=1)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 eval rho MerklePath33AnchorData.output=MerklePath33Meaning.meaning rho 15 :=
 MerklePath33Meaning.arbitrary rho one (CapturedMerkleFirstGlobal186.prior_sound rho satisfied)
 (CapturedMerkleFirstGlobal186.sound rho satisfied) (rest_sound rho satisfied)
theorem anchor (rho : Nat → F) (one : rho 0=1)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 rho 4=MerklePath33Meaning.meaning rho 15 :=
 (CapturedAnchorRowSound165.anchor_value rho satisfied).symm.trans (output rho one satisfied)
end ShielddSecurity.CapturedMerklePathGlobal187
'''
allmods=[mods,{n:dict(body=b,names=['rest_sound','output','anchor'])}]
inputs={}
for p in [W/'mac-merkle-hash27-whole04/source-root/ShielddSecurity/MerkleHash27Whole.lean',W/'mac-merkle-selection26-batch01/source-root/ShielddSecurity/MerkleSelection26Proof.lean',W/'mac-merkle-selection26-batch01/source-root/ShielddSecurity/MerkleSelection26Data.lean',W/'mac-merkle-path33-meaning03/source-root/ShielddSecurity/MerklePath33Meaning.lean',W/'mac-indexed-slices183-source01/source-root/ShielddSecurity/CompilerIndexedSlices183.lean',W/'mac-merkle-global-level185-source01/source-root/ShielddSecurity/CapturedMerkleGlobalLevels185.lean',W/'mac-registry-global-sound176-source01/source-root/ShielddSecurity/CapturedRegistryGlobalSound176.lean',W/'mac-anchor-row-sound165-source01/source-root/ShielddSecurity/CapturedAnchorRowSound165.lean']:
 inputs[str(p)]=pin(p)
for root,modules in zip(roots,allmods):
 root.mkdir();(root/'generate.py').write_text(g);(root/'prepare.py').write_bytes(Path(__file__).read_bytes())
 with(root/'templates01.json').open('x')as f:f.write(json.dumps(dict(inputs=inputs,modules=modules,scope='SOURCE-only full captured indexed relation plus rho0=1 derives16-level field-polynomial path/anchor on one assignment; finite instances and all new audits UNRUN. Boolean/canonical position, legal witness, native/source refinement and full Transfer remain OPEN.'),sort_keys=True,separators=(',',':'))+'\n')
print(json.dumps(dict(roots=list(map(str,roots)),modules=list(map(len,allmods)))))
