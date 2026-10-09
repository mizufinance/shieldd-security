"""Compose six separately checked captured EPK relations and conservative constructors."""
from .generate_transfer_epk_all_native_frames import roles
from .generate_hash_round import _signature_audits


def generate(pairs):
    private,public=roles(pairs)
    name='TransferEpkAllScopes'
    relations=[f'TransferEpkScope{i}Relation' for i in range(6)]
    patches=[f'TransferEpkScope{i}PatchedCompletion' for i in range(6)]
    frames=[f'RuntimeTransferEpk{i}AllNativeFrame' for i in range(6)]
    crosses=[f'TransferEpkScope{i}PreservedBy{j}' for j in range(1,6) for i in range(j)]
    text=''.join(f'import ShielddSecurity.{dep}\n' for dep in [*patches,*frames,*crosses])
    text+=f'''namespace ShielddSecurity.{name}
set_option maxHeartbeats 400000
set_option maxRecDepth 4096

def blocks : List (List Row) := [{','.join(r+'.rows' for r in relations)}]
def rows : List Row := blocks.flatten
def inputColumns : List Nat := {[0,200692,*private]}
def privateColumns : List Nat := {private}
def publicColumns : List (Nat × Nat) := [{','.join(f'({x},{y})' for x,y in public)}]

def inputValues {{F : Type}} (rho : Nat → F) : List F := privateColumns.map rho
def nativePoints {{F : Type}} (rho : Nat → F) : List (Group.Point F) :=
  publicColumns.map (fun columns => ⟨rho columns.1,rho columns.2⟩)

variable {{F : Type}} [Field F]
  [CharP F 52435875175126190479447740508185965837690552500527637822603658699938581184513]

theorem sound {{J : Type}} [AddCommGroup J]
    (model : Group.StandardCurveModel J ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F))
    (rho : Nat → F) (generator : J) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F))
    (imaginarySquare : imaginary * imaginary = -1)
    (baseMeaning : (RuntimeTransferEpk0FixedWindow000.base : Group.Point F) = model.coordinates generator)
    (satisfied : Satisfies rho rows) :
    ∃ values : List Nat,values.length = 6 ∧
      (∀ n ∈ values,0 < n ∧ n < Scalar.order) ∧
      values.map (fun n => (n : F)) = inputValues rho ∧
      nativePoints rho = values.map (fun n => model.coordinates (n • generator)) := by
'''
    for i,rel in enumerate(relations):
        text+=f'''  have sat{i} : Satisfies rho {rel}.rows := by
    intro row member
    exact satisfied row (List.mem_flatten.mpr ⟨{rel}.rows,by simp [blocks],member⟩)
  have derived{i} := {rel}.sound model rho generator one four imaginary nonSquare imaginarySquare baseMeaning sat{i}
'''
    values=[r+'.scalar rho' for r in relations]
    text+=f'''  refine ⟨[{','.join(values)}],rfl,?_,?_,?_⟩
  · intro n member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with {' | '.join('rfl' for _ in values)}
'''
    for i in range(6):text+=f'    · exact ⟨derived{i}.1,derived{i}.2.1⟩\n'
    text+='  · simp only [inputValues,privateColumns,List.map_cons,List.map_nil,'+','.join(f'derived{i}.2.2.1' for i in range(6))+']\n'
    text+='  · simp only [nativePoints,publicColumns,List.map_cons,List.map_nil,'+','.join(f'derived{i}.2.2.2' for i in range(6))+']\n'
    params=' '.join(f'(n{i} : Nat)' for i in range(6))
    expression='rho'
    for i,patch in enumerate(patches):expression=f'({patch}.construct {expression} n{i})'
    text+=f'''
def construct (rho : Nat → F) {params} : Nat → F := {expression}

theorem complete {{J : Type}} [AddCommGroup J]
    (model : Group.StandardCurveModel J ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F))
    (rho : Nat → F) {params} (generator : J) (exactOrder : addOrderOf generator = Scalar.order)
'''
    for i,column in enumerate(private):
        text+=f'    (positive{i} : 0 < n{i}) (canonical{i} : n{i} < Scalar.order) (meaning{i} : rho {column} = (n{i} : F))\n'
    text+='''    (one : rho 0 = 1) (linked : rho 200692 = rho 0) (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare ((19257038036680949359750312669786877991949435402254120286184196891950884077233 : Int) : F))
    (imaginarySquare : imaginary * imaginary = -1)
    (baseMeaning : (RuntimeTransferEpk0FixedWindow000.base : Group.Point F) = model.coordinates generator) :
'''
    args=' '.join(f'n{i}' for i in range(6))
    points=','.join(f'model.coordinates (n{i} • generator)' for i in range(6))
    text+=f'''    Satisfies (construct rho {args}) rows ∧
      (∀ column ∈ inputColumns,construct rho {args} column = rho column) ∧
      nativePoints (construct rho {args}) = [{points}] := by
  let r0 := rho
  have keep0 : ∀ column ∈ inputColumns,r0 column = rho column := by intro column member;rfl
'''
    for i,(patch,frame,column) in enumerate(zip(patches,frames,private)):
        text+=f'''  have done{i} := {patch}.complete model r{i} n{i} generator exactOrder positive{i} canonical{i}
    ((keep{i} {column} (by decide)).trans meaning{i}) ((keep{i} 0 (by decide)).trans one)
    ((keep{i} 200692 (by decide)).trans (linked.trans (keep{i} 0 (by decide)).symm))
    four imaginary nonSquare imaginarySquare baseMeaning
  let r{i+1} := {patch}.construct r{i} n{i}
  have keep{i+1} : ∀ column ∈ inputColumns,r{i+1} column = rho column := by
    intro column member
    have step : r{i+1} column = r{i} column := by
      simp only [inputColumns,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with {' | '.join('rfl' for _ in range(8))}
      all_goals exact {frame}.preserves r{i} n{i} _ (by decide)
    exact step.trans (keep{i} column member)
  have sat{i+1}_{i} : Satisfies r{i+1} {relations[i]}.rows := done{i}.1
  have point{i+1}_{i} : (⟨r{i+1} {public[i][0]},r{i+1} {public[i][1]}⟩ : Group.Point F) =
      model.coordinates (n{i} • generator) := done{i}.2.2
'''
        for prior in range(i):
            x,y=public[prior]
            text+=f'''  have sat{i+1}_{prior} : Satisfies r{i+1} {relations[prior]}.rows :=
    TransferEpkScope{prior}PreservedBy{i}.preserves_rows r{i} n{i} sat{i}_{prior}
  have point{i+1}_{prior} : (⟨r{i+1} {x},r{i+1} {y}⟩ : Group.Point F) =
      model.coordinates (n{prior} • generator) := by
    simpa only [r{i+1},{frame}.preserves r{i} n{i} {x} (by decide),
      {frame}.preserves r{i} n{i} {y} (by decide)] using point{i}_{prior}
'''
    text+=f'''  change Satisfies r6 rows ∧ (∀ column ∈ inputColumns,r6 column = rho column) ∧
    nativePoints r6 = [{points}]
  refine ⟨?_,keep6,?_⟩
  · intro row member
    obtain ⟨block,inside,contained⟩ := List.mem_flatten.mp member
    simp only [blocks,List.mem_cons,List.not_mem_nil,or_false] at inside
    rcases inside with {' | '.join('rfl' for _ in range(6))}
'''
    for i in range(6):text+=f'    · exact sat6_{i} row contained\n'
    text+='  · simp only [nativePoints,publicColumns,List.map_cons,List.map_nil,'+','.join(f'point6_{i}' for i in range(6))+']\n'
    text+=f'''
#print axioms sound
#print axioms complete
end ShielddSecurity.{name}
'''
    return name,_signature_audits(text)
