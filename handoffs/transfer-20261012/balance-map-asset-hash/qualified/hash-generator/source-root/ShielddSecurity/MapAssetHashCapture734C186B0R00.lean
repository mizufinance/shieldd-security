/- Generated from maintained map asset-hash generator; edit generator or templates. -/
import ShielddSecurity.AuthorizationPoseidonPhase517
import ShielddSecurity.TransferPoseidonWidth3Call08Shared01
-- Generated from exact captured rows; no semantic input assumptions.
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapAssetHashCapture734C186B0R00
open Compiler CompilerIndexed01 Poseidon
open CapturedInitial73419Generic01 (p copy)
noncomputable def parameters := TransferPoseidonWidth3Call08Shared01.parameters
noncomputable def before : State Linear 3 := fun i => (Array.mk [[(0,282)],[(6,1)],[]]).getD i.val []
noncomputable def shifted : State Linear 3 := fun i => (Array.mk [[(0,48991097081732275468845314168021420565497297775988823234113406403095118809498)],[(0,38385660029618165285848698857635215143135976511856402182142757680787979296154),(6,1)],[(0,45664917788634056160947231182803089169570746657219074370482409200042991921246)]]).getD i.val []
noncomputable def transformed : State Linear 3 := fun i => (Array.mk [[(0,25745836306983316556041969842380384457731483615716082728498644853554565703974)],[(189329,1)],[(0,12840816370888465575806145242869292314780142063770521291148696217286043664299)]]).getD i.val []
noncomputable def after : State Linear 3 := fun i => (Array.mk [[(0,16894230006088892140655414676935215312425023855206660324872734097275543669960),(189329,25146695260744508059100624982461970690166157722474767565243652164077487269055)],[(0,24203231391944988625025417752245671626197092436371234299545006333147206788279),(189329,13125423966940654332711887575940116829944663267413330181877013057693186361539)],[(0,45233320757308677361425636628945262529761597911900212925735294694276559313742),(189329,1961062001717124873779753860369853658060849384038305407377314938662537282272)]]).getD i.val []
noncomputable def rows : List Row := [⟨[(6,1),(200692,38385660029618165285848698857635215143135976511856402182142757680787979296154)],[(189327,1)]⟩,⟨[(189327,1)],[(189328,1)]⟩,⟨[(6,52435875175126190479447740508185965837690552500527637822603658699938581184512),(189328,1),(200692,14050215145508025193599041650550750694554575988671235640460901019150601888359)],[(189330,1)]⟩,⟨[(6,1),(189328,1),(200692,38385660029618165285848698857635215143135976511856402182142757680787979296154)],[(189329,4),(189330,1)]⟩,⟨[(0,1),(200692,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[]⟩]
noncomputable def data : AuthorizationPoseidonPhase517.Data 3 :=
  ⟨parameters,0,0,0,before,shifted,transformed,after,rows,
    (fun i => (Array.mk [none,some 189327,none]).getD i.val none),
    (fun i => (Array.mk [0,0,0]).getD i.val 0),
    (fun i => (Array.mk [48991097081732275468845314168021420565497297775988823234113406403095118809498,0,45664917788634056160947231182803089169570746657219074370482409200042991921246]).getD i.val 0)⟩
theorem column0 : PoseidonIndexedFolded02.checkColumn p copy rows.toArray parameters 0 before shifted transformed (AuthorizationPoseidonPhase517.hints data) 0=true := by decide +kernel
theorem column1 : PoseidonIndexedFolded02.checkColumn p copy rows.toArray parameters 0 before shifted transformed (AuthorizationPoseidonPhase517.hints data) 1=true := by decide +kernel
theorem column2 : PoseidonIndexedFolded02.checkColumn p copy rows.toArray parameters 0 before shifted transformed (AuthorizationPoseidonPhase517.hints data) 2=true := by decide +kernel
theorem checked : PoseidonIndexedFolded02.checkRound p copy rows.toArray parameters 0 before shifted transformed after (AuthorizationPoseidonPhase517.hints data)=true := by
  simp only [PoseidonIndexedFolded02.checkRound,Bool.and_eq_true]
  constructor
  · apply List.all_eq_true.mpr
    intro i _
    have cases : i=0 ∨ i=1 ∨ i=2 := by have h := i.isLt;simp only [Fin.ext_iff];omega
    rcases cases with rfl|rfl|rfl
    · exact column0
    · exact column1
    · exact column2
  · decide +kernel
theorem copy_checked : checkRow p rows ⟨[(0,1),(copy,-1)],[]⟩=true := by decide +kernel
noncomputable def captureIndices : List Nat := [166589,166590,166591,166592,200769]
theorem arbitrary_round {F : Type} [Field F] [CharP F p] (rho : Nat → F)
    (one : rho 0=1) (sat : Satisfies rho rows) :
    (fun i => eval rho (after i))=Poseidon.round (castParameters parameters) 0
      (fun i => eval rho (before i)) :=
  AuthorizationPoseidonPhase517.arbitrary_round data checked copy_checked rho one sat
end ShielddSecurity.MapAssetHashCapture734C186B0R00
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashCapture734C186B0R00.checked
#print axioms ShielddSecurity.MapAssetHashCapture734C186B0R00.checked
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashCapture734C186B0R00.copy_checked
#print axioms ShielddSecurity.MapAssetHashCapture734C186B0R00.copy_checked
set_option pp.all true in
#check @ShielddSecurity.MapAssetHashCapture734C186B0R00.arbitrary_round
#print axioms ShielddSecurity.MapAssetHashCapture734C186B0R00.arbitrary_round
