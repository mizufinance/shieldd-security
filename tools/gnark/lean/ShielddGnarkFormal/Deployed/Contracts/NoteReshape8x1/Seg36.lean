import ShielddGnarkFormal.Deployed.Contract
import ShielddGnarkFormal.Deployed.Templates.Core
import ShielddGnarkFormal.Deployed.Templates.Generated.TRoutingParametersBind_46f527d3e36d976837f6c928381fedce823324751461dd2d8bd615716c786979
import Mathlib.Data.ZMod.Basic

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

namespace Shieldd.GnarkFormal.Deployed.Contracts.NoteReshape8x1.Seg36

def Order : Nat := 8444461749428370424248824938781546531375899335154063827935233455917409239041
abbrev F := ZMod Order

def wireSeatingTable : List Nat := [0, 25661, 25666, 25671, 25676, 5, 11, 24708, 24710, 24712, 24714, 24716, 24718, 24720, 24722, 24724, 24726, 24728, 24730, 24732, 24734, 24736, 24738, 24740, 24742, 24744, 24746, 24748, 24750, 24752, 24754, 24756, 24758, 24760, 24762, 24764, 24766, 24768, 24770, 24774, 24776, 24778, 24780, 24782, 24784, 24786, 24788, 24790, 24792, 24794, 24796, 24798, 24800, 24802, 24804, 24806, 24808, 24810, 24812, 24814, 24816, 24818, 24820, 24822, 24824, 24826, 24828, 24830, 24832, 24834, 24836, 25677, 25678, 25679, 25680, 25681, 25682, 25683, 25684, 25685, 25686, 25687, 25688, 25689, 25690, 25691, 25692, 25693, 25694, 25695, 25696, 25697, 25698, 25699, 25700, 25701, 25702, 25703, 25704, 25705, 25706, 25707, 25708]

def wireSeating : Nat -> Nat :=
fun localWire => wireSeatingTable.getD localWire 0

def localRho (rho : Nat -> F) : Nat -> F :=
    Shieldd.GnarkFormal.Deployed.Templates.seated rho wireSeating

def relation (rho : Nat -> F) : Prop :=
    Shieldd.GnarkFormal.Deployed.Templates.Generated.TRoutingParametersBind_46f527d3e36d976837f6c928381fedce823324751461dd2d8bd615716c786979.relation (localRho rho)

def spec (rho : Nat -> F) : Prop :=
    Shieldd.GnarkFormal.Deployed.Templates.Generated.TRoutingParametersBind_46f527d3e36d976837f6c928381fedce823324751461dd2d8bd615716c786979.spec (localRho rho)

def contract : Shieldd.GnarkFormal.Deployed.DeployedContract F := {
segmentIndex := 36,
relationSha256Hex := "65bd2f21d55b820fae4b4daaeb0575819f3ea957e042a90c07335bba5417ec65",
wireRoleSha256Hex := "7f1249750dfa212aec94bf7469b1d911c1536cc8ae9371f23ade57eb0f696ea5",
relation := relation,
spec := spec
}

end Shieldd.GnarkFormal.Deployed.Contracts.NoteReshape8x1.Seg36
