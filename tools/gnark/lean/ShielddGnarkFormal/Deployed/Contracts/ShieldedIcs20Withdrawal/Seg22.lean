import ShielddGnarkFormal.Deployed.Contract
import ShielddGnarkFormal.Deployed.Templates.Core
import ShielddGnarkFormal.Deployed.Templates.Generated.TRoutingParametersBind_46f527d3e36d976837f6c928381fedce823324751461dd2d8bd615716c786979
import Mathlib.Data.ZMod.Basic

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

namespace Shieldd.GnarkFormal.Deployed.Contracts.ShieldedIcs20Withdrawal.Seg22

def Order : Nat := 8444461749428370424248824938781546531375899335154063827935233455917409239041
abbrev F := ZMod Order

def wireSeatingTable : List Nat := [0, 23034, 23039, 23044, 23049, 3, 16, 22081, 22083, 22085, 22087, 22089, 22091, 22093, 22095, 22097, 22099, 22101, 22103, 22105, 22107, 22109, 22111, 22113, 22115, 22117, 22119, 22121, 22123, 22125, 22127, 22129, 22131, 22133, 22135, 22137, 22139, 22141, 22143, 22147, 22149, 22151, 22153, 22155, 22157, 22159, 22161, 22163, 22165, 22167, 22169, 22171, 22173, 22175, 22177, 22179, 22181, 22183, 22185, 22187, 22189, 22191, 22193, 22195, 22197, 22199, 22201, 22203, 22205, 22207, 22209, 23050, 23051, 23052, 23053, 23054, 23055, 23056, 23057, 23058, 23059, 23060, 23061, 23062, 23063, 23064, 23065, 23066, 23067, 23068, 23069, 23070, 23071, 23072, 23073, 23074, 23075, 23076, 23077, 23078, 23079, 23080, 23081]

def wireSeating : Nat -> Nat :=
fun localWire => wireSeatingTable.getD localWire 0

def localRho (rho : Nat -> F) : Nat -> F :=
    Shieldd.GnarkFormal.Deployed.Templates.seated rho wireSeating

def relation (rho : Nat -> F) : Prop :=
    Shieldd.GnarkFormal.Deployed.Templates.Generated.TRoutingParametersBind_46f527d3e36d976837f6c928381fedce823324751461dd2d8bd615716c786979.relation (localRho rho)

def spec (rho : Nat -> F) : Prop :=
    Shieldd.GnarkFormal.Deployed.Templates.Generated.TRoutingParametersBind_46f527d3e36d976837f6c928381fedce823324751461dd2d8bd615716c786979.spec (localRho rho)

def contract : Shieldd.GnarkFormal.Deployed.DeployedContract F := {
segmentIndex := 22,
relationSha256Hex := "1af28649373eb52d1f345f1e39b358ebcd354a0f333e2ad25cfceba3bbaeed37",
wireRoleSha256Hex := "d69dd6db71318bf565646d4c961a4c4173b352978c0ee2a30a4f3b9169217497",
relation := relation,
spec := spec
}

end Shieldd.GnarkFormal.Deployed.Contracts.ShieldedIcs20Withdrawal.Seg22
