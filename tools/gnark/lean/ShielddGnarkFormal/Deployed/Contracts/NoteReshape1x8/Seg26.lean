import ShielddGnarkFormal.Deployed.Contract
import ShielddGnarkFormal.Deployed.Templates.Core
import ShielddGnarkFormal.Deployed.Templates.Generated.TRoutingParametersBind_46f527d3e36d976837f6c928381fedce823324751461dd2d8bd615716c786979
import Mathlib.Data.ZMod.Basic

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

namespace Shieldd.GnarkFormal.Deployed.Contracts.NoteReshape1x8.Seg26

def Order : Nat := 8444461749428370424248824938781546531375899335154063827935233455917409239041
abbrev F := ZMod Order

def wireSeatingTable : List Nat := [0, 25086, 25091, 25096, 25101, 5, 11, 24133, 24135, 24137, 24139, 24141, 24143, 24145, 24147, 24149, 24151, 24153, 24155, 24157, 24159, 24161, 24163, 24165, 24167, 24169, 24171, 24173, 24175, 24177, 24179, 24181, 24183, 24185, 24187, 24189, 24191, 24193, 24195, 24199, 24201, 24203, 24205, 24207, 24209, 24211, 24213, 24215, 24217, 24219, 24221, 24223, 24225, 24227, 24229, 24231, 24233, 24235, 24237, 24239, 24241, 24243, 24245, 24247, 24249, 24251, 24253, 24255, 24257, 24259, 24261, 25102, 25103, 25104, 25105, 25106, 25107, 25108, 25109, 25110, 25111, 25112, 25113, 25114, 25115, 25116, 25117, 25118, 25119, 25120, 25121, 25122, 25123, 25124, 25125, 25126, 25127, 25128, 25129, 25130, 25131, 25132, 25133]

def wireSeating : Nat -> Nat :=
fun localWire => wireSeatingTable.getD localWire 0

def localRho (rho : Nat -> F) : Nat -> F :=
    Shieldd.GnarkFormal.Deployed.Templates.seated rho wireSeating

def relation (rho : Nat -> F) : Prop :=
    Shieldd.GnarkFormal.Deployed.Templates.Generated.TRoutingParametersBind_46f527d3e36d976837f6c928381fedce823324751461dd2d8bd615716c786979.relation (localRho rho)

def spec (rho : Nat -> F) : Prop :=
    Shieldd.GnarkFormal.Deployed.Templates.Generated.TRoutingParametersBind_46f527d3e36d976837f6c928381fedce823324751461dd2d8bd615716c786979.spec (localRho rho)

def contract : Shieldd.GnarkFormal.Deployed.DeployedContract F := {
segmentIndex := 26,
relationSha256Hex := "c82f79836b5b2ea619bc48c905bb884c1e639db51702b07ee3d701dc36a50df1",
wireRoleSha256Hex := "636defb6c0cfe7192da68eee6bb7988e9196c37013d95bda6ae7f5cab5885476",
relation := relation,
spec := spec
}

end Shieldd.GnarkFormal.Deployed.Contracts.NoteReshape1x8.Seg26
