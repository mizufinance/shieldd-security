import ShielddGnarkFormal.Deployed.Contract
import ShielddGnarkFormal.Deployed.Templates.Core
import ShielddGnarkFormal.Deployed.Templates.Generated.THistoryClassify_63bcfde2aa853f39c988314bacdeeddfe5aa236959c22bd9f97803415badf545
import Mathlib.Data.ZMod.Basic

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

namespace Shieldd.GnarkFormal.Deployed.Contracts.NoteReshape8x1.Seg100

def Order : Nat := 8444461749428370424248824938781546531375899335154063827935233455917409239041
abbrev F := ZMod Order

def wireSeatingTable : List Nat := [0, 77171, 77172, 77173, 77174, 77175, 77176, 77177, 77178, 77179, 77180, 77181, 77182, 77183, 77184, 77185, 77186, 77187, 77188, 77189, 77190, 77191, 77192, 77193, 77194, 77195, 77196, 77197, 77198, 77199, 77200, 77201, 77202, 77203, 77204, 77205, 77206, 77207, 77208, 77209, 77210, 77211, 77212, 77213, 77214, 77215, 77216, 77217, 77218, 392, 77219, 77220, 77221, 77222, 77223, 77224, 77225, 77226, 77227, 77228, 77229, 77230, 77231, 77232, 77233, 77234, 77235, 77236, 77237, 77238, 77239, 77240, 77241, 77242, 77243, 77244, 77245, 77246, 77247, 77248, 77249, 77250, 77251, 77252, 77253, 77254, 77255, 77256, 77257, 77258, 77259, 77260, 77261, 77262, 77263, 77264, 77265, 77266, 6, 77267, 77268, 77269, 77270, 77271, 77272, 77273, 77274, 77275, 77276, 77277, 77278, 77279, 77280, 77281, 77282, 77283, 77284, 77285, 77286, 77287, 77288, 77289, 77290, 77291, 77292, 77293, 77294, 77295, 77296, 77297, 77298, 77299, 77300, 77301, 77302, 77303, 77304, 77305, 77306, 77307, 77308, 77309, 77310, 77311, 77312, 77313, 77314, 77315, 77316, 467, 77317, 466]

def wireSeating : Nat -> Nat :=
fun localWire => wireSeatingTable.getD localWire 0

def localRho (rho : Nat -> F) : Nat -> F :=
    Shieldd.GnarkFormal.Deployed.Templates.seated rho wireSeating

def relation (rho : Nat -> F) : Prop :=
    Shieldd.GnarkFormal.Deployed.Templates.Generated.THistoryClassify_63bcfde2aa853f39c988314bacdeeddfe5aa236959c22bd9f97803415badf545.relation (localRho rho)

def spec (rho : Nat -> F) : Prop :=
    Shieldd.GnarkFormal.Deployed.Templates.Generated.THistoryClassify_63bcfde2aa853f39c988314bacdeeddfe5aa236959c22bd9f97803415badf545.spec (localRho rho)

def contract : Shieldd.GnarkFormal.Deployed.DeployedContract F := {
segmentIndex := 100,
relationSha256Hex := "1f1bfe59c89c5bf981929660de8ef00ebed304f6e7ed08b68a130f0b463769af",
wireRoleSha256Hex := "b94d3b6cf7397fd38ebb3e3762e02062b2016316a0c9ae7098a56df3d84cb3f1",
relation := relation,
spec := spec
}

end Shieldd.GnarkFormal.Deployed.Contracts.NoteReshape8x1.Seg100
