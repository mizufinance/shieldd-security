import ShielddGnarkFormal.Deployed.Contract
import ShielddGnarkFormal.Deployed.Templates.Core
import ShielddGnarkFormal.Deployed.Templates.Generated.THistoryClassify_63bcfde2aa853f39c988314bacdeeddfe5aa236959c22bd9f97803415badf545
import Mathlib.Data.ZMod.Basic

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

namespace Shieldd.GnarkFormal.Deployed.Contracts.NoteReshape8x1.Seg130

def Order : Nat := 8444461749428370424248824938781546531375899335154063827935233455917409239041
abbrev F := ZMod Order

def wireSeatingTable : List Nat := [0, 102357, 102358, 102359, 102360, 102361, 102362, 102363, 102364, 102365, 102366, 102367, 102368, 102369, 102370, 102371, 102372, 102373, 102374, 102375, 102376, 102377, 102378, 102379, 102380, 102381, 102382, 102383, 102384, 102385, 102386, 102387, 102388, 102389, 102390, 102391, 102392, 102393, 102394, 102395, 102396, 102397, 102398, 102399, 102400, 102401, 102402, 102403, 102404, 558, 102405, 102406, 102407, 102408, 102409, 102410, 102411, 102412, 102413, 102414, 102415, 102416, 102417, 102418, 102419, 102420, 102421, 102422, 102423, 102424, 102425, 102426, 102427, 102428, 102429, 102430, 102431, 102432, 102433, 102434, 102435, 102436, 102437, 102438, 102439, 102440, 102441, 102442, 102443, 102444, 102445, 102446, 102447, 102448, 102449, 102450, 102451, 102452, 6, 102453, 102454, 102455, 102456, 102457, 102458, 102459, 102460, 102461, 102462, 102463, 102464, 102465, 102466, 102467, 102468, 102469, 102470, 102471, 102472, 102473, 102474, 102475, 102476, 102477, 102478, 102479, 102480, 102481, 102482, 102483, 102484, 102485, 102486, 102487, 102488, 102489, 102490, 102491, 102492, 102493, 102494, 102495, 102496, 102497, 102498, 102499, 102500, 102501, 102502, 633, 102503, 632]

def wireSeating : Nat -> Nat :=
fun localWire => wireSeatingTable.getD localWire 0

def localRho (rho : Nat -> F) : Nat -> F :=
    Shieldd.GnarkFormal.Deployed.Templates.seated rho wireSeating

def relation (rho : Nat -> F) : Prop :=
    Shieldd.GnarkFormal.Deployed.Templates.Generated.THistoryClassify_63bcfde2aa853f39c988314bacdeeddfe5aa236959c22bd9f97803415badf545.relation (localRho rho)

def spec (rho : Nat -> F) : Prop :=
    Shieldd.GnarkFormal.Deployed.Templates.Generated.THistoryClassify_63bcfde2aa853f39c988314bacdeeddfe5aa236959c22bd9f97803415badf545.spec (localRho rho)

def contract : Shieldd.GnarkFormal.Deployed.DeployedContract F := {
segmentIndex := 130,
relationSha256Hex := "93709400fdb5abcbdc86b865b8ad24bbb46f143215941a0b6a72194a444970da",
wireRoleSha256Hex := "d5d284b733a5a74e89abc58690b6ed812e366e2f734216922d65c2c1ae3d34f4",
relation := relation,
spec := spec
}

end Shieldd.GnarkFormal.Deployed.Contracts.NoteReshape8x1.Seg130
