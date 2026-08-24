import ShielddGnarkFormal.Deployed.Contract
import ShielddGnarkFormal.Deployed.Templates.Core
import ShielddGnarkFormal.Deployed.Templates.Generated.THistoryClassify_63bcfde2aa853f39c988314bacdeeddfe5aa236959c22bd9f97803415badf545
import Mathlib.Data.ZMod.Basic

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

namespace Shieldd.GnarkFormal.Deployed.Contracts.NoteReshape8x1.Seg160

def Order : Nat := 8444461749428370424248824938781546531375899335154063827935233455917409239041
abbrev F := ZMod Order

def wireSeatingTable : List Nat := [0, 127543, 127544, 127545, 127546, 127547, 127548, 127549, 127550, 127551, 127552, 127553, 127554, 127555, 127556, 127557, 127558, 127559, 127560, 127561, 127562, 127563, 127564, 127565, 127566, 127567, 127568, 127569, 127570, 127571, 127572, 127573, 127574, 127575, 127576, 127577, 127578, 127579, 127580, 127581, 127582, 127583, 127584, 127585, 127586, 127587, 127588, 127589, 127590, 724, 127591, 127592, 127593, 127594, 127595, 127596, 127597, 127598, 127599, 127600, 127601, 127602, 127603, 127604, 127605, 127606, 127607, 127608, 127609, 127610, 127611, 127612, 127613, 127614, 127615, 127616, 127617, 127618, 127619, 127620, 127621, 127622, 127623, 127624, 127625, 127626, 127627, 127628, 127629, 127630, 127631, 127632, 127633, 127634, 127635, 127636, 127637, 127638, 6, 127639, 127640, 127641, 127642, 127643, 127644, 127645, 127646, 127647, 127648, 127649, 127650, 127651, 127652, 127653, 127654, 127655, 127656, 127657, 127658, 127659, 127660, 127661, 127662, 127663, 127664, 127665, 127666, 127667, 127668, 127669, 127670, 127671, 127672, 127673, 127674, 127675, 127676, 127677, 127678, 127679, 127680, 127681, 127682, 127683, 127684, 127685, 127686, 127687, 127688, 799, 127689, 798]

def wireSeating : Nat -> Nat :=
fun localWire => wireSeatingTable.getD localWire 0

def localRho (rho : Nat -> F) : Nat -> F :=
    Shieldd.GnarkFormal.Deployed.Templates.seated rho wireSeating

def relation (rho : Nat -> F) : Prop :=
    Shieldd.GnarkFormal.Deployed.Templates.Generated.THistoryClassify_63bcfde2aa853f39c988314bacdeeddfe5aa236959c22bd9f97803415badf545.relation (localRho rho)

def spec (rho : Nat -> F) : Prop :=
    Shieldd.GnarkFormal.Deployed.Templates.Generated.THistoryClassify_63bcfde2aa853f39c988314bacdeeddfe5aa236959c22bd9f97803415badf545.spec (localRho rho)

def contract : Shieldd.GnarkFormal.Deployed.DeployedContract F := {
segmentIndex := 160,
relationSha256Hex := "88ce5fb51a3a29704fb3ad2209546502b89123b5be423336bbca00d8f784bafe",
wireRoleSha256Hex := "3e56933134ffd54e4bb6f8eea64617c844a09521d556c0873d35b0563f120de8",
relation := relation,
spec := spec
}

end Shieldd.GnarkFormal.Deployed.Contracts.NoteReshape8x1.Seg160
