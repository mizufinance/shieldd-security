import ShielddGnarkFormal.Deployed.Contract
import ShielddGnarkFormal.Deployed.Templates.Core
import ShielddGnarkFormal.Deployed.Templates.Generated.TRoutingParametersBind_46f527d3e36d976837f6c928381fedce823324751461dd2d8bd615716c786979
import Mathlib.Data.ZMod.Basic

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

namespace Shieldd.GnarkFormal.Deployed.Contracts.Transfer.Seg78

def Order : Nat := 8444461749428370424248824938781546531375899335154063827935233455917409239041
abbrev F := ZMod Order

def wireSeatingTable : List Nat := [0, 64515, 64520, 64525, 64530, 4, 11, 63562, 63564, 63566, 63568, 63570, 63572, 63574, 63576, 63578, 63580, 63582, 63584, 63586, 63588, 63590, 63592, 63594, 63596, 63598, 63600, 63602, 63604, 63606, 63608, 63610, 63612, 63614, 63616, 63618, 63620, 63622, 63624, 63628, 63630, 63632, 63634, 63636, 63638, 63640, 63642, 63644, 63646, 63648, 63650, 63652, 63654, 63656, 63658, 63660, 63662, 63664, 63666, 63668, 63670, 63672, 63674, 63676, 63678, 63680, 63682, 63684, 63686, 63688, 63690, 64531, 64532, 64533, 64534, 64535, 64536, 64537, 64538, 64539, 64540, 64541, 64542, 64543, 64544, 64545, 64546, 64547, 64548, 64549, 64550, 64551, 64552, 64553, 64554, 64555, 64556, 64557, 64558, 64559, 64560, 64561, 64562]

def wireSeating : Nat -> Nat :=
fun localWire => wireSeatingTable.getD localWire 0

def localRho (rho : Nat -> F) : Nat -> F :=
    Shieldd.GnarkFormal.Deployed.Templates.seated rho wireSeating

def relation (rho : Nat -> F) : Prop :=
    Shieldd.GnarkFormal.Deployed.Templates.Generated.TRoutingParametersBind_46f527d3e36d976837f6c928381fedce823324751461dd2d8bd615716c786979.relation (localRho rho)

def spec (rho : Nat -> F) : Prop :=
    Shieldd.GnarkFormal.Deployed.Templates.Generated.TRoutingParametersBind_46f527d3e36d976837f6c928381fedce823324751461dd2d8bd615716c786979.spec (localRho rho)

def contract : Shieldd.GnarkFormal.Deployed.DeployedContract F := {
segmentIndex := 78,
relationSha256Hex := "2c52fe6e8c9532530231a0cb5fe023bde83b546fd0306bef0cbfa3137cd032b0",
wireRoleSha256Hex := "976d4525d820b0e7306c9f86db4fd1d4e4ae8dc30b1a90a93bbafcf53a386aca",
relation := relation,
spec := spec
}

end Shieldd.GnarkFormal.Deployed.Contracts.Transfer.Seg78
