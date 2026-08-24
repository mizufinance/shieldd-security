import ShielddGnarkFormal.Deployed.Contract
import ShielddGnarkFormal.Deployed.Templates.Core
import ShielddGnarkFormal.Deployed.Templates.Generated.THistoryClassify_63bcfde2aa853f39c988314bacdeeddfe5aa236959c22bd9f97803415badf545
import Mathlib.Data.ZMod.Basic

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

namespace Shieldd.GnarkFormal.Deployed.Contracts.NoteReshape8x1.Seg115

def Order : Nat := 8444461749428370424248824938781546531375899335154063827935233455917409239041
abbrev F := ZMod Order

def wireSeatingTable : List Nat := [0, 89764, 89765, 89766, 89767, 89768, 89769, 89770, 89771, 89772, 89773, 89774, 89775, 89776, 89777, 89778, 89779, 89780, 89781, 89782, 89783, 89784, 89785, 89786, 89787, 89788, 89789, 89790, 89791, 89792, 89793, 89794, 89795, 89796, 89797, 89798, 89799, 89800, 89801, 89802, 89803, 89804, 89805, 89806, 89807, 89808, 89809, 89810, 89811, 475, 89812, 89813, 89814, 89815, 89816, 89817, 89818, 89819, 89820, 89821, 89822, 89823, 89824, 89825, 89826, 89827, 89828, 89829, 89830, 89831, 89832, 89833, 89834, 89835, 89836, 89837, 89838, 89839, 89840, 89841, 89842, 89843, 89844, 89845, 89846, 89847, 89848, 89849, 89850, 89851, 89852, 89853, 89854, 89855, 89856, 89857, 89858, 89859, 6, 89860, 89861, 89862, 89863, 89864, 89865, 89866, 89867, 89868, 89869, 89870, 89871, 89872, 89873, 89874, 89875, 89876, 89877, 89878, 89879, 89880, 89881, 89882, 89883, 89884, 89885, 89886, 89887, 89888, 89889, 89890, 89891, 89892, 89893, 89894, 89895, 89896, 89897, 89898, 89899, 89900, 89901, 89902, 89903, 89904, 89905, 89906, 89907, 89908, 89909, 550, 89910, 549]

def wireSeating : Nat -> Nat :=
fun localWire => wireSeatingTable.getD localWire 0

def localRho (rho : Nat -> F) : Nat -> F :=
    Shieldd.GnarkFormal.Deployed.Templates.seated rho wireSeating

def relation (rho : Nat -> F) : Prop :=
    Shieldd.GnarkFormal.Deployed.Templates.Generated.THistoryClassify_63bcfde2aa853f39c988314bacdeeddfe5aa236959c22bd9f97803415badf545.relation (localRho rho)

def spec (rho : Nat -> F) : Prop :=
    Shieldd.GnarkFormal.Deployed.Templates.Generated.THistoryClassify_63bcfde2aa853f39c988314bacdeeddfe5aa236959c22bd9f97803415badf545.spec (localRho rho)

def contract : Shieldd.GnarkFormal.Deployed.DeployedContract F := {
segmentIndex := 115,
relationSha256Hex := "ef834bc4681f25ee7f7b9e329d8a31487ab78a450abdbeb61d896224a9b1e4ce",
wireRoleSha256Hex := "5edb3697b40f012136141a26f4d395b2b4dd2e9c806fe594058e29c1e2c32573",
relation := relation,
spec := spec
}

end Shieldd.GnarkFormal.Deployed.Contracts.NoteReshape8x1.Seg115
