import ShielddGnarkFormal.Deployed.Contract
import ShielddGnarkFormal.Deployed.Templates.Core
import ShielddGnarkFormal.Deployed.Templates.Generated.THistoryClassify_63bcfde2aa853f39c988314bacdeeddfe5aa236959c22bd9f97803415badf545
import Mathlib.Data.ZMod.Basic

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

namespace Shieldd.GnarkFormal.Deployed.Contracts.NoteReshape8x1.Seg145

def Order : Nat := 8444461749428370424248824938781546531375899335154063827935233455917409239041
abbrev F := ZMod Order

def wireSeatingTable : List Nat := [0, 114950, 114951, 114952, 114953, 114954, 114955, 114956, 114957, 114958, 114959, 114960, 114961, 114962, 114963, 114964, 114965, 114966, 114967, 114968, 114969, 114970, 114971, 114972, 114973, 114974, 114975, 114976, 114977, 114978, 114979, 114980, 114981, 114982, 114983, 114984, 114985, 114986, 114987, 114988, 114989, 114990, 114991, 114992, 114993, 114994, 114995, 114996, 114997, 641, 114998, 114999, 115000, 115001, 115002, 115003, 115004, 115005, 115006, 115007, 115008, 115009, 115010, 115011, 115012, 115013, 115014, 115015, 115016, 115017, 115018, 115019, 115020, 115021, 115022, 115023, 115024, 115025, 115026, 115027, 115028, 115029, 115030, 115031, 115032, 115033, 115034, 115035, 115036, 115037, 115038, 115039, 115040, 115041, 115042, 115043, 115044, 115045, 6, 115046, 115047, 115048, 115049, 115050, 115051, 115052, 115053, 115054, 115055, 115056, 115057, 115058, 115059, 115060, 115061, 115062, 115063, 115064, 115065, 115066, 115067, 115068, 115069, 115070, 115071, 115072, 115073, 115074, 115075, 115076, 115077, 115078, 115079, 115080, 115081, 115082, 115083, 115084, 115085, 115086, 115087, 115088, 115089, 115090, 115091, 115092, 115093, 115094, 115095, 716, 115096, 715]

def wireSeating : Nat -> Nat :=
fun localWire => wireSeatingTable.getD localWire 0

def localRho (rho : Nat -> F) : Nat -> F :=
    Shieldd.GnarkFormal.Deployed.Templates.seated rho wireSeating

def relation (rho : Nat -> F) : Prop :=
    Shieldd.GnarkFormal.Deployed.Templates.Generated.THistoryClassify_63bcfde2aa853f39c988314bacdeeddfe5aa236959c22bd9f97803415badf545.relation (localRho rho)

def spec (rho : Nat -> F) : Prop :=
    Shieldd.GnarkFormal.Deployed.Templates.Generated.THistoryClassify_63bcfde2aa853f39c988314bacdeeddfe5aa236959c22bd9f97803415badf545.spec (localRho rho)

def contract : Shieldd.GnarkFormal.Deployed.DeployedContract F := {
segmentIndex := 145,
relationSha256Hex := "63dd2711a0aa1d72830b8535c5c58bc7a96177386219b2d4695a9af3a91ac09d",
wireRoleSha256Hex := "30585bf80deeb208d6fd0fad41b88b895c306faa773130541097bd3f01b41c02",
relation := relation,
spec := spec
}

end Shieldd.GnarkFormal.Deployed.Contracts.NoteReshape8x1.Seg145
