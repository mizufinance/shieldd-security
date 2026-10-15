/- GENERATED from the maintained public-statement binding generator. Edit the generator, then regenerate. -/
import ShielddSecurity.PublicStatementLayout979
import ShielddSecurity.TransferSem
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PublicStatementSeed980
open ConcreteJubjubField01
def value (w : TransferSem.Witness) : Nat → F
  | 4272 => (w.auth.rk.x:F)
  | 4273 => (w.auth.rk.y:F)
  | 3 => (w.anchor:F)
  | 4920 => ((w.outputs 0).noteCommitment:F)
  | 4921 => ((w.outputs 0).recovery.commitment:F)
  | 6324 => ((w.outputs 1).noteCommitment:F)
  | 6325 => ((w.outputs 1).recovery.commitment:F)
  | 19848 => (w.routing.tags 0:F)
  | 19849 => (w.routing.tags 1:F)
  | 19589 => (w.routing.parameterSet:F)
  | 8509 => (w.volume.nullifier:F)
  | 8510 => (w.volume.commitment:F)
  | 7739 => (w.volume.dayStart:F)
  | 7607 => (w.volume.context:F)
  | 4532 => ((w.spends 0).nullifier:F)
  | 4785 => ((w.spends 1).nullifier:F)
  | 4 => (w.assetAnchor:F)
  | 5 => (w.userAnchor:F)
  | 8511 => (w.encryption.detection 0:F)
  | 8512 => (w.encryption.detection 1:F)
  | 8513 => (w.encryption.detection 2:F)
  | 8514 => (w.encryption.detection 3:F)
  | 8515 => ((w.encryption.tiers 0).epk.x:F)
  | 8516 => ((w.encryption.tiers 0).epk.y:F)
  | 8517 => ((w.encryption.tiers 0).c2:F)
  | 8519 => ((w.encryption.tiers 0).ciphertext 0:F)
  | 8520 => ((w.encryption.tiers 1).epk.x:F)
  | 8521 => ((w.encryption.tiers 1).epk.y:F)
  | 8522 => ((w.encryption.tiers 1).c2:F)
  | 8523 => ((w.encryption.tiers 1).ciphertext 0:F)
  | 8524 => ((w.encryption.tiers 1).ciphertext 1:F)
  | 8525 => ((w.encryption.tiers 1).ciphertext 2:F)
  | 8526 => ((w.encryption.tiers 2).epk.x:F)
  | 8527 => ((w.encryption.tiers 2).epk.y:F)
  | 8528 => ((w.encryption.tiers 2).c2:F)
  | 8530 => ((w.encryption.tiers 2).ciphertext 0:F)
  | 8531 => ((w.encryption.tiers 3).epk.x:F)
  | 8532 => ((w.encryption.tiers 3).epk.y:F)
  | 8533 => ((w.encryption.tiers 3).c2:F)
  | 8534 => ((w.encryption.tiers 3).ciphertext 0:F)
  | 8535 => ((w.encryption.tiers 3).ciphertext 1:F)
  | 8536 => ((w.encryption.tiers 3).ciphertext 2:F)
  | 7 => (w.timestamp:F)
  | 8518 => ((w.encryption.tiers 0).confirmation:F)
  | 8529 => ((w.encryption.tiers 2).confirmation:F)
  | 8537 => (w.encryption.policy 0:F)
  | 8538 => (w.encryption.policy 1:F)
  | 8539 => (w.encryption.policy 2:F)
  | 8540 => (w.encryption.policy 3:F)
  | 8543 => (w.encryption.salts 0:F)
  | 8544 => (w.encryption.salts 1:F)
  | 8545 => (w.encryption.salts 2:F)
  | 8546 => (w.encryption.salts 3:F)
  | 8542 => (w.encryption.auditEpoch:F)
  | 8547 => ((w.encryption.ownership 0).r.x:F)
  | 8548 => ((w.encryption.ownership 0).r.y:F)
  | 8549 => ((w.encryption.ownership 0).c.x:F)
  | 8550 => ((w.encryption.ownership 0).c.y:F)
  | 10079 => ((w.encryption.ownership 1).r.x:F)
  | 10080 => ((w.encryption.ownership 1).r.y:F)
  | 10081 => ((w.encryption.ownership 1).c.x:F)
  | 10082 => ((w.encryption.ownership 1).c.y:F)
  | _ => 0
def seed (original : Nat → F) (w : TransferSem.Witness) (column : Nat) : F :=
  if column∈PublicStatementLayout979.columns then value w column else original column
theorem field0 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 4272=(((TransferSem.publicFields c w)[0]?.getD 0:Nat):F) := by rfl
theorem field1 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 4273=(((TransferSem.publicFields c w)[1]?.getD 0:Nat):F) := by rfl
theorem field2 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 3=(((TransferSem.publicFields c w)[2]?.getD 0:Nat):F) := by rfl
theorem field3 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 4920=(((TransferSem.publicFields c w)[3]?.getD 0:Nat):F) := by rfl
theorem field4 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 4921=(((TransferSem.publicFields c w)[4]?.getD 0:Nat):F) := by rfl
theorem field5 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 6324=(((TransferSem.publicFields c w)[5]?.getD 0:Nat):F) := by rfl
theorem field6 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 6325=(((TransferSem.publicFields c w)[6]?.getD 0:Nat):F) := by rfl
theorem field9 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 19848=(((TransferSem.publicFields c w)[9]?.getD 0:Nat):F) := by rfl
theorem field10 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 19849=(((TransferSem.publicFields c w)[10]?.getD 0:Nat):F) := by rfl
theorem field11 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 19589=(((TransferSem.publicFields c w)[11]?.getD 0:Nat):F) := by rfl
theorem field12 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8509=(((TransferSem.publicFields c w)[12]?.getD 0:Nat):F) := by rfl
theorem field13 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8510=(((TransferSem.publicFields c w)[13]?.getD 0:Nat):F) := by rfl
theorem field14 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 7739=(((TransferSem.publicFields c w)[14]?.getD 0:Nat):F) := by rfl
theorem field15 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 7607=(((TransferSem.publicFields c w)[15]?.getD 0:Nat):F) := by rfl
theorem field16 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 4532=(((TransferSem.publicFields c w)[16]?.getD 0:Nat):F) := by rfl
theorem field17 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 4785=(((TransferSem.publicFields c w)[17]?.getD 0:Nat):F) := by rfl
theorem field18 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 4=(((TransferSem.publicFields c w)[18]?.getD 0:Nat):F) := by rfl
theorem field19 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 5=(((TransferSem.publicFields c w)[19]?.getD 0:Nat):F) := by rfl
theorem field20 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8511=(((TransferSem.publicFields c w)[20]?.getD 0:Nat):F) := by rfl
theorem field21 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8512=(((TransferSem.publicFields c w)[21]?.getD 0:Nat):F) := by rfl
theorem field22 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8513=(((TransferSem.publicFields c w)[22]?.getD 0:Nat):F) := by rfl
theorem field23 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8514=(((TransferSem.publicFields c w)[23]?.getD 0:Nat):F) := by rfl
theorem field24 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8515=(((TransferSem.publicFields c w)[24]?.getD 0:Nat):F) := by rfl
theorem field25 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8516=(((TransferSem.publicFields c w)[25]?.getD 0:Nat):F) := by rfl
theorem field26 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8517=(((TransferSem.publicFields c w)[26]?.getD 0:Nat):F) := by rfl
theorem field27 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8519=(((TransferSem.publicFields c w)[27]?.getD 0:Nat):F) := by rfl
theorem field28 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8520=(((TransferSem.publicFields c w)[28]?.getD 0:Nat):F) := by rfl
theorem field29 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8521=(((TransferSem.publicFields c w)[29]?.getD 0:Nat):F) := by rfl
theorem field30 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8522=(((TransferSem.publicFields c w)[30]?.getD 0:Nat):F) := by rfl
theorem field31 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8523=(((TransferSem.publicFields c w)[31]?.getD 0:Nat):F) := by rfl
theorem field32 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8524=(((TransferSem.publicFields c w)[32]?.getD 0:Nat):F) := by rfl
theorem field33 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8525=(((TransferSem.publicFields c w)[33]?.getD 0:Nat):F) := by rfl
theorem field34 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8526=(((TransferSem.publicFields c w)[34]?.getD 0:Nat):F) := by rfl
theorem field35 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8527=(((TransferSem.publicFields c w)[35]?.getD 0:Nat):F) := by rfl
theorem field36 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8528=(((TransferSem.publicFields c w)[36]?.getD 0:Nat):F) := by rfl
theorem field37 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8530=(((TransferSem.publicFields c w)[37]?.getD 0:Nat):F) := by rfl
theorem field38 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8531=(((TransferSem.publicFields c w)[38]?.getD 0:Nat):F) := by rfl
theorem field39 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8532=(((TransferSem.publicFields c w)[39]?.getD 0:Nat):F) := by rfl
theorem field40 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8533=(((TransferSem.publicFields c w)[40]?.getD 0:Nat):F) := by rfl
theorem field41 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8534=(((TransferSem.publicFields c w)[41]?.getD 0:Nat):F) := by rfl
theorem field42 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8535=(((TransferSem.publicFields c w)[42]?.getD 0:Nat):F) := by rfl
theorem field43 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8536=(((TransferSem.publicFields c w)[43]?.getD 0:Nat):F) := by rfl
theorem field44 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 7=(((TransferSem.publicFields c w)[44]?.getD 0:Nat):F) := by rfl
theorem field45 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8518=(((TransferSem.publicFields c w)[45]?.getD 0:Nat):F) := by rfl
theorem field46 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8529=(((TransferSem.publicFields c w)[46]?.getD 0:Nat):F) := by rfl
theorem field47 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8537=(((TransferSem.publicFields c w)[47]?.getD 0:Nat):F) := by rfl
theorem field48 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8538=(((TransferSem.publicFields c w)[48]?.getD 0:Nat):F) := by rfl
theorem field49 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8539=(((TransferSem.publicFields c w)[49]?.getD 0:Nat):F) := by rfl
theorem field50 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8540=(((TransferSem.publicFields c w)[50]?.getD 0:Nat):F) := by rfl
theorem field51 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8543=(((TransferSem.publicFields c w)[51]?.getD 0:Nat):F) := by rfl
theorem field52 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8544=(((TransferSem.publicFields c w)[52]?.getD 0:Nat):F) := by rfl
theorem field53 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8545=(((TransferSem.publicFields c w)[53]?.getD 0:Nat):F) := by rfl
theorem field54 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8546=(((TransferSem.publicFields c w)[54]?.getD 0:Nat):F) := by rfl
theorem field55 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8542=(((TransferSem.publicFields c w)[55]?.getD 0:Nat):F) := by rfl
theorem field56 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8547=(((TransferSem.publicFields c w)[56]?.getD 0:Nat):F) := by rfl
theorem field57 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8548=(((TransferSem.publicFields c w)[57]?.getD 0:Nat):F) := by rfl
theorem field58 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8549=(((TransferSem.publicFields c w)[58]?.getD 0:Nat):F) := by rfl
theorem field59 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 8550=(((TransferSem.publicFields c w)[59]?.getD 0:Nat):F) := by rfl
theorem field60 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 10079=(((TransferSem.publicFields c w)[60]?.getD 0:Nat):F) := by rfl
theorem field61 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 10080=(((TransferSem.publicFields c w)[61]?.getD 0:Nat):F) := by rfl
theorem field62 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 10081=(((TransferSem.publicFields c w)[62]?.getD 0:Nat):F) := by rfl
theorem field63 (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness) :
    seed original w 10082=(((TransferSem.publicFields c w)[63]?.getD 0:Nat):F) := by rfl
theorem outside (original : Nat → F) (w : TransferSem.Witness) (column : Nat)
    (separate : column∉PublicStatementLayout979.columns) : seed original w column=original column := by
  exact if_neg separate
theorem zero (original : Nat → F) (w : TransferSem.Witness) : seed original w 0=original 0 :=
  outside original w 0 PublicStatementLayout979.zero_outside
theorem net_x (original : Nat → F) (w : TransferSem.Witness) : seed original w 195230=original 195230 :=
  outside original w 195230 PublicStatementLayout979.net_x_outside
theorem net_y (original : Nat → F) (w : TransferSem.Witness) : seed original w 195234=original 195234 :=
  outside original w 195234 PublicStatementLayout979.net_y_outside
end ShielddSecurity.PublicStatementSeed980


set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field0
#print axioms ShielddSecurity.PublicStatementSeed980.field0

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field1
#print axioms ShielddSecurity.PublicStatementSeed980.field1

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field2
#print axioms ShielddSecurity.PublicStatementSeed980.field2

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field3
#print axioms ShielddSecurity.PublicStatementSeed980.field3

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field4
#print axioms ShielddSecurity.PublicStatementSeed980.field4

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field5
#print axioms ShielddSecurity.PublicStatementSeed980.field5

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field6
#print axioms ShielddSecurity.PublicStatementSeed980.field6

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field9
#print axioms ShielddSecurity.PublicStatementSeed980.field9

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field10
#print axioms ShielddSecurity.PublicStatementSeed980.field10

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field11
#print axioms ShielddSecurity.PublicStatementSeed980.field11

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field12
#print axioms ShielddSecurity.PublicStatementSeed980.field12

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field13
#print axioms ShielddSecurity.PublicStatementSeed980.field13

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field14
#print axioms ShielddSecurity.PublicStatementSeed980.field14

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field15
#print axioms ShielddSecurity.PublicStatementSeed980.field15

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field16
#print axioms ShielddSecurity.PublicStatementSeed980.field16

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field17
#print axioms ShielddSecurity.PublicStatementSeed980.field17

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field18
#print axioms ShielddSecurity.PublicStatementSeed980.field18

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field19
#print axioms ShielddSecurity.PublicStatementSeed980.field19

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field20
#print axioms ShielddSecurity.PublicStatementSeed980.field20

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field21
#print axioms ShielddSecurity.PublicStatementSeed980.field21

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field22
#print axioms ShielddSecurity.PublicStatementSeed980.field22

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field23
#print axioms ShielddSecurity.PublicStatementSeed980.field23

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field24
#print axioms ShielddSecurity.PublicStatementSeed980.field24

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field25
#print axioms ShielddSecurity.PublicStatementSeed980.field25

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field26
#print axioms ShielddSecurity.PublicStatementSeed980.field26

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field27
#print axioms ShielddSecurity.PublicStatementSeed980.field27

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field28
#print axioms ShielddSecurity.PublicStatementSeed980.field28

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field29
#print axioms ShielddSecurity.PublicStatementSeed980.field29

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field30
#print axioms ShielddSecurity.PublicStatementSeed980.field30

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field31
#print axioms ShielddSecurity.PublicStatementSeed980.field31

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field32
#print axioms ShielddSecurity.PublicStatementSeed980.field32

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field33
#print axioms ShielddSecurity.PublicStatementSeed980.field33

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field34
#print axioms ShielddSecurity.PublicStatementSeed980.field34

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field35
#print axioms ShielddSecurity.PublicStatementSeed980.field35

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field36
#print axioms ShielddSecurity.PublicStatementSeed980.field36

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field37
#print axioms ShielddSecurity.PublicStatementSeed980.field37

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field38
#print axioms ShielddSecurity.PublicStatementSeed980.field38

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field39
#print axioms ShielddSecurity.PublicStatementSeed980.field39

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field40
#print axioms ShielddSecurity.PublicStatementSeed980.field40

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field41
#print axioms ShielddSecurity.PublicStatementSeed980.field41

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field42
#print axioms ShielddSecurity.PublicStatementSeed980.field42

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field43
#print axioms ShielddSecurity.PublicStatementSeed980.field43

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field44
#print axioms ShielddSecurity.PublicStatementSeed980.field44

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field45
#print axioms ShielddSecurity.PublicStatementSeed980.field45

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field46
#print axioms ShielddSecurity.PublicStatementSeed980.field46

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field47
#print axioms ShielddSecurity.PublicStatementSeed980.field47

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field48
#print axioms ShielddSecurity.PublicStatementSeed980.field48

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field49
#print axioms ShielddSecurity.PublicStatementSeed980.field49

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field50
#print axioms ShielddSecurity.PublicStatementSeed980.field50

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field51
#print axioms ShielddSecurity.PublicStatementSeed980.field51

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field52
#print axioms ShielddSecurity.PublicStatementSeed980.field52

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field53
#print axioms ShielddSecurity.PublicStatementSeed980.field53

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field54
#print axioms ShielddSecurity.PublicStatementSeed980.field54

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field55
#print axioms ShielddSecurity.PublicStatementSeed980.field55

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field56
#print axioms ShielddSecurity.PublicStatementSeed980.field56

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field57
#print axioms ShielddSecurity.PublicStatementSeed980.field57

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field58
#print axioms ShielddSecurity.PublicStatementSeed980.field58

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field59
#print axioms ShielddSecurity.PublicStatementSeed980.field59

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field60
#print axioms ShielddSecurity.PublicStatementSeed980.field60

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field61
#print axioms ShielddSecurity.PublicStatementSeed980.field61

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field62
#print axioms ShielddSecurity.PublicStatementSeed980.field62

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.field63
#print axioms ShielddSecurity.PublicStatementSeed980.field63

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.outside
#print axioms ShielddSecurity.PublicStatementSeed980.outside

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.zero
#print axioms ShielddSecurity.PublicStatementSeed980.zero

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.net_x
#print axioms ShielddSecurity.PublicStatementSeed980.net_x

set_option pp.all true in
#check @ShielddSecurity.PublicStatementSeed980.net_y
#print axioms ShielddSecurity.PublicStatementSeed980.net_y
