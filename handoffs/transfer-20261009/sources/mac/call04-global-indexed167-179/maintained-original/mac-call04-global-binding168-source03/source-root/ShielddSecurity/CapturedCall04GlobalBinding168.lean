import ShielddSecurity.CapturedCall04GlobalBinding167Pilot
import ShielddSecurity.CapturedCall04GlobalBinding168B00
import ShielddSecurity.CapturedCall04GlobalBinding168B01
import ShielddSecurity.CapturedCall04GlobalBinding168B02
import ShielddSecurity.CapturedCall04GlobalBinding168B03
import ShielddSecurity.CapturedCall04GlobalBinding168B04
import ShielddSecurity.CapturedCall04GlobalBinding168B05
import ShielddSecurity.CapturedCall04GlobalBinding168B06
import ShielddSecurity.CapturedCall04GlobalBinding168B07
import ShielddSecurity.CapturedCall04GlobalBinding168B08
import ShielddSecurity.CapturedCall04GlobalBinding168B09
import ShielddSecurity.CapturedCall04GlobalBinding168B10
import ShielddSecurity.CapturedCall04GlobalBinding168B11
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedCall04GlobalBinding168
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
open CapturedInitial73419Completion01 (callRows)
theorem count : callRows.length=412 := by decide +kernel
theorem partition : ((((((((((((CapturedCall04GlobalBinding167Pilot.rows++CapturedCall04GlobalBinding168B00.rows)++CapturedCall04GlobalBinding168B01.rows)++CapturedCall04GlobalBinding168B02.rows)++CapturedCall04GlobalBinding168B03.rows)++CapturedCall04GlobalBinding168B04.rows)++CapturedCall04GlobalBinding168B05.rows)++CapturedCall04GlobalBinding168B06.rows)++CapturedCall04GlobalBinding168B07.rows)++CapturedCall04GlobalBinding168B08.rows)++CapturedCall04GlobalBinding168B09.rows)++CapturedCall04GlobalBinding168B10.rows)++CapturedCall04GlobalBinding168B11.rows)=callRows := by
  change ((((((((((((callRows.take 32++(callRows.drop 32).take 32)++(callRows.drop 64).take 32)++(callRows.drop 96).take 32)++(callRows.drop 128).take 32)++(callRows.drop 160).take 32)++(callRows.drop 192).take 32)++(callRows.drop 224).take 32)++(callRows.drop 256).take 32)++(callRows.drop 288).take 32)++(callRows.drop 320).take 32)++(callRows.drop 352).take 32)++(callRows.drop 384).take 28)=callRows
  rw [←List.take_add (i:=32) (j:=32),←List.take_add (i:=64) (j:=32),←List.take_add (i:=96) (j:=32),←List.take_add (i:=128) (j:=32),←List.take_add (i:=160) (j:=32),←List.take_add (i:=192) (j:=32),←List.take_add (i:=224) (j:=32),←List.take_add (i:=256) (j:=32),←List.take_add (i:=288) (j:=32),←List.take_add (i:=320) (j:=32),←List.take_add (i:=352) (j:=32),←List.take_add (i:=384) (j:=28)]
  apply List.take_of_length_le
  exact Nat.le_of_eq count
variable {F : Type} [Field F] [CharP F p]
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    Satisfies rho callRows := by
  have merge (a b : List Row) (ha : Satisfies rho a) (hb : Satisfies rho b) : Satisfies rho (a++b) := by
    intro row member
    rcases List.mem_append.mp member with member|member
    · exact ha row member
    · exact hb row member
  rw [←partition]
  exact (merge (((((((((((CapturedCall04GlobalBinding167Pilot.rows++CapturedCall04GlobalBinding168B00.rows)++CapturedCall04GlobalBinding168B01.rows)++CapturedCall04GlobalBinding168B02.rows)++CapturedCall04GlobalBinding168B03.rows)++CapturedCall04GlobalBinding168B04.rows)++CapturedCall04GlobalBinding168B05.rows)++CapturedCall04GlobalBinding168B06.rows)++CapturedCall04GlobalBinding168B07.rows)++CapturedCall04GlobalBinding168B08.rows)++CapturedCall04GlobalBinding168B09.rows)++CapturedCall04GlobalBinding168B10.rows) CapturedCall04GlobalBinding168B11.rows (merge ((((((((((CapturedCall04GlobalBinding167Pilot.rows++CapturedCall04GlobalBinding168B00.rows)++CapturedCall04GlobalBinding168B01.rows)++CapturedCall04GlobalBinding168B02.rows)++CapturedCall04GlobalBinding168B03.rows)++CapturedCall04GlobalBinding168B04.rows)++CapturedCall04GlobalBinding168B05.rows)++CapturedCall04GlobalBinding168B06.rows)++CapturedCall04GlobalBinding168B07.rows)++CapturedCall04GlobalBinding168B08.rows)++CapturedCall04GlobalBinding168B09.rows) CapturedCall04GlobalBinding168B10.rows (merge (((((((((CapturedCall04GlobalBinding167Pilot.rows++CapturedCall04GlobalBinding168B00.rows)++CapturedCall04GlobalBinding168B01.rows)++CapturedCall04GlobalBinding168B02.rows)++CapturedCall04GlobalBinding168B03.rows)++CapturedCall04GlobalBinding168B04.rows)++CapturedCall04GlobalBinding168B05.rows)++CapturedCall04GlobalBinding168B06.rows)++CapturedCall04GlobalBinding168B07.rows)++CapturedCall04GlobalBinding168B08.rows) CapturedCall04GlobalBinding168B09.rows (merge ((((((((CapturedCall04GlobalBinding167Pilot.rows++CapturedCall04GlobalBinding168B00.rows)++CapturedCall04GlobalBinding168B01.rows)++CapturedCall04GlobalBinding168B02.rows)++CapturedCall04GlobalBinding168B03.rows)++CapturedCall04GlobalBinding168B04.rows)++CapturedCall04GlobalBinding168B05.rows)++CapturedCall04GlobalBinding168B06.rows)++CapturedCall04GlobalBinding168B07.rows) CapturedCall04GlobalBinding168B08.rows (merge (((((((CapturedCall04GlobalBinding167Pilot.rows++CapturedCall04GlobalBinding168B00.rows)++CapturedCall04GlobalBinding168B01.rows)++CapturedCall04GlobalBinding168B02.rows)++CapturedCall04GlobalBinding168B03.rows)++CapturedCall04GlobalBinding168B04.rows)++CapturedCall04GlobalBinding168B05.rows)++CapturedCall04GlobalBinding168B06.rows) CapturedCall04GlobalBinding168B07.rows (merge ((((((CapturedCall04GlobalBinding167Pilot.rows++CapturedCall04GlobalBinding168B00.rows)++CapturedCall04GlobalBinding168B01.rows)++CapturedCall04GlobalBinding168B02.rows)++CapturedCall04GlobalBinding168B03.rows)++CapturedCall04GlobalBinding168B04.rows)++CapturedCall04GlobalBinding168B05.rows) CapturedCall04GlobalBinding168B06.rows (merge (((((CapturedCall04GlobalBinding167Pilot.rows++CapturedCall04GlobalBinding168B00.rows)++CapturedCall04GlobalBinding168B01.rows)++CapturedCall04GlobalBinding168B02.rows)++CapturedCall04GlobalBinding168B03.rows)++CapturedCall04GlobalBinding168B04.rows) CapturedCall04GlobalBinding168B05.rows (merge ((((CapturedCall04GlobalBinding167Pilot.rows++CapturedCall04GlobalBinding168B00.rows)++CapturedCall04GlobalBinding168B01.rows)++CapturedCall04GlobalBinding168B02.rows)++CapturedCall04GlobalBinding168B03.rows) CapturedCall04GlobalBinding168B04.rows (merge (((CapturedCall04GlobalBinding167Pilot.rows++CapturedCall04GlobalBinding168B00.rows)++CapturedCall04GlobalBinding168B01.rows)++CapturedCall04GlobalBinding168B02.rows) CapturedCall04GlobalBinding168B03.rows (merge ((CapturedCall04GlobalBinding167Pilot.rows++CapturedCall04GlobalBinding168B00.rows)++CapturedCall04GlobalBinding168B01.rows) CapturedCall04GlobalBinding168B02.rows (merge (CapturedCall04GlobalBinding167Pilot.rows++CapturedCall04GlobalBinding168B00.rows) CapturedCall04GlobalBinding168B01.rows (merge CapturedCall04GlobalBinding167Pilot.rows CapturedCall04GlobalBinding168B00.rows (CapturedCall04GlobalBinding167Pilot.sound rho satisfied) (CapturedCall04GlobalBinding168B00.sound rho satisfied)) (CapturedCall04GlobalBinding168B01.sound rho satisfied)) (CapturedCall04GlobalBinding168B02.sound rho satisfied)) (CapturedCall04GlobalBinding168B03.sound rho satisfied)) (CapturedCall04GlobalBinding168B04.sound rho satisfied)) (CapturedCall04GlobalBinding168B05.sound rho satisfied)) (CapturedCall04GlobalBinding168B06.sound rho satisfied)) (CapturedCall04GlobalBinding168B07.sound rho satisfied)) (CapturedCall04GlobalBinding168B08.sound rho satisfied)) (CapturedCall04GlobalBinding168B09.sound rho satisfied)) (CapturedCall04GlobalBinding168B10.sound rho satisfied)) (CapturedCall04GlobalBinding168B11.sound rho satisfied))
end ShielddSecurity.CapturedCall04GlobalBinding168

set_option pp.all true in
#check @ShielddSecurity.CapturedCall04GlobalBinding168.count
#print axioms ShielddSecurity.CapturedCall04GlobalBinding168.count
set_option pp.all true in
#check @ShielddSecurity.CapturedCall04GlobalBinding168.partition
#print axioms ShielddSecurity.CapturedCall04GlobalBinding168.partition
set_option pp.all true in
#check @ShielddSecurity.CapturedCall04GlobalBinding168.sound
#print axioms ShielddSecurity.CapturedCall04GlobalBinding168.sound
