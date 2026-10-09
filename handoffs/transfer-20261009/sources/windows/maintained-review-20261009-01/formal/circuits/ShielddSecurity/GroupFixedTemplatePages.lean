import ShielddSecurity.GroupFixedTemplateTrace
import ShielddSecurity.GroupFixedCircuitBounds

set_option maxHeartbeats 300000
set_option maxRecDepth 2048

namespace ShielddSecurity.GroupFixedTemplatePages

open GroupFixedTemplateTrace

/-- Carry the actual last weighted table base across a page boundary. -/
def endBase (base : Group.Point Int) : List Window → Group.Point Int
  | [] => base
  | window :: tail => endBase window.nextBase tail

theorem aligned_append (input : Linear × Linear) (base : Group.Point Int)
    (front back : List Window) (first : Aligned input base front)
    (second : Aligned (endpoint input front) (endBase base front) back) :
    Aligned input base (front ++ back) := by
  induction front generalizing input base with
  | nil => exact second
  | cons window tail ih =>
    exact ⟨first.1,first.2.1,ih window.output window.nextBase first.2.2 second⟩

theorem program_aligned_append (input : Linear × Linear)
    (front back : List GroupFixedCircuitCompletion.Program)
    (first : GroupFixedCircuitCompletion.Aligned input front)
    (second : GroupFixedCircuitCompletion.Aligned
      (GroupFixedCircuitCompletion.output input front) back) :
    GroupFixedCircuitCompletion.Aligned input (front ++ back) := by
  induction front generalizing input with
  | nil => exact second
  | cons program tail ih =>
    exact ⟨first.1,ih program.output first.2 second⟩

def endFrame (before : GroupFixedCircuitBounds.Frame) :
    List (GroupFixedCircuitCompletion.Program × GroupFixedCircuitBounds.Frame) →
      GroupFixedCircuitBounds.Frame
  | [] => before
  | segment :: tail => endFrame segment.2 tail

theorem certified_append (highStart copy : Nat)
    (before : GroupFixedCircuitBounds.Frame)
    (front back : List (GroupFixedCircuitCompletion.Program × GroupFixedCircuitBounds.Frame))
    (first : GroupFixedCircuitBounds.Certified highStart copy before front)
    (second : GroupFixedCircuitBounds.Certified highStart copy (endFrame before front) back) :
    GroupFixedCircuitBounds.Certified highStart copy before (front ++ back) := by
  induction front generalizing before with
  | nil => exact second
  | cons segment tail ih =>
    rcases segment with ⟨program,after⟩
    exact ⟨first.1,first.2.1,first.2.2.1,ih after first.2.2.2 second⟩

def CertifiedPages (highStart copy : Nat) (before : GroupFixedCircuitBounds.Frame) :
    List (List (GroupFixedCircuitCompletion.Program × GroupFixedCircuitBounds.Frame)) → Prop
  | [] => True
  | page :: tail => GroupFixedCircuitBounds.Certified highStart copy before page ∧
      CertifiedPages highStart copy (endFrame before page) tail

theorem certified_pages (highStart copy : Nat) (before : GroupFixedCircuitBounds.Frame)
    (pages : List (List (GroupFixedCircuitCompletion.Program × GroupFixedCircuitBounds.Frame)))
    (checked : CertifiedPages highStart copy before pages) :
    GroupFixedCircuitBounds.Certified highStart copy before pages.flatten := by
  induction pages generalizing before with
  | nil => trivial
  | cons page tail ih =>
    exact certified_append highStart copy before page tail.flatten checked.1
      (ih _ checked.2)

def AlignedPages (input : Linear × Linear) (base : Group.Point Int) : List (List Window) → Prop
  | [] => True
  | page :: tail => Aligned input base page ∧
      AlignedPages (endpoint input page) (endBase base page) tail

theorem aligned_pages (input : Linear × Linear) (base : Group.Point Int)
    (pages : List (List Window)) (checked : AlignedPages input base pages) :
    Aligned input base pages.flatten := by
  induction pages generalizing input base with
  | nil => trivial
  | cons page tail ih =>
    exact aligned_append input base page tail.flatten checked.1 (ih _ _ checked.2)

theorem checked_pages (p copy : Nat) (d : Int) (pages : List (List Window))
    (checked : ∀ page ∈ pages, ∀ window ∈ page,
      window.Checked p copy d ∧ window.TableChecked p) :
    ∀ window ∈ pages.flatten, window.Checked p copy d ∧ window.TableChecked p := by
  induction pages with
  | nil => intro window member; cases member
  | cons page tail ih =>
    intro window member
    rcases List.mem_append.mp member with front | back
    · exact checked page (by simp) window front
    · exact ih (by intro next present; exact checked next (List.mem_cons_of_mem _ present)) window back

set_option pp.all true in
#check @aligned_append
#print axioms aligned_append
set_option pp.all true in
#check @program_aligned_append
#print axioms program_aligned_append
set_option pp.all true in
#check @certified_append
#print axioms certified_append
set_option pp.all true in
#check @certified_pages
#print axioms certified_pages
set_option pp.all true in
#check @aligned_pages
#print axioms aligned_pages
set_option pp.all true in
#check @checked_pages
#print axioms checked_pages

end ShielddSecurity.GroupFixedTemplatePages
