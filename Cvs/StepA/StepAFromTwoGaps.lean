import Mathlib
import Cvs.StepA.StepAPredicate
import Cvs.WeilForm.BottomAttained
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.ParallelogramLaw
import Cvs.WeilForm.ParallelogramMinimiserPlanes
import Cvs.WeilForm.SimpleGroundEvenOrOdd
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowReflectionSymmetry
import Cvs.WeilForm.WindowRepresentative

/-!
# Step (a) on the form domain from two spectral gaps

    odd sector strictly above the bottom, and a form beneath `Q` on even classes whose
    second min–max on even planes exceeds the bottom
        ⟹   `∃ η, StepA (weilQW on the form domain) reflD lam η`
-/

noncomputable section

open MeasureTheory

namespace Cvs.StepA.StepAFromTwoGaps

/-- **The even classes** of the form domain. -/
def evenSub {L : ℝ} (hL : 0 ≤ L) : Submodule ℝ (Cvs.WeilForm.FormDomain.formDomain hL) where
  carrier := {v | Cvs.WeilForm.WindowReflectionSymmetry.reflD hL v = v}
  add_mem' := by
    intro a b ha hb
    show Cvs.WeilForm.WindowReflectionSymmetry.reflD hL (a + b) = a + b
    rw [Cvs.WeilForm.EvenOddSplitForm.reflD_add, ha, hb]
  zero_mem' := by
    show Cvs.WeilForm.WindowReflectionSymmetry.reflD hL 0 = 0
    have := Cvs.WeilForm.SimpleGroundEvenOrOdd.reflD_smul hL 0 (0 : Cvs.WeilForm.FormDomain.formDomain hL)
    rwa [zero_smul, zero_smul] at this
  smul_mem' := by
    intro c a ha
    show Cvs.WeilForm.WindowReflectionSymmetry.reflD hL (c • a) = c • a
    rw [Cvs.WeilForm.SimpleGroundEvenOrOdd.reflD_smul, ha]

theorem hpar {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) :
    ∀ x y : Cvs.WeilForm.FormDomain.formDomain hL,
      Cvs.WeilForm.InfimumAttainedSphere.Q hL P R (x + y) + Cvs.WeilForm.InfimumAttainedSphere.Q hL P R (x - y)
        = 2 * Cvs.WeilForm.InfimumAttainedSphere.Q hL P R x + 2 * Cvs.WeilForm.InfimumAttainedSphere.Q hL P R y :=
  fun x y => Cvs.WeilForm.ParallelogramLaw.weilQW_parallelogram hL P R x y

theorem hsmul {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) :
    ∀ (c : ℝ) (x : Cvs.WeilForm.FormDomain.formDomain hL),
      Cvs.WeilForm.InfimumAttainedSphere.Q hL P R (c • x) = c ^ 2 * Cvs.WeilForm.InfimumAttainedSphere.Q hL P R x := by
  intro c x
  show Cvs.WeilForm.WindowRepresentative.weilQW P R ((c • x : Cvs.WeilForm.FormDomain.formDomain hL) :
    Cvs.WeilForm.WeilFormOnWindowL2.window L) = _
  rw [Submodule.coe_smul, Cvs.WeilForm.BottomAttained.weilQW_smul]

set_option maxHeartbeats 1000000 in
/-- **Simplicity from the odd/even gap and a plane gap on the even classes.** -/
theorem simple_of_gaps {L : ℝ} (hL : 0 < L) (P R : ℕ)
    (hodd : ∀ o : Cvs.WeilForm.FormDomain.formDomain hL.le,
      Cvs.WeilForm.WindowReflectionSymmetry.reflD hL.le o = -o → o ≠ 0 →
      Cvs.WeilForm.BottomAttained.lam hL P R * ‖o‖ ^ 2 < Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R o)
    {Qt : Cvs.WeilForm.FormDomain.formDomain hL.le → ℝ} {mu2 : ℝ}
    (hle : ∀ v, Cvs.WeilForm.WindowReflectionSymmetry.reflD hL.le v = v → Qt v ≤ Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R v)
    (hgap : Cvs.WeilForm.BottomAttained.lam hL P R < mu2)
    (hplane : ∀ V : Submodule ℝ (Cvs.WeilForm.FormDomain.formDomain hL.le),
      Module.finrank ℝ V = 2 → V ≤ evenSub hL.le → ∃ v ∈ V, v ≠ 0 ∧ mu2 * ‖v‖ ^ 2 ≤ Qt v) :
    ∀ v w : Cvs.WeilForm.FormDomain.formDomain hL.le,
      Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R v = Cvs.WeilForm.BottomAttained.lam hL P R * ‖v‖ ^ 2 →
      Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R w = Cvs.WeilForm.BottomAttained.lam hL P R * ‖w‖ ^ 2 →
      v ≠ 0 → ∃ c : ℝ, w = c • v := by
  refine Cvs.WeilForm.ParallelogramMinimiserPlanes.simple_of_plane_gap (E := Cvs.WeilForm.FormDomain.formDomain hL.le)
    (Q := Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R) (Qt := Qt) (lam := Cvs.WeilForm.BottomAttained.lam hL P R)
    (mu2 := mu2) (W := evenSub hL.le) ?_ ?_ ?_ ?_ ?_ hgap ?_
  · exact hpar hL.le P R
  · exact hsmul hL.le P R
  · exact Cvs.WeilForm.BottomAttained.bottom hL P R
  · intro v hv
    exact Cvs.WeilForm.EvenOddSplitForm.even_of_odd_gap hL.le P R (Cvs.WeilForm.BottomAttained.bottom hL P R) hodd hv
  · intro v hv
    exact hle v hv
  · exact hplane

set_option maxHeartbeats 1000000 in
/-- **Step (a) from the two gaps.** -/
theorem stepA_of_gaps {L : ℝ} (hL : 0 < L) (P R : ℕ)
    (hodd : ∀ o : Cvs.WeilForm.FormDomain.formDomain hL.le,
      Cvs.WeilForm.WindowReflectionSymmetry.reflD hL.le o = -o → o ≠ 0 →
      Cvs.WeilForm.BottomAttained.lam hL P R * ‖o‖ ^ 2 < Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R o)
    (hQt : ∃ (Qt : Cvs.WeilForm.FormDomain.formDomain hL.le → ℝ) (mu2 : ℝ),
      Cvs.WeilForm.BottomAttained.lam hL P R < mu2 ∧
      (∀ v, Cvs.WeilForm.WindowReflectionSymmetry.reflD hL.le v = v → Qt v ≤ Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R v) ∧
      ∀ V : Submodule ℝ (Cvs.WeilForm.FormDomain.formDomain hL.le),
        Module.finrank ℝ V = 2 → V ≤ evenSub hL.le → ∃ v ∈ V, v ≠ 0 ∧ mu2 * ‖v‖ ^ 2 ≤ Qt v) :
    ∃ η : Cvs.WeilForm.FormDomain.formDomain hL.le,
      Cvs.StepA.StepAPredicate.StepA
        (fun v : Cvs.WeilForm.FormDomain.formDomain hL.le =>
          Cvs.WeilForm.WindowRepresentative.weilQW P R (v : Cvs.WeilForm.WeilFormOnWindowL2.window L))
        (Cvs.WeilForm.WindowReflectionSymmetry.reflD hL.le) (Cvs.WeilForm.BottomAttained.lam hL P R) η := by
  obtain ⟨Qt, mu2, hgap, hle, hplane⟩ := hQt
  exact Cvs.WeilForm.EvenOddSplitForm.stepA_of_odd_gap hL P R hodd fun v w _ _ hv hw hv0 =>
    simple_of_gaps hL P R hodd hle hgap hplane v w hv hw hv0

end Cvs.StepA.StepAFromTwoGaps
