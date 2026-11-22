import Mathlib
import Cvs.Finite.ProperDiagonalMinimum
import Cvs.StepA.CircleEvenStepA
import Cvs.StepA.OddGroundStateSimple
import Cvs.Upstream.TightCoordinateConvergence
import Cvs.WeilForm.DiagonalMinimumZeroMode
import Cvs.WeilForm.EvenDiagonalProper
import Cvs.WeilForm.EvenSectorMinimum
import Cvs.WeilForm.MinimumAvoidsDiagonal
import Cvs.WeilForm.PoleVectorModes
import Cvs.WeilForm.PoleVectorSquareSummable
import Cvs.Zeta.Digamma.ArchPairingLowerBound

/-!
# Where the even-sector minimum sits

    D₀ < λ_min < D_{m₁}

with `m₁` the mode carrying the second level.  Both ends are strict, so the minimum lies in
the open gap, which is the position `Cvs.Finite.ProperDiagonalMinimum`'s isolation argument compares against.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Cvs.Upstream.TightCoordinateConvergence Cvs.Upstream.DiagonalRankOneMinimum Cvs.WeilForm.EvenSectorMinimum Cvs.WeilForm.PoleVectorModes Cvs.StepA.CircleEvenStepA

namespace Cvs.StepA.EvenSectorMinimumGap

variable {κ : Type*}

/-- **The minimum lies strictly inside the first gap.** -/
theorem weil_even_gap {L : ℝ} (hL : 0 < L) (s : Finset κ) (w u : κ → ℝ)
    (hw : ∀ j ∈ s, 0 ≤ w j) {c : ℝ} (hc : 0 < c) :
    ∃ η ∈ sphereDom (fun n : ℕ => weilDiag L s w u n - weilFloor s w),
      ∃ m₁ : ℕ, m₁ ≠ 0
        ∧ (∀ n : ℕ, n ≠ 0 → weilDiag L s w u m₁ ≤ weilDiag L s w u n)
        ∧ (∀ a ∈ sphereDom (fun n : ℕ => weilDiag L s w u n - weilFloor s w),
            diagFormVal (weilDiag L s w u) c (poleCoeff L) η
              ≤ diagFormVal (weilDiag L s w u) c (poleCoeff L) a)
        ∧ weilDiag L s w u 0 < diagFormVal (weilDiag L s w u) c (poleCoeff L) η
        ∧ diagFormVal (weilDiag L s w u) c (poleCoeff L) η < weilDiag L s w u m₁ := by
  classical
  have hvsum := Cvs.WeilForm.PoleVectorSquareSummable.summable_sq_poleCoeff hL
  have hvne : ∀ n : ℕ, poleCoeff L n ≠ 0 := fun n => poleCoeff_ne_zero hL n
  have hD : ∀ m : ℕ, m ≠ 0 → weilDiag L s w u 0 < weilDiag L s w u m := fun m hm =>
    Cvs.WeilForm.DiagonalMinimumZeroMode.diag_lt_of_ne_zero hL s w u hw hm
  have hDle : ∀ n : ℕ, weilDiag L s w u 0 ≤ weilDiag L s w u n := by
    intro n
    by_cases h : n = 0
    · rw [h]
    · exact (hD n h).le
  have hproper : ∀ M : ℝ, {n : ℕ | weilDiag L s w u n < M}.Finite := fun M =>
    Cvs.WeilForm.EvenDiagonalProper.diag_finite_below hL s w u M
  have hSne : ({n : ℕ | n ≠ 0}).Nonempty := ⟨1, one_ne_zero⟩
  obtain ⟨m₁, hm₁ne, hm₁min⟩ :=
    Cvs.Finite.ProperDiagonalMinimum.exists_second (D := weilDiag L s w u) hproper (n₀ := 0) hSne
  obtain ⟨η, hη, hmin⟩ :=
    Cvs.WeilForm.EvenSectorMinimum.exists_weil_minimiser hL s w u c hvsum
  refine ⟨η, hη, m₁, hm₁ne, hm₁min, hmin, ?_, ?_⟩
  · -- above the bottom: it cannot equal it, and it cannot fall below it
    have hge : weilDiag L s w u 0
        ≤ diagFormVal (weilDiag L s w u) c (poleCoeff L) η := by
      obtain ⟨hnorm, hunit, hshift⟩ := hη
      have hDsum : Summable fun n : ℕ => weilDiag L s w u n * (η n) ^ 2 := by
        have h2 := hshift.add (hnorm.mul_left (weilFloor s w))
        refine h2.congr fun n => ?_
        simp only [weilFloor, weilDiag]
        ring
      exact Cvs.StepA.OddGroundStateSimple.diag_le_of_pos hc.le hDle hnorm hunit hDsum
    have hne := Cvs.WeilForm.MinimumAvoidsDiagonal.min_notMem_diag hc hη hmin hD hvne 0
    exact lt_of_le_of_ne hge (Ne.symm hne)
  · -- below the second level
    exact Cvs.WeilForm.MinimumAvoidsDiagonal.min_lt_of_ne hmin hD hvne hm₁ne

end Cvs.StepA.EvenSectorMinimumGap
