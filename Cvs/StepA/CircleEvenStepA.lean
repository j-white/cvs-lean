import Mathlib
import Cvs.Upstream.TightCoordinateConvergence
import Cvs.WeilForm.DiagonalMinimumZeroMode
import Cvs.WeilForm.EvenDiagonalProper
import Cvs.WeilForm.EvenSectorMinimum
import Cvs.WeilForm.MinimiserEulerLagrange
import Cvs.WeilForm.MinimumAvoidsDiagonal
import Cvs.WeilForm.PoleVectorModes
import Cvs.WeilForm.PoleVectorSquareSummable
import Cvs.Zeta.Digamma.ArchPairingLowerBound

/-!
# Connes' step (a), on the even modes of the circle

For the circle of circumference `L` and nonnegative prime weights, the even-sector form has a
ground state, its value meets no diagonal level, and any two minimisers are proportional —
so the minimum is simple, and even because cosine modes are.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Cvs.Upstream.TightCoordinateConvergence Cvs.Upstream.DiagonalRankOneMinimum Cvs.WeilForm.EvenSectorMinimum Cvs.WeilForm.PoleVectorModes

namespace Cvs.StepA.CircleEvenStepA

variable {κ : Type*}

/-- The even-sector diagonal: the archimedean symbol, less the prime side's diagonal. -/
def weilDiag (L : ℝ) (s : Finset κ) (w u : κ → ℝ) : ℕ → ℝ :=
  Cvs.WeilForm.EvenDiagonalProper.diagVal L s w u

/-- The floor the diagonal is shifted against. -/
def weilFloor (s : Finset κ) (w : κ → ℝ) : ℝ :=
  2 * Cvs.Zeta.Digamma.ArchPairingLowerBound.archConst - ∑ j ∈ s, |w j|

/-- A unit vector has a nonzero coordinate. -/
theorem exists_ne_zero {σ : ℕ → ℝ} {η : ℕ → ℝ} (hη : η ∈ sphereDom σ) : ∃ n : ℕ, η n ≠ 0 := by
  by_contra h
  push_neg at h
  obtain ⟨-, hunit, -⟩ := hη
  have hz : ∀ n : ℕ, (η n) ^ 2 = 0 := fun n => by rw [h n]; ring
  rw [tsum_congr hz] at hunit
  simp at hunit

/-- **Step (a) on the even modes.**  A ground state exists; its value avoids every diagonal
level; and any two ground states are proportional. -/
theorem weil_even_step_a {L : ℝ} (hL : 0 < L) (s : Finset κ) (w u : κ → ℝ)
    (hw : ∀ j ∈ s, 0 ≤ w j) {c : ℝ} (hc : 0 < c) :
    ∃ η ∈ sphereDom (fun n => weilDiag L s w u n - weilFloor s w),
      (∀ a ∈ sphereDom (fun n => weilDiag L s w u n - weilFloor s w),
          diagFormVal (weilDiag L s w u) c (poleCoeff L) η
            ≤ diagFormVal (weilDiag L s w u) c (poleCoeff L) a)
        ∧ (∀ n : ℕ, diagFormVal (weilDiag L s w u) c (poleCoeff L) η ≠ weilDiag L s w u n)
        ∧ (∀ η' ∈ sphereDom (fun n => weilDiag L s w u n - weilFloor s w),
            (∀ a ∈ sphereDom (fun n => weilDiag L s w u n - weilFloor s w),
              diagFormVal (weilDiag L s w u) c (poleCoeff L) η'
                ≤ diagFormVal (weilDiag L s w u) c (poleCoeff L) a) →
            ∃ t : ℝ, ∀ n : ℕ, η' n = t * η n) := by
  have hvsum := Cvs.WeilForm.PoleVectorSquareSummable.summable_sq_poleCoeff hL
  have hvne : ∀ n : ℕ, poleCoeff L n ≠ 0 := fun n => poleCoeff_ne_zero hL n
  have hD : ∀ m : ℕ, m ≠ 0 → weilDiag L s w u 0 < weilDiag L s w u m := fun m hm =>
    Cvs.WeilForm.DiagonalMinimumZeroMode.diag_lt_of_ne_zero hL s w u hw hm
  obtain ⟨η, hη, hmin⟩ :=
    Cvs.WeilForm.EvenSectorMinimum.exists_weil_minimiser hL s w u c hvsum
  refine ⟨η, hη, hmin, ?_, ?_⟩
  · intro n
    exact Cvs.WeilForm.MinimumAvoidsDiagonal.min_notMem_diag hc hη hmin hD hvne n
  · intro η' hη' hmin'
    refine Cvs.WeilForm.MinimiserEulerLagrange.minimiser_unique hη hη' hmin hmin' hvsum ?_ (exists_ne_zero hη)
    intro n
    exact Cvs.WeilForm.MinimumAvoidsDiagonal.min_notMem_diag hc hη hmin hD hvne n

end Cvs.StepA.CircleEvenStepA
