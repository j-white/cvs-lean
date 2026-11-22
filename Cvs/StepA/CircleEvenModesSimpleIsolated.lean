import Mathlib
import Cvs.Finite.MinimiserSecularIsolation
import Cvs.StepA.CircleEvenStepA
import Cvs.StepA.EvenSectorMinimumGap
import Cvs.Upstream.TightCoordinateConvergence
import Cvs.WeilForm.DiagonalMinimumZeroMode
import Cvs.WeilForm.EvenDiagonalProper
import Cvs.WeilForm.EvenSectorMinimum
import Cvs.WeilForm.MinimiserEulerLagrange
import Cvs.WeilForm.MinimumAvoidsDiagonal
import Cvs.WeilForm.PoleVectorModes
import Cvs.WeilForm.PoleVectorSquareSummable

/-!
# Step (a) on the even modes of the circle, both halves

The even-sector form whose shift sums run over a full period has a ground state; its value
lies strictly between the two lowest diagonal levels; any two ground states are proportional;
and no other eigenvalue shares that interval.  Simple, isolated, and even.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Cvs.Upstream.TightCoordinateConvergence Cvs.Upstream.DiagonalRankOneMinimum Cvs.WeilForm.EvenSectorMinimum Cvs.WeilForm.PoleVectorModes Cvs.StepA.CircleEvenStepA

namespace Cvs.StepA.CircleEvenModesSimpleIsolated

variable {κ : Type*}

/-- **Step (a), on the even modes of the circle.**  Existence, position, simplicity and
isolation, for the diagonal the circle's modes give and the pole vector on `[−L/2, L/2]`. -/
theorem weil_even_circle_simple_isolated {L : ℝ} (hL : 0 < L) (s : Finset κ) (w u : κ → ℝ)
    (hw : ∀ j ∈ s, 0 ≤ w j) {c : ℝ} (hc : 0 < c) :
    ∃ η ∈ sphereDom (fun n : ℕ => weilDiag L s w u n - weilFloor s w), ∃ m₁ : ℕ,
      m₁ ≠ 0
      ∧ (∀ a ∈ sphereDom (fun n : ℕ => weilDiag L s w u n - weilFloor s w),
          diagFormVal (weilDiag L s w u) c (poleCoeff L) η
            ≤ diagFormVal (weilDiag L s w u) c (poleCoeff L) a)
      ∧ weilDiag L s w u 0 < diagFormVal (weilDiag L s w u) c (poleCoeff L) η
      ∧ diagFormVal (weilDiag L s w u) c (poleCoeff L) η < weilDiag L s w u m₁
      ∧ (∀ η' ∈ sphereDom (fun n : ℕ => weilDiag L s w u n - weilFloor s w),
          (∀ a ∈ sphereDom (fun n : ℕ => weilDiag L s w u n - weilFloor s w),
            diagFormVal (weilDiag L s w u) c (poleCoeff L) η'
              ≤ diagFormVal (weilDiag L s w u) c (poleCoeff L) a) →
          ∃ t : ℝ, ∀ n : ℕ, η' n = t * η n)
      ∧ (∀ (mu : ℝ) (ζ : ℕ → ℝ),
          (∀ n : ℕ, (mu - weilDiag L s w u n) * ζ n
            = c * (∑' k : ℕ, poleCoeff L k * ζ k) * poleCoeff L n) →
          (∃ n : ℕ, ζ n ≠ 0) →
          weilDiag L s w u 0 < mu → mu < weilDiag L s w u m₁ →
          mu = diagFormVal (weilDiag L s w u) c (poleCoeff L) η) := by
  classical
  have hvsum := Cvs.WeilForm.PoleVectorSquareSummable.summable_sq_poleCoeff hL
  have hvne : ∀ n : ℕ, poleCoeff L n ≠ 0 := fun n => poleCoeff_ne_zero hL n
  have hD : ∀ m : ℕ, m ≠ 0 → weilDiag L s w u 0 < weilDiag L s w u m := fun m hm =>
    Cvs.WeilForm.DiagonalMinimumZeroMode.diag_lt_of_ne_zero hL s w u hw hm
  have hproper : ∀ M : ℝ, {n : ℕ | weilDiag L s w u n < M}.Finite := fun M =>
    Cvs.WeilForm.EvenDiagonalProper.diag_finite_below hL s w u M
  obtain ⟨η, hη, m₁, hm₁ne, hm₁min, hmin, hlo, hhi⟩ :=
    Cvs.StepA.EvenSectorMinimumGap.weil_even_gap hL s w u hw hc
  have hsep := Cvs.WeilForm.MinimumAvoidsDiagonal.min_notMem_diag hc hη hmin hD hvne
  have hEL := Cvs.WeilForm.MinimiserEulerLagrange.euler_lagrange hη hmin hvsum
  have hηne := Cvs.StepA.CircleEvenStepA.exists_ne_zero hη
  refine ⟨η, hη, m₁, hm₁ne, hmin, hlo, hhi, ?_, ?_⟩
  · intro η' hη' hmin'
    exact Cvs.WeilForm.MinimiserEulerLagrange.minimiser_unique hη hη' hmin hmin' hvsum hsep hηne
  · intro mu ζ hELmu hζne hlomu hhimu
    exact (Cvs.Finite.MinimiserSecularIsolation.eq_of_both_in_gap hc hproper hvsum (hvne 0) hm₁min
      hELmu hEL hζne hηne hlomu hhimu hlo hhi)

end Cvs.StepA.CircleEvenModesSimpleIsolated
