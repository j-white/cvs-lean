import Mathlib
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.WeilForm.EvenBulkVisibility
import Cvs.WeilForm.ReflectionEvenPositivityRH
import Cvs.WeilForm.WeilFormOnWindowL2

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Routing of `EvenBulkVisibility`'s visibility hypothesis

`EvenBulkVisibility`'s per-`x` visibility clause (`Visible x`) is equivalent to `¬ EvenBulkFloor x 0`, that is to a
reflection-even class `w ⊥ R₁` with `Qx x w < 0`: take `M := Qx x + 4⟪·, w⟫²`, `b := w`.
Hence the hypothesis `hV` of `Cvs.WeilForm.EvenBulkVisibility.rh_of_eventually_evenBulkFloor_of_visible` is
`¬ RH → ∀ᶠ x, ¬ EvenBulkFloor x 0`.
-/

noncomputable section

open Filter
open scoped InnerProductSpace
open Cvs.Route.L1FloorFromBulkD0 (Dom)
open Cvs.Route.WindowPositivityBulkCoupling (Qx)
open Cvs.L2a.EvenSectorReflectionBound (R1)
open Cvs.WeilForm.ReflectionEvenPositivityRH (Ev)
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)

namespace Cvs.Route.Visibility.VisibleIffNotEvenBulkFloor
open Cvs.ZeroCounting

/-- `EvenBulkVisibility`'s visibility clause at `x`. -/
def Visible (x : ℕ) : Prop :=
  ∃ (M : Dom x → ℝ) (b : Dom x), b ∈ Ev x ∧ (∀ u ∈ Ev x, Qx x u ≤ M u - 4 * ⟪u, b⟫_ℝ ^ 2) ∧
    M (b - (R1 x).starProjection b) < 4 * ‖b - (R1 x).starProjection b‖ ^ 4

/-- A reflection-even class `L²`-orthogonal to `R₁` with negative form is visible, with
`M := Qx x + 4⟪·, w⟫²` and `b := w`. -/
theorem visible_of_neg {x : ℕ} {w : Dom x} (hwE : w ∈ Ev x) (hwR : w ∈ (R1 x)ᗮ)
    (hneg : Qx x w < 0) :
    ∃ (M : Dom x → ℝ) (b : Dom x), b ∈ Ev x ∧ (∀ u ∈ Ev x, Qx x u ≤ M u - 4 * ⟪u, b⟫_ℝ ^ 2) ∧
      M (b - (R1 x).starProjection b) < 4 * ‖b - (R1 x).starProjection b‖ ^ 4 := by
  refine ⟨fun u => Qx x u + 4 * ⟪u, w⟫_ℝ ^ 2, w, hwE, fun u _ => le_of_eq (by ring), ?_⟩
  have hP : (R1 x).starProjection w = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff (K := R1 x)).2 hwR
  rw [hP, sub_zero]
  show Qx x w + 4 * ⟪w, w⟫_ℝ ^ 2 < 4 * ‖w‖ ^ 4
  rw [real_inner_self_eq_norm_sq]
  nlinarith [hneg]

/-- `¬ EvenBulkFloor x 0` is a reflection-even class `L²`-orthogonal to `R₁` with negative form. -/
theorem not_evenBulkFloor_zero_iff (x : ℕ) :
    ¬ Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0 ↔ ∃ w ∈ Ev x, w ∈ (R1 x)ᗮ ∧ Qx x w < 0 := by
  unfold Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor
  simp only [zero_mul, not_forall, not_le, exists_prop]

/-- `EvenBulkVisibility`'s visibility clause at `x` is `¬ EvenBulkFloor x 0`. -/
theorem visible_iff_not_evenBulkFloor (x : ℕ) : Visible x ↔ ¬ Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0 := by
  constructor
  · rintro ⟨M, b, hbE, hq, hM⟩
    exact Cvs.WeilForm.EvenBulkVisibility.not_evenBulkFloor_of_visible hbE hq hM
  · intro h
    obtain ⟨w, hwE, hwR, hneg⟩ := (not_evenBulkFloor_zero_iff x).1 h
    exact visible_of_neg hwE hwR hneg

/-- The hypothesis `hV` of `Cvs.WeilForm.EvenBulkVisibility.rh_of_eventually_evenBulkFloor_of_visible` is
`¬ RH → ∀ᶠ x, ¬ EvenBulkFloor x 0`. -/
theorem hV_iff :
    (¬ RiemannHypothesis → ∀ᶠ x : ℕ in atTop, ∃ (M : Dom x → ℝ) (b : Dom x), b ∈ Ev x ∧
      (∀ u ∈ Ev x, Qx x u ≤ M u - 4 * ⟪u, b⟫_ℝ ^ 2) ∧
      M (b - (R1 x).starProjection b) < 4 * ‖b - (R1 x).starProjection b‖ ^ 4) ↔
    (¬ RiemannHypothesis → ∀ᶠ x : ℕ in atTop, ¬ Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0) := by
  constructor
  · intro h hRH
    exact (h hRH).mono fun x hx => (visible_iff_not_evenBulkFloor x).1 hx
  · intro h hRH
    exact (h hRH).mono fun x hx => (visible_iff_not_evenBulkFloor x).2 hx

/-- `RiemannHypothesis` from `EvenBulkFloor x 0` eventually and, off RH, its failure frequently. -/
theorem rh_of_eventually_evenBulkFloor_of_frequently_visible
    (hV : ¬ RiemannHypothesis → ∃ᶠ x : ℕ in atTop, ¬ Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0)
    (hF : ∀ᶠ x : ℕ in atTop, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0) : RiemannHypothesis := by
  by_contra hRH
  obtain ⟨x, hnF, hFx⟩ := ((hV hRH).and_eventually hF).exists
  exact hnF hFx

end Cvs.Route.Visibility.VisibleIffNotEvenBulkFloor

end
