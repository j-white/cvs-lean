import Mathlib
import Cvs.Route.DyadicWorstScale
import Cvs.Route.EvenBulkFloorAlongScales
import Cvs.Route.EvenFloorDownwardClosure
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.PowerLawVisibilityBulkFloor
import Cvs.Route.ScaleSelectionSets
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.MaskedShift.PrimeSideAtomBudget
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowFormDependsOnLog

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The terminal floor along selected scales

`HFAlong S` is the even bulk floor at loss `x^ε`, for every `ε > 0`, at every large `x ∈ S`. Along the phase set
of `Cvs.Route.ScaleSelectionSets`, the dyadic above-mean set and every other infinite `S`, `HFAlong S ↔ RiemannHypothesis`. At each
selected scale the phase factors are at most `(πδ)²`, the form is the one at `L = log x` for every complete
truncation, and the atom budget is at most its dyadic mean, which bounds the floor below.
-/

noncomputable section

open Real Filter Set

namespace Cvs.Route.TerminalFloorAlongScales
open Cvs.ZeroCounting

open Cvs.Route.EvenBulkFloorAlongScales (FloorAlong)
open Cvs.Route.ScaleSelectionSets (phaseSet aboveMeanSet dyadic)

/-- The terminal floor along `S`: the even bulk floor at loss `x^ε` at every large `x ∈ S`, every `ε > 0`. -/
def HFAlong (S : Set ℕ) : Prop := ∀ ε : ℝ, 0 < ε → FloorAlong S fun x => (x : ℝ) ^ ε

/-- **`HFAlong S ↔ RiemannHypothesis` for every infinite `S`.** -/
theorem rh_iff_hFAlong {S : Set ℕ} (hS : S.Infinite) : RiemannHypothesis ↔ HFAlong S :=
  Cvs.Route.EvenBulkFloorAlongScales.rh_iff_rpow_floorAlong hS

/-- **`HFAlong` does not depend on the infinite set**: `HFAlong S ↔ HFAlong S'`. -/
theorem hFAlong_iff {S S' : Set ℕ} (hS : S.Infinite) (hS' : S'.Infinite) : HFAlong S ↔ HFAlong S' :=
  (rh_iff_hFAlong hS).symm.trans (rh_iff_hFAlong hS')

/-- `HFAlong` along every infinite `S` is `HFAlong` along all scales. -/
theorem hFAlong_iff_univ {S : Set ℕ} (hS : S.Infinite) : HFAlong S ↔ HFAlong univ :=
  hFAlong_iff hS Set.infinite_univ

/-- **Along the phase set**: `RiemannHypothesis ↔ HFAlong (phaseSet γ δ)`. -/
theorem rh_iff_hFAlong_phaseSet {ι : Type*} [Fintype ι] (γ : ι → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    RiemannHypothesis ↔ HFAlong (phaseSet γ δ) :=
  rh_iff_hFAlong (Cvs.Route.ScaleSelectionSets.phaseSet_infinite γ hδ)

/-- **Along the dyadic above-mean set of any `Φ`**: `RiemannHypothesis ↔ HFAlong (aboveMeanSet dyadic Φ)`. -/
theorem rh_iff_hFAlong_aboveMean (Φ : ℕ → ℝ) : RiemannHypothesis ↔ HFAlong (aboveMeanSet dyadic Φ) :=
  rh_iff_hFAlong (Cvs.Route.ScaleSelectionSets.aboveMeanSet_dyadic_infinite Φ)

/-- The atom budget at the top truncation of scale `x`. -/
abbrev budget (x : ℕ) : ℝ := Cvs.PrimeOperator.atomBudget x x (Nat.clog 2 x)

/-- **Budget selection**: at `x > 1` in the dyadic above-mean set of `−budget`, the floor holds at
`archSymbol 0` minus the mean of the budget over a dyadic window containing `x`. -/
theorem evenBulkFloor_sub_mean_budget {x : ℕ} (hx : 1 < x)
    (hS : x ∈ aboveMeanSet dyadic fun y => -budget y) :
    ∃ k, x ∈ dyadic k ∧
      Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 - (∑ y ∈ dyadic k, budget y) / (dyadic k).card) := by
  obtain ⟨k, hxk, hmean⟩ := Cvs.Route.ScaleSelectionSets.mean_le_of_mem_aboveMeanSet Cvs.Route.ScaleSelectionSets.dyadic_nonempty hS
  refine ⟨k, hxk, Cvs.Route.PowerLawVisibilityBulkFloor.evenBulkFloor_mono ?_ (Cvs.Route.PowerLawVisibilityBulkFloor.evenBulkFloor_archSymbol_sub_atomBudget hx)⟩
  rw [Finset.sum_neg_distrib, neg_div] at hmean
  linarith

/-- **The phase-set selection**: `RiemannHypothesis ↔ HFAlong S` for `S = phaseSet γ δ`, `HFAlong S ↔
HFAlong univ`, the weighted phase sum is at most `(πδ)² ∑ cᵢ` on `S`, and `Q_x` is the form of every complete
truncation at `L = log x`. -/
theorem phaseSet_selection {ι : Type*} [Fintype ι] (γ c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) {δ : ℝ}
    (hδ : 0 < δ) :
    (RiemannHypothesis ↔ HFAlong (phaseSet γ δ)) ∧ (HFAlong (phaseSet γ δ) ↔ HFAlong univ) ∧
      (∀ x ∈ phaseSet γ δ,
        ∑ i, c i * Real.sin (γ i * Real.log x / 2) ^ 2 ≤ (π * δ) ^ 2 * ∑ i, c i) ∧
      (∀ x : ℕ, 1 ≤ x → ∀ P R : ℕ, Real.exp (Real.log x) ≤ P → Real.log x ≤ R * Real.log 2 →
        ∀ φ : Cvs.Route.L1FloorFromBulkD0.Dom x, Cvs.Route.WindowPositivityBulkCoupling.Qx x φ = Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) P R φ) :=
  ⟨rh_iff_hFAlong_phaseSet γ hδ, hFAlong_iff_univ (Cvs.Route.ScaleSelectionSets.phaseSet_infinite γ hδ),
    fun _ hx => Cvs.Route.ScaleSelectionSets.sum_mul_sin_sq_le_of_mem_phaseSet hc hx,
    fun _ hx _ _ hP hR φ => Cvs.WeilForm.WindowFormDependsOnLog.Qx_eq_Q_of_complete hx hP hR φ⟩

/-- **The worst-scale selection**: `RiemannHypothesis ↔` the worst-scale floor at loss
`(2^k)^ε` for every `ε > 0`, which at each `k` is the floor on all of `[2^k, 2^{k+1})`, and the reflection-even
floor at a fixed `μ` is the same at every scale `x ≥ 1`. -/
theorem worst_selection :
    (RiemannHypothesis ↔
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor (Cvs.Route.DyadicWorstScale.worst k) (-((2 : ℝ) ^ k) ^ ε)) ∧
      (∀ k b, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor (Cvs.Route.DyadicWorstScale.worst k) b ↔ ∀ y ∈ dyadic k, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor y b) ∧
      (∀ μ : ℝ, (∃ᶠ X : ℕ in atTop, Cvs.Route.EvenFloorDownwardClosure.EvenFloor X μ) ↔ ∀ x : ℕ, 1 ≤ x → Cvs.Route.EvenFloorDownwardClosure.EvenFloor x μ) :=
  ⟨Cvs.Route.DyadicWorstScale.rh_iff_worst, Cvs.Route.DyadicWorstScale.evenBulkFloor_worst_iff, Cvs.Route.EvenFloorDownwardClosure.frequently_evenFloor_iff⟩

end Cvs.Route.TerminalFloorAlongScales
