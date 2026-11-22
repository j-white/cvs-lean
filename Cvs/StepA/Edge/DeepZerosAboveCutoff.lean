import Mathlib
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.Visibility.VisibilityClosingStep
import Cvs.StepA.Edge.CaseInfinityJointRates
import Cvs.StepA.Edge.DeepSetZeroSums
import Cvs.StepA.Edge.FiniteTopCorrectedClosing
import Cvs.StepA.Edge.FiniteTopGap
import Cvs.StepA.Edge.GapRectangleBlaschke
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.RiemannHypothesisTarget
import Cvs.Zeta.GaussKernel.WeightedRateLemma
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroCounting.CarlsonCountBridge
import Cvs.Zeta.ZeroCounting.WeightedLocalCountsCutoff
import Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint
import Cvs.Zeta.ZeroSideMoments
import Cvs.Zeta.ZeroTailInverseSquare

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The deep zeros above a gapped cutoff, summed; and the density count from Carlson

On a gapped `H ≥ 1` with `q ≤ ½` and pair mass `P = phiNear δ_D H M + 4#D·tailBound(M) ≤ 1`, the deep zeros above
`H` have `Σ m_ρ‖P_{U_D}U_ρ‖² ≤ 16x^{Θ'}(3P/δ_D + 4K_c²x^{−δ_D/2}(528 log(2H + 5) + 4Z))`, summably (caseinf-W
Theorem C (vi)). `Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint.CarlsonBound` bounds `#deepSet δ_D T` by `CT^{1 − 2δ_D²}`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology Finset
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.StepA.Edge.FiniteTopGap (mult mult_nonneg)
open Cvs.StepA.Edge.DeepSetZeroSums (deepSet mem_deepSet)
open Cvs.StepA.Edge.GapRectangleBlaschke (phi Gap kcg qg)
open Cvs.Zeta.ZeroCounting.WeightedLocalCountsCutoff (phiNear Above)

namespace Cvs.StepA.Edge.DeepZerosAboveCutoff
open Cvs.ZeroCounting

/-- The summand of Lemma C at one deep zero above the cutoff. -/
abbrev summand {x : ℕ} (hx0 : (0 : ℝ) < x) (δD H : ℝ) (ρ : Above δD H) : ℝ :=
  mult ρ * ‖(Cvs.StepA.Edge.FiniteTopCorrectedClosing.USpan hx0 (deepSet δD H)).starProjection
    (Cvs.Route.Visibility.VisibilityClosingStep.ueVec hx0 (Cvs.ZeroCounting.zPoint (ρ : nonTrivialZeroSet)))‖ ^ 2

/-- **Theorem C at one `x`**: on a gapped `H ≥ 1` with `q ≤ ½` and pair mass `P ≤ 1`, the deep zeros above `H` are
summable against `‖P_{U_D}U_ρ‖²` with total at most `16x^{Θ'}(3P/δ_D + 4K_c²x^{−δ_D/2}(528 log(2H + 5) + 4Z))`. -/
theorem sum_above_proj_le {x : ℕ} (hx0 : (0 : ℝ) < x) {δD H M : ℝ} (hδ : 0 < δD) (hδ' : δD < 1 / 2)
    (hH : 1 ≤ H) (hg : Gap δD H) (hq : qg x δD H ≤ 1 / 2) (hM : 2 * H ≤ M) (hM' : 9 + Real.exp 1 ≤ 2 * M)
    (hP : phiNear δD H M + 4 * (deepSet δD H).card * Cvs.Zeta.ZeroTailInverseSquare.tailBound M ≤ 1) :
    Summable (summand hx0 δD H)
      ∧ ∑' ρ, summand hx0 δD H ρ
        ≤ 16 * (x : ℝ) ^ Cvs.StepA.Edge.CaseInfinityJointRates.topDepth * (3 * (phiNear δD H M + 4 * (deepSet δD H).card * Cvs.Zeta.ZeroTailInverseSquare.tailBound M) / δD
          + 4 * kcg δD H ^ 2 * (x : ℝ) ^ (-(δD / 2)) * (528 * Real.log (2 * H + 5) + 4 * Cvs.StepA.Edge.DeepSetZeroSums.invSqSum)) := by
  set P := phiNear δD H M + 4 * (deepSet δD H).card * Cvs.Zeta.ZeroTailInverseSquare.tailBound M
  set C := 16 * (x : ℝ) ^ Cvs.StepA.Edge.CaseInfinityJointRates.topDepth
  set E := 4 * kcg δD H ^ 2 * (x : ℝ) ^ (-(δD / 2))
  have hC0 : 0 ≤ C := by positivity
  have hE0 : 0 ≤ E := by positivity
  have hφ1 : ∀ ρ : Above δD H, phi δD H ρ ≤ 1 := by
    intro ρ
    have h := Cvs.Zeta.ZeroCounting.WeightedLocalCountsCutoff.sum_phi_above_le hH hM hM' {ρ}
    rw [Finset.sum_singleton] at h
    have hm : (1 : ℝ) ≤ mult ρ := by exact_mod_cast Cvs.Criterion.one_le_divisorWeight ρ
    have h0 := Cvs.Zeta.ZeroCounting.WeightedLocalCountsCutoff.phi_nonneg δD H ρ
    nlinarith
  have hpt : ∀ ρ : Above δD H, summand hx0 δD H ρ
      ≤ C * (3 / δD * (mult ρ * phi δD H ρ))
        + C * E * (mult ρ * (1 / (|((ρ : nonTrivialZeroSet) : ℂ).im| - H) ^ 2)) := by
    intro ρ
    have h := Cvs.StepA.Edge.GapRectangleBlaschke.norm_sq_proj_le_gap hx0 hδ hδ' hH hg hq ρ.2.1 ρ.2.2 (hφ1 ρ)
    have hm := mult_nonneg (ρ : nonTrivialZeroSet)
    have := mul_le_mul_of_nonneg_left h hm
    calc summand hx0 δD H ρ ≤ mult ρ * (16 * (x : ℝ) ^ Cvs.StepA.Edge.CaseInfinityJointRates.topDepth * (3 * phi δD H ρ / δD
        + 4 * kcg δD H ^ 2 * (x : ℝ) ^ (-(δD / 2)) / (|((ρ : nonTrivialZeroSet) : ℂ).im| - H) ^ 2)) := this
      _ = _ := by simp only [C, E]; ring
  have hsum : ∀ u : Finset (Above δD H), ∑ ρ ∈ u, summand hx0 δD H ρ
      ≤ C * (3 * P / δD + E * (528 * Real.log (2 * H + 5) + 4 * Cvs.StepA.Edge.DeepSetZeroSums.invSqSum)) := by
    intro u
    refine (Finset.sum_le_sum fun ρ _ => hpt ρ).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    have h1 := Cvs.Zeta.ZeroCounting.WeightedLocalCountsCutoff.sum_phi_above_le hH hM hM' u
    have h2 := Cvs.Zeta.ZeroCounting.WeightedLocalCountsCutoff.sum_above_le hH hg u
    have e1 : C * (3 / δD * ∑ ρ ∈ u, mult ρ * phi δD H ρ) ≤ C * (3 / δD * P) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (by positivity)) hC0
    have e2 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hC0 hE0)
    have : C * (3 * P / δD + E * (528 * Real.log (2 * H + 5) + 4 * Cvs.StepA.Edge.DeepSetZeroSums.invSqSum))
        = C * (3 / δD * P) + C * E * (528 * Real.log (2 * H + 5) + 4 * Cvs.StepA.Edge.DeepSetZeroSums.invSqSum) := by ring
    rw [this]
    linarith
  have h0 : 0 ≤ summand hx0 δD H := fun ρ => mul_nonneg (mult_nonneg _) (sq_nonneg _)
  exact ⟨summable_of_sum_le h0 hsum, Real.tsum_le_of_sum_le h0 hsum⟩

/-! ### The density count -/

theorem deepSet_eq_offLineWindow (δD T : ℝ) :
    deepSet δD T = (Cvs.Zeta.GaussKernel.AdmissibleKernel.offLineWindow_finite δD T).toFinset := by
  ext ρ
  rw [mem_deepSet, Set.Finite.mem_toFinset]
  rfl

/-- **The deep count from Carlson's density theorem**: `#deepSet δ_D T ≤ CT^{1 − 2δ_D²}` for all large `T`. -/
theorem deepSet_card_le_of_carlson (hC : Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint.CarlsonBound) {δD : ℝ} (hδ : 0 < δD)
    (hδ' : δD < 1 / 2) : ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ T : ℝ, T₀ ≤ T →
      ((deepSet δD T).card : ℝ) ≤ C * T ^ (1 - 2 * δD ^ 2) := by
  have h := hC (1 / 2 + δD) (2 * δD ^ 2) (by linarith) (by linarith) (by positivity)
  have he : 4 * (1 / 2 + δD) * (1 - (1 / 2 + δD)) + 2 * δD ^ 2 = 1 - 2 * δD ^ 2 := by ring
  rw [he] at h
  obtain ⟨c, hc⟩ := h.bound
  obtain ⟨T₁, hT₁⟩ := Filter.eventually_atTop.1 hc
  refine ⟨4 * max c 0, max T₁ 1, by positivity, fun T hT => ?_⟩
  have hT1 : T₁ ≤ T := (le_max_left _ _).trans hT
  have hT0 : 0 ≤ T := by linarith [le_max_right T₁ 1]
  have h1 := hT₁ T hT1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (Real.rpow_nonneg hT0 _)] at h1
  have h2 : ((deepSet δD T).card : ℝ) ≤ 4 * (Cvs.GaussKernel.carlsonCount (1 / 2 + δD) T : ℝ) := by
    rw [deepSet_eq_offLineWindow]
    exact_mod_cast Cvs.GaussKernel.offLineCount_le_four_mul_carlsonCount hδ T
  have h3 : (Cvs.GaussKernel.carlsonCount (1 / 2 + δD) T : ℝ) ≤ Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint.N_zero (1 / 2 + δD) T := by
    exact_mod_cast Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint.carlsonCount_le_N_zero (by linarith) hT0
  have h4 : c * T ^ (1 - 2 * δD ^ 2) ≤ max c 0 * T ^ (1 - 2 * δD ^ 2) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hT0 _)
  linarith

end Cvs.StepA.Edge.DeepZerosAboveCutoff

end
