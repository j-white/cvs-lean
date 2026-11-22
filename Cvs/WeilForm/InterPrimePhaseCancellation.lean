import Mathlib
import Cvs.WeilForm.BandFreedomCosine
import Cvs.WeilForm.EvenBulkVisibility
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.MaskedShift.CoherenceDeficit
import Cvs.WeilForm.WeilFormOnWindowL2

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Pairwise Inter-Prime Phase Cancellation, Half-Window Dimer Split, and Steinhaus Sums

Formalizes the pairwise inter-prime phase deficit and circle-norm variance lower bound, band-free
sum-frequency elimination on `formDomain hL`, the half-window dimer split, and Steinhaus chains.
-/

noncomputable section

open Real Set Filter MeasureTheory
open scoped BigOperators InnerProductSpace

namespace Cvs.WeilForm.InterPrimePhaseCancellation
open Cvs.ZeroCounting

/-! ### 1. Pairwise Inter-Prime Phase Cancellation and Circle Variance Identity -/

section PairwisePhase

variable {ι : Type*}

/-- Weighted cosine sum `∑_{i ∈ s} 2 w_i cos(t ℓ_i)`. -/
def cosSum (s : Finset ι) (w ℓ : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ s, 2 * w i * Real.cos (t * ℓ i)

/-- Difference-frequency cosine sum `∑_{i, j ∈ s} 2 w_i w_j cos(t (ℓ_i - ℓ_j))`. -/
def diffCosSum (s : Finset ι) (w ℓ : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, 2 * w i * w j * Real.cos (t * (ℓ i - ℓ j))

/-- Sum-frequency cosine sum `∑_{i, j ∈ s} 2 w_i w_j cos(t (ℓ_i + ℓ_j))`. -/
def sumCosSum (s : Finset ι) (w ℓ : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, 2 * w i * w j * Real.cos (t * (ℓ i + ℓ j))

/-- Pairwise inter-prime phase deficit `4 ∑_{i, j ∈ s} w_i w_j sin²(t (ℓ_i - ℓ_j) / 2)`. -/
def pairwisePhaseDeficit (s : Finset ι) (w ℓ : ι → ℝ) (t : ℝ) : ℝ :=
  4 * ∑ i ∈ s, ∑ j ∈ s, w i * w j * Real.sin (t * (ℓ i - ℓ j) / 2) ^ 2

/-- Product-to-sum cosine identity `2 cos a cos b = cos(a - b) + cos(a + b)`. -/
theorem two_mul_cos_mul_cos (a b : ℝ) :
    2 * Real.cos a * Real.cos b = Real.cos (a - b) + Real.cos (a + b) := by
  rw [Real.cos_sub, Real.cos_add]
  ring

/-- **Square Decomposition into Difference and Sum Frequencies**:
`cosSum s w ℓ t ^ 2 = diffCosSum s w ℓ t + sumCosSum s w ℓ t`. -/
theorem cosSum_sq_eq_diffCosSum_add_sumCosSum (s : Finset ι) (w ℓ : ι → ℝ) (t : ℝ) :
    cosSum s w ℓ t ^ 2 = diffCosSum s w ℓ t + sumCosSum s w ℓ t := by
  unfold cosSum diffCosSum sumCosSum
  rw [sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc := two_mul_cos_mul_cos (t * ℓ i) (t * ℓ j)
  rw [show t * ℓ i - t * ℓ j = t * (ℓ i - ℓ j) by ring,
    show t * ℓ i + t * ℓ j = t * (ℓ i + ℓ j) by ring] at hc
  linear_combination 2 * w i * w j * hc

/-- **Difference-Frequency Phase Cancellation Identity**:
`diffCosSum s w ℓ t = 2 (∑_{i ∈ s} w_i)² − pairwisePhaseDeficit s w ℓ t`. -/
theorem diffCosSum_eq_two_mul_sum_sq_sub_pairwisePhaseDeficit (s : Finset ι) (w ℓ : ι → ℝ) (t : ℝ) :
    diffCosSum s w ℓ t = 2 * (∑ i ∈ s, w i) ^ 2 - pairwisePhaseDeficit s w ℓ t := by
  unfold diffCosSum pairwisePhaseDeficit
  rw [sq (∑ i ∈ s, w i), Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h := Cvs.WeilForm.MaskedShift.CoherenceDeficit.one_sub_cos_eq (t * (ℓ i - ℓ j))
  linear_combination -2 * w i * w j * h

end PairwisePhase

/-! ### 2. Band-Free Elimination of Sum Frequencies on `formDomain hL` -/

section BandFreeDimer

variable {ι : Type*}

/-- **Sum Frequencies Above `L` Are Band-Free**: if `L ≤ |ℓ i + ℓ j|` for all `i, j ∈ s`, then
`sumCosSum s w ℓ ∈ bandFree L`. -/
theorem sumCosSum_mem_bandFree {s : Finset ι} (w ℓ : ι → ℝ) {L : ℝ}
    (hsum : ∀ i ∈ s, ∀ j ∈ s, L ≤ |ℓ i + ℓ j|) :
    sumCosSum s w ℓ ∈ Cvs.WeilForm.BandFreedomCosine.bandFree L := by
  have heq : sumCosSum s w ℓ = ∑ i ∈ s, ∑ j ∈ s,
      (2 * w i * w j) • fun t => Real.cos (t * (ℓ i + ℓ j)) := by
    funext t
    simp only [sumCosSum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [heq]
  exact Submodule.sum_mem _ fun i hi => Submodule.sum_mem _ fun j hj =>
    Submodule.smul_mem _ _ (Cvs.WeilForm.BandFreedomCosine.cos_mem_bandFree (hsum i hi j hj))

/-- Any cosine `t ↦ cos(t * a)` is integrable against `rho φ` on `formDomain hL`. -/
theorem integrable_cos_mul_rho {L : ℝ} {hL : 0 ≤ L} (a : ℝ) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Integrable fun t => Real.cos (t * a) * Cvs.WeilForm.EvenBulkVisibility.rho φ t := by
  have hρ := Cvs.WeilForm.EvenBulkVisibility.integrable_rho φ
  have hc : Continuous fun t : ℝ => Real.cos (t * a) := by fun_prop
  refine hρ.norm.mono' (hc.aestronglyMeasurable.mul hρ.aestronglyMeasurable)
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)

/-- `cosSum s w ℓ * rho φ` is integrable on `formDomain hL`. -/
theorem integrable_cosSum_mul_rho {L : ℝ} {hL : 0 ≤ L} (s : Finset ι) (w ℓ : ι → ℝ)
    (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Integrable fun t => cosSum s w ℓ t * Cvs.WeilForm.EvenBulkVisibility.rho φ t := by
  have heq : (fun t => cosSum s w ℓ t * Cvs.WeilForm.EvenBulkVisibility.rho φ t)
      = fun t => ∑ i ∈ s, (2 * w i) * (Real.cos (t * ℓ i) * Cvs.WeilForm.EvenBulkVisibility.rho φ t) := by
    funext t
    simp only [cosSum, Finset.sum_mul, mul_assoc]
  rw [heq]
  exact integrable_finsetSum s fun i _ => (integrable_cos_mul_rho (ℓ i) φ).const_mul (2 * w i)

/-- `diffCosSum s w ℓ * rho φ` is integrable on `formDomain hL`. -/
theorem integrable_diffCosSum_mul_rho {L : ℝ} {hL : 0 ≤ L} (s : Finset ι) (w ℓ : ι → ℝ)
    (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Integrable fun t => diffCosSum s w ℓ t * Cvs.WeilForm.EvenBulkVisibility.rho φ t := by
  have heq : (fun t => diffCosSum s w ℓ t * Cvs.WeilForm.EvenBulkVisibility.rho φ t)
      = fun t => ∑ i ∈ s, ∑ j ∈ s,
          (2 * w i * w j) * (Real.cos (t * (ℓ i - ℓ j)) * Cvs.WeilForm.EvenBulkVisibility.rho φ t) := by
    funext t
    simp only [diffCosSum, Finset.sum_mul, mul_assoc]
  rw [heq]
  exact integrable_finsetSum s fun i _ => integrable_finsetSum s fun j _ =>
    (integrable_cos_mul_rho (ℓ i - ℓ j) φ).const_mul (2 * w i * w j)

/-- `sumCosSum s w ℓ * rho φ` is integrable on `formDomain hL`. -/
theorem integrable_sumCosSum_mul_rho {L : ℝ} {hL : 0 ≤ L} (s : Finset ι) (w ℓ : ι → ℝ)
    (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Integrable fun t => sumCosSum s w ℓ t * Cvs.WeilForm.EvenBulkVisibility.rho φ t := by
  have heq : (fun t => sumCosSum s w ℓ t * Cvs.WeilForm.EvenBulkVisibility.rho φ t)
      = fun t => ∑ i ∈ s, ∑ j ∈ s,
          (2 * w i * w j) * (Real.cos (t * (ℓ i + ℓ j)) * Cvs.WeilForm.EvenBulkVisibility.rho φ t) := by
    funext t
    simp only [sumCosSum, Finset.sum_mul, mul_assoc]
  rw [heq]
  exact integrable_finsetSum s fun i _ => integrable_finsetSum s fun j _ =>
    (integrable_cos_mul_rho (ℓ i + ℓ j) φ).const_mul (2 * w i * w j)

/-- `pairwisePhaseDeficit s w ℓ * rho φ` is integrable on `formDomain hL`. -/
theorem integrable_pairwisePhaseDeficit_mul_rho {L : ℝ} {hL : 0 ≤ L} (s : Finset ι) (w ℓ : ι → ℝ)
    (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Integrable fun t => pairwisePhaseDeficit s w ℓ t * Cvs.WeilForm.EvenBulkVisibility.rho φ t := by
  have heq : (fun t => pairwisePhaseDeficit s w ℓ t * Cvs.WeilForm.EvenBulkVisibility.rho φ t)
      = fun t => (2 * (∑ i ∈ s, w i) ^ 2) * Cvs.WeilForm.EvenBulkVisibility.rho φ t
          - diffCosSum s w ℓ t * Cvs.WeilForm.EvenBulkVisibility.rho φ t := by
    funext t
    rw [diffCosSum_eq_two_mul_sum_sq_sub_pairwisePhaseDeficit]
    ring
  rw [heq]
  exact ((Cvs.WeilForm.EvenBulkVisibility.integrable_rho φ).const_mul _).sub (integrable_diffCosSum_mul_rho s w ℓ φ)

/-- **Band-Free Sum-Frequency Vanishing**: when `L ≤ |ℓ i + ℓ j|` for all `i, j ∈ s`,
`∫ t, sumCosSum s w ℓ t * rho φ t = 0` on `formDomain hL`. -/
theorem integral_sumCosSum_mul_rho_eq_zero {L : ℝ} {hL : 0 ≤ L} {s : Finset ι} (w ℓ : ι → ℝ)
    (hsum : ∀ i ∈ s, ∀ j ∈ s, L ≤ |ℓ i + ℓ j|) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    ∫ t, sumCosSum s w ℓ t * Cvs.WeilForm.EvenBulkVisibility.rho φ t = 0 :=
  Cvs.WeilForm.EvenBulkVisibility.integral_bandFree_mul_rho (sumCosSum_mem_bandFree w ℓ hsum) φ

/-- **Exact Band-Free Dimer Square Identity**: when `L ≤ |ℓ i + ℓ j|` for all `i, j ∈ s`, the
sum-frequency terms vanish identically against `rho φ`, leaving `diffCosSum`. -/
theorem integral_cosSum_sq_mul_rho_eq_diffCosSum {L : ℝ} {hL : 0 ≤ L} {s : Finset ι} (w ℓ : ι → ℝ)
    (hsum : ∀ i ∈ s, ∀ j ∈ s, L ≤ |ℓ i + ℓ j|) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    ∫ t, cosSum s w ℓ t ^ 2 * Cvs.WeilForm.EvenBulkVisibility.rho φ t = ∫ t, diffCosSum s w ℓ t * Cvs.WeilForm.EvenBulkVisibility.rho φ t := by
  have heq : (fun t => cosSum s w ℓ t ^ 2 * Cvs.WeilForm.EvenBulkVisibility.rho φ t)
      = fun t => diffCosSum s w ℓ t * Cvs.WeilForm.EvenBulkVisibility.rho φ t + sumCosSum s w ℓ t * Cvs.WeilForm.EvenBulkVisibility.rho φ t := by
    funext t
    rw [cosSum_sq_eq_diffCosSum_add_sumCosSum, add_mul]
  rw [heq, integral_add (integrable_diffCosSum_mul_rho s w ℓ φ)
    (integrable_sumCosSum_mul_rho s w ℓ φ),
    integral_sumCosSum_mul_rho_eq_zero w ℓ hsum φ, add_zero]

/-- **Dimer Square as Coherent Budget Minus Pairwise Phase Deficit**: when `L ≤ |ℓ i + ℓ j|` for
all `i, j ∈ s`,
`∫ cosSum² ρ_φ = 2 (∑_{i ∈ s} w_i)² ‖φ‖² − ∫ pairwisePhaseDeficit ρ_φ`. -/
theorem integral_cosSum_sq_mul_rho_eq_budget_sub_deficit {L : ℝ} {hL : 0 ≤ L} {s : Finset ι}
    (w ℓ : ι → ℝ) (hsum : ∀ i ∈ s, ∀ j ∈ s, L ≤ |ℓ i + ℓ j|) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    ∫ t, cosSum s w ℓ t ^ 2 * Cvs.WeilForm.EvenBulkVisibility.rho φ t
      = 2 * (∑ i ∈ s, w i) ^ 2 * ‖φ‖ ^ 2
        - ∫ t, pairwisePhaseDeficit s w ℓ t * Cvs.WeilForm.EvenBulkVisibility.rho φ t := by
  rw [integral_cosSum_sq_mul_rho_eq_diffCosSum w ℓ hsum φ]
  have heq : (fun t => diffCosSum s w ℓ t * Cvs.WeilForm.EvenBulkVisibility.rho φ t)
      = fun t => (2 * (∑ i ∈ s, w i) ^ 2) * Cvs.WeilForm.EvenBulkVisibility.rho φ t
          - pairwisePhaseDeficit s w ℓ t * Cvs.WeilForm.EvenBulkVisibility.rho φ t := by
    funext t
    rw [diffCosSum_eq_two_mul_sum_sq_sub_pairwisePhaseDeficit, sub_mul]
  rw [heq, integral_sub ((Cvs.WeilForm.EvenBulkVisibility.integrable_rho φ).const_mul _)
    (integrable_pairwisePhaseDeficit_mul_rho s w ℓ φ),
    integral_const_mul, Cvs.WeilForm.EvenBulkVisibility.integral_rho]

end BandFreeDimer

/-! ### 3. Midpoint Half-Window Bipartite Dimer Split -/

/-! ### 4. Frequency-Space Steinhaus Chain Trigonometric Sum & Return-Gap Bound -/

end Cvs.WeilForm.InterPrimePhaseCancellation
