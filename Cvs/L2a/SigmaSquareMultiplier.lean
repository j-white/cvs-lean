import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FarFarBound
import Cvs.L2a.FarIntegrationByParts
import Cvs.L2a.QIdentityComplexWeight
import Cvs.L2a.QIdentityCutPoint
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RungExactOrthogonality

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The `σ²`-multiplier: Lemmas PS, H and LP

Expanding `Q_χ^{−(k+1)}` about `χ₀` writes the span bulk `Σ aᵢ∫ eψᵢRᵢ` as a series in `Φ_j = Σ aᵢ(χ₀ − χᵢ)^jψᵢ`, and
`‖Φ_j‖² ≤ D^{2j}P` by orthogonality. Taking the `ℓ²` sum over disjoint windows for each `j` before the `j`-series bounds a
window family by `(N₁/(1 − ρ) + N₂/(1 − ρ)² + N₃/(1 − ρ)³)√P`. Where `Re Q < 0` the Laplace transform in `σ²` factors the
`χ`-dependence through `Σ aᵢe^{−sσᵢ²}ψᵢ`.
-/

namespace Cvs.L2a.SigmaSquareMultiplier

open Real Set Filter Topology MeasureTheory Complex
open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.AngularProlateTailPositive Cvs.L2a.FarIntegrationByParts Cvs.L2a.QIdentityComplexWeight

/-! ### Lemma PS: the expansion about `χ₀` -/

/-- **Lemma PS**: `1/(Q₀ + s)^{k+1} = Σ_j C(j + k, k)(−s)^j/Q₀^{j+k+1}` for `‖s‖ < ‖Q₀‖`. -/
theorem hasSum_inv_pow_shift (k : ℕ) {Q₀ s : ℂ} (hs : ‖s‖ < ‖Q₀‖) :
    HasSum (fun j : ℕ => ((j + k).choose k : ℂ) * (-s) ^ j / Q₀ ^ (j + k + 1)) (1 / (Q₀ + s) ^ (k + 1)) := by
  have hQ : 0 < ‖Q₀‖ := (norm_nonneg s).trans_lt hs
  have hQ0 : Q₀ ≠ 0 := norm_pos_iff.mp hQ
  have hr : ‖-s / Q₀‖ < 1 := by rw [norm_div, norm_neg, div_lt_one hQ]; exact hs
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one k hr).mul_left (1 / Q₀ ^ (k + 1))
  have hsum : Q₀ * (1 - -s / Q₀) = Q₀ + s := by field_simp; ring
  have e1 : (fun j : ℕ => ((j + k).choose k : ℂ) * (-s) ^ j / Q₀ ^ (j + k + 1))
      = fun j : ℕ => 1 / Q₀ ^ (k + 1) * (((j + k).choose k : ℂ) * (-s / Q₀) ^ j) := by
    funext j; rw [div_pow, pow_add, pow_add]; field_simp; ring
  have e2 : 1 / (Q₀ + s) ^ (k + 1) = 1 / Q₀ ^ (k + 1) * (1 / (1 - -s / Q₀) ^ (k + 1)) := by
    rw [← hsum, mul_pow]; field_simp
  rw [e1, e2]; exact h

/-- The `j`-th coefficient of `R` in powers of `χ₀ − χ`. -/
noncomputable def rKc (w w₁ w₂ : ℝ → ℂ) (c χ₀ y : ℝ) (j : ℕ) (x : ℝ) : ℂ :=
  aC₁ w₁ w₂ c y x / qQ c χ₀ y x ^ (j + 1) + ((j + 1).choose 1 : ℂ) * aC₂ w w₁ c y x / qQ c χ₀ y x ^ (j + 2)
    + ((j + 2).choose 2 : ℂ) * aC₃ w c y x / qQ c χ₀ y x ^ (j + 3)

/-- **`R` about `χ₀`**: `R_χ = Σ_j (χ₀ − χ)^j R⁽ʲ⁾_{χ₀}` for `|χ − χ₀| < |Q_{χ₀}|`. -/
theorem hasSum_rRc_shift {w w₁ w₂ : ℝ → ℂ} {c χ χ₀ y x : ℝ} (hs : |χ - χ₀| < ‖qQ c χ₀ y x‖) :
    HasSum (fun j : ℕ => ((χ₀ - χ : ℝ) : ℂ) ^ j * rKc w w₁ w₂ c χ₀ y j x) (rRc w w₁ w₂ c χ y x) := by
  set Q₀ := qQ c χ₀ y x with hQ₀
  set s : ℂ := ((χ - χ₀ : ℝ) : ℂ) with hs_def
  have hsn : ‖s‖ < ‖Q₀‖ := by rw [hs_def, Complex.norm_real, Real.norm_eq_abs]; exact hs
  have hQ : qQ c χ y x = Q₀ + s := Cvs.L2a.QIdentityCutPoint.qQ_add_chi c χ χ₀ y x
  have hQne : qQ c χ y x ≠ 0 := by
    rw [hQ]; intro h
    have : ‖Q₀‖ = ‖s‖ := by rw [eq_neg_of_add_eq_zero_left h, norm_neg]
    linarith
  have h0 := (hasSum_inv_pow_shift 0 hsn).mul_left (aC₁ w₁ w₂ c y x)
  have h1 := (hasSum_inv_pow_shift 1 hsn).mul_left (aC₂ w w₁ c y x)
  have h2 := (hasSum_inv_pow_shift 2 hsn).mul_left (aC₃ w c y x)
  have hneg : -s = ((χ₀ - χ : ℝ) : ℂ) := by rw [hs_def]; push_cast; ring
  have e1 : (fun j : ℕ => ((χ₀ - χ : ℝ) : ℂ) ^ j * rKc w w₁ w₂ c χ₀ y j x)
      = fun j : ℕ => aC₁ w₁ w₂ c y x * (((j + 0).choose 0 : ℂ) * (-s) ^ j / Q₀ ^ (j + 0 + 1))
        + aC₂ w w₁ c y x * (((j + 1).choose 1 : ℂ) * (-s) ^ j / Q₀ ^ (j + 1 + 1))
        + aC₃ w c y x * (((j + 2).choose 2 : ℂ) * (-s) ^ j / Q₀ ^ (j + 2 + 1)) := by
    funext j
    rw [hneg]
    simp only [rKc, ← hQ₀, Nat.add_zero, Nat.choose_zero_right, Nat.cast_one]
    ring
  have e2 : rRc w w₁ w₂ c χ y x = aC₁ w₁ w₂ c y x * (1 / (Q₀ + s) ^ (0 + 1))
      + aC₂ w w₁ c y x * (1 / (Q₀ + s) ^ (1 + 1)) + aC₃ w c y x * (1 / (Q₀ + s) ^ (2 + 1)) := by
    rw [rRc_eq hQne, hQ]; ring
  rw [e1, e2]; exact (h0.add h1).add h2

/-- The atom profiles `|A₁|/|Q₀|`, `|A₂|/|Q₀|²`, `|A₃|/|Q₀|³`. -/
noncomputable def pr₁ (w₁ w₂ : ℝ → ℂ) (c χ₀ y x : ℝ) : ℝ := ‖aC₁ w₁ w₂ c y x‖ / ‖qQ c χ₀ y x‖

/-- The second atom profile `|A₂|/|Q₀|²`. -/
noncomputable def pr₂ (w w₁ : ℝ → ℂ) (c χ₀ y x : ℝ) : ℝ := ‖aC₂ w w₁ c y x‖ / ‖qQ c χ₀ y x‖ ^ 2

/-- The third atom profile `|A₃|/|Q₀|³`. -/
noncomputable def pr₃ (w : ℝ → ℂ) (c χ₀ y x : ℝ) : ℝ := ‖aC₃ w c y x‖ / ‖qQ c χ₀ y x‖ ^ 3

/-- `D^j|R⁽ʲ⁾| ≤ ρ^j(pr₁ + (j + 1)pr₂ + C(j + 2, 2)pr₃)` where `D ≤ ρ|Q₀|`. -/
theorem pow_mul_norm_rKc_le {w w₁ w₂ : ℝ → ℂ} {c χ₀ y x D ρ : ℝ} (hD : 0 ≤ D) (hρ : 0 ≤ ρ)
    (hQ : D ≤ ρ * ‖qQ c χ₀ y x‖) (hQ0 : qQ c χ₀ y x ≠ 0) (j : ℕ) :
    D ^ j * ‖rKc w w₁ w₂ c χ₀ y j x‖
      ≤ ρ ^ j * (pr₁ w₁ w₂ c χ₀ y x + (j + 1) * pr₂ w w₁ c χ₀ y x + ((j + 2).choose 2 : ℝ) * pr₃ w c χ₀ y x) := by
  set q := ‖qQ c χ₀ y x‖ with hq
  have hq0 : 0 < q := norm_pos_iff.mpr hQ0
  set S := pr₁ w₁ w₂ c χ₀ y x + (j + 1) * pr₂ w w₁ c χ₀ y x + ((j + 2).choose 2 : ℝ) * pr₃ w c χ₀ y x with hS
  have hR : ‖rKc w w₁ w₂ c χ₀ y j x‖ ≤ S / q ^ j := by
    unfold rKc
    refine (norm_add₃_le).trans (le_of_eq ?_)
    simp only [norm_div, norm_mul, norm_pow, Complex.norm_natCast, hS, pr₁, pr₂, pr₃, ← hq,
      Nat.choose_one_right]
    push_cast
    field_simp
    ring
  have hS0 : 0 ≤ S := by rw [hS]; unfold pr₁ pr₂ pr₃; positivity
  have hDj : D ^ j ≤ ρ ^ j * q ^ j := by rw [← mul_pow]; exact pow_le_pow_left₀ hD hQ j
  calc D ^ j * ‖rKc w w₁ w₂ c χ₀ y j x‖ ≤ ρ ^ j * q ^ j * (S / q ^ j) :=
        mul_le_mul hDj hR (norm_nonneg _) (by positivity)
    _ = ρ ^ j * S := by field_simp

/-! ### Orthogonality of the monomials -/

/-- `Φ_j = Σ aᵢ(χ₀ − χᵢ)^j ψᵢ`. -/
noncomputable def phiMono {ι : Type*} [Fintype ι] (c χ₀ : ℝ) (χ : ι → ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (j : ℕ)
    (x : ℝ) : ℝ := ∑ i, a i * (χ₀ - χ i) ^ j * psi c (g i) x

/-- **Orthogonality of the monomials**: `‖Φ_j‖² ≤ D^{2j}P` for `|χ₀ − χᵢ| ≤ D`. -/
theorem monomial_sum_le {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ}
    (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ) {χ₀ D : ℝ} (hD : ∀ i, |χ₀ - χ i| ≤ D) (j : ℕ) :
    ∫ x in Ioi 1, phiMono c χ₀ χ g a j x ^ 2 ≤ D ^ (2 * j) * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := by
  have e := Cvs.Prolate.RungExactOrthogonality.integral_span_sq (fun i => a i * (χ₀ - χ i) ^ j) hg hg₁ hg₂c hang hc hχ
  simp only [phiMono]
  rw [e, Cvs.Prolate.RungExactOrthogonality.integral_span_sq a hg hg₁ hg₂c hang hc hχ, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hsq : (χ₀ - χ i) ^ 2 ≤ D ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hD i) 2
  have hp : ((χ₀ - χ i) ^ 2) ^ j ≤ (D ^ 2) ^ j := pow_le_pow_left₀ (sq_nonneg _) hsq j
  have hI : 0 ≤ ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  calc (a i * (χ₀ - χ i) ^ j) ^ 2 * ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2
      = a i ^ 2 * ((χ₀ - χ i) ^ 2) ^ j * ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2 := by
        rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm j 2]
    _ ≤ a i ^ 2 * (D ^ 2) ^ j * ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2 := by gcongr
    _ = D ^ (2 * j) * (a i ^ 2 * ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2) := by rw [pow_mul]; ring

/-! ### Lemma H: the window `ℓ²` sum -/

/-- **Lemma H, the window sum**: `Σ_m ∫_{W_m} f² ≤ ∫_{(1,∞)} f²` for pairwise disjoint windows in `(1, ∞)`. -/
theorem window_sum_le {s : Finset ℕ} {W : ℕ → Set ℝ} (hW : ∀ m ∈ s, MeasurableSet (W m))
    (hW1 : ∀ m ∈ s, W m ⊆ Ioi 1) (hd : (s : Set ℕ).PairwiseDisjoint W) {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioi 1))) :
    ∑ m ∈ s, ∫ x in W m, f x ^ 2 ≤ ∫ x in Ioi 1, f x ^ 2 := by
  have hfi : IntegrableOn (fun x => f x ^ 2) (Ioi 1) :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mp hf
  have hU : (⋃ m ∈ s, W m) ⊆ Ioi 1 := Set.iUnion₂_subset hW1
  rw [← integral_biUnion_finset s hW hd fun m hm => hfi.mono_set (hW1 m hm)]
  exact setIntegral_mono_set hfi (Eventually.of_forall fun x => sq_nonneg _) (Eventually.of_forall hU)

/-- Lemma H for a nonnegative real kernel: `Σ_m ∫_{W_m} f_m|u| ≤ (Σ_m ‖f_m‖²_{W_m})^{1/2}‖u‖_{L²(1,∞)}`. -/
theorem sum_setIntegral_mul_abs_le {s : Finset ℕ} {W : ℕ → Set ℝ} (hW : ∀ m ∈ s, MeasurableSet (W m))
    (hW1 : ∀ m ∈ s, W m ⊆ Ioi 1) (hd : (s : Set ℕ).PairwiseDisjoint W) {f : ℕ → ℝ → ℝ}
    (hf0 : ∀ m ∈ s, ∀ x, 0 ≤ f m x) (hf : ∀ m ∈ s, MemLp (f m) 2 (volume.restrict (W m))) {u : ℝ → ℝ}
    (hu : MemLp u 2 (volume.restrict (Ioi 1))) :
    ∑ m ∈ s, ∫ x in W m, f m x * |u x|
      ≤ √(∑ m ∈ s, ∫ x in W m, f m x ^ 2) * √(∫ x in Ioi 1, u x ^ 2) := by
  have h1 : ∑ m ∈ s, ∫ x in W m, f m x * |u x|
      ≤ ∑ m ∈ s, √(∫ x in W m, f m x ^ 2) * √(∫ x in W m, u x ^ 2) :=
    Finset.sum_le_sum fun m hm => Cvs.L2a.FarFarBound.integral_mul_abs_le (hf0 m hm) (hf m hm)
      (hu.mono_measure (Measure.restrict_mono (hW1 m hm) le_rfl))
  have h2 := Real.sum_sqrt_mul_sqrt_le s (f := fun m => ∫ x in W m, f m x ^ 2)
    (g := fun m => ∫ x in W m, u x ^ 2) (fun m => integral_nonneg fun _ => sq_nonneg _)
    (fun m => integral_nonneg fun _ => sq_nonneg _)
  have h3 := Real.sqrt_le_sqrt (window_sum_le hW hW1 hd hu)
  refine h1.trans (h2.trans (mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)))

/-! ### The local mass -/

/-! ### PS with H: the span bulk on a window family -/

/-- The three geometric series `Σρ^j = 1/(1 − ρ)`, `Σ(j + 1)ρ^j = 1/(1 − ρ)²`, `ΣC(j + 2, 2)ρ^j = 1/(1 − ρ)³`. -/
theorem hasSum_geom_three {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    HasSum (fun j : ℕ => ρ ^ j) (1 / (1 - ρ)) ∧ HasSum (fun j : ℕ => ((j : ℝ) + 1) * ρ ^ j) (1 / (1 - ρ) ^ 2)
      ∧ HasSum (fun j : ℕ => ((j + 2).choose 2 : ℝ) * ρ ^ j) (1 / (1 - ρ) ^ 3) := by
  have h1 : ‖ρ‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hρ0]; exact hρ1
  refine ⟨by simpa using hasSum_choose_mul_geometric_of_norm_lt_one 0 h1, ?_,
    hasSum_choose_mul_geometric_of_norm_lt_one 2 h1⟩
  have h := hasSum_choose_mul_geometric_of_norm_lt_one 1 h1
  have e : (fun n : ℕ => (((n + 1).choose 1 : ℕ) : ℝ) * ρ ^ n) = fun n : ℕ => ((n : ℝ) + 1) * ρ ^ n := by
    funext n; rw [Nat.choose_one_right]; push_cast; ring
  rw [e] at h; exact h

/-- `R⁽ʲ⁾` is a.e.-measurable for a.e.-measurable weights. -/
theorem aemeasurable_rKc {w w₁ w₂ : ℝ → ℂ} {μ : Measure ℝ} (hw : AEMeasurable w μ) (hw₁ : AEMeasurable w₁ μ)
    (hw₂ : AEMeasurable w₂ μ) (c χ₀ y : ℝ) (j : ℕ) : AEMeasurable (rKc w w₁ w₂ c χ₀ y j) μ := by
  have hq : AEMeasurable (fun x => qQ c χ₀ y x) μ :=
    (by unfold qQ; fun_prop : Continuous fun x => qQ c χ₀ y x).measurable.aemeasurable
  have hq₁ : AEMeasurable (fun x => qQ₁ c y x) μ :=
    (by unfold qQ₁; fun_prop : Continuous fun x => qQ₁ c y x).measurable.aemeasurable
  have hk : AEMeasurable (fun x => kK c y x) μ :=
    (by unfold kK pP; fun_prop : Continuous fun x => kK c y x).measurable.aemeasurable
  have hp : AEMeasurable (fun x => ((pP x : ℝ) : ℂ)) μ :=
    (by unfold pP; fun_prop : Continuous fun x => ((pP x : ℝ) : ℂ)).measurable.aemeasurable
  unfold rKc aC₁ aC₂ aC₃
  fun_prop

/-- **PS on one window**: `Σᵢ aᵢ∫_W eψᵢRᵢ = Σ_j ∫_W eΦ_jR⁽ʲ⁾`, each rung's series converging absolutely. -/
theorem hasSum_span_window {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) {W : Set ℝ} (hW : MeasurableSet W) (hW1 : W ⊆ Ioi 1)
    {w w₁ w₂ : ℝ → ℂ} {y χ₀ D ρ : ℝ} (hD : ∀ i, |χ i - χ₀| ≤ D) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hQ : ∀ x ∈ W, D ≤ ρ * ‖qQ c χ₀ y x‖) (hQ0 : ∀ x ∈ W, qQ c χ₀ y x ≠ 0)
    (hp₁ : MemLp (fun x => pr₁ w₁ w₂ c χ₀ y x) 2 (volume.restrict W))
    (hp₂ : MemLp (fun x => pr₂ w w₁ c χ₀ y x) 2 (volume.restrict W))
    (hp₃ : MemLp (fun x => pr₃ w c χ₀ y x) 2 (volume.restrict W))
    (hwm : AEMeasurable w (volume.restrict W)) (hw₁m : AEMeasurable w₁ (volume.restrict W))
    (hw₂m : AEMeasurable w₂ (volume.restrict W)) :
    HasSum (fun j : ℕ => ∫ x in W, eF c y x * (phiMono c χ₀ χ g a j x : ℂ) * rKc w w₁ w₂ c χ₀ y j x)
      (∑ i, (a i : ℂ) * ∫ x in W, eF c y x * (psi c (g i) x : ℂ) * rRc w w₁ w₂ c (χ i) y x) := by
  classical
  have hψc : ∀ i, Continuous (psi c (g i)) := fun i =>
    (Cvs.Prolate.Gram.RungGramFloorAtInfinity.rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)).2.2.1
  have hψW : ∀ i, MemLp (psi c (g i)) 2 (volume.restrict W) := fun i =>
    (Cvs.Prolate.RungExactOrthogonality.memLp_psi (hg i) (hg₁ i) (hg₂c i) (hang i) hc).mono_measure
      (Measure.restrict_mono hW1 le_rfl)
  have hRm : ∀ j, AEStronglyMeasurable (rKc w w₁ w₂ c χ₀ y j) (volume.restrict W) := fun j =>
    (aemeasurable_rKc hwm hw₁m hw₂m c χ₀ y j).aestronglyMeasurable
  obtain ⟨g0, g1, g2⟩ := hasSum_geom_three hρ0 hρ1
  set F : ι → ℕ → ℝ → ℂ := fun i j x =>
    ((χ₀ - χ i : ℝ) : ℂ) ^ j * (eF c y x * (psi c (g i) x : ℂ) * rKc w w₁ w₂ c χ₀ y j x) with hF
  set G : ι → ℕ → ℝ → ℝ := fun i j x => ρ ^ j * (|psi c (g i) x| * pr₁ w₁ w₂ c χ₀ y x
    + (j + 1) * (|psi c (g i) x| * pr₂ w w₁ c χ₀ y x)
    + ((j + 2).choose 2 : ℝ) * (|psi c (g i) x| * pr₃ w c χ₀ y x)) with hG
  have i1 : ∀ i, Integrable (fun x => |psi c (g i) x| * pr₁ w₁ w₂ c χ₀ y x) (volume.restrict W) := fun i =>
    (hψW i).abs.integrable_mul hp₁
  have i2 : ∀ i, Integrable (fun x => |psi c (g i) x| * pr₂ w w₁ c χ₀ y x) (volume.restrict W) := fun i =>
    (hψW i).abs.integrable_mul hp₂
  have i3 : ∀ i, Integrable (fun x => |psi c (g i) x| * pr₃ w c χ₀ y x) (volume.restrict W) := fun i =>
    (hψW i).abs.integrable_mul hp₃
  have hGi : ∀ i j, Integrable (G i j) (volume.restrict W) := fun i j =>
    (((i1 i).add ((i2 i).const_mul _)).add ((i3 i).const_mul _)).const_mul _
  have hGe : ∀ i j, ∫ x in W, G i j x = ρ ^ j * (∫ x in W, |psi c (g i) x| * pr₁ w₁ w₂ c χ₀ y x)
      + (j + 1) * ρ ^ j * (∫ x in W, |psi c (g i) x| * pr₂ w w₁ c χ₀ y x)
      + ((j + 2).choose 2 : ℝ) * ρ ^ j * (∫ x in W, |psi c (g i) x| * pr₃ w c χ₀ y x) := fun i j => by
    simp only [hG]
    rw [integral_const_mul, integral_add ?_ ?_, integral_add ?_ ?_, integral_const_mul, integral_const_mul]
    · ring
    · exact i1 i
    · exact (i2 i).const_mul _
    · exact (i1 i).add ((i2 i).const_mul _)
    · exact (i3 i).const_mul _
  have hFb : ∀ i j, ∀ x ∈ W, ‖F i j x‖ ≤ G i j x := by
    intro i j x hx
    have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD i)
    have hk := pow_mul_norm_rKc_le (w := w) (w₁ := w₁) (w₂ := w₂) hD0 hρ0 (hQ x hx) (hQ0 x hx) j
    have hDi : |χ₀ - χ i| ^ j ≤ D ^ j :=
      pow_le_pow_left₀ (abs_nonneg _) (by rw [abs_sub_comm]; exact hD i) j
    simp only [hF, hG, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, (continuous_eF c y).2, one_mul]
    calc |χ₀ - χ i| ^ j * (|psi c (g i) x| * ‖rKc w w₁ w₂ c χ₀ y j x‖)
        ≤ D ^ j * (|psi c (g i) x| * ‖rKc w w₁ w₂ c χ₀ y j x‖) :=
          mul_le_mul_of_nonneg_right hDi (by positivity)
      _ = |psi c (g i) x| * (D ^ j * ‖rKc w w₁ w₂ c χ₀ y j x‖) := by ring
      _ ≤ |psi c (g i) x| * (ρ ^ j * (pr₁ w₁ w₂ c χ₀ y x + (j + 1) * pr₂ w w₁ c χ₀ y x
            + ((j + 2).choose 2 : ℝ) * pr₃ w c χ₀ y x)) := mul_le_mul_of_nonneg_left hk (abs_nonneg _)
      _ = _ := by ring
  have hFm : ∀ i j, AEStronglyMeasurable (F i j) (volume.restrict W) := fun i j =>
    (((continuous_eF c y).1.aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp (hψc i)).aestronglyMeasurable).mul (hRm j)).const_mul _
  have hFi : ∀ i j, Integrable (F i j) (volume.restrict W) := fun i j =>
    Integrable.mono' (hGi i j) (hFm i j) ((ae_restrict_iff' hW).2 (Eventually.of_forall (hFb i j)))
  have hFs : ∀ i, Summable (fun j => ∫ x in W, ‖F i j x‖) := by
    intro i
    have hsum := ((g0.summable.mul_right (∫ x in W, |psi c (g i) x| * pr₁ w₁ w₂ c χ₀ y x)).add
      (g1.summable.mul_right (∫ x in W, |psi c (g i) x| * pr₂ w w₁ c χ₀ y x))).add
      (g2.summable.mul_right (∫ x in W, |psi c (g i) x| * pr₃ w c χ₀ y x))
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun x => norm_nonneg _) (fun j => ?_) hsum
    calc ∫ x in W, ‖F i j x‖ ≤ ∫ x in W, G i j x :=
          setIntegral_mono_on (hFi i j).norm (hGi i j) hW (hFb i j)
      _ = _ := by rw [hGe]
  have hrung : ∀ i, HasSum (fun j => ∫ x in W, F i j x)
      (∫ x in W, eF c y x * (psi c (g i) x : ℂ) * rRc w w₁ w₂ c (χ i) y x) := by
    intro i
    have key := hasSum_integral_of_summable_integral_norm (hFi i) (hFs i)
    have e2 : ∫ x in W, ∑' j, F i j x = ∫ x in W, eF c y x * (psi c (g i) x : ℂ) * rRc w w₁ w₂ c (χ i) y x := by
      refine setIntegral_congr_fun hW fun x hx => ?_
      have hq : 0 < ‖qQ c χ₀ y x‖ := norm_pos_iff.mpr (hQ0 x hx)
      have hlt : |χ i - χ₀| < ‖qQ c χ₀ y x‖ := (hD i).trans_lt (by nlinarith [hQ x hx])
      have h := (hasSum_rRc_shift (w := w) (w₁ := w₁) (w₂ := w₂) hlt).mul_left
        (eF c y x * (psi c (g i) x : ℂ))
      have e : (fun j => F i j x) = fun j : ℕ => eF c y x * (psi c (g i) x : ℂ)
          * (((χ₀ - χ i : ℝ) : ℂ) ^ j * rKc w w₁ w₂ c χ₀ y j x) := by
        funext j; simp only [hF]; ring
      simp only [e]
      exact h.tsum_eq
    rw [e2] at key
    exact key
  have hall := hasSum_sum (s := Finset.univ) fun i _ => (hrung i).mul_left (a i : ℂ)
  have e3 : (fun j => ∑ i, (a i : ℂ) * ∫ x in W, F i j x)
      = fun j : ℕ => ∫ x in W, eF c y x * (phiMono c χ₀ χ g a j x : ℂ) * rKc w w₁ w₂ c χ₀ y j x := by
    funext j
    simp_rw [← integral_const_mul]
    rw [← integral_finsetSum _ fun i _ => (hFi i j).const_mul _]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hF, phiMono, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast; ring
  rw [e3] at hall
  exact hall

/-- **PS with H on a window family**: for pairwise disjoint `W_m ⊆ (1, ∞)`, `|χᵢ − χ₀| ≤ D ≤ ρ|Q_{χ₀}|` on every
`W_m`, `ρ < 1`, the `ℓ²` sum over windows taken for each `j` before the `j`-series. -/
theorem sum_span_bulk_le {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ) {s : Finset ℕ} {W : ℕ → Set ℝ}
    (hW : ∀ m ∈ s, MeasurableSet (W m)) (hW1 : ∀ m ∈ s, W m ⊆ Ioi 1) (hd : (s : Set ℕ).PairwiseDisjoint W)
    {w w₁ w₂ : ℕ → ℝ → ℂ} {y : ℕ → ℝ} {χ₀ D ρ : ℝ} (hD : ∀ i, |χ i - χ₀| ≤ D) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hQ : ∀ m ∈ s, ∀ x ∈ W m, D ≤ ρ * ‖qQ c χ₀ (y m) x‖) (hQ0 : ∀ m ∈ s, ∀ x ∈ W m, qQ c χ₀ (y m) x ≠ 0)
    (hp₁ : ∀ m ∈ s, MemLp (fun x => pr₁ (w₁ m) (w₂ m) c χ₀ (y m) x) 2 (volume.restrict (W m)))
    (hp₂ : ∀ m ∈ s, MemLp (fun x => pr₂ (w m) (w₁ m) c χ₀ (y m) x) 2 (volume.restrict (W m)))
    (hp₃ : ∀ m ∈ s, MemLp (fun x => pr₃ (w m) c χ₀ (y m) x) 2 (volume.restrict (W m)))
    (hwm : ∀ m ∈ s, AEMeasurable (w m) (volume.restrict (W m)))
    (hw₁m : ∀ m ∈ s, AEMeasurable (w₁ m) (volume.restrict (W m)))
    (hw₂m : ∀ m ∈ s, AEMeasurable (w₂ m) (volume.restrict (W m))) :
    ∑ m ∈ s, ‖∑ i, (a i : ℂ) * ∫ x in W m, eF c (y m) x * (psi c (g i) x : ℂ)
        * rRc (w m) (w₁ m) (w₂ m) c (χ i) (y m) x‖
      ≤ (√(∑ m ∈ s, ∫ x in W m, pr₁ (w₁ m) (w₂ m) c χ₀ (y m) x ^ 2) / (1 - ρ)
          + √(∑ m ∈ s, ∫ x in W m, pr₂ (w m) (w₁ m) c χ₀ (y m) x ^ 2) / (1 - ρ) ^ 2
          + √(∑ m ∈ s, ∫ x in W m, pr₃ (w m) c χ₀ (y m) x ^ 2) / (1 - ρ) ^ 3)
        * √(∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2) := by
  classical
  set P := ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 with hP
  set N₁ := √(∑ m ∈ s, ∫ x in W m, pr₁ (w₁ m) (w₂ m) c χ₀ (y m) x ^ 2) with hN₁
  set N₂ := √(∑ m ∈ s, ∫ x in W m, pr₂ (w m) (w₁ m) c χ₀ (y m) x ^ 2) with hN₂
  set N₃ := √(∑ m ∈ s, ∫ x in W m, pr₃ (w m) c χ₀ (y m) x ^ 2) with hN₃
  set T : ℕ → ℕ → ℂ := fun m j => ∫ x in W m, eF c (y m) x * (phiMono c χ₀ χ g a j x : ℂ)
      * rKc (w m) (w₁ m) (w₂ m) c χ₀ (y m) j x with hT
  have hA : ∀ m ∈ s, HasSum (fun j => T m j) (∑ i, (a i : ℂ) * ∫ x in W m, eF c (y m) x * (psi c (g i) x : ℂ)
      * rRc (w m) (w₁ m) (w₂ m) c (χ i) (y m) x) := fun m hm =>
    hasSum_span_window a hg hg₁ hg₂c hang hc (hW m hm) (hW1 m hm) hD hρ0 hρ1 (hQ m hm) (hQ0 m hm)
      (hp₁ m hm) (hp₂ m hm) (hp₃ m hm) (hwm m hm) (hw₁m m hm) (hw₂m m hm)
  have hψc : ∀ i, Continuous (psi c (g i)) := fun i =>
    (Cvs.Prolate.Gram.RungGramFloorAtInfinity.rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)).2.2.1
  have hψ1 : ∀ i, MemLp (psi c (g i)) 2 (volume.restrict (Ioi 1)) := fun i =>
    Cvs.Prolate.RungExactOrthogonality.memLp_psi (hg i) (hg₁ i) (hg₂c i) (hang i) hc
  have hP0 : 0 ≤ P := integral_nonneg fun _ => sq_nonneg _
  have hN0 : 0 ≤ N₁ ∧ 0 ≤ N₂ ∧ 0 ≤ N₃ := ⟨Real.sqrt_nonneg _, Real.sqrt_nonneg _, Real.sqrt_nonneg _⟩
  set b : ℕ → ℝ := fun j => ρ ^ j * (N₁ + (j + 1) * N₂ + ((j + 2).choose 2 : ℝ) * N₃) * √P with hb
  have hb0 : ∀ j, 0 ≤ b j := fun j => by
    have := hN0.1; have := hN0.2.1; have := hN0.2.2
    simp only [hb]; positivity
  have hB : ∀ j, ∑ m ∈ s, ‖T m j‖ ≤ b j := by
    intro j
    by_cases h0 : ∀ i, (χ₀ - χ i) ^ j = 0
    · have hz : ∀ m, T m j = 0 := by
        intro m
        have : ∀ x, phiMono c χ₀ χ g a j x = 0 := fun x => by simp [phiMono, h0]
        simp [hT, this]
      simp only [hz, norm_zero, Finset.sum_const_zero]; exact hb0 j
    · push Not at h0
      obtain ⟨i₀, hi₀⟩ := h0
      have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD i₀)
      have hDj : 0 < D ^ j := by
        have h1 : 0 < |χ₀ - χ i₀| ^ j := by rw [← abs_pow]; exact abs_pos.mpr hi₀
        have h2 : |χ₀ - χ i₀| ^ j ≤ D ^ j :=
          pow_le_pow_left₀ (abs_nonneg _) (by rw [abs_sub_comm]; exact hD i₀) j
        linarith
      have hΦ1 : MemLp (phiMono c χ₀ χ g a j) 2 (volume.restrict (Ioi 1)) :=
        memLp_finsetSum _ fun i _ => (hψ1 i).const_mul _
      have hΦW : ∀ m ∈ s, MemLp (phiMono c χ₀ χ g a j) 2 (volume.restrict (W m)) := fun m hm =>
        hΦ1.mono_measure (Measure.restrict_mono (hW1 m hm) le_rfl)
      set Φ := phiMono c χ₀ χ g a j with hΦ
      have hwin : ∀ m ∈ s, ‖T m j‖ ≤ ρ ^ j / D ^ j
          * ((∫ x in W m, pr₁ (w₁ m) (w₂ m) c χ₀ (y m) x * |Φ x|)
            + (j + 1) * (∫ x in W m, pr₂ (w m) (w₁ m) c χ₀ (y m) x * |Φ x|)
            + ((j + 2).choose 2 : ℝ) * (∫ x in W m, pr₃ (w m) c χ₀ (y m) x * |Φ x|)) := by
        intro m hm
        have i1 : Integrable (fun x => pr₁ (w₁ m) (w₂ m) c χ₀ (y m) x * |Φ x|) (volume.restrict (W m)) :=
          (hp₁ m hm).integrable_mul (hΦW m hm).abs
        have i2 : Integrable (fun x => pr₂ (w m) (w₁ m) c χ₀ (y m) x * |Φ x|) (volume.restrict (W m)) :=
          (hp₂ m hm).integrable_mul (hΦW m hm).abs
        have i3 : Integrable (fun x => pr₃ (w m) c χ₀ (y m) x * |Φ x|) (volume.restrict (W m)) :=
          (hp₃ m hm).integrable_mul (hΦW m hm).abs
        have hI : Integrable (fun x => ρ ^ j / D ^ j * (pr₁ (w₁ m) (w₂ m) c χ₀ (y m) x * |Φ x|
            + (j + 1) * (pr₂ (w m) (w₁ m) c χ₀ (y m) x * |Φ x|)
            + ((j + 2).choose 2 : ℝ) * (pr₃ (w m) c χ₀ (y m) x * |Φ x|))) (volume.restrict (W m)) :=
          ((i1.add (i2.const_mul _)).add (i3.const_mul _)).const_mul _
        have he : ∫ x in W m, ρ ^ j / D ^ j * (pr₁ (w₁ m) (w₂ m) c χ₀ (y m) x * |Φ x|
            + (j + 1) * (pr₂ (w m) (w₁ m) c χ₀ (y m) x * |Φ x|)
            + ((j + 2).choose 2 : ℝ) * (pr₃ (w m) c χ₀ (y m) x * |Φ x|))
            = ρ ^ j / D ^ j * ((∫ x in W m, pr₁ (w₁ m) (w₂ m) c χ₀ (y m) x * |Φ x|)
              + (j + 1) * (∫ x in W m, pr₂ (w m) (w₁ m) c χ₀ (y m) x * |Φ x|)
              + ((j + 2).choose 2 : ℝ) * (∫ x in W m, pr₃ (w m) c χ₀ (y m) x * |Φ x|)) := by
          rw [integral_const_mul, integral_add ?_ ?_, integral_add ?_ ?_, integral_const_mul, integral_const_mul]
          · exact i1
          · exact i2.const_mul _
          · exact i1.add (i2.const_mul _)
          · exact i3.const_mul _
        rw [← he]
        refine norm_integral_le_of_norm_le hI ((ae_restrict_iff' (hW m hm)).2 (Eventually.of_forall fun x hx => ?_))
        have hk := pow_mul_norm_rKc_le (w := w m) (w₁ := w₁ m) (w₂ := w₂ m) hD0 hρ0 (hQ m hm x hx)
          (hQ0 m hm x hx) j
        have hk' : ‖rKc (w m) (w₁ m) (w₂ m) c χ₀ (y m) j x‖ ≤ ρ ^ j / D ^ j
            * (pr₁ (w₁ m) (w₂ m) c χ₀ (y m) x + (j + 1) * pr₂ (w m) (w₁ m) c χ₀ (y m) x
              + ((j + 2).choose 2 : ℝ) * pr₃ (w m) c χ₀ (y m) x) := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hDj]; linarith
        rw [norm_mul, norm_mul, (continuous_eF c (y m)).2, one_mul, Complex.norm_real, Real.norm_eq_abs]
        calc |Φ x| * ‖rKc (w m) (w₁ m) (w₂ m) c χ₀ (y m) j x‖
            ≤ |Φ x| * (ρ ^ j / D ^ j * (pr₁ (w₁ m) (w₂ m) c χ₀ (y m) x + (j + 1) * pr₂ (w m) (w₁ m) c χ₀ (y m) x
              + ((j + 2).choose 2 : ℝ) * pr₃ (w m) c χ₀ (y m) x)) := mul_le_mul_of_nonneg_left hk' (abs_nonneg _)
          _ = _ := by ring
      have H₁ := sum_setIntegral_mul_abs_le hW hW1 hd (f := fun m x => pr₁ (w₁ m) (w₂ m) c χ₀ (y m) x)
        (fun m _ x => by unfold pr₁; positivity) hp₁ hΦ1
      have H₂ := sum_setIntegral_mul_abs_le hW hW1 hd (f := fun m x => pr₂ (w m) (w₁ m) c χ₀ (y m) x)
        (fun m _ x => by unfold pr₂; positivity) hp₂ hΦ1
      have H₃ := sum_setIntegral_mul_abs_le hW hW1 hd (f := fun m x => pr₃ (w m) c χ₀ (y m) x)
        (fun m _ x => by unfold pr₃; positivity) hp₃ hΦ1
      beta_reduce at H₁ H₂ H₃
      have hΦP : √(∫ x in Ioi 1, Φ x ^ 2) ≤ D ^ j * √P := by
        have h := monomial_sum_le a hg hg₁ hg₂c hang hc hχ (χ₀ := χ₀) (D := D)
          (fun i => by rw [abs_sub_comm]; exact hD i) j
        calc √(∫ x in Ioi 1, Φ x ^ 2) ≤ √(D ^ (2 * j) * P) := Real.sqrt_le_sqrt h
          _ = D ^ j * √P := by
            rw [Real.sqrt_mul (by positivity), mul_comm 2 j, pow_mul, Real.sqrt_sq (pow_nonneg hD0 j)]
      have hj1 : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
      have hC : (0 : ℝ) ≤ ((j + 2).choose 2 : ℝ) := by positivity
      have hρD : 0 ≤ ρ ^ j / D ^ j := by positivity
      set R := √(∫ x in Ioi 1, Φ x ^ 2) with hR
      calc ∑ m ∈ s, ‖T m j‖
          ≤ ∑ m ∈ s, ρ ^ j / D ^ j * ((∫ x in W m, pr₁ (w₁ m) (w₂ m) c χ₀ (y m) x * |Φ x|)
            + (j + 1) * (∫ x in W m, pr₂ (w m) (w₁ m) c χ₀ (y m) x * |Φ x|)
            + ((j + 2).choose 2 : ℝ) * (∫ x in W m, pr₃ (w m) c χ₀ (y m) x * |Φ x|)) := Finset.sum_le_sum hwin
        _ = ρ ^ j / D ^ j * ((∑ m ∈ s, ∫ x in W m, pr₁ (w₁ m) (w₂ m) c χ₀ (y m) x * |Φ x|)
            + (j + 1) * (∑ m ∈ s, ∫ x in W m, pr₂ (w m) (w₁ m) c χ₀ (y m) x * |Φ x|)
            + ((j + 2).choose 2 : ℝ) * (∑ m ∈ s, ∫ x in W m, pr₃ (w m) c χ₀ (y m) x * |Φ x|)) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
            ← Finset.mul_sum]
        _ ≤ ρ ^ j / D ^ j * (N₁ * R + (j + 1) * (N₂ * R) + ((j + 2).choose 2 : ℝ) * (N₃ * R)) :=
          mul_le_mul_of_nonneg_left (add_le_add (add_le_add H₁ (mul_le_mul_of_nonneg_left H₂ hj1))
            (mul_le_mul_of_nonneg_left H₃ hC)) hρD
        _ ≤ ρ ^ j / D ^ j * (N₁ * (D ^ j * √P) + (j + 1) * (N₂ * (D ^ j * √P))
            + ((j + 2).choose 2 : ℝ) * (N₃ * (D ^ j * √P))) := by
          have := hN0.1; have := hN0.2.1; have := hN0.2.2
          gcongr
        _ = b j := by simp only [hb]; field_simp
  obtain ⟨g0, g1, g2⟩ := hasSum_geom_three hρ0 hρ1
  have hbsum : HasSum b ((N₁ / (1 - ρ) + N₂ / (1 - ρ) ^ 2 + N₃ / (1 - ρ) ^ 3) * √P) := by
    have h := (((g0.mul_right N₁).add (g1.mul_right N₂)).add (g2.mul_right N₃)).mul_right √P
    have e1 : b = fun j : ℕ => (ρ ^ j * N₁ + ((j : ℝ) + 1) * ρ ^ j * N₂ + ((j + 2).choose 2 : ℝ) * ρ ^ j * N₃)
        * √P := by funext j; simp only [hb]; ring
    have e2 : (N₁ / (1 - ρ) + N₂ / (1 - ρ) ^ 2 + N₃ / (1 - ρ) ^ 3) * √P
        = (1 / (1 - ρ) * N₁ + 1 / (1 - ρ) ^ 2 * N₂ + 1 / (1 - ρ) ^ 3 * N₃) * √P := by ring
    rw [e1, e2]; exact h
  have hsm : ∀ m ∈ s, Summable (fun j => ‖T m j‖) := fun m hm =>
    Summable.of_nonneg_of_le (fun j => norm_nonneg _)
      (fun j => (Finset.single_le_sum (f := fun m => ‖T m j‖) (fun m _ => norm_nonneg _) hm).trans (hB j))
      hbsum.summable
  calc ∑ m ∈ s, ‖∑ i, (a i : ℂ) * ∫ x in W m, eF c (y m) x * (psi c (g i) x : ℂ)
        * rRc (w m) (w₁ m) (w₂ m) c (χ i) (y m) x‖ ≤ ∑ m ∈ s, ∑' j, ‖T m j‖ :=
        Finset.sum_le_sum fun m hm => by
          rw [← (hA m hm).tsum_eq]; exact norm_tsum_le_tsum_norm (hsm m hm)
    _ = ∑' j, ∑ m ∈ s, ‖T m j‖ := (Summable.tsum_finsetSum hsm).symm
    _ ≤ ∑' j, b j := Summable.tsum_le_tsum hB (summable_sum hsm) hbsum.summable
    _ = _ := hbsum.tsum_eq

/-- **The span bulk on one window**, generalising `FarFarBound`'s `norm_farI_le` to a complex `C²` weight, any `χ₀`,
any measurable `W ⊆ (1, ∞)` (an `Icc` or an `Ioi`). -/
theorem span_bulk_le {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ) {W : Set ℝ} (hW : MeasurableSet W) (hW1 : W ⊆ Ioi 1)
    {w w₁ w₂ : ℝ → ℂ} {y χ₀ D ρ : ℝ} (hD : ∀ i, |χ i - χ₀| ≤ D) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hQ : ∀ x ∈ W, D ≤ ρ * ‖qQ c χ₀ y x‖) (hQ0 : ∀ x ∈ W, qQ c χ₀ y x ≠ 0)
    (hp₁ : MemLp (fun x => pr₁ w₁ w₂ c χ₀ y x) 2 (volume.restrict W))
    (hp₂ : MemLp (fun x => pr₂ w w₁ c χ₀ y x) 2 (volume.restrict W))
    (hp₃ : MemLp (fun x => pr₃ w c χ₀ y x) 2 (volume.restrict W))
    (hwm : AEMeasurable w (volume.restrict W)) (hw₁m : AEMeasurable w₁ (volume.restrict W))
    (hw₂m : AEMeasurable w₂ (volume.restrict W)) :
    ‖∑ i, (a i : ℂ) * ∫ x in W, eF c y x * (psi c (g i) x : ℂ) * rRc w w₁ w₂ c (χ i) y x‖
      ≤ (√(∫ x in W, pr₁ w₁ w₂ c χ₀ y x ^ 2) / (1 - ρ) + √(∫ x in W, pr₂ w w₁ c χ₀ y x ^ 2) / (1 - ρ) ^ 2
          + √(∫ x in W, pr₃ w c χ₀ y x ^ 2) / (1 - ρ) ^ 3)
        * √(∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2) := by
  have h := sum_span_bulk_le a hg hg₁ hg₂c hang hc hχ (s := {0}) (W := fun _ => W) (fun _ _ => hW)
    (fun _ _ => hW1) (by simp) (w := fun _ => w) (w₁ := fun _ => w₁) (w₂ := fun _ => w₂) (y := fun _ => y)
    hD hρ0 hρ1 (fun _ _ => hQ) (fun _ _ => hQ0) (fun _ _ => hp₁) (fun _ _ => hp₂) (fun _ _ => hp₃)
    (fun _ _ => hwm) (fun _ _ => hw₁m) (fun _ _ => hw₂m)
  simp only [Finset.sum_singleton] at h
  exact h

/-! ### Lemma LP: the Laplace transform in `σ²` -/

/-- `s^k e^{−bs}` is integrable on `(0, ∞)` for `b > 0`. -/
theorem integrableOn_pow_mul_exp_neg (k : ℕ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun s : ℝ => s ^ k * Real.exp (-(s * b))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (k : ℝ)) (p := 1) (b := b)
    (by have := Nat.cast_nonneg (α := ℝ) k; linarith) one_pos hb
  refine h.congr_fun (fun s _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast, Real.rpow_one]
  ring_nf

/-- `s^k e^{sQ}` is integrable on `(0, ∞)` for `Re Q < 0`. -/
theorem integrableOn_pow_mul_cexp (k : ℕ) {Q : ℂ} (hQ : Q.re < 0) :
    IntegrableOn (fun s : ℝ => (s : ℂ) ^ k * cexp ((s : ℂ) * Q)) (Ioi 0) := by
  refine Integrable.mono' (integrableOn_pow_mul_exp_neg k (neg_pos.mpr hQ))
    (by fun_prop : Continuous fun s : ℝ => (s : ℂ) ^ k * cexp ((s : ℂ) * Q)).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => le_of_eq ?_))
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, Complex.norm_exp,
    Complex.re_ofReal_mul]
  ring_nf

/-- `∫_0^∞ s^k e^{sQ} ds = (−1)^{k+1}k!/Q^{k+1}` for `Re Q < 0`. -/
theorem integral_pow_mul_cexp (k : ℕ) {Q : ℂ} (hQ : Q.re < 0) :
    ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ k * cexp ((s : ℂ) * Q) = (-1) ^ (k + 1) * (k.factorial : ℂ) / Q ^ (k + 1) := by
  have hQ0 : Q ≠ 0 := fun h => by rw [h, Complex.zero_re] at hQ; exact lt_irrefl _ hQ
  induction k with
  | zero =>
    have h := integral_exp_mul_complex_Ioi hQ 0
    simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one]
    simp_rw [mul_comm _ Q]
    rw [h]; simp
  | succ k ih =>
    have hint := fun n => integrableOn_pow_mul_cexp n hQ
    have hderiv : ∀ s ∈ Ioi (0 : ℝ), HasDerivAt (fun s : ℝ => (s : ℂ) ^ (k + 1) * cexp ((s : ℂ) * Q))
        (((k + 1 : ℕ) : ℂ) * ((s : ℂ) ^ k * cexp ((s : ℂ) * Q)) + Q * ((s : ℂ) ^ (k + 1) * cexp ((s : ℂ) * Q)))
        s := by
      intro s _
      have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) ^ (k + 1)) (((k + 1 : ℕ) : ℂ) * (s : ℂ) ^ k) s := by
        simpa using (hasDerivAt_pow (k + 1) (s : ℂ)).comp_ofReal
      have h2 : HasDerivAt (fun s : ℝ => cexp ((s : ℂ) * Q)) (cexp ((s : ℂ) * Q) * Q) s := by
        simpa using ((hasDerivAt_id (s : ℂ)).mul_const Q).cexp.comp_ofReal
      exact (h1.mul h2).congr_deriv (by ring)
    have hlim : Tendsto (fun s : ℝ => (s : ℂ) ^ (k + 1) * cexp ((s : ℂ) * Q)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((k + 1 : ℕ) : ℝ) (-Q.re) (neg_pos.mpr hQ)
      refine h.congr' ((eventually_gt_atTop 0).mono fun s hs => ?_)
      beta_reduce
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, Complex.norm_exp,
        Complex.re_ofReal_mul, Real.rpow_natCast]
      ring_nf
    have hcont : ContinuousWithinAt (fun s : ℝ => (s : ℂ) ^ (k + 1) * cexp ((s : ℂ) * Q)) (Ici 0) 0 :=
      (by fun_prop : Continuous fun s : ℝ => (s : ℂ) ^ (k + 1) * cexp ((s : ℂ) * Q)).continuousWithinAt
    have hfi : IntegrableOn (fun s : ℝ => ((k + 1 : ℕ) : ℂ) * ((s : ℂ) ^ k * cexp ((s : ℂ) * Q))
        + Q * ((s : ℂ) ^ (k + 1) * cexp ((s : ℂ) * Q))) (Ioi 0) :=
      ((hint k).const_mul _).add ((hint (k + 1)).const_mul _)
    have key := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hfi hlim
    rw [integral_add ((hint k).const_mul _) ((hint (k + 1)).const_mul _), integral_const_mul,
      integral_const_mul, ih] at key
    simp only [Complex.ofReal_zero, zero_pow (Nat.succ_ne_zero k), zero_mul, sub_zero] at key
    have hI : ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (k + 1) * cexp ((s : ℂ) * Q)
        = -(((k + 1 : ℕ) : ℂ) * ((-1) ^ (k + 1) * (k.factorial : ℂ) / Q ^ (k + 1))) / Q := by
      rw [eq_div_iff hQ0]; linear_combination key
    rw [hI, Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- **Lemma LP**: `1/Q^{k+1} = ((−1)^{k+1}/k!)∫_0^∞ s^k e^{sQ} ds` for `Re Q < 0`. -/
theorem laplace_inv_pow (k : ℕ) {Q : ℂ} (hQ : Q.re < 0) :
    1 / Q ^ (k + 1)
      = (-1) ^ (k + 1) / (k.factorial : ℂ) * ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ k * cexp ((s : ℂ) * Q) := by
  have hQ0 : Q ≠ 0 := fun h => by rw [h, Complex.zero_re] at hQ; exact lt_irrefl _ hQ
  have hf : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have h1 : ((-1 : ℂ) ^ (k + 1)) * (-1) ^ (k + 1) = 1 := by rw [← mul_pow]; norm_num
  rw [integral_pow_mul_cexp k hQ]
  calc 1 / Q ^ (k + 1) = ((-1) ^ (k + 1) * (-1) ^ (k + 1)) * (k.factorial : ℂ) / ((k.factorial : ℂ) * Q ^ (k + 1)) := by
        rw [h1]; field_simp
    _ = _ := by ring

/-- `Φ^{(s)} = Σ aᵢ e^{−sσᵢ²}ψᵢ`. -/
noncomputable def phiLap {ι : Type*} [Fintype ι] (c s : ℝ) (χ : ι → ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (x : ℝ) :
    ℝ := ∑ i, a i * Real.exp (-(s * (c ^ 2 - χ i))) * psi c (g i) x

/-- `‖Φ^{(s)}‖² ≤ e^{−2sσ₀}P` for `σᵢ² ≥ σ₀`, `s ≥ 0`. -/
theorem integral_phiLap_sq_le {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ}
    (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ) {σ₀ s : ℝ} (hσ : ∀ i, σ₀ ≤ c ^ 2 - χ i) (hs : 0 ≤ s) :
    ∫ x in Ioi 1, phiLap c s χ g a x ^ 2
      ≤ Real.exp (-(2 * s * σ₀)) * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := by
  have e := Cvs.Prolate.RungExactOrthogonality.integral_span_sq (fun i => a i * Real.exp (-(s * (c ^ 2 - χ i)))) hg hg₁ hg₂c
    hang hc hχ
  simp only [phiLap]
  rw [e, Cvs.Prolate.RungExactOrthogonality.integral_span_sq a hg hg₁ hg₂c hang hc hχ, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hI : 0 ≤ ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hexp : Real.exp (-(s * (c ^ 2 - χ i))) ^ 2 ≤ Real.exp (-(2 * s * σ₀)) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left (hσ i) hs
    push_cast; nlinarith
  calc (a i * Real.exp (-(s * (c ^ 2 - χ i)))) ^ 2 * ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2
      = a i ^ 2 * Real.exp (-(s * (c ^ 2 - χ i))) ^ 2 * ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2 := by ring
    _ ≤ a i ^ 2 * Real.exp (-(2 * s * σ₀)) * ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2 := by gcongr
    _ = Real.exp (-(2 * s * σ₀)) * (a i ^ 2 * ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2) := by ring

/-- **LP on a window**: for `Re Q_{c²} ≤ 0` on `W` and `σᵢ² ≥ σ₀ > 0`,
`|Σᵢ aᵢ∫_W eψᵢA/Q_{χᵢ}^{k+1}| ≤ (1/k!)∫_0^∞ s^k e^{−sσ₀}‖Ae^{sQ_{c²}}‖_{L²(W)} ds · √P`. -/
theorem span_bulk_laplace_le {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ}
    (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ) (k : ℕ) {A : ℝ → ℂ} {W : Set ℝ} {y σ₀ : ℝ}
    (hW : MeasurableSet W) (hW1 : W ⊆ Ioi 1) (hA : MemLp A 2 (volume.restrict W))
    (hre : ∀ x ∈ W, (qQ c (c ^ 2) y x).re ≤ 0) (hσ₀ : 0 < σ₀) (hσ : ∀ i, σ₀ ≤ c ^ 2 - χ i) :
    ‖∑ i, (a i : ℂ) * ∫ x in W, eF c y x * (psi c (g i) x : ℂ) * (A x / qQ c (χ i) y x ^ (k + 1))‖
      ≤ 1 / (k.factorial : ℝ) * (∫ s in Ioi (0 : ℝ), s ^ k * Real.exp (-(s * σ₀))
          * √(∫ x in W, ‖A x‖ ^ 2 * Real.exp (2 * s * (qQ c (c ^ 2) y x).re)))
        * √(∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2) := by
  classical
  set P := ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 with hP
  set κ : ℂ := (-1) ^ (k + 1) / (k.factorial : ℂ) with hκ
  have hψc : ∀ i, Continuous (psi c (g i)) := fun i =>
    (Cvs.Prolate.Gram.RungGramFloorAtInfinity.rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)).2.2.1
  have hψ1 : ∀ i, MemLp (psi c (g i)) 2 (volume.restrict (Ioi 1)) := fun i =>
    Cvs.Prolate.RungExactOrthogonality.memLp_psi (hg i) (hg₁ i) (hg₂c i) (hang i) hc
  have hψW : ∀ i, MemLp (psi c (g i)) 2 (volume.restrict W) := fun i =>
    (hψ1 i).mono_measure (Measure.restrict_mono hW1 le_rfl)
  have hQc : ∀ χ' : ℝ, Continuous fun x => qQ c χ' y x := fun χ' => by unfold qQ; fun_prop
  have hQi : ∀ i x, qQ c (χ i) y x = qQ c (c ^ 2) y x + ((χ i - c ^ 2 : ℝ) : ℂ) := fun i x =>
    Cvs.L2a.QIdentityCutPoint.qQ_add_chi c (χ i) (c ^ 2) y x
  have hreQi : ∀ i, ∀ x ∈ W, (qQ c (χ i) y x).re ≤ -σ₀ := by
    intro i x hx; rw [hQi, Complex.add_re, Complex.ofReal_re]; linarith [hre x hx, hσ i]
  have hgs : IntegrableOn (fun s : ℝ => s ^ k * Real.exp (-(s * σ₀))) (Ioi 0) := integrableOn_pow_mul_exp_neg k hσ₀
  have hAn : Integrable (fun x => ‖A x‖ ^ 2) (volume.restrict W) := (memLp_two_iff_integrable_sq_norm hA.aestronglyMeasurable).mp hA
  -- the joint integrand
  set F : ι → ℝ → ℝ → ℂ := fun i x s =>
    eF c y x * (psi c (g i) x : ℂ) * A x * ((s : ℂ) ^ k * cexp ((s : ℂ) * qQ c (χ i) y x)) with hF
  have hFbd : ∀ i, ∀ x ∈ W, ∀ s ∈ Ioi (0 : ℝ),
      ‖F i x s‖ ≤ (|psi c (g i) x| * ‖A x‖) * (s ^ k * Real.exp (-(s * σ₀))) := by
    intro i x hx s hs
    have hs' : (0 : ℝ) < s := hs
    have he : Real.exp (s * (qQ c (χ i) y x).re) ≤ Real.exp (-(s * σ₀)) :=
      Real.exp_le_exp.mpr (by nlinarith [hreQi i x hx])
    simp only [hF, norm_mul, (continuous_eF c y).2, one_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow,
      abs_of_pos hs', Complex.norm_exp, Complex.re_ofReal_mul]
    have h0 : 0 ≤ |psi c (g i) x| * ‖A x‖ * s ^ k := by positivity
    calc |psi c (g i) x| * ‖A x‖ * (s ^ k * Real.exp (s * (qQ c (χ i) y x).re))
        = |psi c (g i) x| * ‖A x‖ * s ^ k * Real.exp (s * (qQ c (χ i) y x).re) := by ring
      _ ≤ |psi c (g i) x| * ‖A x‖ * s ^ k * Real.exp (-(s * σ₀)) := mul_le_mul_of_nonneg_left he h0
      _ = _ := by ring
  have hFint : ∀ i, Integrable (Function.uncurry (F i)) ((volume.restrict W).prod (volume.restrict (Ioi 0))) := by
    intro i
    have hb : Integrable (fun p : ℝ × ℝ => (|psi c (g i) p.1| * ‖A p.1‖) * (p.2 ^ k * Real.exp (-(p.2 * σ₀))))
        ((volume.restrict W).prod (volume.restrict (Ioi 0))) :=
      Integrable.mul_prod ((hψW i).abs.integrable_mul hA.norm) hgs
    have h1 : Continuous fun p : ℝ × ℝ => eF c y p.1 * (psi c (g i) p.1 : ℂ) := by
      have := (continuous_eF c y).1; have := hψc i; fun_prop
    have h2 : Continuous fun p : ℝ × ℝ => (p.2 : ℂ) ^ k * cexp ((p.2 : ℂ) * qQ c (χ i) y p.1) := by
      have := hQc (χ i); fun_prop
    have h3 : AEStronglyMeasurable (fun p : ℝ × ℝ => A p.1) ((volume.restrict W).prod (volume.restrict (Ioi 0))) :=
      hA.aestronglyMeasurable.comp_fst
    have hm : AEStronglyMeasurable (Function.uncurry (F i))
        ((volume.restrict W).prod (volume.restrict (Ioi 0))) :=
      (h1.aestronglyMeasurable.mul h3).mul h2.aestronglyMeasurable
    refine Integrable.mono' hb hm ?_
    rw [Measure.prod_restrict, ae_restrict_iff' (hW.prod measurableSet_Ioi)]
    exact Eventually.of_forall fun p hp => hFbd i p.1 hp.1 p.2 hp.2
  -- each rung through LP and Fubini
  have hrung : ∀ i, ∫ x in W, eF c y x * (psi c (g i) x : ℂ) * (A x / qQ c (χ i) y x ^ (k + 1))
      = κ * ∫ s in Ioi (0 : ℝ), ∫ x in W, F i x s := by
    intro i
    rw [← integral_integral_swap (hFint i), ← integral_const_mul]
    refine setIntegral_congr_fun hW fun x hx => ?_
    have hlt : (qQ c (χ i) y x).re < 0 := by linarith [hreQi i x hx]
    rw [div_eq_mul_one_div (A x), laplace_inv_pow k hlt]
    simp only [hF]
    rw [integral_const_mul, ← hκ]
    ring
  have hFx : ∀ i, ∀ s ∈ Ioi (0 : ℝ), Integrable (fun x => F i x s) (volume.restrict W) := by
    intro i s hs
    have hb : Integrable (fun x => (|psi c (g i) x| * ‖A x‖) * (s ^ k * Real.exp (-(s * σ₀))))
        (volume.restrict W) := ((hψW i).abs.integrable_mul hA.norm).mul_const _
    have h1 : Continuous fun x => eF c y x * (psi c (g i) x : ℂ) := by
      have := (continuous_eF c y).1; have := hψc i; fun_prop
    have h2 : Continuous fun x => (s : ℂ) ^ k * cexp ((s : ℂ) * qQ c (χ i) y x) := by
      have := hQc (χ i); fun_prop
    exact Integrable.mono' hb ((h1.aestronglyMeasurable.mul hA.aestronglyMeasurable).mul h2.aestronglyMeasurable)
      ((ae_restrict_iff' hW).2 (Eventually.of_forall fun x hx => hFbd i x hx s hs))
  -- the `χ`-dependence factors through `Φ^{(s)}`
  set G : ℝ → ℂ := fun s => ∫ x in W, eF c y x * A x * ((s : ℂ) ^ k * cexp ((s : ℂ) * qQ c (c ^ 2) y x))
    * (phiLap c s χ g a x : ℂ) with hG
  have hsum_s : ∀ s ∈ Ioi (0 : ℝ), ∑ i, (a i : ℂ) * ∫ x in W, F i x s = G s := by
    intro s hs
    have hexp : ∀ i x, cexp ((s : ℂ) * qQ c (χ i) y x)
        = cexp ((s : ℂ) * qQ c (c ^ 2) y x) * ((Real.exp (-(s * (c ^ 2 - χ i))) : ℝ) : ℂ) := by
      intro i x; rw [hQi, Complex.ofReal_exp, ← Complex.exp_add]; congr 1; push_cast; ring
    simp_rw [← integral_const_mul]
    rw [← integral_finsetSum _ fun i _ => (hFx i s hs).const_mul _]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hF, phiLap, Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hexp]; push_cast; ring
  -- the bound for each `s`
  set B : ℝ → ℝ := fun s => s ^ k * Real.exp (-(s * σ₀))
    * √(∫ x in W, ‖A x‖ ^ 2 * Real.exp (2 * s * (qQ c (c ^ 2) y x).re)) with hB
  have hre_c : Continuous fun x => (qQ c (c ^ 2) y x).re := Complex.continuous_re.comp (hQc (c ^ 2))
  have hGb : ∀ s ∈ Ioi (0 : ℝ), ‖G s‖ ≤ B s * √P := by
    intro s hs
    have hs0 : (0 : ℝ) ≤ s := le_of_lt hs
    set u : ℝ → ℝ := fun x => ‖A x‖ * Real.exp (s * (qQ c (c ^ 2) y x).re) with hu
    have hu0 : ∀ x, 0 ≤ u x := fun x => by simp only [hu]; positivity
    have hum : AEStronglyMeasurable u (volume.restrict W) :=
      hA.aestronglyMeasurable.norm.mul (Real.continuous_exp.comp (continuous_const.mul hre_c)).aestronglyMeasurable
    have huL : MemLp u 2 (volume.restrict W) := by
      refine MemLp.of_le hA.norm hum ((ae_restrict_iff' hW).2 (Eventually.of_forall fun x hx => ?_))
      have he : Real.exp (s * (qQ c (c ^ 2) y x).re) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hs0 (hre x hx))
      rw [Real.norm_eq_abs, abs_of_nonneg (hu0 x), Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      simp only [hu]
      nlinarith [norm_nonneg (A x)]
    have hΦ1 : MemLp (phiLap c s χ g a) 2 (volume.restrict (Ioi 1)) :=
      memLp_finsetSum _ fun i _ => (hψ1 i).const_mul _
    have hΦW : MemLp (phiLap c s χ g a) 2 (volume.restrict W) :=
      hΦ1.mono_measure (Measure.restrict_mono hW1 le_rfl)
    have hCS := Cvs.L2a.FarFarBound.integral_mul_abs_le hu0 huL hΦW
    have h1 : ‖G s‖ ≤ s ^ k * ∫ x in W, u x * |phiLap c s χ g a x| := by
      rw [← integral_const_mul]
      refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae
        (Eventually.of_forall fun x => ?_)))
      simp only [hu, norm_mul, (continuous_eF c y).2, one_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hs0, Complex.norm_exp, Complex.re_ofReal_mul]
      ring
    have h2 : ∫ x in W, u x ^ 2 = ∫ x in W, ‖A x‖ ^ 2 * Real.exp (2 * s * (qQ c (c ^ 2) y x).re) :=
      integral_congr_ae (Eventually.of_forall fun x => by
        simp only [hu]; rw [mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf)
    have h3 : ∫ x in W, phiLap c s χ g a x ^ 2 ≤ ∫ x in Ioi 1, phiLap c s χ g a x ^ 2 :=
      setIntegral_mono_set ((memLp_two_iff_integrable_sq hΦ1.aestronglyMeasurable).mp hΦ1)
        (Eventually.of_forall fun x => sq_nonneg _) (Eventually.of_forall hW1)
    have h4 := integral_phiLap_sq_le a hg hg₁ hg₂c hang hc hχ hσ hs0
    have h5 : √(∫ x in W, phiLap c s χ g a x ^ 2) ≤ Real.exp (-(s * σ₀)) * √P := by
      calc √(∫ x in W, phiLap c s χ g a x ^ 2) ≤ √(Real.exp (-(2 * s * σ₀)) * P) :=
            Real.sqrt_le_sqrt (h3.trans h4)
        _ = Real.exp (-(s * σ₀)) * √P := by
          have e : Real.exp (-(2 * s * σ₀)) = Real.exp (-(s * σ₀)) ^ 2 := by
            rw [← Real.exp_nat_mul]; push_cast; ring_nf
          rw [Real.sqrt_mul (Real.exp_pos _).le, e, Real.sqrt_sq (Real.exp_pos _).le]
    rw [h2] at hCS
    have hsk : 0 ≤ s ^ k := pow_nonneg hs0 k
    calc ‖G s‖ ≤ s ^ k * ∫ x in W, u x * |phiLap c s χ g a x| := h1
      _ ≤ s ^ k * (√(∫ x in W, ‖A x‖ ^ 2 * Real.exp (2 * s * (qQ c (c ^ 2) y x).re))
            * √(∫ x in W, phiLap c s χ g a x ^ 2)) := mul_le_mul_of_nonneg_left hCS hsk
      _ ≤ s ^ k * (√(∫ x in W, ‖A x‖ ^ 2 * Real.exp (2 * s * (qQ c (c ^ 2) y x).re))
            * (Real.exp (-(s * σ₀)) * √P)) := by gcongr
      _ = B s * √P := by simp only [hB]; ring
  -- the `s`-integrand is integrable
  have hhi : ∀ s : ℝ, 0 ≤ s →
      Integrable (fun x => ‖A x‖ ^ 2 * Real.exp (2 * s * (qQ c (c ^ 2) y x).re)) (volume.restrict W) := by
    intro s hs
    refine Integrable.mono' hAn (hAn.1.mul (Real.continuous_exp.comp
      (continuous_const.mul hre_c)).aestronglyMeasurable)
      ((ae_restrict_iff' hW).2 (Eventually.of_forall fun x hx => ?_))
    have he : Real.exp (2 * s * (qQ c (c ^ 2) y x).re) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos (by positivity) (hre x hx))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg ‖A x‖, Real.exp_pos (2 * s * (qQ c (c ^ 2) y x).re)]
  have hanti : AntitoneOn (fun s => ∫ x in W, ‖A x‖ ^ 2 * Real.exp (2 * s * (qQ c (c ^ 2) y x).re)) (Ioi 0) := by
    intro s₁ hs₁ s₂ hs₂ h12
    refine setIntegral_mono_on (hhi s₂ (le_of_lt hs₂)) (hhi s₁ (le_of_lt hs₁)) hW fun x hx => ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (sq_nonneg _)
    nlinarith [hre x hx]
  have hhm := aemeasurable_restrict_of_antitoneOn (μ := volume) measurableSet_Ioi hanti
  have hle : ∀ s ∈ Ioi (0 : ℝ),
      ∫ x in W, ‖A x‖ ^ 2 * Real.exp (2 * s * (qQ c (c ^ 2) y x).re) ≤ ∫ x in W, ‖A x‖ ^ 2 := by
    intro s hs
    refine setIntegral_mono_on (hhi s (le_of_lt hs)) hAn hW fun x hx => ?_
    have he : Real.exp (2 * s * (qQ c (c ^ 2) y x).re) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos (by linarith [mem_Ioi.mp hs]) (hre x hx))
    nlinarith [sq_nonneg ‖A x‖]
  have hBi : IntegrableOn (fun s => B s * √P) (Ioi 0) := by
    have hb := hgs.mul_const (√(∫ x in W, ‖A x‖ ^ 2) * √P)
    have hm : AEStronglyMeasurable (fun s => B s * √P) (volume.restrict (Ioi 0)) := by
      have hc1 : Continuous fun s : ℝ => s ^ k * Real.exp (-(s * σ₀)) := by fun_prop
      exact ((hc1.aemeasurable.mul (Real.continuous_sqrt.measurable.comp_aemeasurable hhm)).mul_const
        _).aestronglyMeasurable
    refine Integrable.mono' hb hm ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_))
    have hs0 : (0 : ℝ) ≤ s := le_of_lt hs
    have hsq := Real.sqrt_le_sqrt (hle s hs)
    rw [Real.norm_eq_abs, abs_of_nonneg (by simp only [hB]; positivity)]
    simp only [hB]
    have : 0 ≤ s ^ k * Real.exp (-(s * σ₀)) := by positivity
    calc s ^ k * Real.exp (-(s * σ₀)) * √(∫ x in W, ‖A x‖ ^ 2 * Real.exp (2 * s * (qQ c (c ^ 2) y x).re)) * √P
        ≤ s ^ k * Real.exp (-(s * σ₀)) * √(∫ x in W, ‖A x‖ ^ 2) * √P := by gcongr
      _ = _ := by ring
  -- assemble
  have hL : ∑ i, (a i : ℂ) * ∫ x in W, eF c y x * (psi c (g i) x : ℂ) * (A x / qQ c (χ i) y x ^ (k + 1))
      = κ * ∫ s in Ioi (0 : ℝ), G s := by
    have hsi : ∀ i, Integrable (fun s => (a i : ℂ) * ∫ x in W, F i x s) (volume.restrict (Ioi 0)) := fun i =>
      ((hFint i).integral_prod_right).const_mul _
    simp_rw [hrung]
    rw [← setIntegral_congr_fun measurableSet_Ioi hsum_s, integral_finsetSum _ fun i _ => hsi i, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul]; ring
  have hκn : ‖κ‖ = 1 / (k.factorial : ℝ) := by
    rw [hκ, norm_div, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast]
  rw [hL, norm_mul, hκn, mul_assoc, ← integral_mul_const]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact norm_integral_le_of_norm_le hBi ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hGb))

end Cvs.L2a.SigmaSquareMultiplier
