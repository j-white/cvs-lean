import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RungDecayBeyondEdge
import Cvs.Prolate.RungExactOrthogonality
import Cvs.Prolate.SlepianCommutingRelation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Bernstein's inequality on the exterior span, and its dilations

For `h = Σ f_iψ_i` over rungs with distinct levels in `[0, c²]` and `c ≥ 3`, integrating `(Uh/ξ²)′` from `1`
(`U = (ξ² − 1)h′` vanishes there) gives `∫_{36/25}^T h′² ≤ 9c²∫_{(1,∞)} h²`; with `Σ_k k⁻¹1[12k/25 < s ≤ 11k/10] ≤ 3`,
`Σ_{k=3}^{K}∫_{12/25}^{11/10}(h(kθ)² + c⁻²h′(kθ)²)dθ ≤ 30∫_{(1,∞)} h²`.
-/

noncomputable section

namespace Cvs.Prolate.ExteriorSpanBernstein

open Real Set Filter Topology MeasureTheory intervalIntegral
open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.Prolate.Gram.RungGramFloorAtInfinity (rungU rung_system)
open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval (pP qP)

variable {ι : Type*} [Fintype ι]

/-- A finite family of angular prolate solutions on `[−1, 1]` with levels `χ_i`. -/
def IsRungFamily (c : ℝ) (g g₁ g₂ : ι → ℝ → ℝ) (χ : ι → ℝ) : Prop :=
  (∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    ∧ (∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    ∧ (∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    ∧ (∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)

/-- The span element `h = Σ f_iψ_i`. -/
def spanH (c : ℝ) (g : ι → ℝ → ℝ) (f : ι → ℝ) (ξ : ℝ) : ℝ := ∑ i, f i * psi c (g i) ξ

/-- Its flux `U = Σ f_iu_i`, `u_i = (ξ² − 1)ψ_i'`. -/
def spanU (c : ℝ) (g : ι → ℝ → ℝ) (f : ι → ℝ) (ξ : ℝ) : ℝ := ∑ i, f i * rungU c (g i) ξ

variable {c : ℝ} {g g₁ g₂ : ι → ℝ → ℝ} {χ : ι → ℝ}

omit [Fintype ι] in
/-- The `(ψ, u)` system of each member. -/
theorem IsRungFamily.system (hF : IsRungFamily c g g₁ g₂ χ) (i : ι) :
    (∀ ξ, 1 < ξ → HasDerivAt (psi c (g i)) (rungU c (g i) ξ / pP ξ) ξ)
      ∧ (∀ ξ, HasDerivAt (rungU c (g i)) (-(qP c (χ i) ξ * psi c (g i) ξ)) ξ)
      ∧ Continuous (psi c (g i)) ∧ Continuous (rungU c (g i)) :=
  rung_system (hF.1 i) (hF.2.1 i) (hF.2.2.1 i) (hF.2.2.2 i)

/-- `h` is continuous. -/
theorem continuous_spanH (hF : IsRungFamily c g g₁ g₂ χ) (f : ι → ℝ) : Continuous (spanH c g f) :=
  continuous_finsetSum _ fun i _ => continuous_const.mul (hF.system i).2.2.1

/-- `U` is continuous. -/
theorem continuous_spanU (hF : IsRungFamily c g g₁ g₂ χ) (f : ι → ℝ) : Continuous (spanU c g f) :=
  continuous_finsetSum _ fun i _ => continuous_const.mul (hF.system i).2.2.2

/-- `h′ = U/(ξ² − 1)` on `ξ > 1`. -/
theorem hasDerivAt_spanH (hF : IsRungFamily c g g₁ g₂ χ) (f : ι → ℝ) {ξ : ℝ} (hξ : 1 < ξ) :
    HasDerivAt (spanH c g f) (spanU c g f ξ / pP ξ) ξ := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (A := fun i y => f i * psi c (g i) y)
    fun i _ => ((hF.system i).1 ξ hξ).const_mul (f i)
  refine h.congr_deriv ?_
  rw [spanU, Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `U′ = −c²ξ²h + h_χ`. -/
theorem hasDerivAt_spanU (hF : IsRungFamily c g g₁ g₂ χ) (f : ι → ℝ) (ξ : ℝ) :
    HasDerivAt (spanU c g f) (-(c ^ 2 * ξ ^ 2 * spanH c g f ξ) + spanH c g (fun i => f i * χ i) ξ) ξ := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (A := fun i y => f i * rungU c (g i) y)
    fun i _ => ((hF.system i).2.1 ξ).const_mul (f i)
  refine h.congr_deriv ?_
  simp only [spanH, qP, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `U(1) = 0`. -/
theorem spanU_one (f : ι → ℝ) : spanU c g f 1 = 0 := by
  simp [spanU, rungU, pP]

/-- **Exterior orthogonality on the span**: `∫_{(1,∞)} h² = Σ f_i² ∫_{(1,∞)} ψ_i²`. -/
theorem integral_spanH_sq (hF : IsRungFamily c g g₁ g₂ χ) (hc : 0 < c) (hinj : Function.Injective χ)
    (f : ι → ℝ) :
    ∫ ξ in Ioi 1, spanH c g f ξ ^ 2 = ∑ i, f i ^ 2 * ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2 :=
  Cvs.Prolate.RungExactOrthogonality.integral_span_sq f hF.1 hF.2.1 hF.2.2.1 hF.2.2.2 hc hinj

/-- Reweighting the span by `|w_i| ≤ W` multiplies the exterior mass by at most `W²`. -/
theorem integral_spanH_mul_sq_le (hF : IsRungFamily c g g₁ g₂ χ) (hc : 0 < c) (hinj : Function.Injective χ)
    (f w : ι → ℝ) {W : ℝ} (hw : ∀ i, |w i| ≤ W) :
    ∫ ξ in Ioi 1, spanH c g (fun i => f i * w i) ξ ^ 2 ≤ W ^ 2 * ∫ ξ in Ioi 1, spanH c g f ξ ^ 2 := by
  rw [integral_spanH_sq hF hc hinj, integral_spanH_sq hF hc hinj, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hm : 0 ≤ ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2 := setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have hw2 : w i ^ 2 ≤ W ^ 2 := sq_le_sq' (abs_le.mp (hw i)).1 (abs_le.mp (hw i)).2
  calc (f i * w i) ^ 2 * ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2 = w i ^ 2 * (f i ^ 2 * ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2) := by
        ring
    _ ≤ W ^ 2 * (f i ^ 2 * ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2) :=
        mul_le_mul_of_nonneg_right hw2 (mul_nonneg (sq_nonneg _) hm)

/-- `h ∈ L²(1, ∞)`. -/
theorem integrableOn_spanH_sq (hF : IsRungFamily c g g₁ g₂ χ) (hc : 0 < c) (f : ι → ℝ) :
    IntegrableOn (fun ξ => spanH c g f ξ ^ 2) (Ioi 1) := by
  have hm : MemLp (fun ξ => ∑ i, f i * psi c (g i) ξ) 2 (volume.restrict (Ioi 1)) :=
    memLp_finsetSum _ fun i _ =>
      (Cvs.Prolate.RungExactOrthogonality.memLp_psi (hF.1 i) (hF.2.1 i) (hF.2.2.1 i) (hF.2.2.2 i) hc).const_mul (f i)
  exact hm.integrable_sq

/-- The pointwise inequality behind Bernstein's bound. -/
theorem bern_pointwise {c ξ h hχ U : ℝ} (hc : 0 < c) (hξ : 1 < ξ) :
    c ^ 2 * h ^ 2 - hχ * h / ξ ^ 2 + 2 * U * h / ξ ^ 3
      ≤ U ^ 2 / (pP ξ * ξ ^ 2) / 2 + (3 * c ^ 2 / 2 + 2) * h ^ 2 + hχ ^ 2 / (2 * c ^ 2) := by
  have hp : 0 < pP ξ := Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP_pos hξ
  have hξ0 : 0 < ξ := by linarith
  have hp4 : pP ξ ≤ ξ ^ 4 := by unfold pP; nlinarith [sq_nonneg (ξ ^ 2 - 1)]
  have h1 : -(hχ * h / ξ ^ 2) ≤ c ^ 2 * h ^ 2 / 2 + hχ ^ 2 / (2 * c ^ 2) := by
    have hξ2 : 1 ≤ ξ ^ 2 := by nlinarith
    have a1 : -(hχ * h / ξ ^ 2) ≤ |hχ * h| := by
      rw [← neg_div]
      calc -(hχ * h) / ξ ^ 2 ≤ |hχ * h| / ξ ^ 2 := div_le_div_of_nonneg_right (neg_le_abs _) (by positivity)
        _ ≤ |hχ * h| := div_le_self (abs_nonneg _) hξ2
    have a2 : |hχ * h| ≤ c ^ 2 * h ^ 2 / 2 + hχ ^ 2 / (2 * c ^ 2) := by
      have hc2 : 0 < c ^ 2 := by positivity
      rw [abs_mul]
      have key : 0 ≤ (c ^ 2 * |h| - |hχ|) ^ 2 := sq_nonneg _
      have e : c ^ 2 * |h| ^ 2 / 2 + |hχ| ^ 2 / (2 * c ^ 2) - |hχ| * |h|
          = (c ^ 2 * |h| - |hχ|) ^ 2 / (2 * c ^ 2) := by
        field_simp; ring
      rw [sq_abs, sq_abs] at e
      have : 0 ≤ (c ^ 2 * |h| - |hχ|) ^ 2 / (2 * c ^ 2) := by positivity
      linarith
    linarith
  have h2 : 2 * U * h / ξ ^ 3 ≤ U ^ 2 / (pP ξ * ξ ^ 2) / 2 + 2 * h ^ 2 := by
    have e : U ^ 2 / (pP ξ * ξ ^ 2) / 2 + 2 * h ^ 2 * pP ξ / ξ ^ 4 - 2 * U * h / ξ ^ 3
        = (U - 2 * h * pP ξ / ξ) ^ 2 / (2 * pP ξ * ξ ^ 2) := by
      field_simp; ring
    have e2 : 2 * h ^ 2 * pP ξ / ξ ^ 4 ≤ 2 * h ^ 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg h]
    have : 0 ≤ (U - 2 * h * pP ξ / ξ) ^ 2 / (2 * pP ξ * ξ ^ 2) := by positivity
    linarith
  nlinarith

/-- **Bernstein on a finite exterior interval**: with `F = Uh/ξ²`,
`∫ₐᵀ U²/((ξ² − 1)ξ²) ≤ 2(|F(T)| + |F(a)|) + (3c² + 4)∫ₐᵀ h² + c⁻²∫ₐᵀ h_χ²`. -/
theorem bern_interval (hF : IsRungFamily c g g₁ g₂ χ) (f : ι → ℝ) {a T : ℝ} (ha : 1 < a) (haT : a ≤ T)
    (hc : 0 < c) :
    ∫ ξ in a..T, spanU c g f ξ ^ 2 / (pP ξ * ξ ^ 2)
      ≤ 2 * (|spanU c g f T * spanH c g f T / T ^ 2| + |spanU c g f a * spanH c g f a / a ^ 2|)
        + (3 * c ^ 2 + 4) * (∫ ξ in a..T, spanH c g f ξ ^ 2)
        + (∫ ξ in a..T, spanH c g (fun i => f i * χ i) ξ ^ 2) / c ^ 2 := by
  set h := spanH c g f with hh
  set U := spanU c g f with hU
  set hχ := spanH c g (fun i => f i * χ i) with hhχ
  have hmem : ∀ ξ ∈ uIcc a T, 1 < ξ := fun ξ hξ => by
    rw [uIcc_of_le haT] at hξ; linarith [hξ.1]
  have hpP : ContinuousOn pP (uIcc a T) := by unfold pP; fun_prop
  have hpne : ∀ ξ ∈ uIcc a T, pP ξ ≠ 0 := fun ξ hξ => (Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP_pos (hmem ξ hξ)).ne'
  have hξne : ∀ ξ ∈ uIcc a T, ξ ≠ 0 := fun ξ hξ => by linarith [hmem ξ hξ]
  have hcH : Continuous h := continuous_spanH hF f
  have hcU : Continuous U := continuous_spanU hF f
  have hcHχ : Continuous hχ := continuous_spanH hF (fun i => f i * χ i)
  set F : ℝ → ℝ := fun ξ => U ξ * h ξ / ξ ^ 2 with hFdef
  set F' : ℝ → ℝ := fun ξ =>
    ((-(c ^ 2 * ξ ^ 2 * h ξ) + hχ ξ) * h ξ + U ξ * (U ξ / pP ξ)) / ξ ^ 2 - U ξ * h ξ * (2 * ξ) / (ξ ^ 2) ^ 2
    with hF'def
  have hderiv : ∀ ξ ∈ uIcc a T, HasDerivAt F (F' ξ) ξ := by
    intro ξ hξ
    have h1 := (hasDerivAt_spanU hF f ξ).mul (hasDerivAt_spanH hF f (hmem ξ hξ))
    have h2 : HasDerivAt (fun ξ : ℝ => ξ ^ 2) (2 * ξ) ξ := by simpa using hasDerivAt_pow 2 ξ
    have h3 := h1.div h2 (pow_ne_zero 2 (hξne ξ hξ))
    refine h3.congr_deriv ?_
    have hx := hξne ξ hξ
    simp only [hF'def, Pi.mul_apply]
    field_simp
    ring
  have hF'c : ContinuousOn F' (uIcc a T) := by
    have h1 : Continuous fun ξ => (-(c ^ 2 * ξ ^ 2 * h ξ) + hχ ξ) * h ξ := by fun_prop
    have hN : ContinuousOn (fun ξ => (-(c ^ 2 * ξ ^ 2 * h ξ) + hχ ξ) * h ξ + U ξ * (U ξ / pP ξ))
        (uIcc a T) :=
      h1.continuousOn.add (hcU.continuousOn.mul (hcU.continuousOn.div₀ hpP hpne))
    have hD1 : ContinuousOn (fun ξ : ℝ => ξ ^ 2) (uIcc a T) := (continuous_pow 2).continuousOn
    have hN2 : ContinuousOn (fun ξ => U ξ * h ξ * (2 * ξ)) (uIcc a T) :=
      ((hcU.mul hcH).mul (continuous_const.mul continuous_id)).continuousOn
    have hD2 : ContinuousOn (fun ξ : ℝ => (ξ ^ 2) ^ 2) (uIcc a T) :=
      ((continuous_pow 2).pow 2).continuousOn
    exact (hN.div₀ hD1 fun ξ hξ => pow_ne_zero 2 (hξne ξ hξ)).sub
      (hN2.div₀ hD2 fun ξ hξ => pow_ne_zero 2 (pow_ne_zero 2 (hξne ξ hξ)))
  have hftc : ∫ ξ in a..T, F' ξ = F T - F a :=
    integral_eq_sub_of_hasDerivAt hderiv (hF'c.intervalIntegrable)
  -- the three pieces
  set I := ∫ ξ in a..T, U ξ ^ 2 / (pP ξ * ξ ^ 2) with hI
  have hsq : ContinuousOn (fun ξ : ℝ => ξ ^ 2) (uIcc a T) := (continuous_pow 2).continuousOn
  have hc1 : ContinuousOn (fun ξ => U ξ ^ 2 / (pP ξ * ξ ^ 2)) (uIcc a T) :=
    (hcU.continuousOn.pow 2).div₀ (hpP.mul hsq) fun ξ hξ => mul_ne_zero (hpne ξ hξ) (pow_ne_zero 2 (hξne ξ hξ))
  have hc2 : ContinuousOn (fun ξ => c ^ 2 * h ξ ^ 2 - hχ ξ * h ξ / ξ ^ 2 + 2 * U ξ * h ξ / ξ ^ 3) (uIcc a T) := by
    have hA : Continuous fun ξ => c ^ 2 * h ξ ^ 2 := by fun_prop
    have hB : ContinuousOn (fun ξ => hχ ξ * h ξ / ξ ^ 2) (uIcc a T) :=
      (hcHχ.mul hcH).continuousOn.div₀ hsq fun ξ hξ => pow_ne_zero 2 (hξne ξ hξ)
    have hC0 : Continuous fun ξ => 2 * U ξ * h ξ := by fun_prop
    have hcube : ContinuousOn (fun ξ : ℝ => ξ ^ 3) (uIcc a T) := (continuous_pow 3).continuousOn
    have hC : ContinuousOn (fun ξ => 2 * U ξ * h ξ / ξ ^ 3) (uIcc a T) :=
      hC0.continuousOn.div₀ hcube fun ξ hξ => pow_ne_zero 3 (hξne ξ hξ)
    exact (hA.continuousOn.sub hB).add hC
  have hsplit : ∫ ξ in a..T, F' ξ
      = I - ∫ ξ in a..T, (c ^ 2 * h ξ ^ 2 - hχ ξ * h ξ / ξ ^ 2 + 2 * U ξ * h ξ / ξ ^ 3) := by
    rw [hI, ← intervalIntegral.integral_sub hc1.intervalIntegrable hc2.intervalIntegrable]
    refine intervalIntegral.integral_congr fun ξ hξ => ?_
    have hp := hpne ξ hξ
    have hx := hξne ξ hξ
    simp only [hF'def]
    field_simp
    ring
  have hP2 : Continuous fun ξ => (3 * c ^ 2 / 2 + 2) * h ξ ^ 2 := by fun_prop
  have hP3 : Continuous fun ξ => hχ ξ ^ 2 / (2 * c ^ 2) := by fun_prop
  have hS2 : ContinuousOn (fun ξ => U ξ ^ 2 / (pP ξ * ξ ^ 2) / 2 + (3 * c ^ 2 / 2 + 2) * h ξ ^ 2)
      (uIcc a T) := (hc1.div_const 2).add hP2.continuousOn
  have hS3 : ContinuousOn (fun ξ => U ξ ^ 2 / (pP ξ * ξ ^ 2) / 2 + (3 * c ^ 2 / 2 + 2) * h ξ ^ 2
      + hχ ξ ^ 2 / (2 * c ^ 2)) (uIcc a T) := hS2.add hP3.continuousOn
  have hmono : ∫ ξ in a..T, (c ^ 2 * h ξ ^ 2 - hχ ξ * h ξ / ξ ^ 2 + 2 * U ξ * h ξ / ξ ^ 3)
      ≤ ∫ ξ in a..T, (U ξ ^ 2 / (pP ξ * ξ ^ 2) / 2 + (3 * c ^ 2 / 2 + 2) * h ξ ^ 2 + hχ ξ ^ 2 / (2 * c ^ 2)) := by
    refine intervalIntegral.integral_mono_on haT hc2.intervalIntegrable ?_ fun ξ hξ => ?_
    · exact hS3.intervalIntegrable
    · exact bern_pointwise hc (hmem ξ (by rw [uIcc_of_le haT]; exact hξ))
  have hlin : ∫ ξ in a..T, (U ξ ^ 2 / (pP ξ * ξ ^ 2) / 2 + (3 * c ^ 2 / 2 + 2) * h ξ ^ 2 + hχ ξ ^ 2 / (2 * c ^ 2))
      = I / 2 + (3 * c ^ 2 / 2 + 2) * (∫ ξ in a..T, h ξ ^ 2) + (∫ ξ in a..T, hχ ξ ^ 2) / (2 * c ^ 2) := by
    rw [intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_div,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_div]
    · exact (hc1.div_const 2).intervalIntegrable
    · exact hP2.intervalIntegrable _ _
    · exact hS2.intervalIntegrable
    · exact hP3.intervalIntegrable _ _
  have hFT : F T - F a ≤ |U T * h T / T ^ 2| + |U a * h a / a ^ 2| := by
    simp only [hFdef]
    have := le_abs_self (U T * h T / T ^ 2)
    have := neg_abs_le (U a * h a / a ^ 2)
    linarith
  have hc2pos : 0 < c ^ 2 := by positivity
  have e : (∫ ξ in a..T, hχ ξ ^ 2) / (2 * c ^ 2) = (∫ ξ in a..T, hχ ξ ^ 2) / c ^ 2 / 2 := by
    field_simp
  linarith

/-- The flux-mass product `Uh/ξ²` tends to `0` at infinity. -/
theorem tendsto_flux (hF : IsRungFamily c g g₁ g₂ χ) (hc : 0 < c) (f : ι → ℝ) :
    Tendsto (fun ξ => spanU c g f ξ * spanH c g f ξ / ξ ^ 2) atTop (𝓝 0) := by
  have hD : ∃ D, ∀ ξ, 1 ≤ ξ → |spanH c g f ξ| ≤ D / ξ := by
    refine ⟨∑ i, |f i| * (|g i 1 + g i (-1)| / c + (|g₁ i 1 - g₁ i (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ i s|) / c ^ 2),
      fun ξ hξ => ?_⟩
    rw [Finset.sum_div]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (Cvs.Prolate.RungDecayBeyondEdge.abs_psi_le (hF.1 i) (hF.2.1 i) (hF.2.2.1 i) hc hξ) (abs_nonneg _)
  have hK : ∃ K, ∀ ξ, 1 ≤ ξ → |spanU c g f ξ| ≤ K * ξ := by
    refine ⟨∑ i, |f i| * (2 * |g i 1 + g i (-1)| + (|g i 1 + g₁ i 1 + (g i (-1) - g₁ i (-1))|
      + ∫ s in (-1 : ℝ)..1, 2 * |g₁ i s| + |g₂ i s|) / c), fun ξ hξ => ?_⟩
    rw [Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (Cvs.Prolate.RungDecayBeyondEdge.abs_rungU_le (hF.1 i) (hF.2.1 i) (hF.2.2.1 i) hc hξ) (abs_nonneg _)
  obtain ⟨D, hD⟩ := hD
  obtain ⟨K, hK⟩ := hK
  have hlim : Tendsto (fun ξ : ℝ => K * D * (ξ ^ 2)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (two_ne_zero))).const_mul (K * D)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with ξ hξ
  have hξ0 : 0 < ξ := by linarith
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ξ ^ 2)]
  have h1 := hK ξ hξ
  have h2 := hD ξ hξ
  calc |spanU c g f ξ| * |spanH c g f ξ| / ξ ^ 2 ≤ K * ξ * (D / ξ) / ξ ^ 2 := by
        gcongr
        exact (abs_nonneg _).trans h1
    _ = K * D * (ξ ^ 2)⁻¹ := by field_simp

/-- **Bernstein's inequality on the exterior span**: for rungs with distinct levels in `[0, c²]` and `c ≥ 3`,
`∫_{36/25}^T h′² ≤ 9c²∫_{(1,∞)} h²`, with `h′ = U/(ξ² − 1)`. -/
theorem bernstein (hF : IsRungFamily c g g₁ g₂ χ) (hc : 3 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i ≤ c ^ 2)
    (hinj : Function.Injective χ) (f : ι → ℝ) {T : ℝ} (hT : 36 / 25 ≤ T) :
    ∫ ξ in (36 / 25 : ℝ)..T, (spanU c g f ξ / pP ξ) ^ 2 ≤ 9 * c ^ 2 * ∫ ξ in Ioi 1, spanH c g f ξ ^ 2 := by
  have hc0 : 0 < c := by linarith
  set N := ∫ ξ in Ioi 1, spanH c g f ξ ^ 2 with hN
  have hN0 : 0 ≤ N := setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have hNχ : ∫ ξ in Ioi 1, spanH c g (fun i => f i * χ i) ξ ^ 2 ≤ (c ^ 2) ^ 2 * N :=
    integral_spanH_mul_sq_le hF hc0 hinj f χ fun i => by rw [abs_of_nonneg (hχ0 i)]; exact hχc i
  set F : ℝ → ℝ := fun ξ => spanU c g f ξ * spanH c g f ξ / ξ ^ 2 with hFdef
  set K : ℝ := 1296 / 671
  -- the restricted integrals are at most the exterior masses
  have hsub : ∀ {a b : ℝ} (f' : ι → ℝ), 1 < a → a ≤ b →
      ∫ ξ in a..b, spanH c g f' ξ ^ 2 ≤ ∫ ξ in Ioi 1, spanH c g f' ξ ^ 2 := by
    intro a b f' ha hab
    rw [intervalIntegral.integral_of_le hab]
    exact setIntegral_mono_set (integrableOn_spanH_sq hF hc0 f')
      (ae_of_all _ fun _ => sq_nonneg _) (ae_of_all _ fun ξ (hξ : ξ ∈ Ioc a b) => (show ξ ∈ Ioi 1 from lt_of_lt_of_le ha (le_of_lt hξ.1))) |>.trans
      le_rfl
  have hmain : ∀ a T', 1 < a → a ≤ 36 / 25 → T ≤ T' →
      ∫ ξ in (36 / 25 : ℝ)..T, (spanU c g f ξ / pP ξ) ^ 2 ≤ K * (2 * (|F T'| + |F a|) + (4 * c ^ 2 + 4) * N) := by
    intro a T' ha ha' hT'
    have hpt : ∀ ξ ∈ Icc (36 / 25 : ℝ) T, (spanU c g f ξ / pP ξ) ^ 2 ≤ K * (spanU c g f ξ ^ 2 / (pP ξ * ξ ^ 2)) := by
      intro ξ hξ
      have hξ1 : (1296 / 625 : ℝ) ≤ ξ ^ 2 := by nlinarith [hξ.1]
      have hp : 0 < pP ξ := Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP_pos (by linarith [hξ.1])
      have hp' : pP ξ = ξ ^ 2 - 1 := rfl
      rw [div_pow, div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc, mul_comm K, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      rw [show K = 1296 / 671 from rfl]
      rw [inv_le_comm₀ (by positivity) (by positivity), mul_inv, inv_inv, inv_div]
      rw [hp']
      have : (ξ ^ 2 - 1) * ξ ^ 2 * (671 / 1296) ≤ (ξ ^ 2 - 1) ^ 2 := by nlinarith
      nlinarith
    have hcont : ContinuousOn (fun ξ => spanU c g f ξ ^ 2 / (pP ξ * ξ ^ 2)) (Icc a T') := by
      refine ((continuous_spanU hF f).continuousOn.pow 2).div (by unfold pP; fun_prop) fun ξ hξ => ?_
      exact mul_ne_zero (Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP_pos (by linarith [hξ.1])).ne' (pow_ne_zero 2 (by linarith [hξ.1] : (0 : ℝ) < ξ).ne')
    have hcont' : ContinuousOn (fun ξ => (spanU c g f ξ / pP ξ) ^ 2) (Icc (36 / 25) T) := by
      refine ((continuous_spanU hF f).continuousOn.div (by unfold pP; fun_prop) fun ξ hξ => ?_).pow 2
      exact (Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP_pos (by linarith [hξ.1])).ne'
    have h1 : ∫ ξ in (36 / 25 : ℝ)..T, (spanU c g f ξ / pP ξ) ^ 2
        ≤ ∫ ξ in (36 / 25 : ℝ)..T, K * (spanU c g f ξ ^ 2 / (pP ξ * ξ ^ 2)) :=
      intervalIntegral.integral_mono_on hT (hcont'.intervalIntegrable_of_Icc hT)
        ((hcont.mono (Icc_subset_Icc ha' hT')).const_smul K |>.intervalIntegrable_of_Icc hT) hpt
    have h2 : ∫ ξ in (36 / 25 : ℝ)..T, spanU c g f ξ ^ 2 / (pP ξ * ξ ^ 2)
        ≤ ∫ ξ in a..T', spanU c g f ξ ^ 2 / (pP ξ * ξ ^ 2) := by
      refine intervalIntegral.integral_mono_interval ha' hT hT' ?_ (hcont.intervalIntegrable_of_Icc (by linarith))
      refine ae_restrict_of_forall_mem measurableSet_Ioc fun ξ hξ => ?_
      have hp : 0 < pP ξ := Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP_pos (by linarith [hξ.1])
      have : 0 < ξ := by linarith [hξ.1]
      positivity
    have h3 := bern_interval hF f ha (by linarith) hc0 (T := T')
    have h4 := hsub f ha (show a ≤ T' by linarith)
    have h5 := hsub (fun i => f i * χ i) ha (show a ≤ T' by linarith)
    rw [intervalIntegral.integral_const_mul] at h1
    have hK0 : 0 ≤ K := by norm_num
    have hc2 : 0 < c ^ 2 := by positivity
    have h6 : (∫ ξ in a..T', spanH c g (fun i => f i * χ i) ξ ^ 2) / c ^ 2 ≤ c ^ 2 * N := by
      rw [div_le_iff₀ hc2]; nlinarith
    have h7 : (3 * c ^ 2 + 4) * (∫ ξ in a..T', spanH c g f ξ ^ 2) ≤ (3 * c ^ 2 + 4) * N :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    calc ∫ ξ in (36 / 25 : ℝ)..T, (spanU c g f ξ / pP ξ) ^ 2
        ≤ K * ∫ ξ in a..T', spanU c g f ξ ^ 2 / (pP ξ * ξ ^ 2) := h1.trans (mul_le_mul_of_nonneg_left h2 hK0)
      _ ≤ K * (2 * (|F T'| + |F a|) + (4 * c ^ 2 + 4) * N) := by
        refine mul_le_mul_of_nonneg_left ?_ hK0
        simp only [hFdef]
        linarith
  -- the limits `a → 1⁺` and `T' → ∞`
  have hF1 : Tendsto F (𝓝[>] 1) (𝓝 0) := by
    have hcont : ContinuousAt F 1 := by
      simp only [hFdef]
      exact ((continuous_spanU hF f).continuousAt.mul (continuous_spanH hF f).continuousAt).div
        (by fun_prop) (by norm_num)
    have h0 : F 1 = 0 := by simp [hFdef, spanU, rungU, pP]
    rw [← h0]
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hFinf : Tendsto F atTop (𝓝 0) := tendsto_flux hF hc0 f
  have hstep : ∀ T', T ≤ T' →
      ∫ ξ in (36 / 25 : ℝ)..T, (spanU c g f ξ / pP ξ) ^ 2 ≤ K * (2 * (|F T'| + 0) + (4 * c ^ 2 + 4) * N) := by
    intro T' hT'
    have hlim : Tendsto (fun a => K * (2 * (|F T'| + |F a|) + (4 * c ^ 2 + 4) * N)) (𝓝[>] 1)
        (𝓝 (K * (2 * (|F T'| + |(0 : ℝ)|) + (4 * c ^ 2 + 4) * N))) :=
      ((((tendsto_const_nhds.add hF1.abs).const_mul 2).add tendsto_const_nhds).const_mul K)
    rw [abs_zero] at hlim
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 36 / 25 by norm_num)] with a ha
    exact hmain a T' ha.1 ha.2.le hT'
  have hlimT : Tendsto (fun T' => K * (2 * (|F T'| + 0) + (4 * c ^ 2 + 4) * N)) atTop
      (𝓝 (K * (2 * (|(0 : ℝ)| + 0) + (4 * c ^ 2 + 4) * N))) :=
    (((hFinf.abs.add tendsto_const_nhds).const_mul 2).add tendsto_const_nhds).const_mul K
  have hfin := ge_of_tendsto hlimT (by filter_upwards [eventually_ge_atTop T] with T' hT' using hstep T' hT')
  have hc9 : K * (2 * (|(0 : ℝ)| + 0) + (4 * c ^ 2 + 4) * N) ≤ 9 * c ^ 2 * N := by
    rw [abs_zero]
    have : K * (4 * c ^ 2 + 4) ≤ 9 * c ^ 2 := by
      simp only [K]; nlinarith
    nlinarith
  exact hfin.trans hc9

/-- **The dilation weight**: `Σ_{k=3}^{K} k⁻¹·1[12k/25 < s ≤ 11k/10] ≤ 3`. -/
theorem dilWeight_le (K : ℕ) (s : ℝ) :
    ∑ k ∈ Finset.Icc 3 K, (if (k : ℝ) * (12 / 25) < s ∧ s ≤ (k : ℝ) * (11 / 10) then 1 / (k : ℝ) else 0) ≤ 3 := by
  rw [← Finset.sum_filter]
  set S := (Finset.Icc 3 K).filter fun k : ℕ => (k : ℝ) * (12 / 25) < s ∧ s ≤ (k : ℝ) * (11 / 10)
  rcases S.eq_empty_or_nonempty with hS | ⟨k₀, hk₀⟩
  · rw [hS, Finset.sum_empty]; norm_num
  have hk₀' := (Finset.mem_filter.mp hk₀)
  have hk03 : (3 : ℝ) ≤ k₀ := by exact_mod_cast (Finset.mem_Icc.mp hk₀'.1).1
  have hs : 36 / 25 < s := by linarith [hk₀'.2.1]
  have hs0 : 0 < s := by linarith
  have hterm : ∀ k ∈ S, 1 / (k : ℝ) ≤ 11 / 10 / s := by
    intro k hk
    have hk' := (Finset.mem_filter.mp hk).2
    have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
    rw [div_le_div_iff₀ (by linarith) hs0]
    linarith [hk'.2]
  have hsub : S ⊆ Finset.Icc ⌈s / (11 / 10)⌉₊ ⌊s / (12 / 25)⌋₊ := by
    intro k hk
    have hk' := (Finset.mem_filter.mp hk).2
    rw [Finset.mem_Icc]
    constructor
    · exact Nat.ceil_le.mpr (by rw [div_le_iff₀ (by norm_num)]; linarith [hk'.2])
    · exact Nat.le_floor (by rw [le_div_iff₀ (by norm_num)]; linarith [hk'.1])
  have hcard : (S.card : ℝ) ≤ s / (12 / 25) - s / (11 / 10) + 1 := by
    have h1 := Finset.card_le_card hsub
    rw [Nat.card_Icc] at h1
    have h2 : ((⌊s / (12 / 25)⌋₊ + 1 - ⌈s / (11 / 10)⌉₊ : ℕ) : ℝ) ≤ s / (12 / 25) - s / (11 / 10) + 1 := by
      have hf := Nat.floor_le (show 0 ≤ s / (12 / 25) by positivity)
      have hc := Nat.le_ceil (s / (11 / 10))
      rcases le_or_gt ⌈s / (11 / 10)⌉₊ (⌊s / (12 / 25)⌋₊ + 1) with h | h
      · rw [Nat.cast_sub h]; push_cast; linarith
      · rw [Nat.sub_eq_zero_of_le h.le]; push_cast
        have : s / (11 / 10) ≤ s / (12 / 25) := div_le_div_of_nonneg_left hs0.le (by norm_num) (by norm_num)
        linarith
    exact (Nat.cast_le.mpr h1).trans h2
  calc ∑ k ∈ S, 1 / (k : ℝ) ≤ ∑ _k ∈ S, 11 / 10 / s := Finset.sum_le_sum hterm
    _ = S.card * (11 / 10 / s) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (s / (12 / 25) - s / (11 / 10) + 1) * (11 / 10 / s) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 31 / 24 + 11 / 10 / s := by field_simp; ring
    _ ≤ 3 := by
        have : 11 / 10 / s ≤ 11 / 10 / (36 / 25) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs.le
        linarith

/-- **The dilation sum**: for `Φ ≥ 0` continuous on `[36/25, ∞)` and `K ≥ 3`,
`Σ_{k=3}^{K} ∫_{12/25}^{11/10} Φ(kθ) dθ ≤ 3∫_{36/25}^{11K/10} Φ`. -/
theorem sum_integral_dil_le {Φ : ℝ → ℝ} (hΦ : ∀ s, 0 ≤ Φ s) (hc : ContinuousOn Φ (Ici (36 / 25)))
    {K : ℕ} (hK : 3 ≤ K) :
    ∑ k ∈ Finset.Icc 3 K, ∫ θ in (12 / 25 : ℝ)..(11 / 10), Φ (k * θ)
      ≤ 3 * ∫ s in (36 / 25 : ℝ)..(11 / 10 * K), Φ s := by
  set L : ℝ := 36 / 25
  set U : ℝ := 11 / 10 * K
  have hK' : (3 : ℝ) ≤ K := by exact_mod_cast hK
  have hLU : L ≤ U := by simp only [L, U]; linarith
  have hint : IntegrableOn Φ (Ioc L U) :=
    (hc.mono (Icc_subset_Ici_self)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  set fk : ℕ → ℝ → ℝ := fun k => (Ioc ((k : ℝ) * (12 / 25)) ((k : ℝ) * (11 / 10))).indicator
    (fun s => (k : ℝ)⁻¹ * Φ s) with hfk
  have hk : ∀ k ∈ Finset.Icc 3 K, ∫ θ in (12 / 25 : ℝ)..(11 / 10), Φ (k * θ) = ∫ s in Ioc L U, fk k s := by
    intro k hkm
    have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hkm).1
    have hkK : (k : ℝ) ≤ K := by exact_mod_cast (Finset.mem_Icc.mp hkm).2
    rw [intervalIntegral.integral_comp_mul_left _ (by positivity : (k : ℝ) ≠ 0),
      intervalIntegral.integral_of_le (by nlinarith), smul_eq_mul]
    rw [hfk, MeasureTheory.integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
      MeasureTheory.integral_const_mul]
    congr 2
    rw [Set.inter_eq_left.mpr]
    exact Ioc_subset_Ioc (by simp only [L]; nlinarith) (by simp only [U]; nlinarith)
  have hfi : ∀ k ∈ Finset.Icc 3 K, IntegrableOn (fk k) (Ioc L U) := fun k _ =>
    (hint.const_mul _).indicator measurableSet_Ioc
  rw [Finset.sum_congr rfl hk, ← MeasureTheory.integral_finsetSum _ hfi]
  rw [intervalIntegral.integral_of_le hLU, ← MeasureTheory.integral_const_mul]
  refine setIntegral_mono_on (integrable_finsetSum _ hfi) (hint.const_mul 3) measurableSet_Ioc fun s _ => ?_
  have e : ∑ k ∈ Finset.Icc 3 K, fk k s
      = (∑ k ∈ Finset.Icc 3 K, (if (k : ℝ) * (12 / 25) < s ∧ s ≤ (k : ℝ) * (11 / 10) then 1 / (k : ℝ) else 0))
        * Φ s := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hfk, Set.indicator, Set.mem_Ioc]
    split_ifs <;> simp [one_div]
  rw [e]
  exact mul_le_mul_of_nonneg_right (dilWeight_le K s) (hΦ s)

/-- A finite piece of the exterior mass is at most the whole. -/
theorem integral_spanH_sq_le (hF : IsRungFamily c g g₁ g₂ χ) (hc : 0 < c) (f : ι → ℝ) {a b : ℝ}
    (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ ξ in a..b, spanH c g f ξ ^ 2 ≤ ∫ ξ in Ioi 1, spanH c g f ξ ^ 2 := by
  rw [intervalIntegral.integral_of_le hab]
  exact setIntegral_mono_set (integrableOn_spanH_sq hF hc f)
    (ae_of_all _ fun _ => sq_nonneg _) (ae_of_all _ fun ξ hξ => lt_of_le_of_lt ha hξ.1)

/-- **The dilated energy of a span element**: for `K ≥ 3`,
`Σ_{k=3}^{K} ∫_{12/25}^{11/10} (h(kθ)² + c⁻²h′(kθ)²) dθ ≤ 30∫_{(1,∞)} h²`. -/
theorem sum_integral_energy_le (hF : IsRungFamily c g g₁ g₂ χ) (hc : 3 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i)
    (hχc : ∀ i, χ i ≤ c ^ 2) (hinj : Function.Injective χ) (f : ι → ℝ) {K : ℕ} (hK : 3 ≤ K) :
    ∑ k ∈ Finset.Icc 3 K, ∫ θ in (12 / 25 : ℝ)..(11 / 10),
        (spanH c g f (k * θ) ^ 2 + (spanU c g f (k * θ) / pP (k * θ)) ^ 2 / c ^ 2)
      ≤ 30 * ∫ ξ in Ioi 1, spanH c g f ξ ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hK' : (3 : ℝ) ≤ K := by exact_mod_cast hK
  have hT : (36 / 25 : ℝ) ≤ 11 / 10 * K := by linarith
  have hcont : ContinuousOn (fun s => spanH c g f s ^ 2 + (spanU c g f s / pP s) ^ 2 / c ^ 2) (Ici (36 / 25)) := by
    refine ((continuous_spanH hF f).pow 2).continuousOn.add (ContinuousOn.div_const (ContinuousOn.pow ?_ 2) _)
    refine (continuous_spanU hF f).continuousOn.div (by unfold pP; fun_prop) fun s hs => ?_
    exact (Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP_pos (by linarith [mem_Ici.mp hs])).ne'
  refine (sum_integral_dil_le (fun s => by positivity) hcont hK).trans ?_
  have hcI : ContinuousOn (fun s => (spanU c g f s / pP s) ^ 2) (uIcc (36 / 25) (11 / 10 * K)) := by
    refine ((continuous_spanU hF f).continuousOn.div (by unfold pP; fun_prop) fun s hs => ?_).pow 2
    rw [uIcc_of_le hT] at hs
    exact (Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP_pos (by linarith [hs.1])).ne'
  have hi1 : IntervalIntegrable (fun s => spanH c g f s ^ 2) volume (36 / 25) (11 / 10 * K) :=
    ((continuous_spanH hF f).pow 2).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hi1 (hcI.div_const _).intervalIntegrable, intervalIntegral.integral_div]
  have h1 := integral_spanH_sq_le hF hc0 f (by norm_num : (1 : ℝ) ≤ 36 / 25) hT
  have h2 := bernstein hF hc hχ0 hχc hinj f hT
  have hc2 : 0 < c ^ 2 := by positivity
  have h3 : (∫ s in (36 / 25 : ℝ)..(11 / 10 * K), (spanU c g f s / pP s) ^ 2) / c ^ 2
      ≤ 9 * ∫ ξ in Ioi 1, spanH c g f ξ ^ 2 := by
    rw [div_le_iff₀ hc2]; linarith
  linarith

end Cvs.Prolate.ExteriorSpanBernstein
