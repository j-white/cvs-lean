import Mathlib.Analysis.Fourier.PoissonSummation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Poisson duality for the map `E`

For `E f u = √u Σ_{n ≥ 1} f(nu)` and an even continuous `f` with `f(0) = 𝓕f(0) = 0` and `f`, `𝓕f` both
`O(|x|^{-b})`, `b > 1`, Poisson summation at the dilate `f(u·)` gives `E f u = E (𝓕f) (1/u)` for `u > 0`.
-/

noncomputable section

open Real Filter Asymptotics FourierTransform

namespace Cvs.Xi.PoissonDualitySummationE

/-- The map `E f u = √u Σ_{n ≥ 1} f(nu)`. -/
def E (f : ℝ → ℂ) (u : ℝ) : ℂ := (√u : ℂ) * ∑' n : ℕ+, f (n * u)

/-- The Fourier transform of a dilate: `𝓕(f(u·))(w) = u⁻¹ 𝓕f(w/u)` for `u > 0`. -/
theorem fourier_comp_mul (f : ℝ → ℂ) {u : ℝ} (hu : 0 < u) (w : ℝ) :
    𝓕 (fun x => f (u * x)) w = (u⁻¹ : ℂ) * 𝓕 f (w / u) := by
  rw [fourier_real_eq, fourier_real_eq]
  set g : ℝ → ℂ := fun y => 𝐞 (-(y * (w / u))) • f y
  have hg : (fun v : ℝ => 𝐞 (-(v * w)) • f (u * v)) = fun v => g (u * v) := by
    funext v; simp only [g]; congr 3; field_simp
  rw [hg, MeasureTheory.Measure.integral_comp_mul_left g u, abs_of_pos (inv_pos.2 hu), Complex.real_smul]
  push_cast; rfl

/-- Decay is preserved by a dilation. -/
theorem isBigO_comp_mul {f : ℝ → ℂ} {b : ℝ} (hf : f =O[cocompact ℝ] (|·| ^ (-b))) {u : ℝ} (hu : 0 < u) :
    (fun x => f (u * x)) =O[cocompact ℝ] (|·| ^ (-b)) := by
  have ht : Tendsto (fun x : ℝ => u * x) (cocompact ℝ) (cocompact ℝ) :=
    (Homeomorph.mulLeft₀ u hu.ne').isClosedEmbedding.tendsto_cocompact
  refine (hf.comp_tendsto ht).trans ?_
  refine IsBigO.of_bound (u ^ (-b)) (Eventually.of_forall fun x => ?_)
  simp only [Function.comp_apply]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), abs_mul, abs_of_pos hu,
    Real.mul_rpow hu.le (abs_nonneg x)]

/-- Even, summable over `ℤ`, vanishing at `0`: the sum over `ℤ` is twice the sum over `n ≥ 1`. -/
theorem tsum_int_eq_two_mul {g : ℤ → ℂ} (he : ∀ n, g (-n) = g n) (h0 : g 0 = 0) (hs : Summable g) :
    ∑' n : ℤ, g n = 2 * ∑' n : ℕ+, g n := by
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat (fun n => he n) hs, h0, zero_add, nsmul_eq_mul]; push_cast; ring

/-- **Poisson duality**: `E f u = E (𝓕f) (1/u)` for `u > 0`. -/
theorem E_eq_E_fourier {f : ℝ → ℂ} (hc : Continuous f) {b : ℝ} (hb : 1 < b)
    (hf : f =O[cocompact ℝ] (|·| ^ (-b))) (hFf : 𝓕 f =O[cocompact ℝ] (|·| ^ (-b)))
    (heven : ∀ x, f (-x) = f x) (hf0 : f 0 = 0) (hF0 : 𝓕 f 0 = 0) {u : ℝ} (hu : 0 < u) :
    E f u = E (𝓕 f) (1 / u) := by
  set g : ℝ → ℂ := fun x => f (u * x) with hgd
  have hgc : Continuous g := hc.comp (continuous_const.mul continuous_id)
  have hg := isBigO_comp_mul hf hu
  have hFg : 𝓕 g =O[cocompact ℝ] (|·| ^ (-b)) := by
    have h1 : 𝓕 g = fun w => (u⁻¹ : ℂ) * 𝓕 f (u⁻¹ * w) := by
      funext w; rw [hgd, fourier_comp_mul f hu w, div_eq_inv_mul]
    rw [h1]
    exact (isBigO_comp_mul hFf (inv_pos.2 hu)).const_mul_left _
  have hP := Real.tsum_eq_tsum_fourier_of_rpow_decay hgc hb hg hFg 0
  simp only [zero_add, QuotientAddGroup.mk_zero, fourier_eval_zero, mul_one] at hP
  -- both sides are even and vanish at `0`
  have hsg : Summable fun n : ℤ => g n :=
    summable_of_isBigO (Real.summable_abs_int_rpow hb) (hg.comp_tendsto Int.tendsto_coe_cofinite)
  have hsF : Summable fun n : ℤ => 𝓕 g n :=
    summable_of_isBigO (Real.summable_abs_int_rpow hb) (hFg.comp_tendsto Int.tendsto_coe_cofinite)
  have hFeven : ∀ w, 𝓕 f (-w) = 𝓕 f w := by
    intro w
    rw [fourier_real_eq, fourier_real_eq]
    rw [← MeasureTheory.integral_neg_eq_self]
    congr 1; funext v; rw [heven]; congr 2; ring
  have hL := tsum_int_eq_two_mul (g := fun n : ℤ => g n)
    (fun n => by simp only [hgd, Int.cast_neg, mul_neg, heven]) (by simp [hgd, hf0]) hsg
  have hR := tsum_int_eq_two_mul (g := fun n : ℤ => 𝓕 g n)
    (fun n => by
      simp only [hgd, fourier_comp_mul f hu, Int.cast_neg, neg_div, hFeven]) (by
      simp only [hgd, fourier_comp_mul f hu, Int.cast_zero, zero_div, hF0, mul_zero]) hsF
  rw [hL, hR] at hP
  have hP' : ∑' n : ℕ+, f (n * u) = (u⁻¹ : ℂ) * ∑' n : ℕ+, 𝓕 f (n * (1 / u)) := by
    have e1 : (fun n : ℕ+ => g ((n : ℤ) : ℝ)) = fun n : ℕ+ => f (n * u) := by
      funext n; simp only [hgd, Int.cast_natCast]; ring_nf
    have e2 : (fun n : ℕ+ => 𝓕 g ((n : ℤ) : ℝ)) = fun n : ℕ+ => (u⁻¹ : ℂ) * 𝓕 f (n * (1 / u)) := by
      funext n; simp only [hgd, Int.cast_natCast, fourier_comp_mul f hu]; ring_nf
    have := hP
    simp only [e1, e2, tsum_mul_left] at this
    linear_combination this / 2
  unfold E
  rw [hP']
  have hs : (√u : ℂ) * (u⁻¹ : ℂ) = (√(1 / u) : ℂ) := by
    rw [one_div, Real.sqrt_inv]
    have hsu : (0 : ℝ) < √u := Real.sqrt_pos.2 hu
    have : (u : ℂ) = (√u : ℂ) * (√u : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hu.le]
    rw [this]; push_cast
    field_simp
  rw [← mul_assoc, hs]

end Cvs.Xi.PoissonDualitySummationE
