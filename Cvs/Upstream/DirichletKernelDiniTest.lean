import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Dirichlet kernel, and Dini's test by Riemann–Lebesgue

`1 + 2Σ_{m=1}^M cos(2πmy) = sin((2M+1)πy)/sin(πy)`; for integrable `h`, `∫ h(y) sin((2M+1)πy) dy → 0`.
-/

namespace Cvs.Upstream.DirichletKernelDiniTest

open Real MeasureTheory Filter Topology
open scoped FourierTransform

/-- The Dirichlet kernel `D_M(y) = 1 + 2Σ_{m=1}^M cos(2πmy)`. -/
noncomputable def D (M : ℕ) (y : ℝ) : ℝ := 1 + 2 * ∑ m ∈ Finset.Icc 1 M, cos (2 * π * m * y)

/-- **The closed form**: `sin(πy) D_M(y) = sin((2M+1)πy)`. -/
theorem sin_mul_D (M : ℕ) (y : ℝ) : sin (π * y) * D M y = sin ((2 * M + 1) * π * y) := by
  induction M with
  | zero => simp [D]
  | succ M ih =>
    unfold D at ih ⊢
    rw [Finset.sum_Icc_succ_top (by omega)]
    have step : sin (π * y) * (2 * cos (2 * π * ((M + 1 : ℕ) : ℝ) * y))
        = sin ((2 * ((M + 1 : ℕ) : ℝ) + 1) * π * y) - sin ((2 * M + 1) * π * y) := by
      push_cast
      have h1 : (2 * ((M : ℝ) + 1) + 1) * π * y = (2 * (M + 1)) * π * y + π * y := by ring
      have h2 : (2 * (M : ℝ) + 1) * π * y = (2 * (M + 1)) * π * y - π * y := by ring
      have h3 : 2 * π * ((M : ℝ) + 1) * y = (2 * (M + 1)) * π * y := by ring
      rw [h1, h2, h3, sin_add, sin_sub]; ring
    calc sin (π * y) * (1 + 2 * (∑ m ∈ Finset.Icc 1 M, cos (2 * π * m * y) + cos (2 * π * ((M + 1 : ℕ) : ℝ) * y)))
        = sin (π * y) * (1 + 2 * ∑ m ∈ Finset.Icc 1 M, cos (2 * π * m * y))
          + sin (π * y) * (2 * cos (2 * π * ((M + 1 : ℕ) : ℝ) * y)) := by ring
      _ = sin ((2 * ((M + 1 : ℕ) : ℝ) + 1) * π * y) := by rw [ih, step]; ring

/-- **Riemann–Lebesgue, sine form**: `∫ h(y) sin((2M+1)πy) dy → 0` for integrable `h`. -/
theorem tendsto_integral_sin {h : ℝ → ℝ} (hh : Integrable h) :
    Tendsto (fun M : ℕ => ∫ y, h y * sin ((2 * M + 1) * π * y)) atTop (𝓝 0) := by
  have RL := Real.tendsto_integral_exp_smul_cocompact (fun v => (h v : ℂ))
  have hw : Tendsto (fun M : ℕ => ((2 * M + 1 : ℝ) / 2)) atTop (cocompact ℝ) := by
    apply Tendsto.mono_right _ atTop_le_cocompact
    apply Tendsto.atTop_div_const (by norm_num)
    exact tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
  have hc := ((Complex.continuous_im.tendsto 0).comp (RL.comp hw)).neg
  simp only [Complex.zero_im, neg_zero] at hc
  refine hc.congr fun M => ?_
  simp only [Function.comp]
  set w : ℝ := (2 * M + 1 : ℝ) / 2
  have hint : Integrable (fun v : ℝ => 𝐞 (-(v * w)) • (h v : ℂ)) := by
    refine hh.norm.mono' ?_ (Filter.Eventually.of_forall fun v => ?_)
    · exact ((Real.continuous_fourierChar.comp (by fun_prop : Continuous fun v : ℝ => -(v * w))).aestronglyMeasurable).smul
        hh.ofReal.aestronglyMeasurable
    · rw [Circle.norm_smul, Complex.norm_real]
  have him : (∫ v : ℝ, 𝐞 (-(v * w)) • (h v : ℂ)).im = ∫ v : ℝ, (𝐞 (-(v * w)) • (h v : ℂ)).im := by
    simpa using (integral_im hint).symm
  rw [him, ← integral_neg]
  congr 1; funext v
  rw [Circle.smul_def, Real.fourierChar_apply]
  simp only [smul_eq_mul, Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero]
  rw [show 2 * π * -(v * w) = -((2 * M + 1) * π * v) by simp only [w]; ring, sin_neg]
  ring

theorem integral_D (M : ℕ) : ∫ y in (-(1 / 2 : ℝ))..(1 / 2), D M y = 1 := by
  unfold D
  have hc : ∀ m ∈ Finset.Icc 1 M, ∫ y in (-(1 / 2 : ℝ))..(1 / 2), cos (2 * π * m * y) = 0 := by
    intro m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hk : (2 * π * m : ℝ) ≠ 0 := by positivity
    rw [intervalIntegral.integral_comp_mul_left (fun y => cos y) hk, integral_cos]
    have e1 : 2 * π * m * (1 / 2) = (m : ℝ) * π := by ring
    have e2 : 2 * π * m * (-(1 / 2)) = -((m : ℝ) * π) := by ring
    rw [e1, e2, sin_neg, sin_nat_mul_pi]; simp
  rw [intervalIntegral.integral_add (by simp) (by
      apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum (fun m _ => by
      apply Continuous.intervalIntegrable; fun_prop), Finset.sum_eq_zero hc]
  norm_num

/-- **Dini's test at `0`**: if `(P(y) − P(0))/sin(πy)` is integrable on `[−½, ½]`, the Dirichlet means converge. -/
theorem dini {P : ℝ → ℝ} (hP : IntervalIntegrable P volume (-(1 / 2 : ℝ)) (1 / 2))
    (hh : IntegrableOn (fun y => (P y - P 0) / sin (π * y)) (Set.Icc (-(1 / 2 : ℝ)) (1 / 2))) :
    Tendsto (fun M : ℕ => ∫ y in (-(1 / 2 : ℝ))..(1 / 2), P y * D M y) atTop (𝓝 (P 0)) := by
  set h := fun y => (P y - P 0) / sin (π * y) with hdef
  have hDc : ∀ M, Continuous (D M) := fun M => by unfold D; fun_prop
  -- the error is a sine integral of `h`
  have key : ∀ M : ℕ, ∫ y in (-(1 / 2 : ℝ))..(1 / 2), P y * D M y
      = P 0 + ∫ y, Set.indicator (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) h y * sin ((2 * M + 1) * π * y) := by
    intro M
    have hPD : IntervalIntegrable (fun y => P y * D M y) volume (-(1 / 2 : ℝ)) (1 / 2) :=
      hP.mul_continuousOn (hDc M).continuousOn
    have e1 : ∫ y in (-(1 / 2 : ℝ))..(1 / 2), P y * D M y
        = (∫ y in (-(1 / 2 : ℝ))..(1 / 2), (P y - P 0) * D M y) + P 0 * ∫ y in (-(1 / 2 : ℝ))..(1 / 2), D M y := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add]
      · congr 1; funext y; ring
      · exact (hP.sub intervalIntegrable_const).mul_continuousOn (hDc M).continuousOn
      · exact ((hDc M).const_smul (P 0)).intervalIntegrable _ _
    rw [e1, integral_D, mul_one, add_comm]
    congr 1
    rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc,
      ← integral_indicator measurableSet_Icc]
    congr 1; funext y
    by_cases hy : y ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2)
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
      by_cases hs : sin (π * y) = 0
      · have hy0 : y = 0 := by
          rcases (Real.sin_eq_zero_iff_of_lt_of_lt (by nlinarith [hy.1, pi_pos]) (by nlinarith [hy.2, pi_pos])).mp hs with h0
          · nlinarith [pi_pos, mul_eq_zero.mp h0]
        subst hy0; simp
      · rw [hdef]; simp only
        rw [← sin_mul_D M y]; field_simp
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, zero_mul]
  have hI : Integrable (Set.indicator (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) h) :=
    (integrable_indicator_iff measurableSet_Icc).mpr hh
  have hlim := (tendsto_integral_sin hI).const_add (P 0)
  rw [add_zero] at hlim
  exact hlim.congr fun M => (key M).symm

end Cvs.Upstream.DirichletKernelDiniTest
