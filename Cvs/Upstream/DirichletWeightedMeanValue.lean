import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.Harmonic.Bounds
import Cvs.Upstream.ExpSumIntervalMeanValue

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The `g^{−3/2}`-weighted mean value of a sum over the frequencies `log n`

Summing Cvs.Upstream.ExpSumIntervalMeanValue over the dyadic blocks `[2^k T, 2^{k+1} T]` gives
`∫_T^∞ ‖Σ_{n ≤ x} b_n e^{i(log n − L)g}‖² g^{−3/2} dg ≤ (Σ b_n²)(4T^{−1/2} + 2M T^{−3/2})`, `M = 4x(1 + log x)`.
-/

noncomputable section

open Real Set MeasureTheory Complex intervalIntegral Filter Topology

namespace Cvs.Upstream.DirichletWeightedMeanValue

/-- The exponential sum `J(g) = Σ_{n ≤ x} b_n e^{i(log n − L)g}`. -/
def expSum (x : ℕ) (b : ℕ → ℝ) (L g : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 x, (b n : ℂ) * Complex.exp ((Real.log n - L) * I * g)

theorem continuous_expSum (x : ℕ) (b : ℕ → ℝ) (L : ℝ) : Continuous (expSum x b L) := by
  unfold expSum; fun_prop

/-- `‖J(g)‖ ≤ Σ |b_n|`. -/
theorem norm_expSum_le (x : ℕ) (b : ℕ → ℝ) (L g : ℝ) : ‖expSum x b L g‖ ≤ ∑ n ∈ Finset.Icc 1 x, |b n| := by
  unfold expSum
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have : ‖Complex.exp ((Real.log n - L) * I * g)‖ = 1 := by
    rw [show ((Real.log n : ℂ) - L) * I * g = (((Real.log n - L) * g : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [this, mul_one]

/-- The weighted integrand is integrable on `(T, ∞)`. -/
theorem integrableOn_expSum {x : ℕ} (b : ℕ → ℝ) (L : ℝ) {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun g : ℝ => ‖expSum x b L g‖ ^ 2 * g ^ (-(3 / 2) : ℝ)) (Ioi T) := by
  set B := ∑ n ∈ Finset.Icc 1 x, |b n|
  have hdom : IntegrableOn (fun g : ℝ => B ^ 2 * g ^ (-(3 / 2) : ℝ)) (Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hT).const_mul _
  refine hdom.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun g (hg : T < g) => ?_))
  · exact ((continuous_expSum x b L).norm.pow 2).aestronglyMeasurable.mul
      ((continuousOn_id.rpow_const fun y hy => Or.inl (ne_of_gt (hT.trans hy))).aestronglyMeasurable
        measurableSet_Ioi)
  · have hg0 : 0 < g := hT.trans hg
    have hp : 0 ≤ g ^ (-(3 / 2) : ℝ) := Real.rpow_nonneg hg0.le _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hp)]
    have h1 : ‖expSum x b L g‖ ^ 2 ≤ B ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_expSum_le x b L g) 2
    exact mul_le_mul_of_nonneg_right h1 hp

/-- One dyadic block: `∫_{2^k T}^{2^{k+1} T} ‖J‖² g^{−3/2} ≤ (2^k T)^{−3/2}(2^k T + M)Σ b_n²`. -/
theorem block_le {x : ℕ} (b : ℕ → ℝ) (L : ℝ) {T : ℝ} (hT : 0 < T) (k : ℕ) :
    ∫ g in (2 : ℝ) ^ k * T..(2 : ℝ) ^ (k + 1) * T, ‖expSum x b L g‖ ^ 2 * g ^ (-(3 / 2) : ℝ)
      ≤ ((2 : ℝ) ^ k * T) ^ (-(3 / 2) : ℝ) * ((2 : ℝ) ^ k * T + 4 * x * (1 + Real.log x))
        * ∑ n ∈ Finset.Icc 1 x, b n ^ 2 := by
  set a₁ := (2 : ℝ) ^ k * T with ha₁
  set a₂ := (2 : ℝ) ^ (k + 1) * T with ha₂
  have h1 : 0 < a₁ := by positivity
  have h12 : a₁ ≤ a₂ := by rw [ha₁, ha₂, pow_succ]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) k]
  have hlen : a₂ - a₁ = a₁ := by rw [ha₁, ha₂, pow_succ]; ring
  have hmv := Cvs.Upstream.ExpSumIntervalMeanValue.integral_norm_sq_logSum_le (x := x) b L h12
  have hi1 : IntervalIntegrable (fun g : ℝ => ‖expSum x b L g‖ ^ 2 * g ^ (-(3 / 2) : ℝ)) volume a₁ a₂ :=
    ((continuous_expSum x b L).norm.pow 2).continuousOn.mul
      (continuousOn_id.rpow_const fun y hy => Or.inl (by
        rw [uIcc_of_le h12] at hy; exact ne_of_gt (h1.trans_le hy.1))) |>.intervalIntegrable
  have hi2 : IntervalIntegrable (fun g : ℝ => a₁ ^ (-(3 / 2) : ℝ) * ‖expSum x b L g‖ ^ 2) volume a₁ a₂ :=
    (((continuous_expSum x b L).norm.pow 2).const_mul _).intervalIntegrable _ _
  calc ∫ g in a₁..a₂, ‖expSum x b L g‖ ^ 2 * g ^ (-(3 / 2) : ℝ)
      ≤ ∫ g in a₁..a₂, a₁ ^ (-(3 / 2) : ℝ) * ‖expSum x b L g‖ ^ 2 := by
        refine intervalIntegral.integral_mono_on h12 hi1 hi2 fun g hg => ?_
        rw [mul_comm]
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        exact Real.rpow_le_rpow_of_nonpos h1 hg.1 (by norm_num)
    _ = a₁ ^ (-(3 / 2) : ℝ) * ∫ g in a₁..a₂, ‖expSum x b L g‖ ^ 2 := intervalIntegral.integral_const_mul _ _
    _ ≤ a₁ ^ (-(3 / 2) : ℝ) * ((a₂ - a₁ + 4 * x * (1 + Real.log x)) * ∑ n ∈ Finset.Icc 1 x, b n ^ 2) :=
        mul_le_mul_of_nonneg_left (by simpa [expSum] using hmv) (Real.rpow_nonneg h1.le _)
    _ = _ := by rw [hlen]; ring

/-- `(2^k T)^{−3/2}(2^k T + M) = T^{−1/2}(2^{−1/2})^k + M T^{−3/2}(2^{−3/2})^k`. -/
theorem block_coeff {T : ℝ} (hT : 0 < T) (k : ℕ) (M : ℝ) :
    ((2 : ℝ) ^ k * T) ^ (-(3 / 2) : ℝ) * ((2 : ℝ) ^ k * T + M)
      = T ^ (-(1 / 2) : ℝ) * ((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ k
        + M * T ^ (-(3 / 2) : ℝ) * ((2 : ℝ) ^ (-(3 / 2) : ℝ)) ^ k := by
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have e1 : ((2 : ℝ) ^ k * T) ^ (-(3 / 2) : ℝ) = ((2 : ℝ) ^ (-(3 / 2) : ℝ)) ^ k * T ^ (-(3 / 2) : ℝ) := by
    rw [Real.mul_rpow h2k.le hT.le, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_mul (by norm_num), mul_comm (k : ℝ)]
  have e2 : ((2 : ℝ) ^ (-(3 / 2) : ℝ)) ^ k * (2 : ℝ) ^ k = ((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ k := by
    rw [← mul_pow, ← Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0)]; norm_num
  have e3 : T ^ (-(3 / 2) : ℝ) * T = T ^ (-(1 / 2) : ℝ) := by
    rw [← Real.rpow_add_one hT.ne']; norm_num
  rw [e1]
  calc ((2 : ℝ) ^ (-(3 / 2) : ℝ)) ^ k * T ^ (-(3 / 2) : ℝ) * ((2 : ℝ) ^ k * T + M)
      = (((2 : ℝ) ^ (-(3 / 2) : ℝ)) ^ k * (2 : ℝ) ^ k) * (T ^ (-(3 / 2) : ℝ) * T)
        + M * T ^ (-(3 / 2) : ℝ) * ((2 : ℝ) ^ (-(3 / 2) : ℝ)) ^ k := by ring
    _ = _ := by rw [e2, e3]; ring

/-- `Σ_{k<K} r^k ≤ 1/(1 − r)` for `0 ≤ r < 1`. -/
theorem geom_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (K : ℕ) : ∑ k ∈ Finset.range K, r ^ k ≤ 1 / (1 - r) := by
  rw [geom_sum_eq h1.ne, le_div_iff₀ (by linarith)]
  have : 0 ≤ r ^ K := pow_nonneg h0 K
  rw [div_mul_eq_mul_div, div_le_one_of_neg (by linarith)]; nlinarith

/-- **The weighted mean value inequality**: `∫_T^∞ ‖Σ_{n ≤ x} b_n e^{i(log n − L)g}‖² g^{−3/2} dg
≤ (Σ b_n²)(4T^{−1/2} + 2·4x(1 + log x)·T^{−3/2})`. -/
theorem integral_expSum_le {x : ℕ} (b : ℕ → ℝ) (L : ℝ) {T : ℝ} (hT : 0 < T) :
    ∫ g in Ioi T, ‖expSum x b L g‖ ^ 2 * g ^ (-(3 / 2) : ℝ)
      ≤ (∑ n ∈ Finset.Icc 1 x, b n ^ 2)
        * (4 * T ^ (-(1 / 2) : ℝ) + 2 * (4 * x * (1 + Real.log x)) * T ^ (-(3 / 2) : ℝ)) := by
  set S := ∑ n ∈ Finset.Icc 1 x, b n ^ 2 with hS
  set M := 4 * (x : ℝ) * (1 + Real.log x) with hM
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hM0 : 0 ≤ M := by
    have := Real.log_natCast_nonneg x; positivity
  have hint := integrableOn_expSum (x := x) b L hT
  have htend : Tendsto (fun K : ℕ => (2 : ℝ) ^ K * T) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const hT
  have hlim := intervalIntegral_tendsto_integral_Ioi T hint htend
  refine le_of_tendsto' hlim fun K => ?_
  -- split `[T, 2^K T]` into the dyadic blocks
  have hsplit : ∫ g in T..(2 : ℝ) ^ K * T, ‖expSum x b L g‖ ^ 2 * g ^ (-(3 / 2) : ℝ)
      = ∑ k ∈ Finset.range K, ∫ g in (2 : ℝ) ^ k * T..(2 : ℝ) ^ (k + 1) * T,
          ‖expSum x b L g‖ ^ 2 * g ^ (-(3 / 2) : ℝ) := by
    have := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (a := fun k : ℕ => (2 : ℝ) ^ k * T)
      (f := fun g : ℝ => ‖expSum x b L g‖ ^ 2 * g ^ (-(3 / 2) : ℝ)) (n := K) (fun k _ => by
        have h1 : 0 < (2 : ℝ) ^ k * T := by positivity
        have h12 : (2 : ℝ) ^ k * T ≤ (2 : ℝ) ^ (k + 1) * T := by
          rw [pow_succ]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) k]
        exact ((continuous_expSum x b L).norm.pow 2).continuousOn.mul
          (continuousOn_id.rpow_const fun y hy => Or.inl (by
            rw [uIcc_of_le h12] at hy; exact ne_of_gt (h1.trans_le hy.1))) |>.intervalIntegrable)
    simpa using this.symm
  rw [hsplit]
  calc ∑ k ∈ Finset.range K, ∫ g in (2 : ℝ) ^ k * T..(2 : ℝ) ^ (k + 1) * T,
        ‖expSum x b L g‖ ^ 2 * g ^ (-(3 / 2) : ℝ)
      ≤ ∑ k ∈ Finset.range K, (T ^ (-(1 / 2) : ℝ) * ((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ k
          + M * T ^ (-(3 / 2) : ℝ) * ((2 : ℝ) ^ (-(3 / 2) : ℝ)) ^ k) * S := by
        refine Finset.sum_le_sum fun k _ => (block_le b L hT k).trans (le_of_eq ?_)
        rw [block_coeff hT k M]
    _ = S * (T ^ (-(1 / 2) : ℝ) * ∑ k ∈ Finset.range K, ((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ k
          + M * T ^ (-(3 / 2) : ℝ) * ∑ k ∈ Finset.range K, ((2 : ℝ) ^ (-(3 / 2) : ℝ)) ^ k) := by
        rw [← Finset.sum_mul, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring
    _ ≤ S * (T ^ (-(1 / 2) : ℝ) * 4 + M * T ^ (-(3 / 2) : ℝ) * 2) := by
        have hr1 : (2 : ℝ) ^ (-(1 / 2) : ℝ) ≤ 3 / 4 := by
          rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
          rw [inv_le_comm₀ (Real.sqrt_pos.2 (by norm_num)) (by norm_num)]
          rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
        have hr2 : (2 : ℝ) ^ (-(3 / 2) : ℝ) ≤ 1 / 2 := by
          rw [show (-(3 / 2) : ℝ) = -1 + -(1 / 2) by norm_num, Real.rpow_add (by norm_num), Real.rpow_neg_one]
          have h0 : 0 ≤ (2 : ℝ) ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg (by norm_num) _
          nlinarith
        have hp1 : 0 ≤ (2 : ℝ) ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg (by norm_num) _
        have hp2 : 0 ≤ (2 : ℝ) ^ (-(3 / 2) : ℝ) := Real.rpow_nonneg (by norm_num) _
        have g1 := geom_le hp1 (by linarith) K
        have g2 := geom_le hp2 (by linarith) K
        have g1' : ∑ k ∈ Finset.range K, ((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ k ≤ 4 :=
          g1.trans (by rw [div_le_iff₀ (by linarith)]; nlinarith)
        have g2' : ∑ k ∈ Finset.range K, ((2 : ℝ) ^ (-(3 / 2) : ℝ)) ^ k ≤ 2 :=
          g2.trans (by rw [div_le_iff₀ (by linarith)]; nlinarith)
        have hT1 : 0 ≤ T ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hT.le _
        have hT3 : 0 ≤ T ^ (-(3 / 2) : ℝ) := Real.rpow_nonneg hT.le _
        refine mul_le_mul_of_nonneg_left ?_ hS0
        exact add_le_add (mul_le_mul_of_nonneg_left g1' hT1) (mul_le_mul_of_nonneg_left g2' (by positivity))
    _ = _ := by ring

end Cvs.Upstream.DirichletWeightedMeanValue

end
