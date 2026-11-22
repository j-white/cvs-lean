import Mathlib
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.LawRatioRecurrence
import Cvs.Upstream.ComplexArsinhStrip
import Cvs.Upstream.GammaIntegerStepRatio

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The two lines agree at infinity, in complex form

With `a = iz/2`, `x = 2 + 2K` and `y = x/(2c) + √((x/2c)² + 1)`: `m_G(½ + 2K)/m_G(½ + iz + 2K) = (2/c)^{−a} Γ(¼ + K)/Γ(¼ + K + a)`
and `exp(a ash(x/2c)) = y^a`, so by Cvs.Upstream.GammaIntegerStepRatio their product is `(cy/(2(K − 1)))^a (1 + o(1)) → 1`. With `WkbPhaseVerticalFar`'s vertical
steps, `p → 1`, `1 + r → 2` and `s mel(s) → h₀(1)` on both lines, the ratio
`Q_K = P(½ + iz + 2K) exp(Ψ(½ + 2K) − Ψ(½ + iz + 2K)) / P(½ + 2K) → 1`.
-/

noncomputable section

open Complex Filter Topology

namespace Cvs.Prolate.Mellin.TwoLinesAgreeComplex

open Cvs.Prolate.Mellin.RungThreeTermRecurrence (mel)
open Cvs.Prolate.Mellin.LawRatioRecurrence (mg lawRatio)
open Cvs.Prolate.Mellin.FrozenRootErrorIdentity (csqrt rhoStar)
open Cvs.Upstream.ComplexArsinhStrip (ash csqrt_ofReal)

/-- `ash` of a nonnegative real. -/
theorem ash_ofReal {t : ℝ} (ht : 0 ≤ t) : ash (t : ℂ) = ((Real.log (t + Real.sqrt (t ^ 2 + 1)) : ℝ) : ℂ) := by
  unfold ash
  rw [show (t : ℂ) ^ 2 + 1 = ((t ^ 2 + 1 : ℝ) : ℂ) by push_cast; ring, csqrt_ofReal (by positivity),
    ← Complex.ofReal_add, Complex.ofReal_log (by positivity)]

/-- `exp(a ash t) = (t + √(t² + 1))^a` for real `t ≥ 0`. -/
theorem exp_mul_ash {t : ℝ} (ht : 0 ≤ t) (a : ℂ) :
    Complex.exp (a * ash (t : ℂ)) = ((t + Real.sqrt (t ^ 2 + 1) : ℝ) : ℂ) ^ a := by
  have hpos : 0 < t + Real.sqrt (t ^ 2 + 1) := by
    have := Real.sqrt_pos.mpr (show (0 : ℝ) < t ^ 2 + 1 by positivity); linarith
  rw [ash_ofReal ht, cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'), ← Complex.ofReal_log hpos.le, mul_comm]

/-- The Gaussian reference ratio: `m_G(s)/m_G(s + 2a) = (2/c)^{−a} Γ(s/2)/Γ(s/2 + a)`. -/
theorem mg_ratio {c : ℝ} (hc : 0 < c) (s a : ℂ) :
    mg c s / mg c (s + 2 * a) = ((2 / c : ℝ) : ℂ) ^ (-a) * (Complex.Gamma (s / 2) / Complex.Gamma (s / 2 + a)) := by
  have h2c : ((2 / c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (div_pos two_pos hc).ne'
  unfold mg
  rw [show (s + 2 * a) / 2 = s / 2 + a by ring, cpow_add _ _ h2c, cpow_neg]
  have hp : ((2 / c : ℝ) : ℂ) ^ (s / 2) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl h2c)
  have hq : ((2 / c : ℝ) : ℂ) ^ a ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl h2c)
  by_cases hG : Complex.Gamma (s / 2 + a) = 0
  · rw [hG]; simp
  field_simp

/-- The real base `b_n = (x + √(x² + 4c²))/(4n)`, `x = 2n + 4`, tends to `1`. -/
theorem tendsto_base {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => ((2 * n + 4 : ℝ) + Real.sqrt ((2 * n + 4 : ℝ) ^ 2 + 4 * c ^ 2)) / (4 * n)) atTop (𝓝 1) := by
  have hlo : Tendsto (fun n : ℕ => (4 * (n : ℝ) + 8) / (4 * n)) atTop (𝓝 1) := by
    have : Tendsto (fun n : ℕ => 1 + 2 / (n : ℝ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have : (0 : ℝ) < n := by exact_mod_cast hn
    field_simp; ring
  have hhi : Tendsto (fun n : ℕ => (4 * (n : ℝ) + 8 + 2 * c) / (4 * n)) atTop (𝓝 1) := by
    have : Tendsto (fun n : ℕ => 1 + (8 + 2 * c) / (4 * (n : ℝ))) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.div_atTop
        (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)))
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have : (0 : ℝ) < n := by exact_mod_cast hn
    field_simp; ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have : (0 : ℝ) < n := by exact_mod_cast hn
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : 2 * (n : ℝ) + 4 ≤ Real.sqrt ((2 * n + 4) ^ 2 + 4 * c ^ 2) := by
      rw [Real.le_sqrt (by positivity) (by positivity)]; nlinarith
    linarith
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have : (0 : ℝ) < n := by exact_mod_cast hn
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : Real.sqrt ((2 * (n : ℝ) + 4) ^ 2 + 4 * c ^ 2) ≤ 2 * n + 4 + 2 * c := by
      rw [Real.sqrt_le_left (by positivity)]; nlinarith
    linarith

/-- **The main factor**: `m_G(s′)/m_G(s′ + iz) · exp(a ash(x/2c)) → 1` with `s′ = ½ + 2K`, `x = 2 + 2K`, `K = n + 1`. -/
theorem tendsto_main {c : ℝ} (hc : 0 < c) (z : ℝ) :
    Tendsto (fun n : ℕ => mg c ((1 / 2 : ℂ) + 2 * ((n + 1 : ℕ) : ℂ)) / mg c ((1 / 2 : ℂ) + I * z + 2 * ((n + 1 : ℕ) : ℂ))
      * Complex.exp (I * z / 2 * ash (((2 + 2 * (n + 1 : ℕ) : ℝ) : ℂ) / (2 * c)))) atTop (𝓝 1) := by
  set A : ℂ := I * z / 2
  -- the Gamma ratio, inverted
  have hG := Cvs.Upstream.GammaIntegerStepRatio.tendsto_Gamma_ratio (s := (1 / 4 : ℂ)) (a := A) (by norm_num)
    (by simp [A])
  have hGinv := hG.inv₀ (one_ne_zero)
  rw [inv_one] at hGinv
  -- the base
  have hb := tendsto_base hc
  have hbC : Tendsto (fun n : ℕ => (((((2 * n + 4 : ℝ) + Real.sqrt ((2 * n + 4 : ℝ) ^ 2 + 4 * c ^ 2)) / (4 * n) : ℝ) : ℂ) ^ A))
      atTop (𝓝 ((1 : ℂ) ^ A)) := by
    have h1 := (Complex.continuous_ofReal.tendsto 1).comp hb
    rw [Complex.ofReal_one] at h1
    exact ((continuousAt_cpow_const (b := A) (by simp [mem_slitPlane_iff])).tendsto).comp h1
  rw [one_cpow] at hbC
  have hprod := hbC.mul hGinv
  rw [mul_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc' : (0 : ℝ) < 2 * c := by positivity
  -- rewrite the left side
  rw [show (1 / 2 : ℂ) + I * z + 2 * ((n + 1 : ℕ) : ℂ) = ((1 / 2 : ℂ) + 2 * ((n + 1 : ℕ) : ℂ)) + 2 * A by
    simp only [A]; ring, mg_ratio hc]
  have hx : (((2 + 2 * (n + 1 : ℕ) : ℝ) : ℂ) / (2 * c)) = ((((2 * n + 4) / (2 * c)) : ℝ) : ℂ) := by
    push_cast; ring
  rw [hx, exp_mul_ash (by positivity)]
  have hs2 : ((1 / 2 : ℂ) + 2 * ((n + 1 : ℕ) : ℂ)) / 2 = 1 / 4 + ((n + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [hs2, show (1 / 4 : ℂ) + ((n + 1 : ℕ) : ℂ) + A = 1 / 4 + A + ((n + 1 : ℕ) : ℂ) by ring]
  -- the powers of positive reals
  set y := (2 * (n : ℝ) + 4) / (2 * c) + Real.sqrt (((2 * n + 4) / (2 * c)) ^ 2 + 1)
  have hy : 0 < y := by have := Real.sqrt_nonneg (((2 * (n : ℝ) + 4) / (2 * c)) ^ 2 + 1); positivity
  have hbase : (((2 * n + 4 : ℝ) + Real.sqrt ((2 * n + 4 : ℝ) ^ 2 + 4 * c ^ 2)) / (4 * n) : ℝ)
      = c / 2 * y * (1 / n) := by
    have hs : Real.sqrt ((2 * (n : ℝ) + 4) ^ 2 + 4 * c ^ 2) = 2 * c * Real.sqrt (((2 * n + 4) / (2 * c)) ^ 2 + 1) := by
      rw [show (2 * (n : ℝ) + 4) ^ 2 + 4 * c ^ 2 = (2 * c) ^ 2 * (((2 * n + 4) / (2 * c)) ^ 2 + 1) by field_simp; ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq hc'.le]
    simp only [y]; rw [hs]; field_simp; ring
  rw [hbase]
  have hpow : (((c / 2 * y * (1 / n) : ℝ) : ℂ) ^ A)
      = ((2 / c : ℝ) : ℂ) ^ (-A) * (y : ℂ) ^ A * ((n : ℂ) ^ A)⁻¹ := by
    rw [show ((c / 2 * y * (1 / n) : ℝ) : ℂ) = ((c / 2 * y : ℝ) : ℂ) * ((1 / n : ℝ) : ℂ) by push_cast; ring,
      mul_cpow_ofReal_nonneg (by positivity) (by positivity),
      show ((c / 2 * y : ℝ) : ℂ) = ((c / 2 : ℝ) : ℂ) * (y : ℂ) by push_cast; ring,
      mul_cpow_ofReal_nonneg (by positivity) hy.le, cpow_neg]
    have h1 : ((c / 2 : ℝ) : ℂ) = (((2 / c : ℝ) : ℂ))⁻¹ := by push_cast; field_simp
    have h2 : ((1 / (n : ℝ) : ℝ) : ℂ) = ((n : ℂ))⁻¹ := by push_cast; ring
    rw [h1, h2, inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg (by positivity)]; exact Real.pi_pos.ne),
      inv_cpow _ _ (by rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl,
        Complex.arg_ofReal_of_nonneg (by positivity)]; exact Real.pi_pos.ne)]
  rw [hpow]
  have hnA : (n : ℂ) ^ A ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hn.ne'))
  have hG1 : Complex.Gamma (1 / 4 + ((n + 1 : ℕ) : ℂ)) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; positivity)
  have hG2 : Complex.Gamma (1 / 4 + A + ((n + 1 : ℕ) : ℂ)) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp [A]; positivity)
  field_simp

end Cvs.Prolate.Mellin.TwoLinesAgreeComplex
