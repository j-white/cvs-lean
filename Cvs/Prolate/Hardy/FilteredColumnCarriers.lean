import Mathlib
import Cvs.Prolate.Hardy.AveragedColumnEnergy
import Cvs.Prolate.Hardy.ColumnRungCoefficients
import Cvs.Prolate.Hardy.FourierDefectColumns
import Cvs.Prolate.Hardy.OddCrossLaplaceAmplitude
import Cvs.Prolate.SincTopIsRung

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The filtered exterior column is a sum of two carriers with Laplace amplitudes

For `u > 1` and `|x| < 1`, `Fe_u(x) = Re[P_u(x)e^{icx}] + Re[N_u(x)e^{−icx}]` exactly, where `P_u`, `N_u` are
combinations of `G_c(u ∓ 1, 1 ± z)`, from `∫_{−1}^{1} e^{icqt}/(u − t) dt = e^{icq}G_c(u−1, q) − e^{−icq}G_c(u+1, q)`.
-/

noncomputable section

open Real Set MeasureTheory Filter intervalIntegral
open Complex (I)

namespace Cvs.Prolate.Hardy.FilteredColumnCarriers
open Cvs.ZeroCounting

open Cvs.Prolate.Hardy.OddCrossLaplaceAmplitude (lapG)
open Cvs.Prolate.Hardy.FourierDefectColumns (Fop cosT evenCol)
open Cvs.Prolate.Hardy.ColumnRungCoefficients (eC)

/-- **The Laplace identity**: `∫_{−1}^{1} e^{icqt}/(u − t) dt = e^{icq}G_c(u−1, q) − e^{−icq}G_c(u+1, q)`. -/
theorem laplace_Iq {c u q : ℝ} (hc : 0 < c) (hu : 1 < u) (hq : 0 < q) :
    ∫ t in (-1 : ℝ)..1, Complex.exp (I * (c * q * t)) / (u - t) =
      Complex.exp (I * (c * q)) * lapG c (u - 1) q - Complex.exp (-(I * (c * q))) * lapG c (u + 1) q := by
  have hqre : 0 < (q : ℂ).re := by simpa using hq
  set f : ℝ → ℝ → ℂ := fun t v => Complex.exp (I * (c * q * t)) * (Real.exp (-(u - t) * v) : ℂ) with hf
  have h1 : ∀ t ∈ Ioc (-1 : ℝ) 1, Complex.exp (I * (c * q * t)) / (u - t) = ∫ v in Ioi (0 : ℝ), f t v := by
    intro t ht
    have := Cvs.Prolate.Hardy.AveragedColumnEnergy.integral_laplace (t := t) (u := u) (by linarith [ht.2])
    simp only [hf]
    rw [MeasureTheory.integral_const_mul, integral_complex_ofReal, this]; push_cast; ring
  have hint : Integrable (Function.uncurry f)
      ((volume.restrict (Ioc (-1 : ℝ) 1)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have hg : Integrable (fun p : ℝ × ℝ => (1 : ℝ) * Real.exp (-(u - 1) * p.2))
        ((volume.restrict (Ioc (-1 : ℝ) 1)).prod (volume.restrict (Ioi (0 : ℝ)))) :=
      (integrable_const (1 : ℝ)).mul_prod (exp_neg_integrableOn_Ioi (0 : ℝ) (by linarith : 0 < u - 1))
    refine hg.mono' ?_ ?_
    · exact (by fun_prop : Continuous (Function.uncurry f)).aestronglyMeasurable
    · have hae : ∀ᵐ p ∂((volume.restrict (Ioc (-1 : ℝ) 1)).prod (volume.restrict (Ioi (0 : ℝ)))),
          p ∈ Ioc (-1 : ℝ) 1 ×ˢ Ioi 0 := by
        rw [Measure.prod_restrict]; exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioi)
      filter_upwards [hae] with p hp
      obtain ⟨ht, hv⟩ := hp
      simp only [Function.uncurry, hf, norm_mul, Complex.norm_real, Real.norm_eq_abs, one_mul,
        abs_of_pos (Real.exp_pos _)]
      rw [show I * ((c : ℂ) * q * p.1) = ((c * q * p.1 : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, one_mul]
      refine Real.exp_le_exp.2 ?_
      have : 0 ≤ (1 - p.1) * p.2 := mul_nonneg (by linarith [ht.2]) (le_of_lt hv)
      nlinarith
  have h2 : ∀ v ∈ Ioi (0 : ℝ), ∫ t in Ioc (-1 : ℝ) 1, f t v =
      Complex.exp (I * (c * q)) * ((Real.exp (-(u - 1) * v) : ℂ) / ((v : ℂ) + I * c * q)) -
        Complex.exp (-(I * (c * q))) * ((Real.exp (-(u + 1) * v) : ℂ) / ((v : ℂ) + I * c * q)) := by
    intro v hv
    have hne := Cvs.Prolate.Hardy.OddCrossLaplaceAmplitude.den_ne_zero hc v hqre
    rw [← intervalIntegral.integral_of_le (by norm_num)]
    have e0 : ∀ t : ℝ, f t v = Complex.exp ((-(u * v) : ℝ)) * Complex.exp (((v : ℂ) + I * c * q) * t) := by
      intro t
      simp only [hf]
      rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
    simp_rw [e0]
    rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hne]
    have e1 : Complex.exp ((-(u * v) : ℝ)) * Complex.exp (((v : ℂ) + I * c * q) * ((1 : ℝ) : ℂ)) =
        Complex.exp (I * (c * q)) * (Real.exp (-(u - 1) * v) : ℂ) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
    have e2 : Complex.exp ((-(u * v) : ℝ)) * Complex.exp (((v : ℂ) + I * c * q) * ((-1 : ℝ) : ℂ)) =
        Complex.exp (-(I * (c * q))) * (Real.exp (-(u + 1) * v) : ℂ) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
    calc Complex.exp ((-(u * v) : ℝ)) * ((Complex.exp (((v : ℂ) + I * c * q) * ((1 : ℝ) : ℂ)) -
          Complex.exp (((v : ℂ) + I * c * q) * ((-1 : ℝ) : ℂ))) / ((v : ℂ) + I * c * q))
        = (Complex.exp ((-(u * v) : ℝ)) * Complex.exp (((v : ℂ) + I * c * q) * ((1 : ℝ) : ℂ)) -
          Complex.exp ((-(u * v) : ℝ)) * Complex.exp (((v : ℂ) + I * c * q) * ((-1 : ℝ) : ℂ))) /
            ((v : ℂ) + I * c * q) := by ring
      _ = _ := by rw [e1, e2]; ring
  rw [intervalIntegral.integral_of_le (by norm_num), setIntegral_congr_fun measurableSet_Ioc h1,
    integral_integral_swap hint, setIntegral_congr_fun measurableSet_Ioi h2,
    integral_sub ((Cvs.Prolate.Hardy.OddCrossLaplaceAmplitude.integrableOn_integrand hc (by linarith) hqre).const_mul _)
      ((Cvs.Prolate.Hardy.OddCrossLaplaceAmplitude.integrableOn_integrand hc (by linarith) hqre).const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rfl

theorem continuousOn_kernel {c u q : ℝ} (hu : 1 < u) :
    ContinuousOn (fun t : ℝ => Complex.exp (-(I * (c * u))) * (Complex.exp (I * (c * q * t)) / (u - t)))
      (uIcc (-1) 1) := by
  refine continuousOn_const.mul (ContinuousOn.div₀ (by fun_prop) (by fun_prop) fun t ht => ?_)
  rw [uIcc_of_le (by norm_num)] at ht
  rw [sub_ne_zero]
  exact fun h => by have := congrArg Complex.re h; simp at this; linarith [ht.2]

/-- `∫_{−1}^{1} sin(c(qt − u))/(u − t) dt = Im[e^{−icu}∫_{−1}^{1} e^{icqt}/(u − t) dt]`. -/
theorem integral_sin_div {c u q : ℝ} (hu : 1 < u) :
    ∫ t in (-1 : ℝ)..1, Real.sin (c * (q * t - u)) / (u - t) =
      (Complex.exp (-(I * (c * u))) * ∫ t in (-1 : ℝ)..1, Complex.exp (I * (c * q * t)) / (u - t)).im := by
  have him := intervalIntegral_im (𝕜 := ℂ) (μ := volume) ((continuousOn_kernel (c := c) (q := q) hu).intervalIntegrable)
  simp only [RCLike.im_to_complex] at him
  rw [← intervalIntegral.integral_const_mul, ← him]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [mul_div_assoc', ← Complex.exp_add,
    show -(I * (c * u)) + I * (c * q * t) = ((c * (q * t - u) : ℝ) : ℂ) * I by push_cast; ring,
    show (u : ℂ) - t = ((u - t : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_im, Complex.exp_ofReal_mul_I_im]

/-- The normalisation `κ_c = √(c/2π)/(2π)` of the filtered column. -/
def kap (c : ℝ) : ℝ := √(c / (2 * π)) / (2 * π)

/-- The positive-carrier amplitude `P_u(z) = iκ_c(e^{ic(1−u)}G_c(u−1, 1+z) − e^{−ic(1+u)}G_c(u+1, 1−z))`. -/
def posAmp (c u : ℝ) (z : ℂ) : ℂ :=
  kap c * I * (Complex.exp (I * (c * (1 - u))) * lapG c (u - 1) (1 + z) -
    Complex.exp (-(I * (c * (1 + u)))) * lapG c (u + 1) (1 - z))

/-- The negative-carrier amplitude `N_u(z) = iκ_c(e^{ic(1−u)}G_c(u−1, 1−z) − e^{−ic(1+u)}G_c(u+1, 1+z))`. -/
def negAmp (c u : ℝ) (z : ℂ) : ℂ :=
  kap c * I * (Complex.exp (I * (c * (1 - u))) * lapG c (u - 1) (1 - z) -
    Complex.exp (-(I * (c * (1 + u)))) * lapG c (u + 1) (1 + z))

theorem intervalIntegrable_sinc_cos {c u x : ℝ} (hu : 1 < u) :
    IntervalIntegrable (fun t => Real.sin (c * (t - u)) / (π * (t - u)) * Real.cos (c * x * t)) volume (-1) 1 := by
  refine ContinuousOn.intervalIntegrable (ContinuousOn.fun_mul (ContinuousOn.div₀ (by fun_prop) (by fun_prop)
    fun t ht => ?_) (by fun_prop))
  rw [uIcc_of_le (by norm_num)] at ht
  exact mul_ne_zero Real.pi_pos.ne' (by linarith [ht.2])

theorem intervalIntegrable_sin_div {c u q : ℝ} (hu : 1 < u) :
    IntervalIntegrable (fun t => Real.sin (c * (q * t - u)) / (u - t)) volume (-1) 1 := by
  refine ContinuousOn.intervalIntegrable (ContinuousOn.div₀ (by fun_prop) (by fun_prop) fun t ht => ?_)
  rw [uIcc_of_le (by norm_num)] at ht
  linarith [ht.2]

/-- **The exact two-carrier formula** `Fe_u(x) = Re[P_u(x)e^{icx}] + Re[N_u(x)e^{−icx}]` for `u > 1`, `|x| < 1`. -/
theorem Fop_eC_eq {c u x : ℝ} (hc : 0 < c) (hu : 1 < u) (hx : |x| < 1) :
    Fop c (eC c u) x = (posAmp c u x * Complex.exp (I * (c * x))).re +
      (negAmp c u x * Complex.exp (-(I * (c * x)))).re := by
  obtain ⟨hx1, hx2⟩ := abs_lt.1 hx
  set g : ℝ → ℝ := fun t => Real.sin (c * (t - u)) / (π * (t - u)) * Real.cos (c * x * t) with hg
  -- the clamped column is the even column on `[−1, 1]`, whose cosine transform is that of `k_u`
  have hA : cosT (eC c u) (c * x) = ∫ t in (-1 : ℝ)..1, g t := by
    have e1 : cosT (eC c u) (c * x) = ∫ t in (-1 : ℝ)..1, (g t + g (-t)) / 2 := by
      unfold cosT
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le (by norm_num)] at ht
      simp only [Cvs.Prolate.Hardy.ColumnRungCoefficients.eC, hg]
      rw [Cvs.Prolate.SincTopIsRung.clampExt_of_mem ht, evenCol, mul_neg, Real.cos_neg]
      ring
    have hneg : IntervalIntegrable (fun t => g (-t)) volume (-1) 1 := by
      refine ContinuousOn.intervalIntegrable ?_
      simp only [hg]
      refine ContinuousOn.fun_mul (ContinuousOn.div₀ (by fun_prop) (by fun_prop) fun t ht => ?_) (by fun_prop)
      rw [uIcc_of_le (by norm_num)] at ht
      exact mul_ne_zero Real.pi_pos.ne' (by linarith [ht.1])
    rw [e1, intervalIntegral.integral_div, intervalIntegral.integral_add (intervalIntegrable_sinc_cos hu)
      hneg, intervalIntegral.integral_comp_neg (fun t => g t)]
    norm_num
    show ((∫ t in (-1 : ℝ)..1, g t) + ∫ t in (-1 : ℝ)..1, g t) / 2 = _
    ring
  -- product to sum
  have hB : ∫ t in (-1 : ℝ)..1, g t = -(1 / (2 * π)) * ((∫ t in (-1 : ℝ)..1, Real.sin (c * ((1 + x) * t - u)) /
      (u - t)) + ∫ t in (-1 : ℝ)..1, Real.sin (c * ((1 - x) * t - u)) / (u - t)) := by
    rw [← intervalIntegral.integral_add (intervalIntegrable_sin_div hu) (intervalIntegrable_sin_div hu),
      ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le (by norm_num)] at ht
    have htu : t - u ≠ 0 := by linarith [ht.2]
    have htu' : u - t ≠ 0 := by linarith [ht.2]
    simp only [hg]
    rw [show c * ((1 + x) * t - u) = c * (t - u) + c * x * t by ring,
      show c * ((1 - x) * t - u) = c * (t - u) - c * x * t by ring, Real.sin_add, Real.sin_sub]
    have hπ := Real.pi_pos.ne'
    field_simp
    rw [show u - t = -(t - u) by ring]
    ring
  have hq1 : 0 < 1 + x := by linarith
  have hq2 : 0 < 1 - x := by linarith
  rw [integral_sin_div hu, integral_sin_div hu, laplace_Iq hc hu hq1, laplace_Iq hc hu hq2] at hB
  unfold Fop
  rw [hA, hB]
  push_cast
  simp only [posAmp, negAmp]
  -- the complex identity behind the carriers
  have ex : ∀ a b : ℂ, Complex.exp a * Complex.exp b = Complex.exp (a + b) := fun a b => (Complex.exp_add a b).symm
  set G1p := lapG c (u - 1) (1 + x)
  set G2p := lapG c (u + 1) (1 + x)
  set G1m := lapG c (u - 1) (1 - x)
  set G2m := lapG c (u + 1) (1 - x)
  have key : Complex.exp (-(I * (c * u))) * (Complex.exp (I * (c * (1 + x))) * G1p -
        Complex.exp (-(I * (c * (1 + x)))) * G2p) +
      Complex.exp (-(I * (c * u))) * (Complex.exp (I * (c * (1 - x))) * G1m -
        Complex.exp (-(I * (c * (1 - x)))) * G2m) =
      (Complex.exp (I * (c * (1 - u))) * G1p - Complex.exp (-(I * (c * (1 + u)))) * G2m) *
          Complex.exp (I * (c * x)) +
        (Complex.exp (I * (c * (1 - u))) * G1m - Complex.exp (-(I * (c * (1 + u)))) * G2p) *
          Complex.exp (-(I * (c * x))) := by
    have e1 : Complex.exp (-(I * (c * u))) * Complex.exp (I * (c * (1 + x))) =
        Complex.exp (I * (c * (1 - u))) * Complex.exp (I * (c * x)) := by rw [ex, ex]; congr 1; ring
    have e2 : Complex.exp (-(I * (c * u))) * Complex.exp (-(I * (c * (1 + x)))) =
        Complex.exp (-(I * (c * (1 + u)))) * Complex.exp (-(I * (c * x))) := by rw [ex, ex]; congr 1; ring
    have e3 : Complex.exp (-(I * (c * u))) * Complex.exp (I * (c * (1 - x))) =
        Complex.exp (I * (c * (1 - u))) * Complex.exp (-(I * (c * x))) := by rw [ex, ex]; congr 1; ring
    have e4 : Complex.exp (-(I * (c * u))) * Complex.exp (-(I * (c * (1 - x)))) =
        Complex.exp (-(I * (c * (1 + u)))) * Complex.exp (I * (c * x)) := by rw [ex, ex]; congr 1; ring
    linear_combination G1p * e1 - G2p * e2 + G1m * e3 - G2m * e4
  have hre : ∀ a b : ℂ, ((kap c : ℂ) * I * a * b).re = -(kap c * (a * b).im) := by
    intro a b
    rw [mul_assoc, mul_assoc, Complex.mul_re, Complex.mul_re]
    simp; ring
  have key' := congrArg Complex.im key
  rw [hre, hre]
  simp only [Complex.add_im, kap] at key' ⊢
  linear_combination (-(√(c / (2 * π)) / (2 * π))) * key'

end Cvs.Prolate.Hardy.FilteredColumnCarriers

end
