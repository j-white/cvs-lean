import Mathlib
import Cvs.WeilForm.CentredGaussianTest
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Zeta.ExplicitFormula.CompactTestAdmissibility
import Cvs.Zeta.ExplicitFormula.HannWindowShifts
import Cvs.Zeta.ExplicitFormula.PrimeChannelFiniteSum
import Cvs.Zeta.ExplicitFormula.WindowTransformByParts
import Cvs.Zeta.ExplicitFormula.WindowTransformCubicDecay
import Cvs.Zeta.GaussKernel.AdmissibleKernel

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The centred transform of `testL`: an `L`-uniform envelope and its limit

`V(L, ξ)`, the transform of `testL` centred at `L/2`, is at most `C/(1 + |Re ξ|)` on `|Im ξ| ≤ 3/2`
uniformly in `L ≥ 0` (`WindowTransformByParts`'s integration by parts for `‖ξ‖ > 1`), and tends to `gaussAmp` as
`L → ∞` by one dominated convergence under `2K e^{−t²/2λ} e^{3|t|/2}`.
-/

noncomputable section

open MeasureTheory Real Set

namespace Cvs.WeilForm.GaussianTestEnvelope
open Cvs.ZeroCounting

open Cvs.WeilForm.CentredGaussianTest (gaussTime gaussTime1 testL)

/-! ### Gaussian dominators -/

/-- The Gaussian's amplitude `2(2πλ)^{-1/2}`. -/
def Kc (lam : ℝ) : ℝ := 2 * (2 * π * lam) ^ (-(1 / 2 : ℝ))

/-- The amplitude is nonnegative. -/
theorem Kc_nonneg {lam : ℝ} (hlam : 0 < lam) : 0 ≤ Kc lam := by unfold Kc; positivity

/-- `|gaussTime(t)| ≤ K e^{-t²/2λ}`. -/
theorem abs_gaussTime_le {lam : ℝ} (hlam : 0 < lam) (a t : ℝ) :
    |gaussTime lam a t| ≤ Kc lam * Real.exp (-(t ^ 2) / (2 * lam)) := by
  have hK0 := Kc_nonneg hlam
  have h : gaussTime lam a t = Kc lam * Real.cos (a * t) * Real.exp (-(t ^ 2) / (2 * lam)) := rfl
  rw [h, abs_mul, abs_mul, abs_of_nonneg hK0, abs_of_pos (Real.exp_pos _)]
  have := Real.abs_cos_le_one (a * t)
  calc Kc lam * |Real.cos (a * t)| * Real.exp (-(t ^ 2) / (2 * lam))
      ≤ Kc lam * 1 * Real.exp (-(t ^ 2) / (2 * lam)) := by gcongr
    _ = _ := by ring

/-- `|gaussTime1(t)| ≤ K(|a| + 1/λ) e^{-t²/2λ} e^{|t|}`. -/
theorem abs_gaussTime1_le {lam : ℝ} (hlam : 0 < lam) (a t : ℝ) :
    |gaussTime1 lam a t|
      ≤ Kc lam * (|a| + 1 / lam) * (Real.exp (-(t ^ 2) / (2 * lam)) * Real.exp |t|) := by
  have hK0 := Kc_nonneg hlam
  have h : gaussTime1 lam a t = Kc lam * Real.exp (-(t ^ 2) / (2 * lam))
      * (-a * Real.sin (a * t) - t / lam * Real.cos (a * t)) := rfl
  rw [h, abs_mul, abs_mul, abs_of_nonneg hK0, abs_of_pos (Real.exp_pos _)]
  have hs := Real.abs_sin_le_one (a * t)
  have hc := Real.abs_cos_le_one (a * t)
  have he1 : 1 ≤ Real.exp |t| := Real.one_le_exp (abs_nonneg t)
  have het : |t| ≤ Real.exp |t| := by linarith [Real.add_one_le_exp |t|]
  have hq : |-a * Real.sin (a * t) - t / lam * Real.cos (a * t)|
      ≤ (|a| + 1 / lam) * Real.exp |t| := by
    calc |-a * Real.sin (a * t) - t / lam * Real.cos (a * t)|
        ≤ |a| * |Real.sin (a * t)| + |t| / lam * |Real.cos (a * t)| := by
          refine (abs_sub _ _).trans ?_
          rw [abs_mul, abs_mul, abs_neg, abs_div, abs_of_pos hlam]
      _ ≤ |a| * 1 + |t| / lam * 1 := by gcongr
      _ ≤ |a| * Real.exp |t| + Real.exp |t| / lam := by
          have := abs_nonneg a
          rw [mul_one, mul_one]; gcongr
          nlinarith
      _ = (|a| + 1 / lam) * Real.exp |t| := by ring
  calc Kc lam * Real.exp (-(t ^ 2) / (2 * lam))
        * |-a * Real.sin (a * t) - t / lam * Real.cos (a * t)|
      ≤ Kc lam * Real.exp (-(t ^ 2) / (2 * lam)) * ((|a| + 1 / lam) * Real.exp |t|) := by gcongr
    _ = _ := by ring

/-- `e^{-t²/2λ} e^{c|t|}` is integrable: it sits under `e^{c²λ} e^{-t²/4λ}`. -/
theorem integrable_gauss_exp {lam : ℝ} (hlam : 0 < lam) (c : ℝ) :
    Integrable (fun t : ℝ => Real.exp (-(t ^ 2) / (2 * lam)) * Real.exp (c * |t|)) := by
  have hb : 0 < 1 / (4 * lam) := by positivity
  have hI := (integrable_exp_neg_mul_sq hb).const_mul (Real.exp (c ^ 2 * lam))
  refine hI.mono' (by fun_prop) (ae_of_all _ fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (by positivity), ← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hsq : 0 ≤ (|t| - 2 * c * lam) ^ 2 / (4 * lam) := by positivity
  have e : c ^ 2 * lam + -(1 / (4 * lam)) * t ^ 2 - (-(t ^ 2) / (2 * lam) + c * |t|)
      = (|t| - 2 * c * lam) ^ 2 / (4 * lam) := by
    rw [← sq_abs t]
    field_simp
    ring
  linarith

/-- The `L`-uniform dominator `2K e^{−t²/2λ} e^{3|t|/2}` of the centred integrand. -/
def dom (lam t : ℝ) : ℝ :=
  2 * Kc lam * (Real.exp (-(t ^ 2) / (2 * lam)) * Real.exp (3 / 2 * |t|))

/-- The dominator `K(|a| + 1/λ) e^{−t²/2λ} e^{5|t|/2}` of the differentiated integrand. -/
def dom1 (lam a t : ℝ) : ℝ :=
  Kc lam * (|a| + 1 / lam) * (Real.exp (-(t ^ 2) / (2 * lam)) * Real.exp (5 / 2 * |t|))

/-- `dom` is integrable. -/
theorem integrable_dom {lam : ℝ} (hlam : 0 < lam) : Integrable (dom lam) :=
  (integrable_gauss_exp hlam (3 / 2)).const_mul _

/-- `dom1` is integrable. -/
theorem integrable_dom1 {lam : ℝ} (hlam : 0 < lam) (a : ℝ) : Integrable (dom1 lam a) :=
  (integrable_gauss_exp hlam (5 / 2)).const_mul _

/-- `dom` is nonnegative. -/
theorem dom_nonneg {lam : ℝ} (hlam : 0 < lam) (t : ℝ) : 0 ≤ dom lam t := by
  unfold dom; have := Kc_nonneg hlam; positivity

/-- `dom1` is nonnegative. -/
theorem dom1_nonneg {lam : ℝ} (hlam : 0 < lam) (a t : ℝ) : 0 ≤ dom1 lam a t := by
  unfold dom1; have := Kc_nonneg hlam; positivity

/-- On the strip `|Im ξ| ≤ 3/2`, `e^{t Im ξ} ≤ e^{3|t|/2}`. -/
theorem exp_im_le {ξ : ℂ} (hξ : |ξ.im| ≤ 3 / 2) (t : ℝ) :
    Real.exp (t * ξ.im) ≤ Real.exp (3 / 2 * |t|) := by
  refine Real.exp_le_exp.mpr ?_
  calc t * ξ.im ≤ |t * ξ.im| := le_abs_self _
    _ = |t| * |ξ.im| := abs_mul _ _
    _ ≤ |t| * (3 / 2) := by gcongr
    _ = 3 / 2 * |t| := by ring

/-! ### The centred transform -/

/-- The centred transform of `testL`:
`∫_{−L/2}^{L/2} e^{−itξ}(gaussTime(t) − gaussTime(L/2)) dt`. -/
def V (lam a L : ℝ) (ξ : ℂ) : ℂ :=
  ∫ t in (-(L / 2))..(L / 2),
    Complex.exp (-((t : ℂ) * ξ) * Complex.I)
      * ((gaussTime lam a t - gaussTime lam a (L / 2) : ℝ) : ℂ)

/-- **The shift `s = t + L/2`** of a window transform, for any profile. -/
theorem windowTransform_shift (L : ℝ) (g : ℝ → ℝ) (ξ : ℂ) :
    Cvs.Detection.windowTransform L (Cvs.WeilForm.SelfConvolutionTransform.cf (fun s => g (s - L / 2))) ξ
      = Complex.exp (-(((L / 2 : ℝ) : ℂ) * ξ) * Complex.I) *
        ∫ t in (-(L / 2))..(L / 2), Complex.exp (-((t : ℂ) * ξ) * Complex.I) * ((g t : ℝ) : ℂ) := by
  unfold Cvs.Detection.windowTransform
  rw [← intervalIntegral.integral_const_mul]
  have h := intervalIntegral.integral_comp_add_right
    (fun s : ℝ => Complex.exp (-((s : ℂ) * ξ) * Complex.I) * Cvs.WeilForm.SelfConvolutionTransform.cf (fun s => g (s - L / 2)) s)
    (L / 2) (a := -(L / 2)) (b := L / 2)
  rw [show -(L / 2) + L / 2 = (0:ℝ) by ring, show L / 2 + L / 2 = L by ring] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [Cvs.WeilForm.SelfConvolutionTransform.cf, add_sub_cancel_right]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast; ring

/-- The window transform of `testL` is the phase `e^{−iLξ/2}` times `V`. -/
theorem windowTransform_testL (lam a L : ℝ) (ξ : ℂ) :
    Cvs.Detection.windowTransform L (Cvs.WeilForm.SelfConvolutionTransform.cf (testL lam a L)) ξ
      = Complex.exp (-(((L / 2 : ℝ) : ℂ) * ξ) * Complex.I) * V lam a L ξ :=
  windowTransform_shift L (fun t => gaussTime lam a t - gaussTime lam a (L / 2)) ξ

/-- **The squared transform of `testL` is `V(ξ) V(−ξ)`**: the phases cancel. -/
theorem sqTransform_testL (lam a L : ℝ) (ξ : ℂ) :
    Cvs.Detection.sqTransform L (Cvs.WeilForm.SelfConvolutionTransform.cf (testL lam a L)) ξ = V lam a L ξ * V lam a L (-ξ) := by
  rw [Cvs.Detection.sqTransform, windowTransform_testL, windowTransform_testL]
  have : Complex.exp (-(((L / 2 : ℝ) : ℂ) * ξ) * Complex.I)
      * Complex.exp (-(((L / 2 : ℝ) : ℂ) * -ξ) * Complex.I) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]; congr 1; ring
  linear_combination (V lam a L ξ * V lam a L (-ξ)) * this

/-! ### The `L`-uniform envelope -/

/-- **The centred integrand sits under `dom`, uniformly in `L`**: for `|t| ≤ L/2`,
`|gaussTime(L/2)| ≤ K e^{-t²/2λ}`. -/
theorem norm_integrand_le {lam : ℝ} (hlam : 0 < lam) (a : ℝ) {L t : ℝ} (ht : |t| ≤ L / 2)
    {ξ : ℂ} (hξ : |ξ.im| ≤ 3 / 2) :
    ‖Complex.exp (-((t : ℂ) * ξ) * Complex.I)
        * ((gaussTime lam a t - gaussTime lam a (L / 2) : ℝ) : ℂ)‖ ≤ dom lam t := by
  rw [norm_mul, Cvs.Detection.norm_char, Complex.norm_real, Real.norm_eq_abs]
  have hK0 := Kc_nonneg hlam
  have h2 : |gaussTime lam a t - gaussTime lam a (L / 2)|
      ≤ 2 * Kc lam * Real.exp (-(t ^ 2) / (2 * lam)) := by
    have hA := abs_gaussTime_le hlam a t
    have hB := abs_gaussTime_le hlam a (L / 2)
    have hE : Real.exp (-((L / 2) ^ 2) / (2 * lam)) ≤ Real.exp (-(t ^ 2) / (2 * lam)) := by
      refine Real.exp_le_exp.mpr ?_
      have ht2 : t ^ 2 ≤ (L / 2) ^ 2 := by
        have h0 : 0 ≤ |t| := abs_nonneg t
        calc t ^ 2 = |t| ^ 2 := (sq_abs t).symm
          _ ≤ (L / 2) ^ 2 := by gcongr
      have hneg : -((L / 2) ^ 2) ≤ -(t ^ 2) := neg_le_neg ht2
      have hpos : (0 : ℝ) ≤ (2 * lam)⁻¹ := by positivity
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hneg hpos
    calc |gaussTime lam a t - gaussTime lam a (L / 2)|
        ≤ |gaussTime lam a t| + |gaussTime lam a (L / 2)| := abs_sub _ _
      _ ≤ Kc lam * Real.exp (-(t ^ 2) / (2 * lam))
            + Kc lam * Real.exp (-((L / 2) ^ 2) / (2 * lam)) := add_le_add hA hB
      _ ≤ Kc lam * Real.exp (-(t ^ 2) / (2 * lam))
            + Kc lam * Real.exp (-(t ^ 2) / (2 * lam)) := by gcongr
      _ = 2 * Kc lam * Real.exp (-(t ^ 2) / (2 * lam)) := by ring
  unfold dom
  calc Real.exp (t * ξ.im) * |gaussTime lam a t - gaussTime lam a (L / 2)|
      ≤ Real.exp (3 / 2 * |t|) * (2 * Kc lam * Real.exp (-(t ^ 2) / (2 * lam))) :=
        mul_le_mul (exp_im_le hξ t) h2 (abs_nonneg _) (Real.exp_pos _).le
    _ = _ := by ring

/-- `‖V‖ ≤ ∫ dom`, uniformly in `L ≥ 0`. -/
theorem norm_V_le {lam : ℝ} (hlam : 0 < lam) (a : ℝ) {L : ℝ} (hL : 0 ≤ L) {ξ : ℂ}
    (hξ : |ξ.im| ≤ 3 / 2) : ‖V lam a L ξ‖ ≤ ∫ t, dom lam t := by
  have hI := integrable_dom hlam
  have hab : -(L / 2) ≤ L / 2 := by linarith
  unfold V
  refine (intervalIntegral.norm_integral_le_of_norm_le hab (ae_of_all _ fun t ht => ?_)
    hI.intervalIntegrable).trans ?_
  · exact norm_integrand_le hlam a (abs_le.mpr ⟨ht.1.le, ht.2⟩) hξ
  · rw [intervalIntegral.integral_of_le hab]
    exact setIntegral_le_integral hI (Filter.Eventually.of_forall fun t => dom_nonneg hlam t)

/-- `‖V‖ ≤ (∫ dom1)/‖ξ‖` for `ξ ≠ 0`, uniformly in `L ≥ 0`, by `WindowTransformByParts`'s integration by parts. -/
theorem norm_V_le_div {lam : ℝ} (hlam : 0 < lam) (a : ℝ) {L : ℝ} (hL : 0 ≤ L) {ξ : ℂ}
    (hξ : |ξ.im| ≤ 3 / 2) (hξ0 : ξ ≠ 0) : ‖V lam a L ξ‖ ≤ (∫ t, dom1 lam a t) / ‖ξ‖ := by
  set ph := Complex.exp (-(((L / 2 : ℝ) : ℂ) * ξ) * Complex.I) with hph
  set W := ∫ t in (-(L / 2))..(L / 2),
    Complex.exp (-((t : ℂ) * ξ) * Complex.I) * ((gaussTime1 lam a t : ℝ) : ℂ) with hW
  have h1 : Cvs.Detection.windowTransform L (Cvs.WeilForm.SelfConvolutionTransform.cf (testL lam a L)) ξ = ph * V lam a L ξ :=
    windowTransform_testL lam a L ξ
  have h2 : Cvs.Detection.windowTransform L (Cvs.WeilForm.SelfConvolutionTransform.cf (fun s => gaussTime1 lam a (s - L / 2))) ξ
      = ph * W := windowTransform_shift L (gaussTime1 lam a) ξ
  have h3 := Cvs.Detection.windowTransform_ibp (L := L) (f := Cvs.WeilForm.SelfConvolutionTransform.cf (testL lam a L))
    (f' := Cvs.WeilForm.SelfConvolutionTransform.cf (fun s => gaussTime1 lam a (s - L / 2)))
    (fun s _ => (Cvs.WeilForm.CentredGaussianTest.hasDerivAt_testL lam a L s).ofReal_comp)
    (Complex.continuous_ofReal.comp
      ((Cvs.WeilForm.CentredGaussianTest.continuous_gaussTime1 lam a).comp (continuous_id.sub continuous_const)))
    (by simp [Cvs.WeilForm.SelfConvolutionTransform.cf, Cvs.WeilForm.CentredGaussianTest.testL_zero]) (by simp [Cvs.WeilForm.SelfConvolutionTransform.cf, Cvs.WeilForm.CentredGaussianTest.testL_self]) hξ0
  rw [h1, h2] at h3
  have hph0 : ph ≠ 0 := Complex.exp_ne_zero _
  have hVW : V lam a L ξ = (1 / (ξ * Complex.I)) * W := by
    apply mul_left_cancel₀ hph0
    rw [h3]; ring
  have hWb : ‖W‖ ≤ ∫ t, dom1 lam a t := by
    have hI := integrable_dom1 hlam a
    have hab : -(L / 2) ≤ L / 2 := by linarith
    refine (intervalIntegral.norm_integral_le_of_norm_le hab (ae_of_all _ fun t _ => ?_)
      hI.intervalIntegrable).trans ?_
    · rw [norm_mul, Cvs.Detection.norm_char, Complex.norm_real, Real.norm_eq_abs]
      have hb := abs_gaussTime1_le hlam a t
      have hK := Kc_nonneg hlam
      unfold dom1
      calc Real.exp (t * ξ.im) * |gaussTime1 lam a t|
          ≤ Real.exp (3 / 2 * |t|)
            * (Kc lam * (|a| + 1 / lam) * (Real.exp (-(t ^ 2) / (2 * lam)) * Real.exp |t|)) :=
            mul_le_mul (exp_im_le hξ t) hb (abs_nonneg _) (Real.exp_pos _).le
        _ = Kc lam * (|a| + 1 / lam)
              * (Real.exp (-(t ^ 2) / (2 * lam)) * Real.exp (5 / 2 * |t|)) := by
            rw [show (5 / 2 : ℝ) * |t| = 3 / 2 * |t| + |t| by ring, Real.exp_add]; ring
    · rw [intervalIntegral.integral_of_le hab]
      exact setIntegral_le_integral hI (Filter.Eventually.of_forall fun t => dom1_nonneg hlam a t)
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ0
  rw [hVW, norm_mul, norm_div, norm_one, norm_mul, Complex.norm_I, mul_one, one_div,
    inv_mul_eq_div]
  exact div_le_div_of_nonneg_right hWb hn.le

/-- **The `L`-uniform envelope**: `‖V(L, ξ)‖ ≤ C/(1 + |Re ξ|)` on `|Im ξ| ≤ 3/2`, for all
`L ≥ 0`. -/
theorem exists_V_envelope {lam : ℝ} (hlam : 0 < lam) (a : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 ≤ L → ∀ ξ : ℂ, |ξ.im| ≤ 3 / 2 →
      ‖V lam a L ξ‖ ≤ C / (1 + |ξ.re|) := by
  set A := ∫ t, dom lam t with hA
  set B := ∫ t, dom1 lam a t with hB
  have hA0 : 0 ≤ A := integral_nonneg fun t => dom_nonneg hlam t
  have hB0 : 0 ≤ B := integral_nonneg fun t => dom1_nonneg hlam a t
  refine ⟨2 * (A + B), by positivity, fun L hL ξ hξ => ?_⟩
  have hre : |ξ.re| ≤ ‖ξ‖ := Complex.abs_re_le_norm ξ
  have hpos : 0 < 1 + |ξ.re| := by positivity
  rw [le_div_iff₀ hpos]
  by_cases h1 : ‖ξ‖ ≤ 1
  · have h := norm_V_le hlam a hL hξ
    calc ‖V lam a L ξ‖ * (1 + |ξ.re|) ≤ A * 2 :=
          mul_le_mul h (by linarith) hpos.le hA0
      _ ≤ 2 * (A + B) := by linarith
  · push Not at h1
    have hξ0 : ξ ≠ 0 := by intro h; rw [h, norm_zero] at h1; linarith
    have h := norm_V_le_div hlam a hL hξ hξ0
    have hn : 0 < ‖ξ‖ := by linarith
    calc ‖V lam a L ξ‖ * (1 + |ξ.re|) ≤ (B / ‖ξ‖) * (2 * ‖ξ‖) :=
          mul_le_mul h (by linarith) hpos.le (by positivity)
      _ = 2 * B := by field_simp
      _ ≤ 2 * (A + B) := by linarith

/-! ### The limit `L → ∞` -/

/-- The endpoint value `gaussTime(L/2)` tends to `0`. -/
theorem tendsto_gaussTime_half {lam : ℝ} (hlam : 0 < lam) (a : ℝ) :
    Filter.Tendsto (fun L : ℝ => gaussTime lam a (L / 2)) Filter.atTop (nhds 0) := by
  have hq : Filter.Tendsto (fun L : ℝ => -((L / 2) ^ 2) / (2 * lam)) Filter.atTop
      Filter.atBot := by
    have h1 : Filter.Tendsto (fun L : ℝ => (L / 2) ^ 2 / (2 * lam)) Filter.atTop Filter.atTop :=
      ((Filter.tendsto_pow_atTop two_ne_zero).comp
        (Filter.tendsto_id.atTop_div_const two_pos)).atTop_div_const (by positivity)
    refine (Filter.tendsto_neg_atTop_atBot.comp h1).congr fun L => ?_
    simp only [Function.comp_apply]; ring
  have he := (Real.tendsto_exp_atBot.comp hq).const_mul (Kc lam)
  rw [mul_zero] at he
  refine squeeze_zero_norm (fun L => ?_) he
  rw [Real.norm_eq_abs]; exact abs_gaussTime_le hlam a (L / 2)

/-- **The centred transform tends to the full transform of `gaussTime`**: one dominated
convergence under `dom`. -/
theorem tendsto_V_integral {lam : ℝ} (hlam : 0 < lam) (a : ℝ) {ξ : ℂ} (hξ : |ξ.im| ≤ 3 / 2) :
    Filter.Tendsto (fun L => V lam a L ξ) Filter.atTop
      (nhds (∫ t : ℝ,
        Complex.exp (-((t : ℂ) * ξ) * Complex.I) * ((gaussTime lam a t : ℝ) : ℂ))) := by
  set F : ℝ → ℝ → ℂ := fun L => (Set.Ioc (-(L / 2)) (L / 2)).indicator (fun t =>
    Complex.exp (-((t : ℂ) * ξ) * Complex.I)
      * ((gaussTime lam a t - gaussTime lam a (L / 2) : ℝ) : ℂ)) with hF
  have hV : ∀ L : ℝ, 0 ≤ L → V lam a L ξ = ∫ t, F L t := by
    intro L hL
    unfold V
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_indicator measurableSet_Ioc]
  have hcont : ∀ L : ℝ, Continuous (fun t : ℝ =>
      Complex.exp (-((t : ℂ) * ξ) * Complex.I)
        * ((gaussTime lam a t - gaussTime lam a (L / 2) : ℝ) : ℂ)) :=
    fun L => (Cvs.Detection.continuous_char ξ).mul
      (Complex.continuous_ofReal.comp ((Cvs.WeilForm.CentredGaussianTest.continuous_gaussTime lam a).sub continuous_const))
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (l := Filter.atTop) (F := F)
    (f := fun t => Complex.exp (-((t : ℂ) * ξ) * Complex.I) * ((gaussTime lam a t : ℝ) : ℂ))
    (dom lam)
    (Filter.Eventually.of_forall fun L =>
      ((hcont L).aestronglyMeasurable.indicator measurableSet_Ioc))
    ((Filter.eventually_ge_atTop 0).mono fun L hL => ae_of_all _ fun t => by
      simp only [hF, Set.indicator_apply]
      split_ifs with ht
      · exact norm_integrand_le hlam a (abs_le.mpr ⟨ht.1.le, ht.2⟩) hξ
      · rw [norm_zero]; exact dom_nonneg hlam t)
    (integrable_dom hlam)
    (ae_of_all _ fun t => by
      have hev : ∀ᶠ L in Filter.atTop, F L t = Complex.exp (-((t : ℂ) * ξ) * Complex.I)
          * ((gaussTime lam a t - gaussTime lam a (L / 2) : ℝ) : ℂ) := by
        filter_upwards [Filter.eventually_ge_atTop (2 * |t| + 2)] with L hL
        have hmem : t ∈ Set.Ioc (-(L / 2)) (L / 2) := by
          constructor <;> cases abs_cases t <;> linarith
        simp only [hF, Set.indicator_of_mem hmem]
      have ht : Filter.Tendsto (fun L : ℝ => Complex.exp (-((t : ℂ) * ξ) * Complex.I)
          * ((gaussTime lam a t - gaussTime lam a (L / 2) : ℝ) : ℂ)) Filter.atTop
          (nhds (Complex.exp (-((t : ℂ) * ξ) * Complex.I)
            * ((gaussTime lam a t - 0 : ℝ) : ℂ))) :=
        ((Complex.continuous_ofReal.tendsto _).comp
          (tendsto_const_nhds.sub (tendsto_gaussTime_half hlam a))).const_mul _
      rw [sub_zero] at ht
      exact ht.congr' (hev.mono fun L h => h.symm))
  exact hlim.congr' ((Filter.eventually_ge_atTop 0).mono fun L hL => (hV L hL).symm)

/-- **The centred transform tends to `gaussAmp`** on the strip `|Im ξ| ≤ 3/2`. -/
theorem tendsto_V {lam : ℝ} (hlam : 0 < lam) (a : ℝ) {ξ : ℂ} (hξ : |ξ.im| ≤ 3 / 2) :
    Filter.Tendsto (fun L => V lam a L ξ) Filter.atTop
      (nhds (Cvs.Zeta.GaussKernel.AdmissibleKernel.gaussAmp lam a ξ)) := by
  rw [← Cvs.WeilForm.CentredGaussianTest.fourier_gaussTime hlam a ξ]; exact tendsto_V_integral hlam a hξ

end Cvs.WeilForm.GaussianTestEnvelope
