import Mathlib
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.LiouvilleGreen.ComplexSymbols
import Cvs.Prolate.LiouvilleGreen.HalfStripPhase
import Cvs.Prolate.LiouvilleGreen.RecessiveSolvesProlate
import Cvs.Prolate.LiouvilleGreen.RecessiveVolterra
import Cvs.Upstream.HalfStripRayIntegrals
import Cvs.Upstream.NonStationaryPhaseParts

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The normalisation bounds the recessive coefficient: `|α|² ≤ 2`

If `f = Re(2αH)` on `I` and `∫_I f² ≤ 1`, then `2|α|²(∫_I|H|² − |∫_I H²|) ≤ 1`. For `H₊` with `T ≥ ¾`, `|ε| ≤ 1/10` and
`c ≥ 60`, `∫_I|H₊|² ≥ (1 − B)²` and `|∫_I H₊²| ≤ 6/c + 2(2B + B²)` by one integration by parts, so `|α|² ≤ 2`.
-/

noncomputable section

open Real Set MeasureTheory intervalIntegral
open Complex (I)
open ComplexConjugate
open Cvs.Upstream.HalfStripRayIntegrals (strip)
open Cvs.Prolate.LiouvilleGreen.ComplexSymbols
open Cvs.Prolate.LiouvilleGreen.HalfStripPhase
open Cvs.Prolate.LiouvilleGreen.RecessiveVolterra
open Cvs.Prolate.LiouvilleGreen.RecessiveSolvesProlate

namespace Cvs.Prolate.LiouvilleGreen.RecessiveCoefficientBound

/-- **The normalisation inequality** `2|α|²(∫_I|H|² − |∫_I H²|) ≤ ∫_I f²` for `f = Re(2αH)` on `I`. -/
theorem norm_sq_alpha_le {f : ℝ → ℝ} {H : ℝ → ℂ} {α : ℂ} (hH : ContinuousOn H (uIcc (-(1 / 2)) (1 / 2)))
    (hf : ∀ t ∈ uIcc (-(1 / 2) : ℝ) (1 / 2), f t = (2 * α * H t).re) :
    2 * ‖α‖ ^ 2 * ((∫ t in (-(1 / 2) : ℝ)..(1 / 2), ‖H t‖ ^ 2) - ‖∫ t in (-(1 / 2) : ℝ)..(1 / 2), H t ^ 2‖) ≤
      ∫ t in (-(1 / 2) : ℝ)..(1 / 2), f t ^ 2 := by
  have hpt : ∀ t ∈ uIcc (-(1 / 2) : ℝ) (1 / 2), f t ^ 2 = 2 * ‖α‖ ^ 2 * ‖H t‖ ^ 2 + 2 * (α ^ 2 * H t ^ 2).re := by
    intro t ht
    rw [hf t ht]
    have e1 : ‖α‖ ^ 2 = α.re ^ 2 + α.im ^ 2 := by rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    have e2 : ‖H t‖ ^ 2 = (H t).re ^ 2 + (H t).im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    rw [e1, e2]
    simp only [Complex.mul_re, Complex.mul_im, sq, Complex.re_ofNat, Complex.im_ofNat]
    ring
  have hc1 : ContinuousOn (fun t => ‖H t‖ ^ 2) (uIcc (-(1 / 2) : ℝ) (1 / 2)) := hH.norm.pow 2
  have hc2 : ContinuousOn (fun t => H t ^ 2) (uIcc (-(1 / 2) : ℝ) (1 / 2)) := hH.pow 2
  have hc3 : ContinuousOn (fun t => α ^ 2 * H t ^ 2) (uIcc (-(1 / 2) : ℝ) (1 / 2)) := continuousOn_const.mul hc2
  have i1 : IntervalIntegrable (fun t => 2 * ‖α‖ ^ 2 * ‖H t‖ ^ 2) volume (-(1 / 2) : ℝ) (1 / 2) :=
    (hc1.intervalIntegrable).const_mul _
  have i2 : IntervalIntegrable (fun t => 2 * (α ^ 2 * H t ^ 2).re) volume (-(1 / 2) : ℝ) (1 / 2) :=
    ((Complex.continuous_re.comp_continuousOn hc3).intervalIntegrable).const_mul 2
  rw [integral_congr hpt, integral_add i1 i2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  have hre : (∫ t in (-(1 / 2) : ℝ)..(1 / 2), (α ^ 2 * H t ^ 2).re) =
      (α ^ 2 * ∫ t in (-(1 / 2) : ℝ)..(1 / 2), H t ^ 2).re := by
    rw [← intervalIntegral.integral_const_mul]
    exact (Complex.reCLM.intervalIntegral_comp_comm hc3.intervalIntegrable)
  rw [hre]
  have hb : -(‖α‖ ^ 2 * ‖∫ t in (-(1 / 2) : ℝ)..(1 / 2), H t ^ 2‖) ≤
      (α ^ 2 * ∫ t in (-(1 / 2) : ℝ)..(1 / 2), H t ^ 2).re := by
    have := Complex.abs_re_le_norm (α ^ 2 * ∫ t in (-(1 / 2) : ℝ)..(1 / 2), H t ^ 2)
    rw [norm_mul, norm_pow] at this
    linarith [neg_abs_le (α ^ 2 * ∫ t in (-(1 / 2) : ℝ)..(1 / 2), H t ^ 2).re]
  nlinarith

section real

variable {a T c : ℝ}

theorem mem_strip_of_mem {t : ℝ} (ha : 1 / 2 < a) (ht : t ∈ uIcc (-(1 / 2) : ℝ) (1 / 2)) : (t : ℂ) ∈ strip a := by
  rw [uIcc_of_le (by norm_num)] at ht
  refine ⟨?_, by simp⟩
  simp only [Complex.ofReal_re]
  rw [abs_lt]; constructor <;> linarith [ht.1, ht.2]

theorem abs_le_half {t : ℝ} (ht : t ∈ uIcc (-(1 / 2) : ℝ) (1 / 2)) : |t| ≤ 1 / 2 := by
  rw [uIcc_of_le (by norm_num)] at ht; rw [abs_le]; exact ⟨ht.1, ht.2⟩

/-- `Φ′(t) = √((T − t²)/(1 − t²)) ∈ [1/√2, 1]` on `I` for `T ∈ [¾, 1]`. -/
theorem phiD_bounds (ha : 1 / 2 < a) (hT34 : 3 / 4 ≤ T) (hT : a ^ 2 < T) (hT1 : T ≤ 1) {t : ℝ}
    (ht : t ∈ uIcc (-(1 / 2) : ℝ) (1 / 2)) :
    (phiD T t).im = 0 ∧ 1 / 2 ≤ (phiD T t).re ^ 2 ∧ (phiD T t).re ≤ 1 ∧ 0 ≤ (phiD T t).re := by
  have hta := abs_le_half ht
  have hat : |t| < a := lt_of_le_of_lt hta ha
  have h := phiD_ofReal hT hT1 hat
  have ht2 : t ^ 2 ≤ 1 / 4 := by rw [← sq_abs]; nlinarith [abs_nonneg t]
  have hd : 0 < 1 - t ^ 2 := by linarith
  have hr : 0 ≤ (T - t ^ 2) / (1 - t ^ 2) := div_nonneg (by linarith) hd.le
  rw [h, Complex.ofReal_im, Complex.ofReal_re, Real.sq_sqrt hr]
  refine ⟨rfl, ?_, ?_, Real.sqrt_nonneg _⟩
  · rw [le_div_iff₀ hd]; nlinarith
  · rw [Real.sqrt_le_one]; rw [div_le_one hd]; linarith

/-- `|Λ(t)|² ∈ [1, 2]` on `I`. -/
theorem norm_lam_sq_bounds (ha : 1 / 2 < a) (hT34 : 3 / 4 ≤ T) (hT : a ^ 2 < T) (hT1 : T ≤ 1) {t : ℝ}
    (ht : t ∈ uIcc (-(1 / 2) : ℝ) (1 / 2)) : 1 ≤ ‖lam T t‖ ^ 2 ∧ ‖lam T t‖ ^ 2 ≤ 2 := by
  have hs := mem_strip_of_mem ha ht
  have hPne := pP_ne hT hT1 hs
  have h1 := lam_sq_mul (T := T) hPne
  have h2 : ‖lam T t‖ ^ 2 * (‖pP t‖ * ‖phiD T t‖) = 1 := by
    have := congrArg norm h1
    rwa [norm_mul, norm_mul, norm_pow, norm_one, mul_assoc] at this
  obtain ⟨him, hlo, hhi, hnn⟩ := phiD_bounds ha hT34 hT hT1 ht
  have hφn : ‖phiD T t‖ = (phiD T t).re := by
    rw [← Complex.re_add_im (phiD T t), him]; simp [abs_of_nonneg hnn]
  have hta := abs_le_half ht
  have ht2 : t ^ 2 ≤ 1 / 4 := by rw [← sq_abs]; nlinarith [abs_nonneg t]
  have hPn : ‖pP t‖ = 1 - t ^ 2 := by
    unfold pP
    rw [show (1 : ℂ) - (t : ℂ) ^ 2 = ((1 - t ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  rw [hφn, hPn] at h2
  have hφ1 : (1 / 2 : ℝ) ≤ (phiD T t).re := by nlinarith
  have hprod_le : (1 - t ^ 2) * (phiD T t).re ≤ 1 := by nlinarith
  have hprod_ge : 1 / 2 ≤ (1 - t ^ 2) * (phiD T t).re := by
    have : (3 / 4 : ℝ) ≤ 1 - t ^ 2 := by linarith
    have hsq : (1 - t ^ 2) ^ 2 * (phiD T t).re ^ 2 ≥ (9 / 16) * (1 / 2) := by
      have := mul_le_mul (pow_le_pow_left₀ (by norm_num) this 2) hlo (by norm_num) (by positivity)
      nlinarith
    nlinarith
  constructor
  · by_contra h; push Not at h; nlinarith
  · by_contra h; push Not at h; nlinarith

/-- `|ℓ(t)| ≤ 5/6` on `I`. -/
theorem norm_ell_le (hT34 : 3 / 4 ≤ T) {t : ℝ} (ht : t ∈ uIcc (-(1 / 2) : ℝ) (1 / 2)) : ‖ell T t‖ ≤ 5 / 6 := by
  have hta := abs_le_half ht
  have ht2 : t ^ 2 ≤ 1 / 4 := by rw [← sq_abs]; nlinarith [abs_nonneg t]
  have e : ell T t = ((t / (2 * (1 - t ^ 2)) + t / (2 * (T - t ^ 2)) : ℝ) : ℂ) := by
    unfold ell pP pQ; push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs]
  refine (abs_add_le _ _).trans ?_
  rw [abs_div, abs_div, abs_of_pos (by nlinarith : (0 : ℝ) < 2 * (1 - t ^ 2)),
    abs_of_pos (by nlinarith : (0 : ℝ) < 2 * (T - t ^ 2))]
  have h1 : |t| / (2 * (1 - t ^ 2)) ≤ 1 / 3 := by
    rw [div_le_iff₀ (by nlinarith)]; nlinarith
  have h2 : |t| / (2 * (T - t ^ 2)) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by nlinarith)]; nlinarith
  linarith

/-- `|Φ″(t)| = |Φ′(t) t(1/P − 1/Q)| ≤ 1/3` on `I`. -/
theorem norm_phiDD_le (ha : 1 / 2 < a) (hT34 : 3 / 4 ≤ T) (hT : a ^ 2 < T) (hT1 : T ≤ 1) {t : ℝ}
    (ht : t ∈ uIcc (-(1 / 2) : ℝ) (1 / 2)) : ‖phiD T t * (t / pP t - t / pQ T t)‖ ≤ 1 / 3 := by
  obtain ⟨him, -, hhi, hnn⟩ := phiD_bounds ha hT34 hT hT1 ht
  have hφn : ‖phiD T t‖ ≤ 1 := by
    rw [← Complex.re_add_im (phiD T t), him]; simp [abs_of_nonneg hnn]; exact hhi
  have hta := abs_le_half ht
  have ht2 : t ^ 2 ≤ 1 / 4 := by rw [← sq_abs]; nlinarith [abs_nonneg t]
  have e : (t : ℂ) / pP t - t / pQ T t = ((-(t * (1 - T)) / ((1 - t ^ 2) * (T - t ^ 2)) : ℝ) : ℂ) := by
    have h1 : (1 : ℂ) - (t : ℂ) ^ 2 ≠ 0 := by
      rw [show (1 : ℂ) - (t : ℂ) ^ 2 = ((1 - t ^ 2 : ℝ) : ℂ) by push_cast; ring]
      exact_mod_cast (by nlinarith : (1 - t ^ 2 : ℝ) ≠ 0)
    have h2 : (T : ℂ) - (t : ℂ) ^ 2 ≠ 0 := by
      rw [show (T : ℂ) - (t : ℂ) ^ 2 = ((T - t ^ 2 : ℝ) : ℂ) by push_cast; ring]
      exact_mod_cast (by nlinarith : (T - t ^ 2 : ℝ) ≠ 0)
    unfold pP pQ; push_cast; field_simp; ring
  rw [norm_mul, e, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_neg, abs_mul, abs_of_nonneg (by linarith :
    (0 : ℝ) ≤ 1 - T), abs_of_pos (by nlinarith : (0 : ℝ) < (1 - t ^ 2) * (T - t ^ 2))]
  have h3 : |t| * (1 - T) / ((1 - t ^ 2) * (T - t ^ 2)) ≤ 1 / 3 := by
    rw [div_le_iff₀ (by nlinarith)]
    have : (3 / 4 : ℝ) * (1 / 2) ≤ (1 - t ^ 2) * (T - t ^ 2) :=
      mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)
    nlinarith [abs_nonneg t]
  calc ‖phiD T t‖ * (|t| * (1 - T) / ((1 - t ^ 2) * (T - t ^ 2))) ≤ 1 * (1 / 3) :=
        mul_le_mul hφn h3 (div_nonneg (mul_nonneg (abs_nonneg t) (by linarith)) (by nlinarith)) zero_le_one
    _ = 1 / 3 := one_mul _

end real

section main

variable {a T c : ℝ}

/-- **The oscillatory integral** `|∫_I Λ²e^{2icΦ_T}| ≤ 6/c` for `c > 0`. -/
theorem norm_integral_lam_sq_le (ha : 1 / 2 < a) (hT34 : 3 / 4 ≤ T) (hT : a ^ 2 < T) (hT1 : T ≤ 1) (hc : 0 < c) :
    ‖∫ t in (-(1 / 2) : ℝ)..(1 / 2), lam T t ^ 2 * Complex.exp (I * ((2 * c * (Phi T t).re : ℝ) : ℂ))‖ ≤ 6 / c := by
  have hs : ∀ t ∈ Icc (-(1 / 2) : ℝ) (1 / 2), (t : ℂ) ∈ strip a := fun t ht =>
    mem_strip_of_mem ha (by rw [uIcc_of_le (by norm_num)]; exact ht)
  have hu : ∀ t ∈ Icc (-(1 / 2) : ℝ) (1 / 2), t ∈ uIcc (-(1 / 2) : ℝ) (1 / 2) := fun t ht => by
    rw [uIcc_of_le (by norm_num)]; exact ht
  have hg : ∀ t ∈ Icc (-(1 / 2) : ℝ) (1 / 2),
      HasDerivAt (fun t : ℝ => lam T t ^ 2) (2 * lam T t ^ 2 * ell T t) t := by
    intro t ht
    have := ((hasDerivAt_lam hT hT1 (hs t ht)).pow 2).comp_ofReal
    refine this.congr_deriv ?_
    push_cast; ring
  have hlc : ContinuousOn (fun t : ℝ => lam T t) (Icc (-(1 / 2)) (1 / 2)) :=
    (differentiableOn_lam hT hT1).continuousOn.comp Complex.continuous_ofReal.continuousOn hs
  have hec : ContinuousOn (fun t : ℝ => ell T t) (Icc (-(1 / 2)) (1 / 2)) := fun t ht =>
    ((hasDerivAt_ell hT hT1 (hs t ht)).continuousAt.comp Complex.continuous_ofReal.continuousAt).continuousWithinAt
  have hg' : ContinuousOn (fun t : ℝ => 2 * lam T t ^ 2 * ell T t) (Icc (-(1 / 2)) (1 / 2)) :=
    (continuousOn_const.mul (hlc.pow 2)).mul hec
  have hΦ : ∀ t ∈ Icc (-(1 / 2) : ℝ) (1 / 2),
      HasDerivAt (fun t : ℝ => 2 * c * (Phi T t).re) (2 * c * (phiD T t).re) t := fun t ht =>
    ((hasDerivAt_Phi hT hT1 (hs t ht)).real_of_complex).const_mul (2 * c)
  have hΦ₁ : ∀ t ∈ Icc (-(1 / 2) : ℝ) (1 / 2), HasDerivAt (fun t : ℝ => 2 * c * (phiD T t).re)
      (2 * c * (phiD T t * (t / pP t - t / pQ T t)).re) t := fun t ht =>
    ((hasDerivAt_phiD hT hT1 (hs t ht)).real_of_complex).const_mul (2 * c)
  have hΦ₂ : ContinuousOn (fun t : ℝ => 2 * c * (phiD T t * (t / pP t - t / pQ T t)).re) (Icc (-(1 / 2)) (1 / 2)) := by
    refine continuousOn_const.mul (Complex.continuous_re.comp_continuousOn
      (f := fun t : ℝ => phiD T t * (t / pP t - t / pQ T t)) ?_)
    have hφc : ContinuousOn (fun t : ℝ => phiD T t) (Icc (-(1 / 2)) (1 / 2)) :=
      (differentiableOn_phiD hT hT1).continuousOn.comp Complex.continuous_ofReal.continuousOn hs
    refine hφc.mul ((Complex.continuous_ofReal.continuousOn.div ?_ ?_).sub
      (Complex.continuous_ofReal.continuousOn.div ?_ ?_))
    · exact (by unfold pP; fun_prop : Continuous fun t : ℝ => pP t).continuousOn
    · exact fun t ht => pP_ne hT hT1 (hs t ht)
    · exact (by unfold pQ; fun_prop : Continuous fun t : ℝ => pQ T t).continuousOn
    · exact fun t ht => pQ_ne hT (hs t ht)
  have h := Cvs.Upstream.NonStationaryPhaseParts.norm_integral_mul_exp_le (α := -(1 / 2)) (β := 1 / 2) (κ := 2 * c * (1 / √2)) (G₀ := 2)
    (G₁ := 10 / 3) (D := 2 * c * (1 / 3)) (by norm_num) (by positivity) hg hg' hΦ hΦ₁ hΦ₂
    (fun t ht => by rw [norm_pow]; exact (norm_lam_sq_bounds ha hT34 hT hT1 (hu t ht)).2)
    (fun t ht => by
      rw [norm_mul, norm_mul, norm_pow, show ‖(2 : ℂ)‖ = 2 by simp]
      have h1 := (norm_lam_sq_bounds ha hT34 hT hT1 (hu t ht)).2
      have h2 := norm_ell_le hT34 (hu t ht)
      nlinarith [norm_nonneg (ell T t), norm_nonneg (lam T t)])
    (fun t ht => by
      obtain ⟨-, hlo, -, hnn⟩ := phiD_bounds ha hT34 hT hT1 (hu t ht)
      have h1 : 1 / √2 ≤ (phiD T t).re := by
        rw [div_le_iff₀ (by positivity)]
        have : √2 * (phiD T t).re = √(2 * (phiD T t).re ^ 2) := by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hnn]
        rw [mul_comm, this, show (1 : ℝ) = √1 by simp]
        exact Real.sqrt_le_sqrt (by linarith)
      rw [abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left h1 (by positivity))
    (fun t ht => by
      rw [abs_mul, abs_of_pos (by positivity)]
      exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans
        (norm_phiDD_le ha hT34 hT hT1 (hu t ht))) (by positivity))
  refine h.trans ?_
  have hs2 : 0 < √2 := by positivity
  have hs2' : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2'' : (1.4 : ℝ) ≤ √2 := by
    rw [show (1.4 : ℝ) = √(1.4 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hκ : 2 * c * (1 / √2) = √2 * c := by field_simp; nlinarith [hs2']
  rw [hκ]
  have e1 : 2 * 2 / (√2 * c) = 2 * √2 / c := by field_simp; nlinarith [hs2']
  have e2 : (1 / 2 - -(1 / 2) : ℝ) * (10 / 3 / (√2 * c) + 2 * (2 * c * (1 / 3)) / (√2 * c) ^ 2) =
      (5 * √2 / 3 + 2 / 3) / c := by
    field_simp; rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring
  rw [e1, e2, ← add_div, div_le_div_iff_of_pos_right hc]
  have : √2 ≤ 1.42 := by
    rw [show (1.42 : ℝ) = √(1.42 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  linarith

/-- **The recessive coefficient is bounded**: `|α|² ≤ 2` when `h_k = Re(2αH₊)` on `|t| < a`. -/
theorem norm_alpha_sq_le (ha : 1 / 2 < a) (hT34 : 3 / 4 ≤ T) (hT : a ^ 2 < T) (hT1 : T ≤ 1) (hc : 60 ≤ c)
    {ε : ℂ → ℂ} {B : ℝ} (hε : Good a ε B) (hB : B ≤ 1 / 10) {k : ℕ}
    (hk : ∃ χ, Cvs.Prolate.EvenRungsByIndex.IsLevelIdx c k χ) {α : ℂ}
    (hα : ∀ t : ℝ, |t| < a → Cvs.Prolate.EvenRungsByIndex.rung c k t = (2 * α * hP c T ε t).re) : ‖α‖ ^ 2 ≤ 2 := by
  have hc0 : 0 < c := by linarith
  have hB0 : 0 ≤ B := B_nonneg hε (by linarith)
  have hs : ∀ t ∈ uIcc (-(1 / 2) : ℝ) (1 / 2), (t : ℂ) ∈ strip a := fun t ht => mem_strip_of_mem ha ht
  set H : ℝ → ℂ := fun t => hP c T ε t
  have hHc : ContinuousOn H (uIcc (-(1 / 2)) (1 / 2)) := by
    have hd : DifferentiableOn ℂ (hP c T ε) (strip a) :=
      (((differentiableOn_lam hT hT1).mul (((differentiableOn_Phi hT hT1).const_mul _).cexp)).mul
        ((differentiableOn_const 1).add hε.1))
    exact hd.continuousOn.comp Complex.continuous_ofReal.continuousOn hs
  -- the normalisation on `I`
  obtain ⟨hg, -, -, -, -, hnorm⟩ := Cvs.Prolate.EvenRungsByIndex.rung_spec hk
  have hrc : ContinuousOn (Cvs.Prolate.EvenRungsByIndex.rung c k) (uIcc (-1) 1) := fun t ht => (hg t ht).continuousAt.continuousWithinAt
  have hI1 : ∫ t in (-(1 / 2) : ℝ)..(1 / 2), Cvs.Prolate.EvenRungsByIndex.rung c k t ^ 2 ≤ 1 := by
    refine (intervalIntegral.integral_mono_interval (c := -1) (d := 1) (by norm_num) (by norm_num) (by norm_num)
      (Filter.Eventually.of_forall fun _ => sq_nonneg _) (hrc.pow 2).intervalIntegrable).trans_eq hnorm
  have hmain := norm_sq_alpha_le hHc (fun t ht => hα t (lt_of_le_of_lt (abs_le_half ht) ha))
  -- pointwise facts on `I`
  have hΦr : ∀ t ∈ uIcc (-(1 / 2) : ℝ) (1 / 2), Phi T t = ((Phi T t).re : ℂ) := fun t ht => by
    apply Complex.ext <;> simp [im_Phi_ofReal hT hT1 (lt_of_le_of_lt (abs_le_half ht) ha)]
  have hexp1 : ∀ t ∈ uIcc (-(1 / 2) : ℝ) (1 / 2), ‖Complex.exp (I * c * Phi T t)‖ = 1 := fun t ht => by
    rw [hΦr t ht, show I * (c : ℂ) * ((Phi T t).re : ℂ) = ((c * (Phi T t).re : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have hεt : ∀ t ∈ uIcc (-(1 / 2) : ℝ) (1 / 2), ‖ε t‖ ≤ B := fun t ht => hε.2 _ (hs t ht)
  -- `∫_I |H₊|² ≥ (1 − B)²`
  have hA : (1 - B) ^ 2 ≤ ∫ t in (-(1 / 2) : ℝ)..(1 / 2), ‖H t‖ ^ 2 := by
    have hpt : ∀ t ∈ Icc (-(1 / 2) : ℝ) (1 / 2), (1 - B) ^ 2 ≤ ‖H t‖ ^ 2 := by
      intro t ht
      have htu : t ∈ uIcc (-(1 / 2) : ℝ) (1 / 2) := by rw [uIcc_of_le (by norm_num)]; exact ht
      have h1 := (norm_lam_sq_bounds ha hT34 hT hT1 htu).1
      have h2 : 1 - B ≤ ‖1 + ε t‖ := by
        have := norm_sub_le (1 + ε t) (ε t)
        rw [add_sub_cancel_right, norm_one] at this
        linarith [hεt t htu]
      have h3 : ‖H t‖ = ‖lam T t‖ * ‖1 + ε t‖ := by
        simp only [H, hP, norm_mul, hexp1 t htu, mul_one]
      rw [h3, mul_pow]
      have : (1 - B) ^ 2 ≤ ‖1 + ε t‖ ^ 2 := pow_le_pow_left₀ (by linarith) h2 2
      nlinarith [sq_nonneg ‖1 + ε t‖]
    have := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2)
      intervalIntegrable_const ((hHc.norm.pow 2).intervalIntegrable) hpt
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    simp only [Pi.pow_apply] at this
    norm_num at this
    linarith
  -- `|∫_I H₊²| ≤ 6/c + 2B(2 + B)`
  set G : ℝ → ℂ := fun t => lam T t ^ 2 * Complex.exp (I * ((2 * c * (Phi T t).re : ℝ) : ℂ))
  have hsplit : ∀ t ∈ uIcc (-(1 / 2) : ℝ) (1 / 2), H t ^ 2 = G t + G t * ((1 + ε t) ^ 2 - 1) := fun t ht => by
    simp only [H, G, hP]
    rw [show I * ((2 * c * (Phi T t).re : ℝ) : ℂ) = 2 * (I * c * ((Phi T t).re : ℂ)) by push_cast; ring,
      ← hΦr t ht, show Complex.exp (2 * (I * c * Phi T t)) = Complex.exp (I * c * Phi T t) ^ 2 by
        rw [← Complex.exp_nat_mul]; push_cast; ring_nf]
    ring
  have hGc : ContinuousOn G (uIcc (-(1 / 2)) (1 / 2)) := by
    have hl : ContinuousOn (fun t : ℝ => lam T t) (uIcc (-(1 / 2)) (1 / 2)) :=
      (differentiableOn_lam hT hT1).continuousOn.comp Complex.continuous_ofReal.continuousOn hs
    have hφ : ContinuousOn (fun t : ℝ => Phi T t) (uIcc (-(1 / 2)) (1 / 2)) :=
      (differentiableOn_Phi hT hT1).continuousOn.comp Complex.continuous_ofReal.continuousOn hs
    exact (hl.pow 2).mul (Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul
      (Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.mul
        (Complex.continuous_re.comp_continuousOn hφ)))))
  have hεc : ContinuousOn (fun t : ℝ => ε t) (uIcc (-(1 / 2)) (1 / 2)) :=
    hε.1.continuousOn.comp Complex.continuous_ofReal.continuousOn hs
  have hRc : ContinuousOn (fun t => G t * ((1 + ε t) ^ 2 - 1)) (uIcc (-(1 / 2)) (1 / 2)) :=
    hGc.mul (((continuousOn_const.add hεc).pow 2).sub continuousOn_const)
  have hBn : ‖∫ t in (-(1 / 2) : ℝ)..(1 / 2), H t ^ 2‖ ≤ 6 / c + 2 * (B * (2 + B)) := by
    rw [intervalIntegral.integral_congr hsplit, intervalIntegral.integral_add hGc.intervalIntegrable
      hRc.intervalIntegrable]
    refine (norm_add_le _ _).trans (add_le_add (norm_integral_lam_sq_le ha hT34 hT hT1 hc0) ?_)
    have hpt : ∀ t ∈ uIoc (-(1 / 2) : ℝ) (1 / 2), ‖G t * ((1 + ε t) ^ 2 - 1)‖ ≤ 2 * (B * (2 + B)) := by
      intro t ht
      have htu : t ∈ uIcc (-(1 / 2) : ℝ) (1 / 2) := uIoc_subset_uIcc ht
      have h1 : ‖G t‖ ≤ 2 := by
        simp only [G, norm_mul, norm_pow, Complex.norm_exp_ofReal_mul_I, mul_comm I, mul_one]
        exact (norm_lam_sq_bounds ha hT34 hT hT1 htu).2
      have h2 : ‖(1 + ε t) ^ 2 - 1‖ ≤ B * (2 + B) := by
        rw [show (1 + ε t) ^ 2 - 1 = ε t * (2 + ε t) by ring, norm_mul]
        refine mul_le_mul (hεt t htu) ((norm_add_le _ _).trans ?_) (norm_nonneg _) hB0
        rw [show ‖(2 : ℂ)‖ = 2 by simp]; linarith [hεt t htu]
      rw [norm_mul]
      exact mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
    have := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2 - -(1 / 2))] at this
    linarith
  have hcb : 6 / c ≤ 1 / 10 := by rw [div_le_iff₀ hc0]; linarith
  have hD : 1 / 4 ≤ (∫ t in (-(1 / 2) : ℝ)..(1 / 2), ‖H t‖ ^ 2) - ‖∫ t in (-(1 / 2) : ℝ)..(1 / 2), H t ^ 2‖ := by
    nlinarith
  nlinarith [sq_nonneg ‖α‖]

end main

end Cvs.Prolate.LiouvilleGreen.RecessiveCoefficientBound

end
