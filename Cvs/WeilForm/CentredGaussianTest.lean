import Mathlib
import Cvs.Finite.OddSectorZeroSide
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Zeta.ExplicitFormula.HannWindowShifts
import Cvs.Zeta.GaussKernel.AdmissibleKernel
import Cvs.Zeta.GaussKernel.KernelPrimeSideClosed

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The centred Gaussian test on `[0, L]`

`gaussTime` has transform `gaussAmp` (`KernelPrimeSideClosed`'s Gaussian integrals). Its centred, endpoint-corrected
restriction `testL` vanishes at `0` and `L`, meets `OddSectorZeroSide`'s admissibility bounds, and extended by
zero off `[0, L]` it is continuous and Lipschitz.
-/

noncomputable section

open MeasureTheory Real Set

namespace Cvs.WeilForm.CentredGaussianTest
open Cvs.ZeroCounting

/-! ### The time-domain Gaussian -/

/-- The time-domain Gaussian `2(2πλ)^{-1/2} cos(at) e^{-t²/2λ}`. -/
def gaussTime (lam a t : ℝ) : ℝ :=
  2 * (2 * π * lam) ^ (-(1 / 2 : ℝ)) * Real.cos (a * t) * Real.exp (-(t ^ 2) / (2 * lam))

/-- `gaussTime` is even. -/
theorem gaussTime_neg (lam a t : ℝ) : gaussTime lam a (-t) = gaussTime lam a t := by
  unfold gaussTime; rw [mul_neg, Real.cos_neg, neg_sq]

/-- **The transform of `gaussTime` is `gaussAmp`**, at every complex frequency. -/
theorem fourier_gaussTime {lam : ℝ} (hlam : 0 < lam) (a : ℝ) (ξ : ℂ) :
    ∫ t : ℝ, Complex.exp (-((t : ℂ) * ξ) * Complex.I) * ((gaussTime lam a t : ℝ) : ℂ)
      = Cvs.Zeta.GaussKernel.AdmissibleKernel.gaussAmp lam a ξ := by
  set μ : ℝ := 1 / (2 * lam) with hμ
  have hμ0 : 0 < μ := by positivity
  set K : ℝ := (2 * π * lam) ^ (-(1 / 2 : ℝ)) with hK
  set c₁ : ℂ := -(Complex.I * ξ) + Complex.I * a with hc₁
  set c₂ : ℂ := -(Complex.I * ξ) - Complex.I * a with hc₂
  have hpt : ∀ t : ℝ, Complex.exp (-((t : ℂ) * ξ) * Complex.I) * ((gaussTime lam a t : ℝ) : ℂ)
      = (K : ℂ) * (Complex.exp (-(μ : ℂ) * (t : ℂ) ^ 2 + c₁ * (t : ℂ) + 0)
        + Complex.exp (-(μ : ℂ) * (t : ℂ) ^ 2 + c₂ * (t : ℂ) + 0)) := by
    intro t
    simp only [gaussTime]
    push_cast
    rw [Complex.cos, show (-((t:ℂ) ^ 2) / (2 * (lam:ℂ))) = -(μ : ℂ) * (t : ℂ) ^ 2 by
      rw [hμ]; push_cast; field_simp]
    have e1 : Complex.exp (-(μ : ℂ) * (t : ℂ) ^ 2 + c₁ * (t : ℂ) + 0)
        = Complex.exp (-((t : ℂ) * ξ) * Complex.I) * Complex.exp ((a:ℂ) * t * Complex.I)
          * Complex.exp (-(μ : ℂ) * (t : ℂ) ^ 2) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; rw [hc₁]; ring
    have e2 : Complex.exp (-(μ : ℂ) * (t : ℂ) ^ 2 + c₂ * (t : ℂ) + 0)
        = Complex.exp (-((t : ℂ) * ξ) * Complex.I) * Complex.exp (-((a:ℂ) * t) * Complex.I)
          * Complex.exp (-(μ : ℂ) * (t : ℂ) ^ 2) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; rw [hc₂]; ring
    rw [e1, e2, hK]
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_add (Cvs.GaussKernel.integrable_quad hμ0 _ _)
    (Cvs.GaussKernel.integrable_quad hμ0 _ _), Cvs.GaussKernel.integral_quad hμ0,
    Cvs.GaussKernel.integral_quad hμ0]
  have hpow : (K : ℂ) * ((π : ℂ) / (μ : ℂ)) ^ (1 / 2 : ℂ) = 1 := by
    have h2 : ((π : ℂ) / (μ : ℂ)) = ((2 * π * lam : ℝ) : ℂ) := by
      rw [hμ]; push_cast; field_simp
    rw [h2, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (by positivity), hK, ← Complex.ofReal_mul,
      ← Real.rpow_add (by positivity)]
    norm_num
  rw [← mul_add, ← mul_assoc] at *
  rw [hpow, one_mul]
  unfold Cvs.Zeta.GaussKernel.AdmissibleKernel.gaussAmp
  refine congrArg₂ (· + ·) (congrArg Complex.exp ?_) (congrArg Complex.exp ?_)
  · rw [hc₁, hμ]; push_cast; field_simp; ring_nf; simp [Complex.I_sq]; ring
  · rw [hc₂, hμ]; push_cast; field_simp; ring_nf; simp [Complex.I_sq]; ring

/-- The first derivative of `gaussTime`. -/
def gaussTime1 (lam a t : ℝ) : ℝ :=
  2 * (2 * π * lam) ^ (-(1 / 2 : ℝ)) * Real.exp (-(t ^ 2) / (2 * lam))
    * (-a * Real.sin (a * t) - t / lam * Real.cos (a * t))

/-- The second derivative of `gaussTime`. -/
def gaussTime2 (lam a t : ℝ) : ℝ :=
  2 * (2 * π * lam) ^ (-(1 / 2 : ℝ)) * Real.exp (-(t ^ 2) / (2 * lam))
    * ((t ^ 2 / lam ^ 2 - 1 / lam - a ^ 2) * Real.cos (a * t)
      + 2 * a * t / lam * Real.sin (a * t))

/-- The derivative of `e^{-t²/2λ}`. -/
theorem hasDerivAt_gexp (lam t : ℝ) :
    HasDerivAt (fun t => Real.exp (-(t ^ 2) / (2 * lam)))
      (Real.exp (-(t ^ 2) / (2 * lam)) * (-(t / lam))) t := by
  have h := ((hasDerivAt_pow 2 t).neg.div_const (2 * lam)).exp
  exact h.congr_deriv (by simp only [Pi.neg_apply]; push_cast; ring)

/-- `gaussTime' = gaussTime1`. -/
theorem hasDerivAt_gaussTime (lam a t : ℝ) :
    HasDerivAt (gaussTime lam a) (gaussTime1 lam a t) t := by
  have h1 : HasDerivAt (fun t => Real.cos (a * t)) (-Real.sin (a * t) * a) t := by
    simpa using ((hasDerivAt_id t).const_mul a).cos
  have h := (h1.const_mul (2 * (2 * π * lam) ^ (-(1 / 2 : ℝ)))).mul (hasDerivAt_gexp lam t)
  exact h.congr_deriv (by unfold gaussTime1; ring)

/-- `gaussTime1' = gaussTime2`. -/
theorem hasDerivAt_gaussTime1 (lam a t : ℝ) :
    HasDerivAt (gaussTime1 lam a) (gaussTime2 lam a t) t := by
  have hs : HasDerivAt (fun t => Real.sin (a * t)) (Real.cos (a * t) * a) t := by
    simpa using ((hasDerivAt_id t).const_mul a).sin
  have hc : HasDerivAt (fun t => Real.cos (a * t)) (-Real.sin (a * t) * a) t := by
    simpa using ((hasDerivAt_id t).const_mul a).cos
  have hq := (hs.const_mul (-a)).sub (((hasDerivAt_id t).div_const lam).mul hc)
  have h := ((hasDerivAt_gexp lam t).const_mul (2 * (2 * π * lam) ^ (-(1 / 2 : ℝ)))).mul hq
  exact h.congr_deriv (by unfold gaussTime2; simp only [Pi.sub_apply, Pi.mul_apply, id]; ring)

/-- `gaussTime` is continuous. -/
theorem continuous_gaussTime (lam a : ℝ) : Continuous (gaussTime lam a) := by
  unfold gaussTime; fun_prop

/-- `gaussTime1` is continuous. -/
theorem continuous_gaussTime1 (lam a : ℝ) : Continuous (gaussTime1 lam a) := by
  unfold gaussTime1; fun_prop

/-- `gaussTime2` is continuous. -/
theorem continuous_gaussTime2 (lam a : ℝ) : Continuous (gaussTime2 lam a) := by
  unfold gaussTime2; fun_prop

/-- **`gaussTime` and its first two derivatives are bounded** on `ℝ`, by one constant. -/
theorem exists_gaussTime_bound {lam : ℝ} (hlam : 0 < lam) (a : ℝ) :
    ∃ M : ℝ, ∀ t, |gaussTime lam a t| ≤ M ∧ |gaussTime1 lam a t| ≤ M
      ∧ |gaussTime2 lam a t| ≤ M := by
  set K : ℝ := 2 * (2 * π * lam) ^ (-(1 / 2 : ℝ)) with hK
  have hK0 : 0 ≤ K := by positivity
  have hE1 : ∀ t : ℝ, Real.exp (-(t ^ 2) / (2 * lam)) ≤ 1 := fun t =>
    Real.exp_le_one_iff.mpr
      (div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg t]) (by positivity))
  have hE2 : ∀ t : ℝ, t ^ 2 * Real.exp (-(t ^ 2) / (2 * lam)) ≤ 2 * lam := fun t => by
    have h := (Real.mul_exp_neg_le_exp_neg_one (t ^ 2 / (2 * lam))).trans
      (Real.exp_le_one_iff.mpr (by norm_num))
    rw [show -(t ^ 2 / (2 * lam)) = -(t ^ 2) / (2 * lam) by ring] at h
    have : t ^ 2 * Real.exp (-(t ^ 2) / (2 * lam))
        = 2 * lam * (t ^ 2 / (2 * lam) * Real.exp (-(t ^ 2) / (2 * lam))) := by field_simp
    rw [this]; nlinarith
  have hE3 : ∀ t : ℝ, |t| * Real.exp (-(t ^ 2) / (2 * lam)) ≤ 1 + 2 * lam := fun t => by
    have ht : |t| ≤ 1 + t ^ 2 := by nlinarith [abs_nonneg t, sq_abs t, sq_nonneg (|t| - 1)]
    have hp := Real.exp_pos (-(t ^ 2) / (2 * lam))
    calc |t| * Real.exp (-(t ^ 2) / (2 * lam))
        ≤ (1 + t ^ 2) * Real.exp (-(t ^ 2) / (2 * lam)) := mul_le_mul_of_nonneg_right ht hp.le
      _ = Real.exp (-(t ^ 2) / (2 * lam)) + t ^ 2 * Real.exp (-(t ^ 2) / (2 * lam)) := by ring
      _ ≤ 1 + 2 * lam := add_le_add (hE1 t) (hE2 t)
  set S : ℝ := |a| + (1 + 2 * lam) / lam + 2 * lam / lam ^ 2 + 1 / lam + a ^ 2
    + 2 * |a| * (1 + 2 * lam) / lam + 1 with hS
  set M₀ : ℝ := K * S with hM
  refine ⟨M₀, fun t => ?_⟩
  set E := Real.exp (-(t ^ 2) / (2 * lam)) with hEdef
  have hEp : 0 < E := Real.exp_pos _
  have hc := Real.abs_cos_le_one (a * t)
  have hsn := Real.abs_sin_le_one (a * t)
  have e1 := hE1 t; have e2 := hE2 t; have e3 := hE3 t
  have hl : 0 < lam := hlam
  have ha := abs_nonneg a
  have hta : |t| * E / lam ≤ (1 + 2 * lam) / lam := by gcongr
  have ht2 : t ^ 2 * E / lam ^ 2 ≤ 2 * lam / lam ^ 2 := by gcongr
  have hpos1 : 0 ≤ (1 + 2 * lam) / lam := by positivity
  have hpos2 : 0 ≤ 2 * lam / lam ^ 2 := by positivity
  have hpos3 : 0 ≤ 2 * |a| * (1 + 2 * lam) / lam := by positivity
  refine ⟨?_, ?_, ?_⟩
  · unfold gaussTime
    rw [abs_mul, abs_mul, abs_of_nonneg hK0, abs_of_pos hEp]
    have h1S : 1 ≤ S := by
      have : 0 ≤ 1 / lam := by positivity
      rw [hS]; nlinarith [sq_nonneg a]
    calc K * |Real.cos (a * t)| * E ≤ K * 1 * 1 := by gcongr
      _ = K * 1 := by ring
      _ ≤ M₀ := mul_le_mul_of_nonneg_left h1S hK0
  · unfold gaussTime1
    rw [abs_mul, abs_mul, abs_of_nonneg hK0, abs_of_pos hEp]
    have hb : E * |-a * Real.sin (a * t) - t / lam * Real.cos (a * t)|
        ≤ |a| + (1 + 2 * lam) / lam := by
      calc E * |-a * Real.sin (a * t) - t / lam * Real.cos (a * t)|
          ≤ E * (|a| * |Real.sin (a * t)| + |t| / lam * |Real.cos (a * t)|) := by
            gcongr
            refine (abs_sub _ _).trans ?_
            rw [abs_mul, abs_mul, abs_neg, abs_div, abs_of_pos hl]
        _ ≤ E * (|a| * 1 + |t| / lam * 1) := by gcongr
        _ = |a| * E + |t| * E / lam := by ring
        _ ≤ |a| * 1 + (1 + 2 * lam) / lam := by gcongr
        _ = |a| + (1 + 2 * lam) / lam := by ring
    calc K * E * |-a * Real.sin (a * t) - t / lam * Real.cos (a * t)|
        = K * (E * |-a * Real.sin (a * t) - t / lam * Real.cos (a * t)|) := by ring
      _ ≤ K * (|a| + (1 + 2 * lam) / lam) := by gcongr
      _ ≤ M₀ := by
          refine mul_le_mul_of_nonneg_left ?_ hK0
          have : 0 ≤ 1 / lam := by positivity
          rw [hS]; nlinarith [sq_nonneg a]
  · unfold gaussTime2
    rw [abs_mul, abs_mul, abs_of_nonneg hK0, abs_of_pos hEp]
    have hb : E * |(t ^ 2 / lam ^ 2 - 1 / lam - a ^ 2) * Real.cos (a * t)
        + 2 * a * t / lam * Real.sin (a * t)|
        ≤ 2 * lam / lam ^ 2 + 1 / lam + a ^ 2 + 2 * |a| * (1 + 2 * lam) / lam := by
      have hq : |t ^ 2 / lam ^ 2 - 1 / lam - a ^ 2| ≤ t ^ 2 / lam ^ 2 + 1 / lam + a ^ 2 := by
        have h1 : 0 ≤ t ^ 2 / lam ^ 2 := by positivity
        have h2 : 0 ≤ 1 / lam := by positivity
        rw [abs_le]; constructor <;> nlinarith [sq_nonneg a]
      have hr : |2 * a * t / lam| = 2 * |a| * |t| / lam := by
        rw [abs_div, abs_mul, abs_mul, abs_of_pos hl, abs_two]
      calc E * |(t ^ 2 / lam ^ 2 - 1 / lam - a ^ 2) * Real.cos (a * t)
            + 2 * a * t / lam * Real.sin (a * t)|
          ≤ E * ((t ^ 2 / lam ^ 2 + 1 / lam + a ^ 2) * 1 + 2 * |a| * |t| / lam * 1) := by
            gcongr
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul, hr]
            gcongr
        _ = t ^ 2 * E / lam ^ 2 + E * (1 / lam + a ^ 2) + 2 * |a| * (|t| * E / lam) := by ring
        _ ≤ 2 * lam / lam ^ 2 + 1 * (1 / lam + a ^ 2) + 2 * |a| * ((1 + 2 * lam) / lam) := by
            have : 0 ≤ 1 / lam + a ^ 2 := by positivity
            gcongr
        _ = _ := by ring
    calc K * E * |(t ^ 2 / lam ^ 2 - 1 / lam - a ^ 2) * Real.cos (a * t)
            + 2 * a * t / lam * Real.sin (a * t)|
        = K * (E * |(t ^ 2 / lam ^ 2 - 1 / lam - a ^ 2) * Real.cos (a * t)
            + 2 * a * t / lam * Real.sin (a * t)|) := by ring
      _ ≤ K * (2 * lam / lam ^ 2 + 1 / lam + a ^ 2 + 2 * |a| * (1 + 2 * lam) / lam) := by
          gcongr
      _ ≤ M₀ := by
          refine mul_le_mul_of_nonneg_left ?_ hK0
          rw [hS]; nlinarith

/-! ### The centred test -/

/-- The centred, endpoint-corrected Gaussian test on `[0, L]`:
`gaussTime(s − L/2) − gaussTime(L/2)`. -/
def testL (lam a L s : ℝ) : ℝ := gaussTime lam a (s - L / 2) - gaussTime lam a (L / 2)

/-- `testL` vanishes at `0`. -/
theorem testL_zero (lam a L : ℝ) : testL lam a L 0 = 0 := by
  unfold testL; rw [zero_sub, gaussTime_neg, sub_self]

/-- `testL` vanishes at `L`. -/
theorem testL_self (lam a L : ℝ) : testL lam a L L = 0 := by
  unfold testL; rw [show L - L / 2 = L / 2 by ring, sub_self]

/-- `testL` is continuous. -/
theorem continuous_testL (lam a L : ℝ) : Continuous (testL lam a L) := by
  have h1 : Continuous (fun s : ℝ => gaussTime lam a (s - L / 2)) :=
    (continuous_gaussTime lam a).comp (continuous_id.sub continuous_const)
  exact h1.sub continuous_const

/-- `testL' = gaussTime1(· − L/2)`. -/
theorem hasDerivAt_testL (lam a L s : ℝ) :
    HasDerivAt (testL lam a L) (gaussTime1 lam a (s - L / 2)) s := by
  have h : HasDerivAt (fun s : ℝ => gaussTime lam a (s - L / 2)) (gaussTime1 lam a (s - L / 2)) s :=
    HasDerivAt.comp_sub_const s (L / 2) (hasDerivAt_gaussTime lam a (s - L / 2))
  exact h.sub_const (gaussTime lam a (L / 2))

/-- `gaussTime1(· − L/2)' = gaussTime2(· − L/2)`, the second derivative of `testL`. -/
theorem hasDerivAt_gaussTime1_sub (lam a L s : ℝ) :
    HasDerivAt (fun s => gaussTime1 lam a (s - L / 2)) (gaussTime2 lam a (s - L / 2)) s := by
  exact HasDerivAt.comp_sub_const s (L / 2) (hasDerivAt_gaussTime1 lam a (s - L / 2))

/-- **`testL` is admissible**: its window transform is bounded on `|Im ξ| ≤ 3/2` and `O(‖ξ‖⁻²)`
there (Cvs.Finite.OddSectorZeroSide). -/
theorem testL_admissible {lam : ℝ} (hlam : 0 < lam) (a : ℝ) {L : ℝ} (hL : 0 < L) :
    ∃ C0 C2 : ℝ, 0 ≤ C0 ∧ 0 ≤ C2
      ∧ (∀ ξ : ℂ, |ξ.im| ≤ 3 / 2 →
          ‖Cvs.Detection.windowTransform L (Cvs.WeilForm.SelfConvolutionTransform.cf (testL lam a L)) ξ‖ ≤ C0)
      ∧ (∀ ξ : ℂ, ξ ≠ 0 → |ξ.im| ≤ 3 / 2 →
          ‖Cvs.Detection.windowTransform L (Cvs.WeilForm.SelfConvolutionTransform.cf (testL lam a L)) ξ‖ ≤ C2 / ‖ξ‖ ^ 2) := by
  obtain ⟨M, hM⟩ := exists_gaussTime_bound hlam a
  refine Cvs.Finite.OddSectorZeroSide.admissible_of_C2 hL (hasDerivAt_testL lam a L) (hasDerivAt_gaussTime1_sub lam a L)
    (continuous_testL lam a L)
    ((continuous_gaussTime1 lam a).comp (continuous_id.sub continuous_const))
    ((continuous_gaussTime2 lam a).comp (continuous_id.sub continuous_const))
    (testL_zero lam a L) (testL_self lam a L) (M0 := M + M) (M2 := M) (fun s => ?_)
    (fun s => (hM _).2.2)
  unfold testL
  exact (abs_sub _ _).trans (add_le_add (hM _).1 (hM _).1)

/-- **`testL` on `[0, L]`, extended by zero, is Lipschitz.** -/
theorem lipschitz_indicator_testL {lam : ℝ} (hlam : 0 < lam) (a : ℝ) {L : ℝ} (hL : 0 < L) :
    ∃ K : ℝ, ∀ s t : ℝ, |(Set.Icc (0:ℝ) L).indicator (testL lam a L) s
      - (Set.Icc (0:ℝ) L).indicator (testL lam a L) t| ≤ K * |s - t| := by
  obtain ⟨M, hM⟩ := exists_gaussTime_bound hlam a
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0).1
  have hlip : ∀ s t : ℝ, |testL lam a L s - testL lam a L t| ≤ M * |s - t| := by
    intro s t
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := testL lam a L)
      (f' := fun u => gaussTime1 lam a (u - L / 2)) (s := Set.univ) (C := M)
      (fun u _ => (hasDerivAt_testL lam a L u).hasDerivWithinAt)
      (fun u _ => by rw [Real.norm_eq_abs]; exact (hM _).2.1) convex_univ (Set.mem_univ t)
      (Set.mem_univ s)
    simpa [Real.norm_eq_abs] using h
  have h : (Set.Icc (0:ℝ) L).indicator (testL lam a L)
      = fun s => testL lam a L (Set.projIcc 0 L hL.le s) := by
    funext s
    by_cases h0 : s < 0
    · rw [indicator_of_notMem (fun (h : s ∈ Set.Icc (0:ℝ) L) => absurd h.1 (not_le.2 h0)), Set.projIcc_of_le_left _ h0.le]
      simp [testL_zero]
    by_cases h1 : L < s
    · rw [indicator_of_notMem (fun (h : s ∈ Set.Icc (0:ℝ) L) => absurd h.2 (not_le.2 h1)),
        Set.projIcc_of_right_le _ h1.le]
      simp [testL_self]
    push Not at h0 h1
    rw [indicator_of_mem (show s ∈ Set.Icc (0:ℝ) L from ⟨h0, h1⟩),
      Set.projIcc_of_mem _ (show s ∈ Set.Icc (0:ℝ) L from ⟨h0, h1⟩)]
  refine ⟨M, fun s t => ?_⟩
  rw [h]
  refine (hlip _ _).trans (mul_le_mul_of_nonneg_left ?_ hM0)
  have := (LipschitzWith.projIcc (a := (0:ℝ)) (b := L) hL.le).dist_le_mul s t
  simp only [NNReal.coe_one, one_mul, Subtype.dist_eq, Real.dist_eq] at this
  exact this

/-- `testL` on `[0, L]`, extended by zero, is continuous. -/
theorem continuous_indicator_testL (lam a : ℝ) {L : ℝ} (hL : 0 < L) :
    Continuous ((Set.Icc (0:ℝ) L).indicator (testL lam a L)) := by
  have h : (Set.Icc (0:ℝ) L).indicator (testL lam a L)
      = Set.IccExtend hL.le (fun s => testL lam a L s) := by
    funext s
    by_cases h0 : s < 0
    · rw [indicator_of_notMem (fun (h : s ∈ Set.Icc (0:ℝ) L) => absurd h.1 (not_le.2 h0)),
        Set.IccExtend_of_le_left _ _ h0.le]
      simp [testL_zero]
    by_cases h1 : L < s
    · rw [indicator_of_notMem (fun (h : s ∈ Set.Icc (0:ℝ) L) => absurd h.2 (not_le.2 h1)),
        Set.IccExtend_of_right_le _ _ h1.le]
      simp [testL_self]
    push Not at h0 h1
    rw [indicator_of_mem (show s ∈ Set.Icc (0:ℝ) L from ⟨h0, h1⟩),
      Set.IccExtend_of_mem _ _ (show s ∈ Set.Icc (0:ℝ) L from ⟨h0, h1⟩)]
  rw [h]
  exact ((continuous_testL lam a L).comp continuous_subtype_val).Icc_extend'

end Cvs.WeilForm.CentredGaussianTest
