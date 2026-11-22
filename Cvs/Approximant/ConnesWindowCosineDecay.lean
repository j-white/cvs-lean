import Mathlib
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.Finite.WindowCosineBessel
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowFormTailLimit
import Cvs.Upstream.RealFunctionTransformSplit
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.WeilForm.WindowFourierBoundedLipschitz
import Cvs.Xi.EImageWindowPoisson
import Cvs.Zeta.ZeroCounting.BucketStepTightened

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Reciprocal cosine decay for the actual Connes window

The actual Connes cosine coefficients sample the real part of its tame window's Mellin
transform, and are bounded by a fixed multiple of the reciprocal mode number.
-/

noncomputable section

open Real Set MeasureTheory Filter
open scoped FourierTransform

namespace Cvs.Approximant.ConnesWindowCosineDecay
open Cvs.ZeroCounting

set_option maxHeartbeats 1200000

/-- The theta-space window whose translated log scale is Connes' test. -/
def connesWindow (x : ℕ) : ℝ → ℝ :=
  Cvs.Xi.EImageWindowPoisson.window (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (S := {1}) fun _ => 1)

/-- Connes' actual theta-space window is tame on `[1/x,1]`. -/
theorem tame_connesWindow {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    Cvs.L2a.WindowFormTailLimit.Tame (connesWindow x) (1 / x) 1 := by
  have h := Cvs.Approximant.SpineSubspace.tame_spine hx (Cvs.Approximant.CosineColumnTailPairing.singleton_lt_of_scale hx) (fun _ => 1)
  have ha : 2 * π / (2 * π * x) = 1 / x := by field_simp
  simpa only [ha, connesWindow] using h

/-- Connes' actual test is integrable on the line. -/
theorem integrable_connesK {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    Integrable (Cvs.Approximant.ConnesVectorRealScale.connesK x) := by
  have h := (tame_connesWindow hx).log.1.comp_add_right (-Real.log x)
  change Integrable (fun s => Cvs.L2a.TailLogScaleTest.logScale (connesWindow x) (s - Real.log x))
  simpa only [sub_eq_add_neg] using h

/-- A nonzero cosine coefficient of an integrable window function samples its Fourier real part. -/
theorem coef_eq_fourier_re {L : ℝ} (hL : 0 < L) {g : ℝ → ℝ} (hg : Integrable g)
    (hsupp : ∀ᵐ s ∂volume, s ∉ Ioc (0 : ℝ) L → g s = 0) {n : ℕ} (hn : n ≠ 0) :
    Cvs.Finite.WindowCosineBessel.coef L g n = 2 / L * (𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf g) ((n : ℝ) / L)).re := by
  have hcos : (∫ s, g s * Real.cos (2 * π * ((n : ℝ) / L) * s))
      = ∫ s in Ioc (0 : ℝ) L, g s * Real.cos (2 * π * ((n : ℝ) / L) * s) := by
    rw [← integral_indicator measurableSet_Ioc]
    refine integral_congr_ae ?_
    filter_upwards [hsupp] with s hs
    by_cases hmem : s ∈ Ioc (0 : ℝ) L
    · rw [indicator_of_mem hmem]
    · rw [indicator_of_notMem hmem, hs hmem, zero_mul]
  have hRe : (𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf g) ((n : ℝ) / L)).re
      = Cvs.Upstream.RealFunctionTransformSplit.cosPart g ((n : ℝ) / L) := by
    rw [show Cvs.WeilForm.SelfConvolutionTransform.cf g = (fun s => (g s : ℂ)) from rfl, Cvs.Upstream.RealFunctionTransformSplit.fourier_real_split hg]
    simp
  rw [Cvs.Finite.WindowCosineBessel.coef, ite_eq_right hn, hRe, Cvs.Upstream.RealFunctionTransformSplit.cosPart, hcos,
    intervalIntegral.integral_of_le hL.le]
  refine congrArg (2 / L * ·) (setIntegral_congr_fun measurableSet_Ioc fun s _ => ?_)
  exact congrArg (g s * ·) (congrArg Real.cos (by ring))

/-- Translation through the whole log window preserves each grid cosine pairing. -/
theorem cosPart_connesK_grid {x : ℕ} (hx : (1 : ℝ) < x) (n : ℕ) :
    Cvs.Upstream.RealFunctionTransformSplit.cosPart (Cvs.Approximant.ConnesVectorRealScale.connesK x) ((n : ℝ) / Real.log x)
      = Cvs.Upstream.RealFunctionTransformSplit.cosPart (Cvs.L2a.TailLogScaleTest.logScale (connesWindow x)) ((n : ℝ) / Real.log x) := by
  have hL : Real.log (x : ℝ) ≠ 0 := (Real.log_pos hx).ne'
  unfold Cvs.Upstream.RealFunctionTransformSplit.cosPart
  rw [← integral_add_right_eq_self (μ := volume)
    (fun s => Cvs.Approximant.ConnesVectorRealScale.connesK x s * Real.cos (2 * π * ((n : ℝ) / Real.log x) * s)) (Real.log x)]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  change Cvs.L2a.TailLogScaleTest.logScale (connesWindow x) (s + Real.log x - Real.log x)
      * Real.cos (2 * π * ((n : ℝ) / Real.log x) * (s + Real.log x))
    = Cvs.L2a.TailLogScaleTest.logScale (connesWindow x) s * Real.cos (2 * π * ((n : ℝ) / Real.log x) * s)
  rw [add_sub_cancel_right]
  rw [show 2 * π * ((n : ℝ) / Real.log x) * (s + Real.log x)
      = 2 * π * ((n : ℝ) / Real.log x) * s + (n : ℝ) * (2 * π) by field_simp,
    Real.cos_add_nat_mul_two_pi]

/-- The actual Connes cosine coefficient is an exact Mellin sample on the critical line. -/
theorem connes_coef_eq_mellin {x : ℕ} (hx : 80 ≤ 2 * π * x) {n : ℕ} (hn : n ≠ 0) :
    Cvs.Finite.WindowCosineBessel.coef (Real.log x) (Cvs.Approximant.ConnesVectorRealScale.connesK x) n
      = 2 / Real.log x * (Cvs.WeilForm.ThetaSpaceParseval.mellinR (connesWindow x)
        (1 / 2 - ((2 * π * n / Real.log x : ℝ) : ℂ) * Complex.I)).re := by
  have hx1 := Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx
  have hK := integrable_connesK hx
  have hF := (tame_connesWindow hx).log.1
  rw [coef_eq_fourier_re (Real.log_pos hx1) hK
    (Cvs.Approximant.ConnesVectorRealScale.connesK_ae_supp (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx)) hn]
  have hReK : (𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Approximant.ConnesVectorRealScale.connesK x)) ((n : ℝ) / Real.log x)).re
      = Cvs.Upstream.RealFunctionTransformSplit.cosPart (Cvs.Approximant.ConnesVectorRealScale.connesK x) ((n : ℝ) / Real.log x) := by
    rw [show Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Approximant.ConnesVectorRealScale.connesK x) = (fun s => (Cvs.Approximant.ConnesVectorRealScale.connesK x s : ℂ)) from rfl,
      Cvs.Upstream.RealFunctionTransformSplit.fourier_real_split hK]
    simp
  have hReF : (𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.L2a.TailLogScaleTest.logScale (connesWindow x))) ((n : ℝ) / Real.log x)).re
      = Cvs.Upstream.RealFunctionTransformSplit.cosPart (Cvs.L2a.TailLogScaleTest.logScale (connesWindow x)) ((n : ℝ) / Real.log x) := by
    rw [show Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.L2a.TailLogScaleTest.logScale (connesWindow x))
      = (fun s => (Cvs.L2a.TailLogScaleTest.logScale (connesWindow x) s : ℂ)) from rfl,
      Cvs.Upstream.RealFunctionTransformSplit.fourier_real_split hF]
    simp
  have hgrid : (2 * π * n / Real.log x) / (2 * π) = (n : ℝ) / Real.log x := by field_simp
  have hm := Cvs.WeilForm.ThetaSpaceParseval.fourier_logScale (connesWindow x) (2 * π * n / Real.log x)
  rw [hgrid] at hm
  rw [hReK, cosPart_connesK_grid hx1, ← hReF, hm]

/-- The actual Connes window has reciprocal Mellin decay at every positive critical-line height. -/
theorem exists_connes_mellin_bound {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t →
      ‖Cvs.WeilForm.ThetaSpaceParseval.mellinR (connesWindow x) (1 / 2 - (t : ℂ) * Complex.I)‖ ≤ C / t := by
  have hF := tame_connesWindow hx
  obtain ⟨C, hC⟩ := hF.dec
  let A : ℝ := ∫ s, ‖Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.L2a.TailLogScaleTest.logScale (connesWindow x)) s‖
  have hA : 0 ≤ A := integral_nonneg fun _ => norm_nonneg _
  refine ⟨max C A, le_trans hA (le_max_right _ _), fun t ht => ?_⟩
  by_cases ht1 : 1 ≤ t
  · have h := hC (1 / 2 - (t : ℂ) * Complex.I) (by norm_num) (by norm_num) (by simpa [abs_of_pos ht] using ht1)
    have h' : ‖Cvs.WeilForm.ThetaSpaceParseval.mellinR (connesWindow x) (1 / 2 - (t : ℂ) * Complex.I)‖ ≤ C / t := by
      simpa [abs_of_pos ht] using h
    exact h'.trans (div_le_div_of_nonneg_right (le_max_left _ _) ht.le)
  · have hb : ‖Cvs.WeilForm.ThetaSpaceParseval.mellinR (connesWindow x) (1 / 2 - (t : ℂ) * Complex.I)‖ ≤ A := by
      rw [← Cvs.WeilForm.ThetaSpaceParseval.fourier_logScale]
      exact Cvs.WeilForm.WindowFourierBoundedLipschitz.norm_fourier_le _ _
    apply (le_div_iff₀ ht).mpr
    have ht2 : t ≤ 1 := (lt_of_not_ge ht1).le
    have hmax := le_max_right C A
    nlinarith [mul_le_mul_of_nonneg_right hb ht.le, mul_le_mul_of_nonneg_left ht2 hA]

/-- Every nonzero cosine coefficient of the actual Connes profile has reciprocal mode decay. -/
theorem exists_connes_coef_bound {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, n ≠ 0 →
      |Cvs.Finite.WindowCosineBessel.coef (Real.log x) (Cvs.Approximant.ConnesVectorRealScale.connesK x) n| ≤ C / (π * n) := by
  obtain ⟨C, hC, hb⟩ := exists_connes_mellin_bound hx
  refine ⟨C, hC, fun n hn => ?_⟩
  have hL := Real.log_pos (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have ht : 0 < 2 * π * n / Real.log x := by positivity
  rw [connes_coef_eq_mellin hx hn, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / Real.log x)]
  calc
    (2 / Real.log x) * |(Cvs.WeilForm.ThetaSpaceParseval.mellinR (connesWindow x)
        (1 / 2 - ((2 * π * n / Real.log x : ℝ) : ℂ) * Complex.I)).re|
        ≤ (2 / Real.log x) * ‖Cvs.WeilForm.ThetaSpaceParseval.mellinR (connesWindow x)
          (1 / 2 - ((2 * π * n / Real.log x : ℝ) : ℂ) * Complex.I)‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by positivity)
    _ ≤ (2 / Real.log x) * (C / (2 * π * n / Real.log x)) :=
      mul_le_mul_of_nonneg_left (hb _ ht) (by positivity)
    _ = C / (π * n) := by field_simp

/-- The actual Connes cosine coefficients have summable logarithm-squared weighted squares. -/
theorem summable_connes_coef_log_sq {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    Summable (fun n : ℕ => (1 + Real.log ((n + 1 : ℕ) : ℝ)) ^ 2
      * Cvs.Finite.WindowCosineBessel.coef (Real.log x) (Cvs.Approximant.ConnesVectorRealScale.connesK x) (n + 1) ^ 2) := by
  obtain ⟨C, hC, hb⟩ := exists_connes_coef_bound hx
  have hp : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2) : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hps : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-(3 / 2) : ℝ)) :=
    hp.comp_injective (fun m n h => by omega)
  apply Summable.of_nonneg_of_le (fun _ => by positivity) (f := fun n : ℕ =>
    (34 * C ^ 2 / π ^ 2) * ((n + 1 : ℕ) : ℝ) ^ (-(3 / 2) : ℝ)) _ (hps.mul_left _)
  intro n
  let z : ℝ := ((n + 1 : ℕ) : ℝ)
  have hz1 : 1 ≤ z := by dsimp [z]; exact_mod_cast (show 1 ≤ n + 1 by omega)
  have hz : 0 < z := lt_of_lt_of_le zero_lt_one hz1
  have hzpow : 1 ≤ z ^ (1 / 2 : ℝ) := Real.one_le_rpow hz1 (by norm_num)
  have hl := Cvs.Zeta.ZeroCounting.BucketStepTightened.logsq_le hz1
  have hw : (1 + Real.log z) ^ 2 ≤ 34 * z ^ (1 / 2 : ℝ) := by
    nlinarith [sq_nonneg (Real.log z - 1)]
  have ha : |Cvs.Finite.WindowCosineBessel.coef (Real.log x) (Cvs.Approximant.ConnesVectorRealScale.connesK x) (n + 1)| ≤ C / (π * z) :=
    hb (n + 1) (by omega)
  have hasq : Cvs.Finite.WindowCosineBessel.coef (Real.log x) (Cvs.Approximant.ConnesVectorRealScale.connesK x) (n + 1) ^ 2
      ≤ C ^ 2 / (π ^ 2 * z ^ 2) := by
    have h := pow_le_pow_left₀ (abs_nonneg _) ha 2
    simpa only [sq_abs, div_pow, mul_pow] using h
  have hr : z ^ (-(3 / 2) : ℝ) = z ^ (1 / 2 : ℝ) / z ^ 2 := by
    rw [← Real.rpow_natCast z 2, ← Real.rpow_sub hz]
    norm_num
  change (1 + Real.log z) ^ 2 * Cvs.Finite.WindowCosineBessel.coef (Real.log x) (Cvs.Approximant.ConnesVectorRealScale.connesK x) (n + 1) ^ 2
    ≤ 34 * C ^ 2 / π ^ 2 * z ^ (-(3 / 2) : ℝ)
  calc
    (1 + Real.log z) ^ 2 * Cvs.Finite.WindowCosineBessel.coef (Real.log x) (Cvs.Approximant.ConnesVectorRealScale.connesK x) (n + 1) ^ 2
        ≤ (34 * z ^ (1 / 2 : ℝ)) * (C ^ 2 / (π ^ 2 * z ^ 2)) :=
      mul_le_mul hw hasq (sq_nonneg _) (by positivity)
    _ = 34 * C ^ 2 / π ^ 2 * z ^ (-(3 / 2) : ℝ) := by rw [hr]; ring

end Cvs.Approximant.ConnesWindowCosineDecay
