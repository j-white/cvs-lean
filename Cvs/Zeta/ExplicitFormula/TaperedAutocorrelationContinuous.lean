import Mathlib.Analysis.Fourier.Convolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Cvs.Zeta.ExplicitFormula.AutocorrelationConvolution
import Cvs.Zeta.ExplicitFormula.AutocorrelationSupport
import Cvs.Zeta.ExplicitFormula.WindowTransformFullLine

/-!
# The taper makes the truncated test continuous, and the autocorrelation with it

The inversion step needs `Continuous R`, and Mathlib's convolution-continuity lemmas
(`HasCompactSupport.continuous_convolution_right` and its variants) all require one factor to
be continuous.
-/

namespace Cvs.Detection

open Complex MeasureTheory Convolution
open scoped Real

/-- The indicator on `Ioc 0 L` agrees with a two-sided cutoff once `f 0 = 0`. -/
theorem truncate_eq_ite {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℂ} (h0 : f 0 = 0) (s : ℝ) :
    Cvs.Detection.truncate L f s = if 0 ≤ s then (if s ≤ L then f s else 0) else 0 := by
  by_cases hs : s ∈ Set.Ioc (0 : ℝ) L
  · rw [Set.mem_Ioc] at hs
    rw [Cvs.Detection.truncate_of_mem (Set.mem_Ioc.mpr hs), if_pos hs.1.le, if_pos hs.2]
  · rw [Cvs.Detection.truncate_of_not_mem hs]
    rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hs
    rcases hs with h | h
    · -- s ≤ 0
      rcases eq_or_lt_of_le h with heq | hlt
      · rw [if_pos (by linarith : (0:ℝ) ≤ s), if_pos (by linarith : s ≤ L), heq, h0]
      · rw [if_neg (by linarith)]
    · -- L < s
      rw [if_pos (by linarith : (0:ℝ) ≤ s), if_neg (by linarith)]

/-- **The taper makes the truncated test continuous.** -/
theorem continuous_truncate {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℂ} (hf : Continuous f)
    (h0 : f 0 = 0) (hLz : f L = 0) : Continuous (Cvs.Detection.truncate L f) := by
  have hinner : Continuous (fun s : ℝ => if s ≤ L then f s else 0) := by
    refine hf.if_le continuous_const continuous_id continuous_const (fun x hx => ?_)
    rw [hx]
    exact hLz
  have houter : Continuous (fun s : ℝ => if (0:ℝ) ≤ s then (if s ≤ L then f s else 0) else 0) := by
    refine Continuous.if_le hinner continuous_const continuous_const continuous_id (fun x hx => ?_)
    rw [← hx, if_pos hL, h0]
  exact houter.congr (fun s => (truncate_eq_ite hL h0 s).symm)

theorem continuous_reflect_truncate {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℂ} (hf : Continuous f)
    (h0 : f 0 = 0) (hLz : f L = 0) :
    Continuous (Cvs.Detection.reflect (Cvs.Detection.truncate L f)) := by
  show Continuous (fun u : ℝ => Cvs.Detection.truncate L f (-u))
  exact (continuous_truncate hL hf h0 hLz).comp continuous_neg

theorem hasCompactSupport_reflect_truncate (L : ℝ) (f : ℝ → ℂ) :
    HasCompactSupport (Cvs.Detection.reflect (Cvs.Detection.truncate L f)) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc (a := (-L : ℝ)) (b := (0:ℝ))) ?_
  intro u hu
  have hne : Cvs.Detection.truncate L f (-u) ≠ 0 := hu
  have hmem := Cvs.Detection.support_truncate L f hne
  rw [Set.mem_Ioc] at hmem
  rw [Set.mem_Icc]
  constructor <;> linarith [hmem.1, hmem.2]

/-- **The autocorrelation is continuous** — the first of inversion's three
hypotheses. -/
theorem continuous_autocorr {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℂ} (hf : Continuous f)
    (h0 : f 0 = 0) (hLz : f L = 0) : Continuous (Cvs.Detection.autocorr L f) := by
  rw [Cvs.Detection.autocorr_eq_convolution]
  exact (hasCompactSupport_reflect_truncate L f).continuous_convolution_right _
    (continuous_truncate hL hf h0 hLz).locallyIntegrable
    (continuous_reflect_truncate hL hf h0 hLz)

end Cvs.Detection
