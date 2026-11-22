import Mathlib
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyMeasure
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SelfConvolutionMaximum
import Cvs.Zeta.WeilPositivityStatement

/-!
# A Lipschitz test with compact support has an integrable Lévy term

    IntegrableOn (u ↦ ρ(u)·(g 0 − g (u/2))) (Ioi 0)

The deficit vanishes quadratically at the origin, which is what the density's `1/u`
singularity there needs; `|F|` is Lipschitz whenever `F` is, so one lemma serves both.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Real Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.Archimedean.LipschitzLevyIntegrable

open Cvs.WeilForm.Archimedean.LevyDensity Cvs.WeilForm.Archimedean.ArchimedeanUnbounded

/-- **The deficit vanishes quadratically.**  A Lipschitz test supported in `[0, L]` has
`g 0 − g v` at most `K²v²(L + 2|v|)/2`. -/
theorem deficit_le_sq {L K : ℝ} (hL : 0 ≤ L) {F : ℝ → ℝ}
    (hlip : ∀ s t : ℝ, |F s - F t| ≤ K * |s - t|)
    (hsupp : ∀ x, x ∉ Icc (0:ℝ) L → F x = 0)
    (hsq : Integrable fun s => (F s) ^ 2) (v : ℝ)
    (hcross : Integrable fun s => F s * F (s + v)) :
    selfConvolution F 0 - selfConvolution F v
      ≤ K ^ 2 * v ^ 2 * (L + 2 * |v|) / 2 := by
  have hshift : Integrable fun s => (F (s + v)) ^ 2 := by
    have := hsq.comp_add_right v
    simpa using this
  have hdiff : Integrable fun s => (F s - F (s + v)) ^ 2 := by
    have hexp : (fun s : ℝ => (F s - F (s + v)) ^ 2)
        = fun s => ((F s) ^ 2 + (F (s + v)) ^ 2) - 2 * (F s * F (s + v)) := by
      funext s; ring
    rw [hexp]
    exact (hsq.add hshift).sub (hcross.const_mul 2)
  -- the integrand is supported in a window of length `L + 2|v|`
  set A : Set ℝ := Icc (-|v|) (L + |v|) with hA
  have hbound : ∀ s : ℝ, (F s - F (s + v)) ^ 2
      ≤ A.indicator (fun _ => K ^ 2 * v ^ 2) s := by
    intro s
    by_cases hs : s ∈ A
    · rw [Set.indicator_of_mem hs]
      have h := hlip s (s + v)
      have habs : |s - (s + v)| = |v| := by
        rw [show s - (s + v) = -v by ring, abs_neg]
      rw [habs] at h
      have hnn : (0:ℝ) ≤ |F s - F (s + v)| := abs_nonneg _
      nlinarith [h, hnn, sq_abs (F s - F (s + v)), sq_abs v]
    · rw [Set.indicator_of_notMem hs]
      have h1 : F s = 0 := by
        refine hsupp s fun hc => hs ?_
        obtain ⟨hc1, hc2⟩ := hc
        exact ⟨by linarith [abs_nonneg v], by linarith [abs_nonneg v]⟩
      have h2 : F (s + v) = 0 := by
        refine hsupp _ fun hc => hs ?_
        obtain ⟨hc1, hc2⟩ := hc
        exact ⟨by linarith [neg_abs_le v, le_abs_self v],
          by linarith [neg_abs_le v, le_abs_self v]⟩
      rw [h1, h2]
      norm_num
  have hindint : Integrable (A.indicator fun _ : ℝ => K ^ 2 * v ^ 2) := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const (measure_Icc_lt_top).ne
  have hle : (∫ s : ℝ, (F s - F (s + v)) ^ 2)
      ≤ ∫ s : ℝ, A.indicator (fun _ => K ^ 2 * v ^ 2) s :=
    integral_mono hdiff hindint hbound
  have hval : (∫ s : ℝ, A.indicator (fun _ => K ^ 2 * v ^ 2) s)
      = K ^ 2 * v ^ 2 * (L + 2 * |v|) := by
    rw [integral_indicator measurableSet_Icc, setIntegral_const,
      Real.volume_real_Icc_of_le (by linarith [abs_nonneg v])]
    rw [show L + |v| - -|v| = L + 2 * |v| by ring]
    ring
  rw [hval] at hle
  rw [Cvs.WeilForm.SelfConvolutionFunctional.integral_sq_sub_eq v hsq hcross] at hle
  linarith

/-- **So the Lévy term is integrable.**  The density's `1/u` singularity at the origin is
absorbed by the deficit's quadratic vanishing. -/
theorem integrableOn_levy_of_lipschitz {L K : ℝ} (hL : 0 ≤ L) {F : ℝ → ℝ}
    (hFc : Continuous F) (hlip : ∀ s t : ℝ, |F s - F t| ≤ K * |s - t|)
    (hsupp : ∀ x, x ∉ Icc (0:ℝ) L → F x = 0)
    (hsq : Integrable fun s => (F s) ^ 2)
    (hcross : ∀ v : ℝ, Integrable fun s => F s * F (s + v)) :
    IntegrableOn (fun u => densityU u
      * (selfConvolution F 0 - selfConvolution F (u / 2))) (Ioi (0:ℝ)) := by
  set C : ℝ := 2 * selfConvolution F 0 + K ^ 2 * (L + 1) / 8 with hC
  have hg0 : 0 ≤ selfConvolution F 0 := by
    have h := Cvs.WeilForm.SelfConvolutionMaximum.selfConvolution_le (f := F) 0 hsq (hcross 0)
    have h2 := Cvs.WeilForm.SelfConvolutionMaximum.neg_le_selfConvolution (f := F) 0 hsq (hcross 0)
    linarith
  have hCnn : 0 ≤ C := by
    rw [hC]
    nlinarith [hg0, sq_nonneg K, hL]
  have hmeas : Measurable fun u : ℝ => selfConvolution F (u / 2) := by
    have hjoint : Measurable (Function.uncurry fun u s : ℝ => F s * F (s + u / 2)) :=
      (hFc.measurable.comp measurable_snd).mul
        (hFc.measurable.comp (measurable_snd.add (measurable_fst.div_const 2)))
    exact (MeasureTheory.StronglyMeasurable.integral_prod_right
      (ν := (volume : Measure ℝ)) hjoint.stronglyMeasurable).measurable
  refine Integrable.mono'
    ((Cvs.WeilForm.Archimedean.LevyMeasure.integrableOn_min_mul_densityU).const_mul C) ?_ ?_
  · exact ((Cvs.WeilForm.Archimedean.LevyMeasure.measurable_densityU.mul
      (measurable_const.sub hmeas)).aestronglyMeasurable)
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun u hu => ?_
    have hu0 : (0:ℝ) < u := hu
    have hd : 0 ≤ densityU u := (densityU_pos hu0).le
    have hlo : 0 ≤ selfConvolution F 0 - selfConvolution F (u / 2) := by
      have := Cvs.WeilForm.SelfConvolutionMaximum.selfConvolution_le (f := F) (u / 2) hsq (hcross _)
      linarith
    have hhi : selfConvolution F 0 - selfConvolution F (u / 2) ≤ C * min 1 (u ^ 2) := by
      rcases le_or_gt u 1 with h1 | h1
      · have hmin : min 1 (u ^ 2) = u ^ 2 := by
          refine min_eq_right ?_
          nlinarith [hu0, h1]
        rw [hmin]
        have hdef := deficit_le_sq hL hlip hsupp hsq (u / 2) (hcross _)
        have habs : |u / 2| = u / 2 := abs_of_pos (by linarith)
        rw [habs] at hdef
        have hkey : K ^ 2 * (u / 2) ^ 2 * (L + 2 * (u / 2)) / 2 ≤ C * u ^ 2 := by
          rw [hC]
          nlinarith [sq_nonneg K, sq_nonneg u, hg0, hu0, h1, hL,
            mul_nonneg (sq_nonneg K) (sq_nonneg u)]
        linarith
      · have hmin : min 1 (u ^ 2) = 1 := by
          refine min_eq_left ?_
          nlinarith [h1]
        rw [hmin, mul_one, hC]
        have := Cvs.WeilForm.SelfConvolutionMaximum.neg_le_selfConvolution (f := F) (u / 2) hsq (hcross _)
        nlinarith [sq_nonneg K, hL, hg0]
    rw [Real.norm_of_nonneg (mul_nonneg hd hlo)]
    calc densityU u * (selfConvolution F 0 - selfConvolution F (u / 2))
        ≤ densityU u * (C * min 1 (u ^ 2)) := mul_le_mul_of_nonneg_left hhi hd
      _ = C * (min 1 (u ^ 2) * densityU u) := by ring

end Cvs.WeilForm.Archimedean.LipschitzLevyIntegrable
