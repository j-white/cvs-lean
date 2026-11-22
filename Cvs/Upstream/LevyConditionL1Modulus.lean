import Mathlib
import Cvs.Finite.DiagonalCutSymbol
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.TruncatedArchContinuous
import Cvs.WeilForm.SelfConvolutionContinuous
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Lévy condition from an `L¹` modulus of continuity

`(f⋆f)(0) − (f⋆f)(v) = ∫ f(s)(f(s) − f(s+v))`, so for `|f| ≤ H` and `∫|f(s) − f(s+v)| ≤ Lv` the Lévy integrand is
bounded near `0`; with `|f⋆f| ≤ ∫f²` it is integrable on `(0, ∞)`. Functions with jumps qualify.
-/

namespace Cvs.Upstream.LevyConditionL1Modulus

open Real Set MeasureTheory Cvs.Zeta.Explicit.Weil

/-- `(f⋆f)(0) − (f⋆f)(v) = ∫ f(s)(f(s) − f(s+v))`. -/
theorem selfConvolution_sub {f : ℝ → ℝ} (hf : MemLp f 2 volume) (v : ℝ) :
    selfConvolution f 0 - selfConvolution f v = ∫ s, f s * (f s - f (s + v)) := by
  have hfv : MemLp (fun s => f (s + v)) 2 volume :=
    hf.comp_measurePreserving (measurePreserving_add_right volume v)
  unfold selfConvolution
  simp only [add_zero]
  have h1 : Integrable (fun x => f x * f x) volume := hf.integrable_mul hf
  have h2 : Integrable (fun x => f x * f (x + v)) volume := hf.integrable_mul hfv
  rw [← integral_sub h1 h2]
  congr 1; funext s; ring

/-- **The Lévy condition** for a bounded `L²` function with a linear `L¹` modulus. -/
theorem integrableOn_levy {f : ℝ → ℝ} {H L : ℝ} (hf : MemLp f 2 volume) (hH : ∀ s, |f s| ≤ H)
    (hdi : ∀ v, 0 ≤ v → Integrable (fun s => f s - f (s + v)) volume)
    (hmod : ∀ v, 0 ≤ v → ∫ s, |f s - f (s + v)| ≤ L * v) :
    IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Ioi 0) volume := by
  have hH0 : 0 ≤ H := le_trans (abs_nonneg _) (hH 0)
  have hm : Measurable (selfConvolution f) :=
    (Cvs.WeilForm.SelfConvolutionContinuous.continuous_selfConvolution hf).measurable
  have hinc : ∀ u, 0 ≤ u → u ≤ 2 * 1 → |selfConvolution f 0 - selfConvolution f (u / 2)| ≤ H * L / 2 * u := by
    intro u hu _
    rw [selfConvolution_sub hf]
    have hv : 0 ≤ u / 2 := by linarith
    have hint : Integrable (fun s => f s * (f s - f (s + u / 2))) volume := by
      have hd := hdi (u / 2) hv
      refine hd.bdd_mul (c := H) hf.aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)
      rw [Real.norm_eq_abs]; exact hH s
    calc |∫ s, f s * (f s - f (s + u / 2))| ≤ ∫ s, |f s * (f s - f (s + u / 2))| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ s, H * |f s - f (s + u / 2)| := by
          apply integral_mono hint.abs ((hdi (u / 2) hv).abs.const_mul H)
          intro s; simp only; rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hH s) (abs_nonneg _)
      _ = H * ∫ s, |f s - f (s + u / 2)| := integral_const_mul _ _
      _ ≤ H * (L * (u / 2)) := mul_le_mul_of_nonneg_left (hmod _ hv) hH0
      _ = H * L / 2 * u := by ring
  have hb : ∀ u, 0 ≤ u → |selfConvolution f 0 - selfConvolution f (u / 2)| ≤ 2 * ∫ x, f x ^ 2 := by
    intro u _
    calc |selfConvolution f 0 - selfConvolution f (u / 2)|
        ≤ |selfConvolution f 0| + |selfConvolution f (u / 2)| := abs_sub _ _
      _ ≤ (∫ x, f x ^ 2) + ∫ x, f x ^ 2 :=
          add_le_add (Cvs.WeilForm.Archimedean.TruncatedArchContinuous.abs_selfConvolution_le 0 hf)
            (Cvs.WeilForm.Archimedean.TruncatedArchContinuous.abs_selfConvolution_le _ hf)
      _ = 2 * ∫ x, f x ^ 2 := by ring
  exact Cvs.Finite.DiagonalCutSymbol.integrableOn_densityU_mul_cut one_pos hm hinc hb

/-- **The `L¹` modulus of a cut function**: `f = 1_{(0,B]} h`, `h` bounded by `H` and `Lh`-Lipschitz on `(0, B]`. -/
theorem modulus_cut {h : ℝ → ℝ} {B H Lh v : ℝ} (hB : 0 ≤ B) (hv : 0 ≤ v) (hLh : 0 ≤ Lh) (hH0 : 0 ≤ H)
    (hint : IntegrableOn h (Ioc 0 B) volume) (hbd : ∀ s ∈ Ioc 0 B, |h s| ≤ H)
    (hlip : ∀ s ∈ Ioc 0 B, ∀ t ∈ Ioc 0 B, |h s - h t| ≤ Lh * |s - t|) :
    Integrable (fun s => indicator (Ioc 0 B) h s - indicator (Ioc 0 B) h (s + v)) volume
      ∧ ∫ s, |indicator (Ioc 0 B) h s - indicator (Ioc 0 B) h (s + v)| ≤ (Lh * B + 2 * H) * v := by
  set f := indicator (Ioc 0 B) h with hfdef
  have hfi : Integrable f volume := (integrable_indicator_iff measurableSet_Ioc).mpr hint
  have hfv : Integrable (fun s => f (s + v)) volume := hfi.comp_add_right v
  have hdi : Integrable (fun s => f s - f (s + v)) volume := hfi.sub hfv
  refine ⟨hdi, ?_⟩
  set g1 := indicator (Ioc 0 B) (fun _ => Lh * v) with hg1
  set g2 := indicator (Ioc (-v) 0) (fun _ => H) with hg2
  set g3 := indicator (Ioc (B - v) B) (fun _ => H) with hg3
  have hpt : ∀ s, |f s - f (s + v)| ≤ g1 s + g2 s + g3 s := by
    intro s
    have n1 : 0 ≤ g1 s := indicator_nonneg (fun _ _ => by positivity) s
    have n2 : 0 ≤ g2 s := indicator_nonneg (fun _ _ => hH0) s
    have n3 : 0 ≤ g3 s := indicator_nonneg (fun _ _ => hH0) s
    by_cases h1 : s ∈ Ioc 0 B <;> by_cases h2 : s + v ∈ Ioc 0 B
    · rw [hfdef, indicator_of_mem h1, indicator_of_mem h2, hg1, indicator_of_mem h1]
      have := hlip s h1 (s + v) h2
      rw [show s - (s + v) = -v by ring, abs_neg, abs_of_nonneg hv] at this
      linarith
    · have hs3 : s ∈ Ioc (B - v) B := by
        refine ⟨?_, h1.2⟩
        by_contra hc; push_neg at hc
        exact h2 ⟨by linarith [h1.1], by linarith⟩
      rw [hfdef, indicator_of_mem h1, indicator_of_notMem h2, sub_zero, hg3, indicator_of_mem hs3]
      linarith [hbd s h1]
    · have hs2 : s ∈ Ioc (-v) 0 := by
        refine ⟨by linarith [h2.1], ?_⟩
        by_contra hc; push_neg at hc
        exact h1 ⟨hc, by linarith [h2.2]⟩
      rw [hfdef, indicator_of_notMem h1, indicator_of_mem h2, zero_sub, abs_neg, hg2, indicator_of_mem hs2]
      linarith [hbd (s + v) h2]
    · rw [hfdef, indicator_of_notMem h1, indicator_of_notMem h2, sub_zero, abs_zero]
      linarith
  have i1 : Integrable g1 volume := (integrable_indicator_iff measurableSet_Ioc).mpr (integrableOn_const (by simp))
  have i2 : Integrable g2 volume := (integrable_indicator_iff measurableSet_Ioc).mpr (integrableOn_const (by simp))
  have i3 : Integrable g3 volume := (integrable_indicator_iff measurableSet_Ioc).mpr (integrableOn_const (by simp))
  calc ∫ s, |f s - f (s + v)| ≤ ∫ s, (g1 s + g2 s + g3 s) := integral_mono hdi.abs ((i1.add i2).add i3) hpt
    _ = (∫ s, g1 s) + (∫ s, g2 s) + ∫ s, g3 s := by
        have e := integral_add (i1.add i2) i3
        have e2 := integral_add i1 i2
        simp only [Pi.add_apply] at e e2
        rw [e, e2]
    _ = B * (Lh * v) + v * H + v * H := by
        rw [hg1, hg2, hg3, integral_indicator_const _ measurableSet_Ioc,
          integral_indicator_const _ measurableSet_Ioc, integral_indicator_const _ measurableSet_Ioc,
          Real.volume_real_Ioc_of_le hB, Real.volume_real_Ioc_of_le (by linarith),
          Real.volume_real_Ioc_of_le (by linarith)]
        simp only [smul_eq_mul]; ring
    _ = (Lh * B + 2 * H) * v := by ring

end Cvs.Upstream.LevyConditionL1Modulus
