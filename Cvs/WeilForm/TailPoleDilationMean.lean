import Mathlib
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Finite.SymmetricModeSet
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailPoleChannel
import Cvs.L2a.FullTailWeilFormLimit
import Cvs.L2a.WindowFormTailLimit
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.PoleTermDilationMean
import Cvs.WeilForm.SeparatedArchDilationPairing
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.WeilForm.WeilFormOnWindowL2

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The remaining tail pole is the continuous dilation mean

The finite continuous mean is a compactly weighted tail primitive. Actual
Fourier tails supply the boundedness and improper primitive convergence needed
to pass to the limit. The Connes column is consequently a prime-versus-
continuous discrepancy plus `SeparatedArchDilationPairing`'s convergent cubic arch correction.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology

namespace Cvs.WeilForm.TailPoleDilationMean
open Cvs.ZeroCounting

open Cvs.WeilForm.PoleTermDilationMean (dilR)
open Cvs.L2a.WindowFormTailLimit (Tame)
open Cvs.WeilForm.ThetaSpaceParseval (poleP poleM dil weilθ)
open Cvs.L2a.FullTailConvergence (fullTail)
open Cvs.L2a.AngularProlateTailPositive (psi)

/-- The primitive of a tail vanishing below `1` is zero before `1`,
including the negative upper limits. -/
theorem primitive_eq_zero_of_le {F : ℝ → ℝ} (hF : ∀ θ ≤ 1, F θ = 0)
    {Y : ℝ} (hY : Y ≤ 1) : (∫ θ in (0 : ℝ)..Y, F θ) = 0 := by
  calc (∫ θ in (0 : ℝ)..Y, F θ) = ∫ θ in (0 : ℝ)..Y, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro θ hθ
          exact hF θ (hθ.2.trans (max_le zero_le_one hY))
    _ = 0 := by simp

/-- A measurable globally bounded tail is integrable over every finite
interval, even though its improper integral need not be absolute. -/
theorem intervalIntegrable_of_bdd {F : ℝ → ℝ} {B : ℝ}
    (hFm : Measurable F) (hB : ∀ θ, |F θ| ≤ B) (p q : ℝ) :
    IntervalIntegrable F volume p q := by
  refine IntervalIntegrable.mono_fun' (g := fun _ => B) intervalIntegrable_const
    hFm.aestronglyMeasurable (ae_of_all _ fun θ => ?_)
  simpa only [Real.norm_eq_abs] using hB θ

/-- The finite mean integrand is jointly integrable from a bounded tail
and the actual compactly supported tame test. -/
theorem integrable_finite_mean_prod {F G : ℝ → ℝ} {B α β : ℝ}
    (hFm : Measurable F) (hB : ∀ θ, |F θ| ≤ B) (hG : Tame G α β) (R : ℝ) :
    Integrable (fun p : ℝ × ℝ => G p.2 * F (p.1 * p.2))
      ((volume.restrict (Ioc (1 : ℝ) R)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  obtain ⟨M, hM⟩ := hG.bdd
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => G p.2 * F (p.1 * p.2))
      ((volume.restrict (Ioc (1 : ℝ) R)).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    ((hG.meas.comp measurable_snd).mul
      (hFm.comp (measurable_fst.mul measurable_snd))).aestronglyMeasurable
  have h1 : Integrable (fun _ : ℝ => M * B) (volume.restrict (Ioc (1 : ℝ) R)) :=
    integrableOn_const measure_Ioc_lt_top.ne
  have h2 : Integrable ((Icc α β).indicator fun _ => (1 : ℝ))
      (volume.restrict (Ioi (0 : ℝ))) :=
    Integrable.restrict ((integrable_indicator_iff measurableSet_Icc).2
      (integrableOn_const measure_Icc_lt_top.ne))
  refine Integrable.mono' (h1.mul_prod h2) hm (ae_of_all _ fun p => ?_)
  simp only [Real.norm_eq_abs, abs_mul]
  by_cases hs : p.2 ∈ Icc α β
  · rw [indicator_of_mem hs, mul_one]
    exact mul_le_mul (hM _) (hB _) (abs_nonneg _) hM0
  · rw [hG.supp _ hs, abs_zero, zero_mul, indicator_of_notMem hs, mul_zero]

/-- The finite continuous correlation mean equals the weighted primitive
at `Rθ`. For `R≤1`, both sides are exactly zero. -/
theorem finite_mean_eq_primitive {F G : ℝ → ℝ} {B α β : ℝ}
    (hFm : Measurable F) (hB : ∀ θ, |F θ| ≤ B)
    (hF : ∀ θ ≤ 1, F θ = 0) (hG : Tame G α β) (hβ : β ≤ 1) (R : ℝ) :
    (∫ r in (1 : ℝ)..R, dilR G F r) =
      ∫ θ in Ioi (0 : ℝ), G θ / θ * (∫ η in (0 : ℝ)..R * θ, F η) := by
  by_cases hR : 1 ≤ R
  · rw [intervalIntegral.integral_of_le hR]
    unfold dilR
    rw [integral_integral_swap (integrable_finite_mean_prod hFm hB hG R)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro θ hθ
    change 0 < θ at hθ
    change (∫ r in Ioc (1 : ℝ) R, G θ * F (r * θ)) =
      G θ / θ * (∫ η in (0 : ℝ)..R * θ, F η)
    by_cases hs : θ ∈ Icc α β
    · rw [← intervalIntegral.integral_of_le hR, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_mul_right F hθ.ne', smul_eq_mul]
      have hz := primitive_eq_zero_of_le hF (hs.2.trans hβ)
      have ha := intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_of_bdd hFm hB 0 θ)
        (intervalIntegrable_of_bdd hFm hB θ (R * θ))
      rw [hz, zero_add] at ha
      rw [one_mul, ha]
      field_simp
    · simp only [hG.supp θ hs, zero_mul, integral_zero, zero_div]
  · have hR1 : R ≤ 1 := le_of_not_ge hR
    have hleft : (∫ r in (1 : ℝ)..R, dilR G F r) = 0 := by
      calc (∫ r in (1 : ℝ)..R, dilR G F r) = ∫ r in (1 : ℝ)..R, (0 : ℝ) := by
              apply intervalIntegral.integral_congr
              intro r hr
              have hr1 : r ≤ 1 := by simpa only [max_eq_left hR1] using hr.2
              unfold dilR
              apply setIntegral_eq_zero_of_forall_eq_zero
              intro θ hθ
              change 0 < θ at hθ
              by_cases hs : θ ∈ Icc α β
              · rw [hF (r * θ) (by nlinarith [hs.2.trans hβ]), mul_zero]
              · rw [hG.supp θ hs, zero_mul]
        _ = 0 := by simp
    rw [hleft]
    symm
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro θ hθ
    change 0 < θ at hθ
    by_cases hs : θ ∈ Icc α β
    · rw [primitive_eq_zero_of_le hF (by nlinarith [hs.2.trans hβ]), mul_zero]
    · simp only [hG.supp θ hs, zero_div, zero_mul]

/-- Compactly supported tests turn a convergent tail primitive into the
continuous correlation mean. The convergence premise is supplied by actual
Fourier tails below. -/
theorem tendsto_finite_mean_of_primitive {F G : ℝ → ℝ} {B α β p : ℝ}
    (hFm : Measurable F) (hB : ∀ θ, |F θ| ≤ B)
    (hF : ∀ θ ≤ 1, F θ = 0) (hG : Tame G α β) (hβ : β ≤ 1)
    (hp : Tendsto (fun Y : ℝ => ∫ η in (0 : ℝ)..Y, F η) atTop (𝓝 p)) :
    Tendsto (fun R : ℝ => ∫ r in (1 : ℝ)..R, dilR G F r) atTop (𝓝 (p * poleM G)) := by
  have hpc : Continuous (fun Y : ℝ => ∫ η in (0 : ℝ)..Y, F η) :=
    intervalIntegral.continuous_primitive (intervalIntegrable_of_bdd hFm hB) 0
  have hnear : ∀ᶠ Y in atTop, |(∫ η in (0 : ℝ)..Y, F η) - p| < 1 := by
    simpa only [Real.dist_eq] using hp.eventually (Metric.ball_mem_nhds p one_pos)
  obtain ⟨T, hT⟩ := eventually_atTop.1 hnear
  have hmeas : ∀ R : ℝ, AEStronglyMeasurable
      (fun θ => G θ / θ * (∫ η in (0 : ℝ)..R * θ, F η)) (volume.restrict (Ioi (0 : ℝ))) := by
    intro R
    exact ((hG.meas.div measurable_id).mul
      (hpc.measurable.comp (measurable_const_mul R))).aestronglyMeasurable
  have hbd : ∀ᶠ R : ℝ in atTop, ∀ᵐ θ ∂volume.restrict (Ioi (0 : ℝ)),
      ‖G θ / θ * (∫ η in (0 : ℝ)..R * θ, F η)‖ ≤
        (|p| + 1) * |G θ / θ| := by
    filter_upwards [eventually_ge_atTop (max 1 (T / α))] with R hR
    apply ae_of_all
    intro θ
    by_cases hs : θ ∈ Icc α β
    · have hR0 : 0 ≤ R := by linarith [le_trans (le_max_left _ _) hR]
      have hRT : T ≤ R * θ := by
        have hTα : T ≤ R * α := (div_le_iff₀ hG.pos).1 ((le_max_right _ _).trans hR)
        exact hTα.trans (mul_le_mul_of_nonneg_left hs.1 hR0)
      have hprim : |∫ η in (0 : ℝ)..R * θ, F η| ≤ |p| + 1 := by
        have hn := hT (R * θ) hRT
        calc |∫ η in (0 : ℝ)..R * θ, F η| =
              |((∫ η in (0 : ℝ)..R * θ, F η) - p) + p| := by congr 1; ring
          _ ≤ |(∫ η in (0 : ℝ)..R * θ, F η) - p| + |p| := abs_add_le _ _
          _ ≤ |p| + 1 := by linarith
      rw [Real.norm_eq_abs, abs_mul]
      nlinarith [abs_nonneg (G θ / θ)]
    · simp only [hG.supp θ hs, zero_div, zero_mul, norm_zero, abs_zero, mul_zero, le_refl]
  have hlim : ∀ᵐ θ ∂volume.restrict (Ioi (0 : ℝ)),
      Tendsto (fun R : ℝ => G θ / θ * (∫ η in (0 : ℝ)..R * θ, F η)) atTop
        (𝓝 (G θ / θ * p)) := by
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro θ hθ
    have hmul : Tendsto (fun R : ℝ => R * θ) atTop atTop :=
      (tendsto_mul_const_atTop_of_pos hθ).2 tendsto_id
    exact tendsto_const_nhds.mul (hp.comp hmul)
  have hbi : Integrable (fun θ => (|p| + 1) * |G θ / θ|)
      (volume.restrict (Ioi (0 : ℝ))) := by
    simpa only [Real.norm_eq_abs] using (hG.div.norm.const_mul (|p| + 1)).restrict
  have h := tendsto_integral_filter_of_dominated_convergence
    (fun θ => (|p| + 1) * |G θ / θ|) (Eventually.of_forall hmeas) hbd
    hbi hlim
  have he : (∫ θ in Ioi (0 : ℝ), G θ / θ * p) = p * poleM G := by
    rw [integral_mul_const, poleM]
    ring
  rw [he] at h
  exact h.congr (fun R => (finite_mean_eq_primitive hFm hB hF hG hβ R).symm)

/-- The actual Fourier tail supplies the improper primitive convergence,
so its remaining pole channel is the continuous dilation mean. -/
theorem tendsto_finite_mean_fullTail {g g₁ g₂ : ℝ → ℝ} {c : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1)) (hc : 0 < c)
    {w : ℝ → ℝ} {α β : ℝ} (hw : Tame w α β) (hβ : β ≤ 1) :
    Tendsto (fun R : ℝ => ∫ r in (1 : ℝ)..R, dilR w (fullTail (psi c g)) r) atTop
      (𝓝 (poleP (fullTail (psi c g)) * poleM w)) := by
  have hp := Cvs.L2a.WindowFormTailLimit.tendsto_integral_fullTail hg hg₁ hg₂c hc
  rw [Cvs.WeilForm.ThetaSpaceParseval.poleP_eq_of_tendsto hp]
  exact tendsto_finite_mean_of_primitive
    (Cvs.L2a.FullTailConvergence.measurable_fullTail hg hg₁ hg₂c hc)
    (Cvs.L2a.WindowFormTailLimit.abs_fullTail_le_BG hg hg₁ hg₂c hc)
    (fun θ hθ => Cvs.L2a.FullTailWeilFormLimit.fullTail_of_le_one _ hθ) hw hβ hp

/-- The actual Connes tail has a finite continuous mean for every cosine
test and the correct pole limit. -/
theorem tendsto_connesTail_mean {x : ℕ} (hx : 80 ≤ 2 * π * x)
    (N : ℕ) (f : Cvs.Finite.SymmetricModeSet.Idx N → ℝ) :
    Tendsto (fun R : ℝ => ∫ r in (1 : ℝ)..R,
      dilR (Cvs.Approximant.CosineColumnTailPairing.modeTest x N f) (Cvs.Approximant.CosineColumnTailPairing.connesTail x) r) atTop
      (𝓝 (poleP (Cvs.Approximant.CosineColumnTailPairing.connesTail x) * poleM (Cvs.Approximant.CosineColumnTailPairing.modeTest x N f))) := by
  obtain ⟨G₁, G₂, hg, hg₁, hg₂c, _, _⟩ :=
    Cvs.Approximant.SpineCouplingTailPairing.spine_profile_data hx (Cvs.Approximant.CosineColumnTailPairing.singleton_lt_of_scale hx) (fun _ => 1)
  obtain ⟨H₁, H₂, hH, hH₁, hH₂c⟩ := Cvs.WeilForm.SeparatedArchDilationPairing.regProfile_derivative_data hg hg₁ hg₂c
  exact tendsto_finite_mean_fullTail hH hH₁ hH₂c (by linarith)
    (Cvs.Approximant.CosineColumnTailPairing.tame_modeTest (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N f) (le_refl 1)

/-- The actual untruncated Connes pairing is the limit of its prime
sampling minus finite continuous mean, plus the convergent cubic correction.
The infinite prime sum is retained explicitly. -/
theorem tendsto_connes_prime_discrepancy {x : ℕ} (hx : 80 ≤ 2 * π * x)
    (N : ℕ) (f : Cvs.Finite.SymmetricModeSet.Idx N → ℝ) :
    Tendsto (fun R : ℝ =>
      (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        dil (Cvs.Approximant.CosineColumnTailPairing.modeTest x N f) (Cvs.Approximant.CosineColumnTailPairing.connesTail x) n)
      - (∫ r in (1 : ℝ)..R, dilR (Cvs.Approximant.CosineColumnTailPairing.modeTest x N f) (Cvs.Approximant.CosineColumnTailPairing.connesTail x) r)
      + (∫ r in Ioi (1 : ℝ), dilR (Cvs.Approximant.CosineColumnTailPairing.modeTest x N f) (Cvs.Approximant.CosineColumnTailPairing.connesTail x) r /
          (r * (r ^ 2 - 1)))) atTop
      (𝓝 (Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x)
        (Cvs.Approximant.CosineColumnTailPairing.connesClass hx) (Cvs.Approximant.CosineColumnTailPairing.modeMap (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N f))) := by
  rw [Cvs.WeilForm.SeparatedArchDilationPairing.QWbil_connesClass_modeMap_eq_cubic hx N f]
  exact (tendsto_const_nhds.sub (tendsto_connesTail_mean hx N f)).add tendsto_const_nhds

end Cvs.WeilForm.TailPoleDilationMean
