import Mathlib
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyIntegrandNonneg
import Cvs.WeilForm.Archimedean.LevyTruncationExhausts
import Cvs.WeilForm.Archimedean.TruncatedArchContinuous
import Cvs.WeilForm.CentredWindowTranslate
import Cvs.WeilForm.ConstraintSetSeqCompact
import Cvs.WeilForm.LevyEnergySublevelBound
import Cvs.WeilForm.PoleChannelWindowL2
import Cvs.WeilForm.PrimeChannelL2Continuous
import Cvs.WeilForm.RegularisedSpectralMass
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SupportNormSurviveL2Limit
import Cvs.WeilForm.TruncatedArchDomain
import Cvs.WeilForm.WindowConstraintSet
import Cvs.Zeta.WeilPositivityStatement

/-!
# The limit is admissible, and `hcpt` holds

    F n ∈ D,  weilForm (F n) ≤ B   ⟹   a subsequence converges in L² to some g ∈ D

the hypothesis `Cvs.WeilForm.DirectMethodBottomAttained`'s direct method takes, discharged for the window's constraint set.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Filter Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.ConstraintLimitAdmissible

/-- A vanishing squared integral off the window forces the function to vanish there. -/
theorem ae_zero_of_integral_sq_eq_zero {L : ℝ} {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume : Measure ℝ))
    (h : (∫ x in (Set.Ioc (0:ℝ) L)ᶜ, g x ^ 2) = 0) :
    Set.indicator (Set.Ioc (0:ℝ) L) g =ᵐ[(volume : Measure ℝ)] g := by
  have hint : IntegrableOn (fun x : ℝ => g x ^ 2) (Set.Ioc (0:ℝ) L)ᶜ (volume : Measure ℝ) :=
    hg.integrable_sq.integrableOn
  have hzero : ∀ᵐ x ∂((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) L)ᶜ), g x ^ 2 = 0 := by
    have := (integral_eq_zero_iff_of_nonneg
      (fun x => sq_nonneg (g x)) hint).mp h
    filter_upwards [this] with x hx using hx
  have hg0 : ∀ᵐ x ∂((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) L)ᶜ), g x = 0 := by
    filter_upwards [hzero] with x hx using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hx
  have hg0' : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ (Set.Ioc (0:ℝ) L)ᶜ → g x = 0 :=
    (ae_restrict_iff' measurableSet_Ioc.compl).mp hg0
  filter_upwards [hg0'] with x hx
  by_cases hmem : x ∈ Set.Ioc (0:ℝ) L
  · rw [Set.indicator_of_mem hmem]
  · rw [Set.indicator_of_notMem hmem, hx hmem]

/-- **The constraint set is sequentially compact along form-bounded sequences.** -/
theorem hcpt {L B : ℝ} (hL : 0 ≤ L) (P R : ℕ) {F : ℕ → ℝ → ℝ}
    (hFD : ∀ n, F n ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L)
    (hFB : ∀ n, Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (F n) ≤ B) :
    ∃ (φ : ℕ → ℕ) (g : ℝ → ℝ), StrictMono φ ∧ g ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L ∧
      Tendsto (fun k => ∫ x : ℝ, (F (φ k) x - g x) ^ 2) atTop (nhds 0) := by
  obtain ⟨φ, g₀, hφ, hg₀, htend⟩ :=
    Cvs.WeilForm.ConstraintSetSeqCompact.exists_subseq_tendsto_integral hL P R hFD hFB
  -- the limit is supported in the window, after correcting on a null set
  have hsupp0 := Cvs.WeilForm.SupportNormSurviveL2Limit.support_of_tendsto
    (fun k => (hFD (φ k)).2.1) (fun k => (hFD (φ k)).1) hg₀ htend
  set g : ℝ → ℝ := Set.indicator (Set.Ioc (0:ℝ) L) g₀ with hgdef
  have hgae : g =ᵐ[(volume : Measure ℝ)] g₀ := ae_zero_of_integral_sq_eq_zero hg₀ hsupp0
  have hgmem : MemLp g 2 (volume : Measure ℝ) := hg₀.ae_eq hgae.symm
  have hgint : Integrable g (volume : Measure ℝ) :=
    Cvs.WeilForm.CentredWindowTranslate.integrable_of_support hL hgmem (fun s hs => by
      rw [hgdef, Set.indicator_of_notMem hs])
  -- the convergence is unchanged by the correction
  have htend' : Tendsto (fun k => ∫ x : ℝ, (F (φ k) x - g x) ^ 2) atTop (nhds 0) := by
    refine htend.congr fun k => ?_
    exact integral_congr_ae (hgae.mono fun x hx => by simp only; rw [hx])
  -- the norm survives
  have hnorm : (∫ x : ℝ, g x ^ 2) = 1 :=
    Cvs.WeilForm.SupportNormSurviveL2Limit.norm_of_tendsto (fun k => (hFD (φ k)).1) hgmem
      (fun k => (hFD (φ k)).2.2.1) htend'
  -- the Lévy energy is capped, so the limit lies in the domain
  have hmeasg : AEStronglyMeasurable (selfConvolution g) (volume : Measure ℝ) := by
    have := (Cvs.WeilForm.RegularisedSpectralMass.integrable_selfConvolution hgint).re
    simpa using this.aestronglyMeasurable
  set C : ℝ := B + 2 * Real.sqrt (∫ x : ℝ, Cvs.WeilForm.PoleChannelWindowL2.poleWeightPos L x ^ 2)
        * Real.sqrt (∫ x : ℝ, Cvs.WeilForm.PoleChannelWindowL2.poleWeightNeg L x ^ 2)
      + |Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0|
      + 2 * Cvs.WeilForm.PrimeChannelL2Continuous.primeMass P R with hC
  have hcap : ∀ δ : ℝ, 0 < δ → Cvs.WeilForm.Archimedean.TruncatedArchContinuous.archTrunc δ g ≤ C := by
    intro δ hδ
    set Dm : ℝ := ∫ u in Set.Ioi δ, Cvs.WeilForm.Archimedean.LevyDensity.densityU u with hDm
    have hDmnn : 0 ≤ Dm := setIntegral_nonneg measurableSet_Ioi fun u hu =>
      (Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos (lt_trans hδ hu)).le
    set s : ℕ → ℝ := fun k => Real.sqrt (∫ x : ℝ, (F (φ k) x - g x) ^ 2) with hs
    have hstend : Tendsto s atTop (nhds 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp htend'
      simpa [hs, Real.sqrt_zero, Function.comp_def] using this
    have hbound : ∀ k, Cvs.WeilForm.Archimedean.TruncatedArchContinuous.archTrunc δ g ≤ C + 4 * s k * Dm := by
      intro k
      have hmeasF : AEStronglyMeasurable (selfConvolution (F (φ k)))
          (volume : Measure ℝ) := by
        have := (Cvs.WeilForm.RegularisedSpectralMass.integrable_selfConvolution
          (Cvs.WeilForm.WindowConstraintSet.integrable_of_mem hL (hFD (φ k)))).re
        simpa using this.aestronglyMeasurable
      have hb := Cvs.WeilForm.Archimedean.TruncatedArchContinuous.abs_archTrunc_sub_le hδ hgmem (hFD (φ k)).1
        hmeasg hmeasF
      rw [hnorm, (hFD (φ k)).2.2.1, Real.sqrt_one] at hb
      have hsym : (∫ x : ℝ, (g x - F (φ k) x) ^ 2) = ∫ x : ℝ, (F (φ k) x - g x) ^ 2 :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
      rw [hsym] at hb
      have hupper : Cvs.WeilForm.Archimedean.TruncatedArchContinuous.archTrunc δ (F (φ k)) ≤ C := by
        refine le_trans (Cvs.WeilForm.Archimedean.LevyIntegrandNonneg.archTrunc_le_archFull hδ (hFD (φ k)).1
          (hFD (φ k)).2.2.2) ?_
        exact Cvs.WeilForm.LevyEnergySublevelBound.archFull_le P R (hFD (φ k)).1 (hFD (φ k)).2.1
          (hFD (φ k)).2.2.1 (hFB (φ k))
      have habs := abs_le.mp hb
      have : Cvs.WeilForm.Archimedean.TruncatedArchContinuous.archTrunc δ g
          ≤ Cvs.WeilForm.Archimedean.TruncatedArchContinuous.archTrunc δ (F (φ k)) + 2 * (s k * (1 + 1)) * Dm := by
        linarith [habs.2]
      calc Cvs.WeilForm.Archimedean.TruncatedArchContinuous.archTrunc δ g
          ≤ Cvs.WeilForm.Archimedean.TruncatedArchContinuous.archTrunc δ (F (φ k)) + 2 * (s k * (1 + 1)) * Dm := this
        _ ≤ C + 4 * s k * Dm := by nlinarith [hupper]
    have htC : Tendsto (fun k : ℕ => C + 4 * s k * Dm) atTop (nhds C) := by
      have h0 : Tendsto (fun k : ℕ => C + 4 * s k * Dm) atTop (nhds (C + 4 * 0 * Dm)) :=
        tendsto_const_nhds.add ((hstend.const_mul 4).mul_const Dm)
      simpa using h0
    exact ge_of_tendsto htC (Filter.Eventually.of_forall hbound)
  have hdom := Cvs.WeilForm.TruncatedArchDomain.integrableOn_levy_of_bounded hgmem hmeasg hcap
  exact ⟨φ, g, hφ, ⟨hgmem, fun s hs => by rw [hgdef, Set.indicator_of_notMem hs], hnorm, hdom⟩,
    htend'⟩

end Cvs.WeilForm.ConstraintLimitAdmissible
