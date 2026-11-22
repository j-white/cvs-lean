import Mathlib
import Cvs.Upstream.L2TranslationContinuity
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.LevyTruncationExhausts
import Cvs.WeilForm.Mollify.ChannelsLipschitz
import Cvs.WeilForm.Mollify.ComposedApproximant
import Cvs.WeilForm.Mollify.ComposedApproximantL2
import Cvs.WeilForm.Mollify.DilateTranslate
import Cvs.WeilForm.Mollify.MollifiedL2
import Cvs.WeilForm.Mollify.MollifierKernel
import Cvs.WeilForm.Mollify.MollifyContinuous
import Cvs.WeilForm.Mollify.MollifyLevyPointwise
import Cvs.WeilForm.Mollify.MollifyShiftedEnergy
import Cvs.WeilForm.Mollify.WindowNormalisation
import Cvs.WeilForm.SelfConvolutionContinuous
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.WindowConstraintSet
import Cvs.Zeta.WeilPositivityStatement

/-!
# The window's constraint set is approximated by continuous members

    ∃ Ξ n ∈ windowSet L, each continuous, with Ξ n → η in `L²` and their forms → the form

the three moves of `Cvs.WeilForm.Mollify.ComposedApproximant` composed, normalised, and read as one statement about `η`.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Filter Cvs.Zeta.Explicit.Weil Cvs.Upstream.L2DilationContinuity

namespace Cvs.WeilForm.Mollify.ContinuousApproximation

variable {L : ℝ} {η : ℝ → ℝ}

/-- **Continuous members of the constraint set approximate any member, in `L²` and in
form.** -/
theorem exists_windowApprox (hL : 0 < L) (P R : ℕ)
    (hη : η ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L) (hηm : Measurable η) :
    ∃ Ξ : ℕ → ℝ → ℝ,
      (∀ n, Ξ n ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L) ∧
      (∀ n, Continuous (Ξ n)) ∧
      Filter.Tendsto (fun n : ℕ => ∫ x : ℝ, (Ξ n x - η x) ^ 2) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun n : ℕ => Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Ξ n)) Filter.atTop
        (nhds (Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R η)) ∧
      (∀ n, ∃ (c : ℝ) (m : ℕ),
        Ξ n = fun x => c * Cvs.WeilForm.Mollify.ComposedApproximant.pre hL η m x) := by
  obtain ⟨hmem, hsupp, hnorm, hlevy⟩ := hη
  set ρ : ℕ → ℝ → ℝ := fun n => Cvs.WeilForm.Mollify.MollifierKernel.kernel
    (Cvs.WeilForm.Mollify.ComposedApproximant.shift_pos hL n) with hρ
  have hρc : ∀ n, Continuous (ρ n) := fun n => Cvs.WeilForm.Mollify.MollifierKernel.continuous_kernel _
  have hρs : ∀ n, HasCompactSupport (ρ n) := fun n =>
    Cvs.WeilForm.Mollify.MollifierKernel.hasCompactSupport_kernel _
  have hρm : ∀ n, Measurable (ρ n) := fun n => Cvs.WeilForm.Mollify.MollifierKernel.measurable_kernel _
  have hρi : ∀ n, Integrable (ρ n) (volume : Measure ℝ) := fun n =>
    Cvs.WeilForm.Mollify.MollifierKernel.integrable_kernel _
  have hρnn : ∀ n, ∀ t : ℝ, 0 ≤ ρ n t := fun n t => Cvs.WeilForm.Mollify.MollifierKernel.kernel_nonneg _ t
  have hρ1 : ∀ n, (∫ t : ℝ, ρ n t) = 1 := fun n => Cvs.WeilForm.Mollify.MollifierKernel.integral_kernel _
  -- the dilate-and-translate
  set S : ℕ → ℝ → ℝ := fun n => Cvs.WeilForm.Mollify.ComposedApproximant.shifted L η n with hS
  have hSwin : ∀ n, S n ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L := fun n =>
    Cvs.WeilForm.Mollify.DilateTranslate.mem_windowSet_shifted hL ⟨hmem, hsupp, hnorm, hlevy⟩ n
  have hSmem : ∀ n, MemLp (S n) 2 (volume : Measure ℝ) := fun n => (hSwin n).1
  have hSm : ∀ n, Measurable (S n) := fun n =>
    Cvs.WeilForm.Mollify.ComposedApproximant.measurable_shifted hηm L n
  have hSlevy : ∀ n, IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (S n)) (Set.Ioi 0)
      (volume : Measure ℝ) := fun n => (hSwin n).2.2.2
  have hSnorm : ∀ n, (∫ x : ℝ, S n x ^ 2) = 1 := fun n => (hSwin n).2.2.1
  -- the mollification
  set F : ℕ → ℝ → ℝ := fun n => Cvs.WeilForm.Mollify.ComposedApproximant.pre hL η n with hF
  have hFmem : ∀ n, MemLp (F n) 2 (volume : Measure ℝ) := fun n =>
    Cvs.WeilForm.Mollify.MollifiedL2.memLp_conv (hSmem n) (hSm n) (hρc n) (hρs n) (hρm n) (hρi n)
      (hρnn n) (hρ1 n)
  have hFs : ∀ n, ∀ s ∉ Set.Ioc (0:ℝ) L, F n s = 0 := fun n =>
    Cvs.WeilForm.Mollify.ComposedApproximant.support_pre hL hsupp n
  have hFlevy : ∀ n, IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (F n)) (Set.Ioi 0)
      (volume : Measure ℝ) := fun n =>
    Cvs.WeilForm.Mollify.MollifyLevyPointwise.integrableOn_levy_conv (hSmem n) (hSm n) (hρc n) (hρs n) (hρm n)
      (hρi n) (hρnn n) (hρ1 n) (hSlevy n)
  have hFbdd : ∀ n, (∫ x : ℝ, F n x ^ 2) ≤ 1 := by
    intro n
    have h := Cvs.WeilForm.Mollify.MollifyLevyPointwise.integral_conv_sq_le (hSmem n) (hSm n) (hρc n) (hρs n)
      (hρm n) (hρi n) (hρnn n) (hρ1 n)
    rwa [hSnorm n] at h
  have hconv := Cvs.WeilForm.Mollify.ComposedApproximantL2.tendsto_pre_error hL hmem hηm
  have hFcont : ∀ n, Continuous (F n) := fun n =>
    Cvs.WeilForm.Mollify.MollifyContinuous.continuous_conv (hSmem n) (hρc n) (hρs n)
  -- the archimedean channel converges
  have harchle : ∀ n, Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (F n)
      ≤ Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (S n) := fun n =>
    Cvs.WeilForm.Mollify.MollifyLevyPointwise.archFull_conv_le (hSmem n) (hSm n) (hρc n) (hρs n) (hρm n)
      (hρi n) (hρnn n) (hρ1 n) (hSlevy n)
  have hηwin : η ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L := ⟨hmem, hsupp, hnorm, hlevy⟩
  have hbtend := Cvs.WeilForm.Mollify.DilateTranslate.tendsto_archFull_shifted hηwin L
  have hFc : ∀ n, AEStronglyMeasurable (selfConvolution (F n)) (volume : Measure ℝ) := fun n =>
    (Cvs.WeilForm.SelfConvolutionContinuous.continuous_selfConvolution (hFmem n)).aestronglyMeasurable
  have hηc : AEStronglyMeasurable (selfConvolution η) (volume : Measure ℝ) :=
    (Cvs.WeilForm.SelfConvolutionContinuous.continuous_selfConvolution hmem).aestronglyMeasurable
  have harch := Cvs.WeilForm.Mollify.ChannelsLipschitz.tendsto_archFull_of_le (C := 1) hmem hFmem hηc hFc
    hlevy hFlevy hconv hFbdd harchle hbtend
  have hform := Cvs.WeilForm.Mollify.ChannelsLipschitz.tendsto_weilForm_of_tendsto_archFull (L := L) (C := 1)
    P R (by norm_num) hmem hFmem hsupp hFs hFbdd hconv harch
  have hE := Cvs.WeilForm.Mollify.WindowNormalisation.tendsto_integral_sq (C := 1) hmem hFmem hconv hFbdd
  rw [hnorm] at hE
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hE (1/2) (by norm_num)
  have hEpos : ∀ n : ℕ, 0 < ∫ x : ℝ, F (n + N) x ^ 2 := by
    intro n
    have h := hN (n + N) (Nat.le_add_left N n)
    rw [Real.dist_eq, abs_lt] at h
    linarith [h.1]
  refine ⟨fun n => fun x => (Real.sqrt (∫ y : ℝ, F (n + N) y ^ 2))⁻¹ * F (n + N) x,
    fun n => Cvs.WeilForm.Mollify.WindowNormalisation.mem_windowSet_normalised (hFmem _) (hFs _) (hFlevy _)
      (hEpos n),
    fun n => continuous_const.mul (hFcont _), ?_, ?_,
    fun n => ⟨(Real.sqrt (∫ y : ℝ, F (n + N) y ^ 2))⁻¹, n + N, rfl⟩⟩
  · -- the `L²` distance
    set c : ℕ → ℝ := fun n => (Real.sqrt (∫ y : ℝ, F (n + N) y ^ 2))⁻¹ with hc
    set e : ℕ → ℝ := fun n => Real.sqrt (∫ y : ℝ, F (n + N) y ^ 2) with he
    have hEshift : Filter.Tendsto (fun n : ℕ => ∫ y : ℝ, F (n + N) y ^ 2)
        Filter.atTop (nhds 1) := (Filter.tendsto_add_atTop_iff_nat N).mpr hE
    have hetend : Filter.Tendsto e Filter.atTop (nhds 1) := by
      have := (Real.continuous_sqrt.tendsto 1).comp hEshift
      simpa [he, Function.comp_def] using this
    have hctend : Filter.Tendsto c Filter.atTop (nhds 1) := by
      have := hetend.inv₀ one_ne_zero
      rw [inv_one] at this
      exact this
    set d : ℕ → ℝ := fun n => Real.sqrt (∫ x : ℝ, (F (n + N) x - η x) ^ 2) with hd
    have hdtend : Filter.Tendsto d Filter.atTop (nhds 0) := by
      have hshift : Filter.Tendsto (fun n : ℕ => ∫ x : ℝ, (F (n + N) x - η x) ^ 2)
          Filter.atTop (nhds 0) := (Filter.tendsto_add_atTop_iff_nat N).mpr hconv
      have := (Real.continuous_sqrt.tendsto 0).comp hshift
      simpa [hd, Real.sqrt_zero, Function.comp_def] using this
    have hbtot : Filter.Tendsto (fun n : ℕ => (|c n - 1| * e n + d n) ^ 2)
        Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun n : ℕ => |c n - 1|) Filter.atTop (nhds 0) := by
        have hs : Filter.Tendsto (fun n : ℕ => c n - 1) Filter.atTop (nhds 0) := by
          have h0 := hctend.sub_const 1
          rw [sub_self] at h0
          exact h0
        have := (continuous_abs.tendsto (0:ℝ)).comp hs
        simpa [Function.comp_def] using this
      have h2 := (h1.mul hetend).add hdtend
      have h3 := h2.pow 2
      simpa using h3
    refine squeeze_zero (fun n => integral_nonneg fun x => sq_nonneg _) (fun n => ?_) hbtot
    have hcF : MemLp (fun x : ℝ => c n * F (n + N) x) 2 (volume : Measure ℝ) :=
      (hFmem _).const_mul _
    have htri := Cvs.Upstream.L2TranslationContinuity.sqrt_integral_sub_sq_triangle hcF
      (hFmem (n + N)) hmem
    have hfirst : (∫ x : ℝ, (c n * F (n + N) x - F (n + N) x) ^ 2)
        = (c n - 1) ^ 2 * ∫ y : ℝ, F (n + N) y ^ 2 := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    have hsqrt1 : Real.sqrt (∫ x : ℝ, (c n * F (n + N) x - F (n + N) x) ^ 2)
        = |c n - 1| * e n := by
      rw [hfirst, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, he]
    rw [hsqrt1] at htri
    have hnn : 0 ≤ ∫ x : ℝ, (c n * F (n + N) x - η x) ^ 2 :=
      integral_nonneg fun x => sq_nonneg _
    nlinarith [Real.sq_sqrt hnn, htri,
      Real.sqrt_nonneg (∫ x : ℝ, (c n * F (n + N) x - η x) ^ 2),
      abs_nonneg (c n - 1), Real.sqrt_nonneg (∫ y : ℝ, F (n + N) y ^ 2), hdtend]
  · -- the form
    have hEshift : Filter.Tendsto (fun n : ℕ => ∫ y : ℝ, F (n + N) y ^ 2)
        Filter.atTop (nhds 1) := (Filter.tendsto_add_atTop_iff_nat N).mpr hE
    have hinv : Filter.Tendsto (fun n : ℕ => (∫ y : ℝ, F (n + N) y ^ 2)⁻¹)
        Filter.atTop (nhds 1) := by
      have := hEshift.inv₀ one_ne_zero
      rw [inv_one] at this
      exact this
    have hWshift : Filter.Tendsto
        (fun n : ℕ => Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (F (n + N))) Filter.atTop
        (nhds (Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R η)) :=
      (Filter.tendsto_add_atTop_iff_nat N).mpr hform
    have hprod := hinv.mul hWshift
    rw [one_mul] at hprod
    refine hprod.congr (fun n => ?_)
    exact (Cvs.WeilForm.Mollify.WindowNormalisation.weilForm_normalised P R (hEpos n) (F (n + N))).symm

end Cvs.WeilForm.Mollify.ContinuousApproximation
