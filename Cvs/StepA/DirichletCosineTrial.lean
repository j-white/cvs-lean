import Mathlib
import Cvs.Finite.ExponentialKernelLocalises
import Cvs.WeilForm.Archimedean.ArchEnergySpectral
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.HatLevyDeficit
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.OffWindowDefect
import Cvs.WeilForm.Archimedean.TruncatedLevyDensityBelow
import Cvs.WeilForm.Archimedean.TruncatedSymbolConstant
import Cvs.WeilForm.CentredWindowTranslate
import Cvs.WeilForm.ChannelFormOnWave
import Cvs.WeilForm.ChannelFunctionalL2
import Cvs.WeilForm.ChannelKernelCosineEigen
import Cvs.WeilForm.ChannelQuadGreenFunction
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.OddCapTransfer
import Cvs.WeilForm.PrimeSideVanishesLogTwo
import Cvs.WeilForm.SelfConvolutionContinuous
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SelfConvolutionWindowEdge
import Cvs.WeilForm.TruncatedArchChannelSum
import Cvs.WeilForm.TruncatedArchDomain
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.Digamma.DigammaQuarterConstant
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-!
# The Dirichlet-mode cosine as a window trial

At `t = π/L` the centred cosine vanishes at both window endpoints, so its window class is nonzero
and has squared norm `L/2`.
-/

noncomputable section

open MeasureTheory Set Real Cvs.Zeta.Explicit.Weil

namespace Cvs.StepA.DirichletCosineTrial

variable {L : ℝ}

/-- The Dirichlet-mode frequency: `wave (π/L) L` vanishes at `0` and `L`. -/
def tw (L : ℝ) : ℝ := Real.pi / L

theorem wave_zero (hL : 0 < L) : Cvs.WeilForm.ChannelKernelCosineEigen.wave (tw L) L 0 = 0 := by
  unfold Cvs.WeilForm.ChannelKernelCosineEigen.wave tw
  rw [show Real.pi / L * (0 - L / 2) = -(Real.pi / 2) from by field_simp; ring]
  rw [Real.cos_neg, Real.cos_pi_div_two]

theorem wave_L (hL : 0 < L) : Cvs.WeilForm.ChannelKernelCosineEigen.wave (tw L) L L = 0 := by
  unfold Cvs.WeilForm.ChannelKernelCosineEigen.wave tw
  rw [show Real.pi / L * (L - L / 2) = Real.pi / 2 from by field_simp; ring]
  rw [Real.cos_pi_div_two]

/-- The Dirichlet-mode cosine, held to the window. -/
def waveFn (L : ℝ) : ℝ → ℝ := (Set.Icc 0 L).indicator (Cvs.WeilForm.ChannelKernelCosineEigen.wave (tw L) L)

theorem waveFn_abs_le (x : ℝ) : |waveFn L x| ≤ (Set.Icc 0 L).indicator (fun _ => (1:ℝ)) x := by
  unfold waveFn
  by_cases hx : x ∈ Set.Icc (0:ℝ) L
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    exact (abs_le.mpr ⟨neg_one_le_cos _, cos_le_one _⟩)
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, abs_zero]

theorem waveFn_memLp (_hL : 0 < L) : MemLp (waveFn L) 2 (volume : Measure ℝ) := by
  have hg : MemLp ((Set.Icc 0 L).indicator (fun _ => (1:ℝ))) 2 (volume : Measure ℝ) :=
    memLp_indicator_const 2 measurableSet_Icc.nullMeasurableSet 1 (Or.inr (by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  have hmeas : AEStronglyMeasurable (waveFn L) (volume : Measure ℝ) := by
    unfold waveFn
    exact (Continuous.aestronglyMeasurable (by unfold Cvs.WeilForm.ChannelKernelCosineEigen.wave; fun_prop)).indicator measurableSet_Icc
  refine hg.mono hmeas (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) x)]
  exact waveFn_abs_le x

theorem waveFn_eq_zero (hL : 0 < L) {x : ℝ} (hx : x ∉ Set.Ioc (0:ℝ) L) : waveFn L x = 0 := by
  unfold waveFn
  by_cases hxc : x ∈ Set.Icc (0:ℝ) L
  · rw [Set.indicator_of_mem hxc]
    -- x ∈ Icc but ∉ Ioc means x = 0
    have hx0 : x = 0 := by
      rcases hxc with ⟨h0, h1⟩
      by_contra hne
      exact hx ⟨lt_of_le_of_ne h0 (Ne.symm hne), h1⟩
    rw [hx0]; exact wave_zero hL
  · rw [Set.indicator_of_notMem hxc]

/-- The Dirichlet-mode cosine as a class in the window. -/
def waveW (hL : 0 < L) : Cvs.WeilForm.WeilFormOnWindowL2.window L :=
  ⟨(waveFn_memLp hL).toLp _, by
    show ∀ᵐ x ∂(volume : Measure ℝ), x ∉ Set.Ioc (0:ℝ) L → ((waveFn_memLp hL).toLp _ : ℝ → ℝ) x = 0
    filter_upwards [(waveFn_memLp hL).coeFn_toLp] with x hx hxL
    rw [hx]; exact waveFn_eq_zero hL hxL⟩

theorem rep_waveW_ae (hL : 0 < L) :
    Cvs.WeilForm.WindowRepresentative.rep (waveW hL) =ᵐ[(volume : Measure ℝ)] waveFn L := by
  refine (Cvs.WeilForm.WindowRepresentative.ae_eq_rep (waveW hL)).symm.trans ?_
  exact (waveFn_memLp hL).coeFn_toLp

theorem tw_ne_zero (hL : 0 < L) : tw L ≠ 0 := by
  unfold tw; positivity

/-- **The squared norm is `L/2`.** -/
theorem waveW_norm_sq (hL : 0 < L) : ‖waveW hL‖ ^ 2 = L / 2 := by
  rw [Cvs.WeilForm.OddCapTransfer.sq_norm_eq_integral_rep]
  rw [MeasureTheory.integral_congr_ae ((rep_waveW_ae hL).mono (fun x hx => by rw [hx]))]
  have hpow : (fun x => waveFn L x ^ 2)
      = (Set.Icc (0:ℝ) L).indicator (fun x => Cvs.WeilForm.ChannelKernelCosineEigen.wave (tw L) L x ^ 2) := by
    funext x
    unfold waveFn
    by_cases hx : x ∈ Set.Icc (0:ℝ) L
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; ring
  rw [hpow, MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hL.le,
    Cvs.WeilForm.ChannelFormOnWave.integral_wave_sq (tw_ne_zero hL) L]
  have : Real.sin (tw L * L) = 0 := by
    unfold tw; rw [div_mul_cancel₀ _ (ne_of_gt hL)]; exact Real.sin_pi
  rw [this]; ring

theorem waveW_ne_zero (hL : 0 < L) : waveW hL ≠ 0 := by
  intro h
  have : ‖waveW hL‖ ^ 2 = 0 := by rw [h]; simp
  rw [waveW_norm_sq hL] at this
  exact absurd this (by positivity)

theorem tw_half (hL : 0 < L) : tw L * (L / 2) = Real.pi / 2 := by
  unfold tw; field_simp

/-- **The `e^{s/2}` moment of the wave.** -/
theorem leftMoment_half (hL : 0 < L) :
    Cvs.Finite.ExponentialKernelLocalises.leftMoment (1 / 2) (Cvs.WeilForm.ChannelKernelCosineEigen.wave (tw L) L) L
      = tw L * (Real.exp (L / 2) + 1) / (1 / 4 + tw L ^ 2) := by
  have hbt : (1 / 2 : ℝ) ^ 2 + tw L ^ 2 ≠ 0 := by positivity
  rw [Cvs.WeilForm.ChannelKernelCosineEigen.leftMoment_wave hbt]
  unfold Cvs.WeilForm.ChannelKernelCosineEigen.leftAnti
  rw [show tw L * (L - L / 2) = Real.pi / 2 from by rw [show L - L/2 = L/2 from by ring]; exact tw_half hL,
    show tw L * (0 - L / 2) = -(Real.pi / 2) from by rw [show (0:ℝ) - L/2 = -(L/2) from by ring, mul_neg]; rw [tw_half hL]]
  rw [Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_neg, Real.sin_neg,
    Real.cos_pi_div_two, Real.sin_pi_div_two, mul_zero, Real.exp_zero]
  ring

/-- **The `e^{-s/2}` moment of the wave.** -/
theorem leftMoment_neg_half (hL : 0 < L) :
    Cvs.Finite.ExponentialKernelLocalises.leftMoment (-(1 / 2)) (Cvs.WeilForm.ChannelKernelCosineEigen.wave (tw L) L) L
      = tw L * (Real.exp (-(L / 2)) + 1) / (1 / 4 + tw L ^ 2) := by
  have hbt : (-(1 / 2) : ℝ) ^ 2 + tw L ^ 2 ≠ 0 := by positivity
  rw [Cvs.WeilForm.ChannelKernelCosineEigen.leftMoment_wave hbt]
  unfold Cvs.WeilForm.ChannelKernelCosineEigen.leftAnti
  rw [show tw L * (L - L / 2) = Real.pi / 2 from by rw [show L - L/2 = L/2 from by ring]; exact tw_half hL,
    show tw L * (0 - L / 2) = -(Real.pi / 2) from by rw [show (0:ℝ) - L/2 = -(L/2) from by ring, mul_neg]; rw [tw_half hL]]
  rw [Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_neg, Real.sin_neg,
    Real.cos_pi_div_two, Real.sin_pi_div_two, mul_zero, Real.exp_zero]
  ring

theorem tw_pos (hL : 0 < L) : 0 < tw L := by unfold tw; positivity

/-- **The wave is Lipschitz with constant `π/L`.** -/
theorem abs_wave_sub_le (hL : 0 < L) (a b : ℝ) :
    |Cvs.WeilForm.ChannelKernelCosineEigen.wave (tw L) L a - Cvs.WeilForm.ChannelKernelCosineEigen.wave (tw L) L b|
      ≤ tw L * |a - b| := by
  unfold Cvs.WeilForm.ChannelKernelCosineEigen.wave
  have hc := Real.lipschitzWith_cos.dist_le_mul (tw L * (a - L / 2)) (tw L * (b - L / 2))
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] at hc
  calc |Real.cos (tw L * (a - L / 2)) - Real.cos (tw L * (b - L / 2))|
      ≤ |tw L * (a - L / 2) - tw L * (b - L / 2)| := hc
    _ = tw L * |a - b| := by
        rw [show tw L * (a - L / 2) - tw L * (b - L / 2) = tw L * (a - b) from by ring,
          abs_mul, abs_of_pos (tw_pos hL)]

/-- **The pointwise deficit bound.**  `waveFn` is Lipschitz-`π/L` and vanishes at the endpoints. -/
theorem waveFn_sub_sq_le (hL : 0 < L) {h : ℝ} (hh : 0 ≤ h) (s : ℝ) :
    (waveFn L s - waveFn L (s + h)) ^ 2 ≤ (tw L) ^ 2 * h ^ 2 := by
  have key : |waveFn L s - waveFn L (s + h)| ≤ tw L * h := by
    unfold waveFn
    by_cases hs : s ∈ Set.Icc (0:ℝ) L <;> by_cases hsh : s + h ∈ Set.Icc (0:ℝ) L
    · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hsh]
      calc |_| ≤ tw L * |s - (s + h)| := abs_wave_sub_le hL s (s + h)
        _ = tw L * h := by rw [show s - (s + h) = -h from by ring, abs_neg, abs_of_nonneg hh]
    · -- s ∈ Icc, s+h ∉ Icc : s+h > L, so s ∈ (L-h, L]
      rw [Set.indicator_of_mem hs, Set.indicator_of_notMem hsh, sub_zero]
      have hsL : s + h > L := by
        rcases hs with ⟨h0, h1⟩; by_contra hle; push Not at hle
        exact hsh ⟨by linarith, hle⟩
      have : Cvs.WeilForm.ChannelKernelCosineEigen.wave (tw L) L s
          = Cvs.WeilForm.ChannelKernelCosineEigen.wave (tw L) L s - Cvs.WeilForm.ChannelKernelCosineEigen.wave (tw L) L L := by
        rw [wave_L hL]; ring
      rw [this]
      calc |_| ≤ tw L * |s - L| := abs_wave_sub_le hL s L
        _ ≤ tw L * h := by
            apply mul_le_mul_of_nonneg_left _ (tw_pos hL).le
            rw [abs_of_nonpos (by rcases hs with ⟨_, h1⟩; linarith)]; linarith [hs.2]
    · -- s ∉ Icc, s+h ∈ Icc : s < 0, so s+h ∈ [0, h)
      rw [Set.indicator_of_notMem hs, Set.indicator_of_mem hsh, zero_sub, abs_neg]
      have hs0 : s < 0 := by
        rcases hsh with ⟨h0, h1⟩; by_contra hle; push Not at hle
        exact hs ⟨hle, by linarith⟩
      have : Cvs.WeilForm.ChannelKernelCosineEigen.wave (tw L) L (s + h)
          = Cvs.WeilForm.ChannelKernelCosineEigen.wave (tw L) L (s + h) - Cvs.WeilForm.ChannelKernelCosineEigen.wave (tw L) L 0 := by
        rw [wave_zero hL]; ring
      rw [this]
      calc |_| ≤ tw L * |(s + h) - 0| := abs_wave_sub_le hL (s + h) 0
        _ ≤ tw L * h := by
            apply mul_le_mul_of_nonneg_left _ (tw_pos hL).le
            rw [sub_zero, abs_of_nonneg (by rcases hsh with ⟨h0, _⟩; exact h0)]; linarith
    · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hsh, sub_zero, abs_zero]
      exact mul_nonneg (tw_pos hL).le hh
  calc (waveFn L s - waveFn L (s + h)) ^ 2 = |waveFn L s - waveFn L (s + h)| ^ 2 := (sq_abs _).symm
    _ ≤ (tw L * h) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) key 2
    _ = (tw L) ^ 2 * h ^ 2 := by ring

theorem waveFn_sq_int (hL : 0 < L) : Integrable (fun s => waveFn L s ^ 2) (volume : Measure ℝ) :=
  (waveFn_memLp hL).integrable_sq

theorem waveFn_mul_int (hL : 0 < L) (h : ℝ) :
    Integrable (fun s => waveFn L s * waveFn L (s + h)) (volume : Measure ℝ) :=
  (waveFn_memLp hL).integrable_mul (Cvs.WeilForm.CentredWindowTranslate.memLp_translate h (waveFn_memLp hL))

/-- **The deficit is second order.** -/
theorem deficit_wave_le (hL : 0 < L) {h : ℝ} (hh : 0 ≤ h) :
    selfConvolution (waveFn L) 0 - selfConvolution (waveFn L) h
      ≤ (tw L) ^ 2 * h ^ 2 * (L + h) / 2 := by
  have hid := Cvs.WeilForm.SelfConvolutionFunctional.integral_sq_sub_eq h (waveFn_sq_int hL) (waveFn_mul_int hL h)
  have hsupp : ∀ s, s ∉ Set.Icc (-h) L → (waveFn L s - waveFn L (s + h)) ^ 2 = 0 := by
    intro s hs
    have h1 : waveFn L s = 0 := by
      refine waveFn_eq_zero hL (fun h' => hs ⟨by linarith [h'.1], h'.2⟩)
    have h2 : waveFn L (s + h) = 0 := by
      refine waveFn_eq_zero hL (fun h' => hs ⟨by linarith [h'.1], by linarith [h'.2]⟩)
    rw [h1, h2]; ring
  have hI : IntegrableOn (fun s => (waveFn L s - waveFn L (s + h)) ^ 2) (Set.Icc (-h) L) volume :=
    ((waveFn_sq_int hL).sub ((waveFn_mul_int hL h).const_mul 2) |>.add
      ((waveFn_sq_int hL).comp_add_right h) |>.congr (Filter.Eventually.of_forall fun s => by
        simp only [Pi.add_apply, Pi.sub_apply]; ring)).integrableOn
  have hint : ∫ s, (waveFn L s - waveFn L (s + h)) ^ 2 ≤ (tw L) ^ 2 * h ^ 2 * (L + h) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
    calc ∫ s in Set.Icc (-h) L, (waveFn L s - waveFn L (s + h)) ^ 2
        ≤ ∫ _ in Set.Icc (-h) L, (tw L) ^ 2 * h ^ 2 :=
          setIntegral_mono_on hI continuous_const.integrableOn_Icc measurableSet_Icc
            fun s _ => waveFn_sub_sq_le hL hh s
      _ = (tw L) ^ 2 * h ^ 2 * (L + h) := by
          rw [setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Icc,
            ENNReal.toReal_ofReal (by linarith)]; ring
  linarith

theorem selfConvolution_rep_waveW (hL : 0 < L) (v : ℝ) :
    selfConvolution (Cvs.WeilForm.WindowRepresentative.rep (waveW hL)) v = selfConvolution (waveFn L) v := by
  unfold selfConvolution
  refine integral_congr_ae ?_
  have h1 := rep_waveW_ae hL
  have h2 : (fun s => Cvs.WeilForm.WindowRepresentative.rep (waveW hL) (s + v))
      =ᵐ[volume] fun s => waveFn L (s + v) :=
    (measurePreserving_add_right volume v).quasiMeasurePreserving.ae_eq_comp h1
  filter_upwards [h1, h2] with s hs1 hs2
  rw [hs1, hs2]

/-- **The wave trial's Lévy integrand is integrable on `(0, ∞)`.** -/
theorem integrableOn_levy_waveW (hL : 0 < L) :
    MeasureTheory.IntegrableOn
      (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep (waveW hL)))
      (Set.Ioi 0) (volume : Measure ℝ) := by
  set φ := waveW hL with hφ
  have hmeas : AEStronglyMeasurable (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep φ))
      (volume.restrict (Set.Ioi 0)) :=
    Cvs.WeilForm.TruncatedArchDomain.aestronglyMeasurable_levy
      (Cvs.WeilForm.SelfConvolutionContinuous.continuous_selfConvolution
        (Cvs.WeilForm.WindowRepresentative.memLp_rep φ)).aestronglyMeasurable
  have hnn : ∀ u, 0 < u → 0 ≤ Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep φ) u := fun u hu =>
    Cvs.WeilForm.Archimedean.ArchEnergySpectral.levy_nonneg (Cvs.WeilForm.WindowRepresentative.integrable_sq_rep φ)
      (Cvs.WeilForm.WindowRepresentative.integrable_cross_rep φ) hu
  have h1 : MeasureTheory.IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep φ))
      (Set.Ioc 0 1) volume := by
    refine MeasureTheory.Integrable.mono' (g := fun _ : ℝ => (tw L) ^ 2 * (L + 1) / 4)
      ((continuous_const.integrableOn_Icc (a := (0:ℝ)) (b := 1)).mono_set Set.Ioc_subset_Icc_self)
      (hmeas.mono_measure (MeasureTheory.Measure.restrict_mono Set.Ioc_subset_Ioi_self le_rfl)) ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun u hu => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn u hu.1)]
    show Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep φ) u ≤ (tw L) ^ 2 * (L + 1) / 4
    unfold Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy
    rw [selfConvolution_rep_waveW, selfConvolution_rep_waveW]
    have hdef := deficit_wave_le hL (show (0:ℝ) ≤ u / 2 by linarith [hu.1])
    have hdens := Cvs.WeilForm.Archimedean.HatLevyDeficit.densityU_le_two_div hu.1 hu.2
    have hdpos := Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu.1
    have hdefnn : 0 ≤ selfConvolution (waveFn L) 0 - selfConvolution (waveFn L) (u / 2) := by
      have := hnn u hu.1
      unfold Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy at this
      rw [selfConvolution_rep_waveW, selfConvolution_rep_waveW] at this
      exact nonneg_of_mul_nonneg_right this hdpos
    calc Cvs.WeilForm.Archimedean.LevyDensity.densityU u * (selfConvolution (waveFn L) 0 - selfConvolution (waveFn L) (u / 2))
        ≤ (2 / u) * ((tw L) ^ 2 * (u / 2) ^ 2 * (L + u / 2) / 2) :=
          mul_le_mul hdens hdef hdefnn (div_pos two_pos hu.1).le
      _ = (tw L) ^ 2 * u * (L + u / 2) / 4 := by field_simp; ring
      _ ≤ (tw L) ^ 2 * (L + 1) / 4 := by
          have hub : u * (L + u / 2) ≤ L + 1 := by
            nlinarith [hu.1, hu.2, hL, mul_nonneg (sub_nonneg.mpr hu.2) hL.le]
          rw [show (tw L) ^ 2 * u * (L + u / 2) / 4 = (tw L) ^ 2 / 4 * (u * (L + u / 2)) from by ring,
            show (tw L) ^ 2 * (L + 1) / 4 = (tw L) ^ 2 / 4 * (L + 1) from by ring]
          exact mul_le_mul_of_nonneg_left hub (by positivity)
  have h2 : MeasureTheory.IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep φ)) (Set.Ioi 1) volume := by
    refine MeasureTheory.Integrable.mono' ((Cvs.WeilForm.SelfConvolutionWindowEdge.densityU_integrableOn one_pos).const_mul
      (2 * selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ) 0))
      (hmeas.mono_measure (MeasureTheory.Measure.restrict_mono (Set.Ioi_subset_Ioi zero_le_one) le_rfl)) ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u hu => ?_)
    have hu0 : (0:ℝ) < u := lt_trans zero_lt_one hu
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn u hu0)]
    show Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep φ) u
      ≤ 2 * selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ) 0 * Cvs.WeilForm.Archimedean.LevyDensity.densityU u
    unfold Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (Cvs.WeilForm.Archimedean.HatLevyDeficit.deficit_le_two φ (u / 2))
      (Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu0).le
  exact (h1.union h2).mono_set Set.Ioi_subset_Ioc_union_Ioi

/-- **The wave trial, as an element of the form domain.** -/
def waveD (hL : 0 < L) : Cvs.WeilForm.FormDomain.formDomain hL.le :=
  ⟨waveW hL, integrableOn_levy_waveW hL⟩

theorem waveD_ne_zero (hL : 0 < L) : waveD hL ≠ 0 := fun h =>
  waveW_ne_zero hL (congrArg Subtype.val h)

/-- **The `e^{s/2}` moment of the trial's representative** (the full-line integral equals the
window integral, since the representative is supported in `[0, L]`). -/
theorem integral_rep_exp_half (hL : 0 < L) :
    (∫ x : ℝ, Cvs.WeilForm.WindowRepresentative.rep (waveW hL) x * Real.exp (x / 2))
      = tw L * (Real.exp (L / 2) + 1) / (1 / 4 + tw L ^ 2) := by
  rw [MeasureTheory.integral_congr_ae ((rep_waveW_ae hL).mono (fun x hx => by rw [hx]))]
  have hind : (fun x => waveFn L x * Real.exp (x / 2))
      = (Set.Icc (0:ℝ) L).indicator (fun x => Cvs.WeilForm.ChannelKernelCosineEigen.wave (tw L) L x * Real.exp (x / 2)) := by
    funext x; unfold waveFn
    by_cases hx : x ∈ Set.Icc (0:ℝ) L
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
  rw [hind, MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hL.le,
    ← leftMoment_half hL]
  unfold Cvs.Finite.ExponentialKernelLocalises.leftMoment
  exact intervalIntegral.integral_congr fun x _ => by rw [show x / 2 = 1 / 2 * x from by ring]; ring

/-- **The `e^{-s/2}` moment of the trial's representative.** -/
theorem integral_rep_exp_neg_half (hL : 0 < L) :
    (∫ x : ℝ, Cvs.WeilForm.WindowRepresentative.rep (waveW hL) x * Real.exp (-(x / 2)))
      = tw L * (Real.exp (-(L / 2)) + 1) / (1 / 4 + tw L ^ 2) := by
  rw [MeasureTheory.integral_congr_ae ((rep_waveW_ae hL).mono (fun x hx => by rw [hx]))]
  have hind : (fun x => waveFn L x * Real.exp (-(x / 2)))
      = (Set.Icc (0:ℝ) L).indicator (fun x => Cvs.WeilForm.ChannelKernelCosineEigen.wave (tw L) L x * Real.exp (-(x / 2))) := by
    funext x; unfold waveFn
    by_cases hx : x ∈ Set.Icc (0:ℝ) L
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
  rw [hind, MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hL.le,
    ← leftMoment_neg_half hL]
  unfold Cvs.Finite.ExponentialKernelLocalises.leftMoment
  exact intervalIntegral.integral_congr fun x _ => by rw [show -(x / 2) = -(1 / 2) * x from by ring]; ring

/-- **The edge mass in closed form at the Dirichlet frequency.**  The oscillatory endpoint terms
vanish (`cos(±π/2)=0`), leaving `2t(1+e^{−bL})/(b²+t²)`. -/
theorem edgeMass_wave (hL : 0 < L) (b : ℝ) :
    Cvs.WeilForm.ChannelFormOnWave.edgeMass b (tw L) L
      = 2 * tw L * (1 + Real.exp (-b * L)) / (b ^ 2 + tw L ^ 2) := by
  have htw : 0 < tw L := tw_pos hL
  have hbt : b ^ 2 + tw L ^ 2 ≠ 0 := by positivity
  have hargL : tw L * (L - L / 2) = Real.pi / 2 := by
    rw [show L - L / 2 = L / 2 from by ring]; exact tw_half hL
  have harg0 : tw L * (0 - L / 2) = -(Real.pi / 2) := by
    rw [show (0:ℝ) - L / 2 = -(L / 2) from by ring, mul_neg]; rw [tw_half hL]
  rw [Cvs.WeilForm.ChannelFormOnWave.edgeMass_eq hbt]
  unfold Cvs.WeilForm.ChannelKernelCosineEigen.rightAnti Cvs.WeilForm.ChannelKernelCosineEigen.leftAnti
  rw [hargL, harg0, Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_neg, Real.sin_neg,
    Real.cos_pi_div_two, Real.sin_pi_div_two,
    show -b * L = -(b * L) from by ring, show -b * (0:ℝ) = -(b * 0) from by ring]
  simp only [mul_zero, neg_zero, Real.exp_zero, Real.exp_neg]
  have hEne : Real.exp (b * L) ≠ 0 := Real.exp_ne_zero _
  field_simp
  ring

/-- **The trial is continuous** (the cosine vanishes at both endpoints). -/
theorem continuous_waveFn (hL : 0 < L) : Continuous (waveFn L) := by
  unfold waveFn
  rw [← Set.piecewise_eq_indicator]
  apply Continuous.piecewise
  · intro a ha
    rw [frontier_Icc hL.le] at ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with h | h
    · rw [h]; simpa using wave_zero hL
    · rw [h]; simpa using wave_L hL
  · unfold Cvs.WeilForm.ChannelKernelCosineEigen.wave; fun_prop
  · exact continuous_const

theorem hasCompactSupport_waveFn (hL : 0 < L) : HasCompactSupport (waveFn L) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (0:ℝ)) (b := L)) ?_
  intro s hs
  by_contra hmem
  exact hs (by
    have : s ∉ Set.Ioc (0:ℝ) L := fun h => hmem (Set.Ioc_subset_Icc_self h)
    exact waveFn_eq_zero hL this)

set_option maxHeartbeats 6400000 in
/-- **Euler's constant from the 127th harmonic number**, `log 128 = 7 log 2`. -/
theorem gamma_gt_harmonic127 :
    (36224297430743310519741406921577722033292201622850612663 / 6676878045498705789701874602220118271269436344024536000 : ℝ) - 7 * Real.log 2 < Real.eulerMascheroniConstant := by
  have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 127
  rw [Real.eulerMascheroniSeq] at h
  have hh : ((harmonic 127 : ℚ) : ℝ) = (36224297430743310519741406921577722033292201622850612663 / 6676878045498705789701874602220118271269436344024536000 : ℝ) := by norm_num [harmonic]
  have hl : Real.log (((127 : ℕ) : ℝ) + 1) = 7 * Real.log 2 := by
    rw [show (((127 : ℕ) : ℝ) + 1) = 2 ^ (7 : ℕ) from by norm_num, Real.log_pow]; push_cast; ring
  rw [hh, hl] at h
  exact h

/-- **A sharp upper bound for the archimedean constant**, `γ` from index 127. -/
theorem archSymbol_zero_upper : Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 ≤ (-5.368 : ℝ) := by
  obtain ⟨hlp, hlp'⟩ := Cvs.Moments.log_pi_bounds
  have hg := gamma_gt_harmonic127
  have hl2 := Real.log_two_lt_d9
  have hp1 := Real.pi_gt_d6
  rw [Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.archSymbol_zero_eq]
  linarith

theorem waveFn_eq_wave_of_mem {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) L) :
    waveFn L x = Cvs.WeilForm.ChannelKernelCosineEigen.wave (tw L) L x := by
  unfold waveFn; rw [Set.indicator_of_mem hx]

theorem convSplit_waveFn (hL : 0 < L) (b : ℝ) {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) L) :
    Cvs.Finite.ExponentialKernelLocalises.convSplit b L (waveFn L) s
      = Cvs.Finite.ExponentialKernelLocalises.convSplit b L (Cvs.WeilForm.ChannelKernelCosineEigen.wave (tw L) L) s := by
  unfold Cvs.Finite.ExponentialKernelLocalises.convSplit Cvs.Finite.ExponentialKernelLocalises.leftMoment Cvs.Finite.ExponentialKernelLocalises.rightMoment
  have hlm : (∫ u in (0:ℝ)..s, Real.exp (b * u) * waveFn L u)
      = ∫ u in (0:ℝ)..s, Real.exp (b * u) * Cvs.WeilForm.ChannelKernelCosineEigen.wave (tw L) L u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le hs.1] at hu
    simp only []
    rw [waveFn_eq_wave_of_mem ⟨hu.1, le_trans hu.2 hs.2⟩]
  have hrm : (∫ u in s..L, Real.exp (-b * u) * waveFn L u)
      = ∫ u in s..L, Real.exp (-b * u) * Cvs.WeilForm.ChannelKernelCosineEigen.wave (tw L) L u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le hs.2] at hu
    simp only []
    rw [waveFn_eq_wave_of_mem ⟨le_trans hs.1 hu.1, hu.2⟩]
  rw [hlm, hrm]

theorem chanInt_rep_eq_waveFn (hL : 0 < L) (b : ℝ) :
    Cvs.WeilForm.ChannelFunctionalL2.chanInt b (Cvs.WeilForm.WindowRepresentative.rep (waveW hL))
      = Cvs.WeilForm.ChannelFunctionalL2.chanInt b (waveFn L) := by
  unfold Cvs.WeilForm.ChannelFunctionalL2.chanInt
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v _
  simp only []
  rw [selfConvolution_rep_waveW hL v]

/-- **(A) The channel functional equals the exact wave quadratic form.** -/
theorem chanInt_eq_quadForm (hL : 0 < L) (b : ℝ) (hb : 0 < b) :
    Cvs.WeilForm.ChannelFunctionalL2.chanInt b (Cvs.WeilForm.WindowRepresentative.rep (waveW hL))
      = ∫ s in (0:ℝ)..L, Cvs.WeilForm.ChannelKernelCosineEigen.wave (tw L) L s
          * Cvs.Finite.ExponentialKernelLocalises.convSplit b L (Cvs.WeilForm.ChannelKernelCosineEigen.wave (tw L) L) s := by
  rw [chanInt_rep_eq_waveFn hL b,
    Cvs.WeilForm.ChannelFunctionalL2.chanInt_eq_double (continuous_waveFn hL) (hasCompactSupport_waveFn hL) hb,
    Cvs.WeilForm.ChannelQuadGreenFunction.channelQuad_convSplit hL.le (continuous_waveFn hL)
      (fun x hx => waveFn_eq_zero hL (fun h => hx (Set.Ioc_subset_Icc_self h))) b]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le hL.le] at hs
  simp only []
  rw [waveFn_eq_wave_of_mem hs, convSplit_waveFn hL b hs]

theorem integral_wave_sq_value (hL : 0 < L) :
    (∫ s in (0:ℝ)..L, Cvs.WeilForm.ChannelKernelCosineEigen.wave (tw L) L s ^ 2) = L / 2 := by
  rw [Cvs.WeilForm.ChannelFormOnWave.integral_wave_sq (tw_ne_zero hL) L]
  have : Real.sin (tw L * L) = 0 := by
    unfold tw; rw [div_mul_cancel₀ _ (ne_of_gt hL)]; exact Real.sin_pi
  rw [this]; ring

/-- **The channel functional on the trial, in closed form.** -/
theorem chanInt_value (hL : 0 < L) (b : ℝ) (hb : 0 < b) :
    Cvs.WeilForm.ChannelFunctionalL2.chanInt b (Cvs.WeilForm.WindowRepresentative.rep (waveW hL))
      = b * L / (b ^ 2 + tw L ^ 2)
        + 2 * tw L ^ 2 * (1 + Real.exp (-b * L)) / (b ^ 2 + tw L ^ 2) ^ 2 := by
  have htw := tw_pos hL
  have hbt : b ^ 2 + tw L ^ 2 ≠ 0 := by positivity
  rw [chanInt_eq_quadForm hL b hb, Cvs.WeilForm.ChannelFormOnWave.quadForm_wave hbt,
    integral_wave_sq_value hL, edgeMass_wave hL b, tw_half hL,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  field_simp
  ring

theorem selfConv_rep_zero (hL : 0 < L) :
    selfConvolution (Cvs.WeilForm.WindowRepresentative.rep (waveW hL)) 0 = L / 2 := by
  have h : selfConvolution (Cvs.WeilForm.WindowRepresentative.rep (waveW hL)) 0 = ‖waveW hL‖ ^ 2 := by
    rw [Cvs.WeilForm.OddCapTransfer.sq_norm_eq_integral_rep]
    unfold selfConvolution
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [add_zero, pow_two])
  rw [h, waveW_norm_sq hL]

/-- **The truncated Lévy integral is the finite channel sum** (from `Cvs.WeilForm.TruncatedArchChannelSum`). -/
theorem partialLevy_eq (hL : 0 < L) (N : ℕ) :
    (∫ u in Set.Ioi (0:ℝ), Cvs.WeilForm.Archimedean.TruncatedLevyDensityBelow.densityTrunc N u
        * (selfConvolution (Cvs.WeilForm.WindowRepresentative.rep (waveW hL)) 0
          - selfConvolution (Cvs.WeilForm.WindowRepresentative.rep (waveW hL)) (u / 2)))
      = ∑ k ∈ Finset.range N, ((1 / ((k : ℝ) + 1 / 4)) * (L / 2)
          - Cvs.WeilForm.ChannelFunctionalL2.chanInt (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k)
              (Cvs.WeilForm.WindowRepresentative.rep (waveW hL))) := by
  have hb := Cvs.WeilForm.TruncatedArchChannelSum.archLevy_eq_channelSum (waveW hL) N
  rw [selfConv_rep_zero hL] at hb ⊢
  simp only [Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst] at hb
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  linear_combination hb

theorem tsq_lower : (128389299 / 6250000 : ℝ) ≤ (tw (Real.log 2)) ^ 2 := by
  have hpi := Real.pi_gt_d20
  have hl2 := Real.log_two_lt_d9
  have hl2p : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  unfold tw
  rw [div_pow, le_div_iff₀ (by positivity)]
  nlinarith [hpi, hl2, hl2p, Real.pi_pos, mul_pos hl2p hl2p]

theorem tsq_upper : (tw (Real.log 2)) ^ 2 ≤ (1027114429 / 50000000 : ℝ) := by
  have hpi := Real.pi_lt_d20
  have hl2 := Real.log_two_gt_d9
  have hl2p : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  unfold tw
  rw [div_pow, div_le_iff₀ (by positivity)]
  nlinarith [hpi, hl2, hl2p, Real.pi_pos, mul_pos hl2p hl2p]

/-- **`exp(−bIdx k · log 2) = (1/4)^k / √2`.** -/
theorem exp_neg_bIdx_logtwo (k : ℕ) :
    Real.exp (-(Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k) * Real.log 2) = (1/4)^k / Real.sqrt 2 := by
  have h2 : (0:ℝ) < 2 := by norm_num
  rw [Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx]
  have hre : -(2 * (k:ℝ) + 1/2) * Real.log 2 = Real.log 2 * (-(2*(k:ℝ)+1/2)) := by ring
  rw [hre, Real.exp_mul, Real.exp_log h2, Real.rpow_neg (by norm_num), Real.rpow_add h2,
    show (2*(k:ℝ)) = ((2*k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
    show (2:ℝ)^(2*k) = 4^k by rw [pow_mul]; norm_num, ← Real.sqrt_eq_rpow]
  rw [mul_inv, ← inv_pow]; norm_num [div_eq_mul_inv]

/-- **`exp(log 2 / 2) = √2`.** -/
theorem exp_logtwo_half : Real.exp (Real.log 2 / 2) = Real.sqrt 2 := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num)]; congr 1; ring

/-- **`exp(−log 2 / 2) = (√2)⁻¹`.** -/
theorem exp_neg_logtwo_half : Real.exp (-(Real.log 2 / 2)) = (Real.sqrt 2)⁻¹ := by
  rw [← exp_logtwo_half, ← Real.exp_neg]

/-- **The rank-one term of the trial, bounded.** -/
theorem rank1_le (hL : 0 < Real.log 2) :
    2 * (∫ x : ℝ, Cvs.WeilForm.WindowRepresentative.rep (waveW hL) x * Real.exp (x / 2))
        * (∫ x : ℝ, Cvs.WeilForm.WindowRepresentative.rep (waveW hL) x * Real.exp (-(x / 2)))
      ≤ 195831 / 500000 := by
  rw [integral_rep_exp_half hL, integral_rep_exp_neg_half hL, exp_logtwo_half, exp_neg_logtwo_half]
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsp : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hinv : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by field_simp; linarith [hs2]
  have ht := tsq_lower
  have ht' := tsq_upper
  have hs : (1.41421356 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1.41421356:ℝ) = Real.sqrt (1.41421356^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hs' : Real.sqrt 2 ≤ 1.41421357 := by
    rw [show (1.41421357:ℝ) = Real.sqrt (1.41421357^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hden : (0:ℝ) < 1/4 + tw (Real.log 2)^2 := by positivity
  rw [hinv]
  have key : 2 * (tw (Real.log 2) * (Real.sqrt 2 + 1) / (1/4 + tw (Real.log 2)^2))
        * (tw (Real.log 2) * (Real.sqrt 2/2 + 1) / (1/4 + tw (Real.log 2)^2))
      = (2 * tw (Real.log 2)^2 * (Real.sqrt 2+1) * (Real.sqrt 2/2+1)) / (1/4 + tw (Real.log 2)^2)^2 := by
    field_simp
  rw [key, div_le_iff₀ (by positivity)]
  nlinarith [ht, ht', hs, hs', hden, hs2, tw_pos hL, mul_pos hden hden, sq_nonneg (tw (Real.log 2))]

theorem chanLevy_0_le (hL : 0 < Real.log 2) :
    (1 / ((0:ℕ) + 1/4 : ℝ)) * (Real.log 2 / 2)
      - Cvs.WeilForm.ChannelFunctionalL2.chanInt (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 0) (Cvs.WeilForm.WindowRepresentative.rep (waveW hL))
    ≤ (241479/200000 : ℝ) := by
  have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 0 = 1/2 := by rw [Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx]; norm_num
  have hsp : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hinv' : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by field_simp; linarith [hs2]
  rw [chanInt_value hL (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 0) (by rw [hb]; norm_num),
      exp_neg_bIdx_logtwo 0, hb,
      show ((1:ℝ)/4)^0 / Real.sqrt 2 = (1/1:ℝ) * (Real.sqrt 2 / 2) from by
        rw [show ((1:ℝ)/4)^0 = (1/1:ℝ) by norm_num, div_eq_mul_inv, hinv']]
  have ht := tsq_lower
  have ht' := tsq_upper
  have hl9 := Real.log_two_gt_d9
  have hl9' := Real.log_two_lt_d9
  have hs : (1.41421356 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1.41421356:ℝ) = Real.sqrt (1.41421356^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hs' : Real.sqrt 2 ≤ 1.41421357 := by
    rw [show (1.41421357:ℝ) = Real.sqrt (1.41421357^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hD : (0:ℝ) < (1/2:ℝ)^2 + tw (Real.log 2)^2 := by positivity
  rw [show (1:ℝ)/((0:ℕ)+1/4) = (4/1:ℝ) by norm_num]
  have key : (4/1:ℝ) * (Real.log 2/2)
      - ((1/2:ℝ) * Real.log 2 / ((1/2:ℝ)^2 + tw (Real.log 2)^2)
        + 2 * tw (Real.log 2)^2 * (1 + (1/1:ℝ) * (Real.sqrt 2 / 2)) / ((1/2:ℝ)^2 + tw (Real.log 2)^2)^2)
      = ((4/1:ℝ) * (Real.log 2/2) * ((1/2:ℝ)^2 + tw (Real.log 2)^2)^2
          - (1/2:ℝ) * Real.log 2 * ((1/2:ℝ)^2 + tw (Real.log 2)^2)
          - 2 * tw (Real.log 2)^2 * (1 + (1/1:ℝ) * (Real.sqrt 2 / 2)))
        / ((1/2:ℝ)^2 + tw (Real.log 2)^2)^2 := by field_simp; ring
  rw [key, div_le_iff₀ (by positivity)]
  nlinarith [ht, ht', hl9, hl9', hs, hs', hsp, hD, tw_pos hL, mul_pos hD hD,
    sq_nonneg (tw (Real.log 2)), mul_pos (mul_pos hD hD) hD]

theorem chanLevy_1_le (hL : 0 < Real.log 2) :
    (1 / ((1:ℕ) + 1/4 : ℝ)) * (Real.log 2 / 2)
      - Cvs.WeilForm.ChannelFunctionalL2.chanInt (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 1) (Cvs.WeilForm.WindowRepresentative.rep (waveW hL))
    ≤ (145229/1000000 : ℝ) := by
  have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 1 = 5/2 := by rw [Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx]; norm_num
  have hsp : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hinv' : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by field_simp; linarith [hs2]
  rw [chanInt_value hL (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 1) (by rw [hb]; norm_num),
      exp_neg_bIdx_logtwo 1, hb,
      show ((1:ℝ)/4)^1 / Real.sqrt 2 = (1/4:ℝ) * (Real.sqrt 2 / 2) from by
        rw [show ((1:ℝ)/4)^1 = (1/4:ℝ) by norm_num, div_eq_mul_inv, hinv']]
  have ht := tsq_lower
  have ht' := tsq_upper
  have hl9 := Real.log_two_gt_d9
  have hl9' := Real.log_two_lt_d9
  have hs : (1.41421356 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1.41421356:ℝ) = Real.sqrt (1.41421356^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hs' : Real.sqrt 2 ≤ 1.41421357 := by
    rw [show (1.41421357:ℝ) = Real.sqrt (1.41421357^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hD : (0:ℝ) < (5/2:ℝ)^2 + tw (Real.log 2)^2 := by positivity
  rw [show (1:ℝ)/((1:ℕ)+1/4) = (4/5:ℝ) by norm_num]
  have key : (4/5:ℝ) * (Real.log 2/2)
      - ((5/2:ℝ) * Real.log 2 / ((5/2:ℝ)^2 + tw (Real.log 2)^2)
        + 2 * tw (Real.log 2)^2 * (1 + (1/4:ℝ) * (Real.sqrt 2 / 2)) / ((5/2:ℝ)^2 + tw (Real.log 2)^2)^2)
      = ((4/5:ℝ) * (Real.log 2/2) * ((5/2:ℝ)^2 + tw (Real.log 2)^2)^2
          - (5/2:ℝ) * Real.log 2 * ((5/2:ℝ)^2 + tw (Real.log 2)^2)
          - 2 * tw (Real.log 2)^2 * (1 + (1/4:ℝ) * (Real.sqrt 2 / 2)))
        / ((5/2:ℝ)^2 + tw (Real.log 2)^2)^2 := by field_simp; ring
  rw [key, div_le_iff₀ (by positivity)]
  nlinarith [ht, ht', hl9, hl9', hs, hs', hsp, hD, tw_pos hL, mul_pos hD hD,
    sq_nonneg (tw (Real.log 2)), mul_pos (mul_pos hD hD) hD]

theorem chanLevy_2_le (hL : 0 < Real.log 2) :
    (1 / ((2:ℕ) + 1/4 : ℝ)) * (Real.log 2 / 2)
      - Cvs.WeilForm.ChannelFunctionalL2.chanInt (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 2) (Cvs.WeilForm.WindowRepresentative.rep (waveW hL))
    ≤ (51787/1000000 : ℝ) := by
  have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 2 = 9/2 := by rw [Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx]; norm_num
  have hsp : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hinv' : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by field_simp; linarith [hs2]
  rw [chanInt_value hL (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 2) (by rw [hb]; norm_num),
      exp_neg_bIdx_logtwo 2, hb,
      show ((1:ℝ)/4)^2 / Real.sqrt 2 = (1/16:ℝ) * (Real.sqrt 2 / 2) from by
        rw [show ((1:ℝ)/4)^2 = (1/16:ℝ) by norm_num, div_eq_mul_inv, hinv']]
  have ht := tsq_lower
  have ht' := tsq_upper
  have hl9 := Real.log_two_gt_d9
  have hl9' := Real.log_two_lt_d9
  have hs : (1.41421356 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1.41421356:ℝ) = Real.sqrt (1.41421356^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hs' : Real.sqrt 2 ≤ 1.41421357 := by
    rw [show (1.41421357:ℝ) = Real.sqrt (1.41421357^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hD : (0:ℝ) < (9/2:ℝ)^2 + tw (Real.log 2)^2 := by positivity
  rw [show (1:ℝ)/((2:ℕ)+1/4) = (4/9:ℝ) by norm_num]
  have key : (4/9:ℝ) * (Real.log 2/2)
      - ((9/2:ℝ) * Real.log 2 / ((9/2:ℝ)^2 + tw (Real.log 2)^2)
        + 2 * tw (Real.log 2)^2 * (1 + (1/16:ℝ) * (Real.sqrt 2 / 2)) / ((9/2:ℝ)^2 + tw (Real.log 2)^2)^2)
      = ((4/9:ℝ) * (Real.log 2/2) * ((9/2:ℝ)^2 + tw (Real.log 2)^2)^2
          - (9/2:ℝ) * Real.log 2 * ((9/2:ℝ)^2 + tw (Real.log 2)^2)
          - 2 * tw (Real.log 2)^2 * (1 + (1/16:ℝ) * (Real.sqrt 2 / 2)))
        / ((9/2:ℝ)^2 + tw (Real.log 2)^2)^2 := by field_simp; ring
  rw [key, div_le_iff₀ (by positivity)]
  nlinarith [ht, ht', hl9, hl9', hs, hs', hsp, hD, tw_pos hL, mul_pos hD hD,
    sq_nonneg (tw (Real.log 2)), mul_pos (mul_pos hD hD) hD]

theorem chanLevy_3_le (hL : 0 < Real.log 2) :
    (1 / ((3:ℕ) + 1/4 : ℝ)) * (Real.log 2 / 2)
      - Cvs.WeilForm.ChannelFunctionalL2.chanInt (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 3) (Cvs.WeilForm.WindowRepresentative.rep (waveW hL))
    ≤ (761/31250 : ℝ) := by
  have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 3 = 13/2 := by rw [Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx]; norm_num
  have hsp : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hinv' : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by field_simp; linarith [hs2]
  rw [chanInt_value hL (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 3) (by rw [hb]; norm_num),
      exp_neg_bIdx_logtwo 3, hb,
      show ((1:ℝ)/4)^3 / Real.sqrt 2 = (1/64:ℝ) * (Real.sqrt 2 / 2) from by
        rw [show ((1:ℝ)/4)^3 = (1/64:ℝ) by norm_num, div_eq_mul_inv, hinv']]
  have ht := tsq_lower
  have ht' := tsq_upper
  have hl9 := Real.log_two_gt_d9
  have hl9' := Real.log_two_lt_d9
  have hs : (1.41421356 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1.41421356:ℝ) = Real.sqrt (1.41421356^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hs' : Real.sqrt 2 ≤ 1.41421357 := by
    rw [show (1.41421357:ℝ) = Real.sqrt (1.41421357^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hD : (0:ℝ) < (13/2:ℝ)^2 + tw (Real.log 2)^2 := by positivity
  rw [show (1:ℝ)/((3:ℕ)+1/4) = (4/13:ℝ) by norm_num]
  have key : (4/13:ℝ) * (Real.log 2/2)
      - ((13/2:ℝ) * Real.log 2 / ((13/2:ℝ)^2 + tw (Real.log 2)^2)
        + 2 * tw (Real.log 2)^2 * (1 + (1/64:ℝ) * (Real.sqrt 2 / 2)) / ((13/2:ℝ)^2 + tw (Real.log 2)^2)^2)
      = ((4/13:ℝ) * (Real.log 2/2) * ((13/2:ℝ)^2 + tw (Real.log 2)^2)^2
          - (13/2:ℝ) * Real.log 2 * ((13/2:ℝ)^2 + tw (Real.log 2)^2)
          - 2 * tw (Real.log 2)^2 * (1 + (1/64:ℝ) * (Real.sqrt 2 / 2)))
        / ((13/2:ℝ)^2 + tw (Real.log 2)^2)^2 := by field_simp; ring
  rw [key, div_le_iff₀ (by positivity)]
  nlinarith [ht, ht', hl9, hl9', hs, hs', hsp, hD, tw_pos hL, mul_pos hD hD,
    sq_nonneg (tw (Real.log 2)), mul_pos (mul_pos hD hD) hD]

theorem chanLevy_4_le (hL : 0 < Real.log 2) :
    (1 / ((4:ℕ) + 1/4 : ℝ)) * (Real.log 2 / 2)
      - Cvs.WeilForm.ChannelFunctionalL2.chanInt (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 4) (Cvs.WeilForm.WindowRepresentative.rep (waveW hL))
    ≤ (13269/1000000 : ℝ) := by
  have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 4 = 17/2 := by rw [Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx]; norm_num
  have hsp : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hinv' : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by field_simp; linarith [hs2]
  rw [chanInt_value hL (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 4) (by rw [hb]; norm_num),
      exp_neg_bIdx_logtwo 4, hb,
      show ((1:ℝ)/4)^4 / Real.sqrt 2 = (1/256:ℝ) * (Real.sqrt 2 / 2) from by
        rw [show ((1:ℝ)/4)^4 = (1/256:ℝ) by norm_num, div_eq_mul_inv, hinv']]
  have ht := tsq_lower
  have ht' := tsq_upper
  have hl9 := Real.log_two_gt_d9
  have hl9' := Real.log_two_lt_d9
  have hs : (1.41421356 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1.41421356:ℝ) = Real.sqrt (1.41421356^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hs' : Real.sqrt 2 ≤ 1.41421357 := by
    rw [show (1.41421357:ℝ) = Real.sqrt (1.41421357^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hD : (0:ℝ) < (17/2:ℝ)^2 + tw (Real.log 2)^2 := by positivity
  rw [show (1:ℝ)/((4:ℕ)+1/4) = (4/17:ℝ) by norm_num]
  have key : (4/17:ℝ) * (Real.log 2/2)
      - ((17/2:ℝ) * Real.log 2 / ((17/2:ℝ)^2 + tw (Real.log 2)^2)
        + 2 * tw (Real.log 2)^2 * (1 + (1/256:ℝ) * (Real.sqrt 2 / 2)) / ((17/2:ℝ)^2 + tw (Real.log 2)^2)^2)
      = ((4/17:ℝ) * (Real.log 2/2) * ((17/2:ℝ)^2 + tw (Real.log 2)^2)^2
          - (17/2:ℝ) * Real.log 2 * ((17/2:ℝ)^2 + tw (Real.log 2)^2)
          - 2 * tw (Real.log 2)^2 * (1 + (1/256:ℝ) * (Real.sqrt 2 / 2)))
        / ((17/2:ℝ)^2 + tw (Real.log 2)^2)^2 := by field_simp; ring
  rw [key, div_le_iff₀ (by positivity)]
  nlinarith [ht, ht', hl9, hl9', hs, hs', hsp, hD, tw_pos hL, mul_pos hD hD,
    sq_nonneg (tw (Real.log 2)), mul_pos (mul_pos hD hD) hD]

theorem chanLevy_5_le (hL : 0 < Real.log 2) :
    (1 / ((5:ℕ) + 1/4 : ℝ)) * (Real.log 2 / 2)
      - Cvs.WeilForm.ChannelFunctionalL2.chanInt (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 5) (Cvs.WeilForm.WindowRepresentative.rep (waveW hL))
    ≤ (1593/200000 : ℝ) := by
  have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 5 = 21/2 := by rw [Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx]; norm_num
  have hsp : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hinv' : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by field_simp; linarith [hs2]
  rw [chanInt_value hL (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 5) (by rw [hb]; norm_num),
      exp_neg_bIdx_logtwo 5, hb,
      show ((1:ℝ)/4)^5 / Real.sqrt 2 = (1/1024:ℝ) * (Real.sqrt 2 / 2) from by
        rw [show ((1:ℝ)/4)^5 = (1/1024:ℝ) by norm_num, div_eq_mul_inv, hinv']]
  have ht := tsq_lower
  have ht' := tsq_upper
  have hl9 := Real.log_two_gt_d9
  have hl9' := Real.log_two_lt_d9
  have hs : (1.41421356 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1.41421356:ℝ) = Real.sqrt (1.41421356^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hs' : Real.sqrt 2 ≤ 1.41421357 := by
    rw [show (1.41421357:ℝ) = Real.sqrt (1.41421357^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hD : (0:ℝ) < (21/2:ℝ)^2 + tw (Real.log 2)^2 := by positivity
  rw [show (1:ℝ)/((5:ℕ)+1/4) = (4/21:ℝ) by norm_num]
  have key : (4/21:ℝ) * (Real.log 2/2)
      - ((21/2:ℝ) * Real.log 2 / ((21/2:ℝ)^2 + tw (Real.log 2)^2)
        + 2 * tw (Real.log 2)^2 * (1 + (1/1024:ℝ) * (Real.sqrt 2 / 2)) / ((21/2:ℝ)^2 + tw (Real.log 2)^2)^2)
      = ((4/21:ℝ) * (Real.log 2/2) * ((21/2:ℝ)^2 + tw (Real.log 2)^2)^2
          - (21/2:ℝ) * Real.log 2 * ((21/2:ℝ)^2 + tw (Real.log 2)^2)
          - 2 * tw (Real.log 2)^2 * (1 + (1/1024:ℝ) * (Real.sqrt 2 / 2)))
        / ((21/2:ℝ)^2 + tw (Real.log 2)^2)^2 := by field_simp; ring
  rw [key, div_le_iff₀ (by positivity)]
  nlinarith [ht, ht', hl9, hl9', hs, hs', hsp, hD, tw_pos hL, mul_pos hD hD,
    sq_nonneg (tw (Real.log 2)), mul_pos (mul_pos hD hD) hD]

theorem chanLevy_6_le (hL : 0 < Real.log 2) :
    (1 / ((6:ℕ) + 1/4 : ℝ)) * (Real.log 2 / 2)
      - Cvs.WeilForm.ChannelFunctionalL2.chanInt (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 6) (Cvs.WeilForm.WindowRepresentative.rep (waveW hL))
    ≤ (5129/1000000 : ℝ) := by
  have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 6 = 25/2 := by rw [Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx]; norm_num
  have hsp : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hinv' : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by field_simp; linarith [hs2]
  rw [chanInt_value hL (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 6) (by rw [hb]; norm_num),
      exp_neg_bIdx_logtwo 6, hb,
      show ((1:ℝ)/4)^6 / Real.sqrt 2 = (1/4096:ℝ) * (Real.sqrt 2 / 2) from by
        rw [show ((1:ℝ)/4)^6 = (1/4096:ℝ) by norm_num, div_eq_mul_inv, hinv']]
  have ht := tsq_lower
  have ht' := tsq_upper
  have hl9 := Real.log_two_gt_d9
  have hl9' := Real.log_two_lt_d9
  have hs : (1.41421356 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1.41421356:ℝ) = Real.sqrt (1.41421356^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hs' : Real.sqrt 2 ≤ 1.41421357 := by
    rw [show (1.41421357:ℝ) = Real.sqrt (1.41421357^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hD : (0:ℝ) < (25/2:ℝ)^2 + tw (Real.log 2)^2 := by positivity
  rw [show (1:ℝ)/((6:ℕ)+1/4) = (4/25:ℝ) by norm_num]
  have key : (4/25:ℝ) * (Real.log 2/2)
      - ((25/2:ℝ) * Real.log 2 / ((25/2:ℝ)^2 + tw (Real.log 2)^2)
        + 2 * tw (Real.log 2)^2 * (1 + (1/4096:ℝ) * (Real.sqrt 2 / 2)) / ((25/2:ℝ)^2 + tw (Real.log 2)^2)^2)
      = ((4/25:ℝ) * (Real.log 2/2) * ((25/2:ℝ)^2 + tw (Real.log 2)^2)^2
          - (25/2:ℝ) * Real.log 2 * ((25/2:ℝ)^2 + tw (Real.log 2)^2)
          - 2 * tw (Real.log 2)^2 * (1 + (1/4096:ℝ) * (Real.sqrt 2 / 2)))
        / ((25/2:ℝ)^2 + tw (Real.log 2)^2)^2 := by field_simp; ring
  rw [key, div_le_iff₀ (by positivity)]
  nlinarith [ht, ht', hl9, hl9', hs, hs', hsp, hD, tw_pos hL, mul_pos hD hD,
    sq_nonneg (tw (Real.log 2)), mul_pos (mul_pos hD hD) hD]

theorem chanLevy_7_le (hL : 0 < Real.log 2) :
    (1 / ((7:ℕ) + 1/4 : ℝ)) * (Real.log 2 / 2)
      - Cvs.WeilForm.ChannelFunctionalL2.chanInt (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 7) (Cvs.WeilForm.WindowRepresentative.rep (waveW hL))
    ≤ (871/250000 : ℝ) := by
  have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 7 = 29/2 := by rw [Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx]; norm_num
  have hsp : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hinv' : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by field_simp; linarith [hs2]
  rw [chanInt_value hL (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 7) (by rw [hb]; norm_num),
      exp_neg_bIdx_logtwo 7, hb,
      show ((1:ℝ)/4)^7 / Real.sqrt 2 = (1/16384:ℝ) * (Real.sqrt 2 / 2) from by
        rw [show ((1:ℝ)/4)^7 = (1/16384:ℝ) by norm_num, div_eq_mul_inv, hinv']]
  have ht := tsq_lower
  have ht' := tsq_upper
  have hl9 := Real.log_two_gt_d9
  have hl9' := Real.log_two_lt_d9
  have hs : (1.41421356 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1.41421356:ℝ) = Real.sqrt (1.41421356^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hs' : Real.sqrt 2 ≤ 1.41421357 := by
    rw [show (1.41421357:ℝ) = Real.sqrt (1.41421357^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hD : (0:ℝ) < (29/2:ℝ)^2 + tw (Real.log 2)^2 := by positivity
  rw [show (1:ℝ)/((7:ℕ)+1/4) = (4/29:ℝ) by norm_num]
  have key : (4/29:ℝ) * (Real.log 2/2)
      - ((29/2:ℝ) * Real.log 2 / ((29/2:ℝ)^2 + tw (Real.log 2)^2)
        + 2 * tw (Real.log 2)^2 * (1 + (1/16384:ℝ) * (Real.sqrt 2 / 2)) / ((29/2:ℝ)^2 + tw (Real.log 2)^2)^2)
      = ((4/29:ℝ) * (Real.log 2/2) * ((29/2:ℝ)^2 + tw (Real.log 2)^2)^2
          - (29/2:ℝ) * Real.log 2 * ((29/2:ℝ)^2 + tw (Real.log 2)^2)
          - 2 * tw (Real.log 2)^2 * (1 + (1/16384:ℝ) * (Real.sqrt 2 / 2)))
        / ((29/2:ℝ)^2 + tw (Real.log 2)^2)^2 := by field_simp; ring
  rw [key, div_le_iff₀ (by positivity)]
  nlinarith [ht, ht', hl9, hl9', hs, hs', hsp, hD, tw_pos hL, mul_pos hD hD,
    sq_nonneg (tw (Real.log 2)), mul_pos (mul_pos hD hD) hD]

theorem chanLevy_8_le (hL : 0 < Real.log 2) :
    (1 / ((8:ℕ) + 1/4 : ℝ)) * (Real.log 2 / 2)
      - Cvs.WeilForm.ChannelFunctionalL2.chanInt (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 8) (Cvs.WeilForm.WindowRepresentative.rep (waveW hL))
    ≤ (2469/1000000 : ℝ) := by
  have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 8 = 33/2 := by rw [Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx]; norm_num
  have hsp : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hinv' : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by field_simp; linarith [hs2]
  rw [chanInt_value hL (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 8) (by rw [hb]; norm_num),
      exp_neg_bIdx_logtwo 8, hb,
      show ((1:ℝ)/4)^8 / Real.sqrt 2 = (1/65536:ℝ) * (Real.sqrt 2 / 2) from by
        rw [show ((1:ℝ)/4)^8 = (1/65536:ℝ) by norm_num, div_eq_mul_inv, hinv']]
  have ht := tsq_lower
  have ht' := tsq_upper
  have hl9 := Real.log_two_gt_d9
  have hl9' := Real.log_two_lt_d9
  have hs : (1.41421356 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1.41421356:ℝ) = Real.sqrt (1.41421356^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hs' : Real.sqrt 2 ≤ 1.41421357 := by
    rw [show (1.41421357:ℝ) = Real.sqrt (1.41421357^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hD : (0:ℝ) < (33/2:ℝ)^2 + tw (Real.log 2)^2 := by positivity
  rw [show (1:ℝ)/((8:ℕ)+1/4) = (4/33:ℝ) by norm_num]
  have key : (4/33:ℝ) * (Real.log 2/2)
      - ((33/2:ℝ) * Real.log 2 / ((33/2:ℝ)^2 + tw (Real.log 2)^2)
        + 2 * tw (Real.log 2)^2 * (1 + (1/65536:ℝ) * (Real.sqrt 2 / 2)) / ((33/2:ℝ)^2 + tw (Real.log 2)^2)^2)
      = ((4/33:ℝ) * (Real.log 2/2) * ((33/2:ℝ)^2 + tw (Real.log 2)^2)^2
          - (33/2:ℝ) * Real.log 2 * ((33/2:ℝ)^2 + tw (Real.log 2)^2)
          - 2 * tw (Real.log 2)^2 * (1 + (1/65536:ℝ) * (Real.sqrt 2 / 2)))
        / ((33/2:ℝ)^2 + tw (Real.log 2)^2)^2 := by field_simp; ring
  rw [key, div_le_iff₀ (by positivity)]
  nlinarith [ht, ht', hl9, hl9', hs, hs', hsp, hD, tw_pos hL, mul_pos hD hD,
    sq_nonneg (tw (Real.log 2)), mul_pos (mul_pos hD hD) hD]

theorem chanLevy_9_le (hL : 0 < Real.log 2) :
    (1 / ((9:ℕ) + 1/4 : ℝ)) * (Real.log 2 / 2)
      - Cvs.WeilForm.ChannelFunctionalL2.chanInt (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 9) (Cvs.WeilForm.WindowRepresentative.rep (waveW hL))
    ≤ (181/100000 : ℝ) := by
  have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 9 = 37/2 := by rw [Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx]; norm_num
  have hsp : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hinv' : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by field_simp; linarith [hs2]
  rw [chanInt_value hL (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 9) (by rw [hb]; norm_num),
      exp_neg_bIdx_logtwo 9, hb,
      show ((1:ℝ)/4)^9 / Real.sqrt 2 = (1/262144:ℝ) * (Real.sqrt 2 / 2) from by
        rw [show ((1:ℝ)/4)^9 = (1/262144:ℝ) by norm_num, div_eq_mul_inv, hinv']]
  have ht := tsq_lower
  have ht' := tsq_upper
  have hl9 := Real.log_two_gt_d9
  have hl9' := Real.log_two_lt_d9
  have hs : (1.41421356 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1.41421356:ℝ) = Real.sqrt (1.41421356^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hs' : Real.sqrt 2 ≤ 1.41421357 := by
    rw [show (1.41421357:ℝ) = Real.sqrt (1.41421357^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hD : (0:ℝ) < (37/2:ℝ)^2 + tw (Real.log 2)^2 := by positivity
  rw [show (1:ℝ)/((9:ℕ)+1/4) = (4/37:ℝ) by norm_num]
  have key : (4/37:ℝ) * (Real.log 2/2)
      - ((37/2:ℝ) * Real.log 2 / ((37/2:ℝ)^2 + tw (Real.log 2)^2)
        + 2 * tw (Real.log 2)^2 * (1 + (1/262144:ℝ) * (Real.sqrt 2 / 2)) / ((37/2:ℝ)^2 + tw (Real.log 2)^2)^2)
      = ((4/37:ℝ) * (Real.log 2/2) * ((37/2:ℝ)^2 + tw (Real.log 2)^2)^2
          - (37/2:ℝ) * Real.log 2 * ((37/2:ℝ)^2 + tw (Real.log 2)^2)
          - 2 * tw (Real.log 2)^2 * (1 + (1/262144:ℝ) * (Real.sqrt 2 / 2)))
        / ((37/2:ℝ)^2 + tw (Real.log 2)^2)^2 := by field_simp; ring
  rw [key, div_le_iff₀ (by positivity)]
  nlinarith [ht, ht', hl9, hl9', hs, hs', hsp, hD, tw_pos hL, mul_pos hD hD,
    sq_nonneg (tw (Real.log 2)), mul_pos (mul_pos hD hD) hD]

theorem chanLevy_10_le (hL : 0 < Real.log 2) :
    (1 / ((10:ℕ) + 1/4 : ℝ)) * (Real.log 2 / 2)
      - Cvs.WeilForm.ChannelFunctionalL2.chanInt (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 10) (Cvs.WeilForm.WindowRepresentative.rep (waveW hL))
    ≤ (273/200000 : ℝ) := by
  have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 10 = 41/2 := by rw [Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx]; norm_num
  have hsp : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hinv' : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by field_simp; linarith [hs2]
  rw [chanInt_value hL (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 10) (by rw [hb]; norm_num),
      exp_neg_bIdx_logtwo 10, hb,
      show ((1:ℝ)/4)^10 / Real.sqrt 2 = (1/1048576:ℝ) * (Real.sqrt 2 / 2) from by
        rw [show ((1:ℝ)/4)^10 = (1/1048576:ℝ) by norm_num, div_eq_mul_inv, hinv']]
  have ht := tsq_lower
  have ht' := tsq_upper
  have hl9 := Real.log_two_gt_d9
  have hl9' := Real.log_two_lt_d9
  have hs : (1.41421356 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1.41421356:ℝ) = Real.sqrt (1.41421356^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hs' : Real.sqrt 2 ≤ 1.41421357 := by
    rw [show (1.41421357:ℝ) = Real.sqrt (1.41421357^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hD : (0:ℝ) < (41/2:ℝ)^2 + tw (Real.log 2)^2 := by positivity
  rw [show (1:ℝ)/((10:ℕ)+1/4) = (4/41:ℝ) by norm_num]
  have key : (4/41:ℝ) * (Real.log 2/2)
      - ((41/2:ℝ) * Real.log 2 / ((41/2:ℝ)^2 + tw (Real.log 2)^2)
        + 2 * tw (Real.log 2)^2 * (1 + (1/1048576:ℝ) * (Real.sqrt 2 / 2)) / ((41/2:ℝ)^2 + tw (Real.log 2)^2)^2)
      = ((4/41:ℝ) * (Real.log 2/2) * ((41/2:ℝ)^2 + tw (Real.log 2)^2)^2
          - (41/2:ℝ) * Real.log 2 * ((41/2:ℝ)^2 + tw (Real.log 2)^2)
          - 2 * tw (Real.log 2)^2 * (1 + (1/1048576:ℝ) * (Real.sqrt 2 / 2)))
        / ((41/2:ℝ)^2 + tw (Real.log 2)^2)^2 := by field_simp; ring
  rw [key, div_le_iff₀ (by positivity)]
  nlinarith [ht, ht', hl9, hl9', hs, hs', hsp, hD, tw_pos hL, mul_pos hD hD,
    sq_nonneg (tw (Real.log 2)), mul_pos (mul_pos hD hD) hD]

theorem chanLevy_11_le (hL : 0 < Real.log 2) :
    (1 / ((11:ℕ) + 1/4 : ℝ)) * (Real.log 2 / 2)
      - Cvs.WeilForm.ChannelFunctionalL2.chanInt (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 11) (Cvs.WeilForm.WindowRepresentative.rep (waveW hL))
    ≤ (527/500000 : ℝ) := by
  have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 11 = 45/2 := by rw [Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx]; norm_num
  have hsp : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hinv' : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by field_simp; linarith [hs2]
  rw [chanInt_value hL (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 11) (by rw [hb]; norm_num),
      exp_neg_bIdx_logtwo 11, hb,
      show ((1:ℝ)/4)^11 / Real.sqrt 2 = (1/4194304:ℝ) * (Real.sqrt 2 / 2) from by
        rw [show ((1:ℝ)/4)^11 = (1/4194304:ℝ) by norm_num, div_eq_mul_inv, hinv']]
  have ht := tsq_lower
  have ht' := tsq_upper
  have hl9 := Real.log_two_gt_d9
  have hl9' := Real.log_two_lt_d9
  have hs : (1.41421356 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1.41421356:ℝ) = Real.sqrt (1.41421356^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hs' : Real.sqrt 2 ≤ 1.41421357 := by
    rw [show (1.41421357:ℝ) = Real.sqrt (1.41421357^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hD : (0:ℝ) < (45/2:ℝ)^2 + tw (Real.log 2)^2 := by positivity
  rw [show (1:ℝ)/((11:ℕ)+1/4) = (4/45:ℝ) by norm_num]
  have key : (4/45:ℝ) * (Real.log 2/2)
      - ((45/2:ℝ) * Real.log 2 / ((45/2:ℝ)^2 + tw (Real.log 2)^2)
        + 2 * tw (Real.log 2)^2 * (1 + (1/4194304:ℝ) * (Real.sqrt 2 / 2)) / ((45/2:ℝ)^2 + tw (Real.log 2)^2)^2)
      = ((4/45:ℝ) * (Real.log 2/2) * ((45/2:ℝ)^2 + tw (Real.log 2)^2)^2
          - (45/2:ℝ) * Real.log 2 * ((45/2:ℝ)^2 + tw (Real.log 2)^2)
          - 2 * tw (Real.log 2)^2 * (1 + (1/4194304:ℝ) * (Real.sqrt 2 / 2)))
        / ((45/2:ℝ)^2 + tw (Real.log 2)^2)^2 := by field_simp; ring
  rw [key, div_le_iff₀ (by positivity)]
  nlinarith [ht, ht', hl9, hl9', hs, hs', hsp, hD, tw_pos hL, mul_pos hD hD,
    sq_nonneg (tw (Real.log 2)), mul_pos (mul_pos hD hD) hD]

theorem chanLevy_12_le (hL : 0 < Real.log 2) :
    (1 / ((12:ℕ) + 1/4 : ℝ)) * (Real.log 2 / 2)
      - Cvs.WeilForm.ChannelFunctionalL2.chanInt (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 12) (Cvs.WeilForm.WindowRepresentative.rep (waveW hL))
    ≤ (83/100000 : ℝ) := by
  have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 12 = 49/2 := by rw [Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx]; norm_num
  have hsp : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hinv' : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by field_simp; linarith [hs2]
  rw [chanInt_value hL (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 12) (by rw [hb]; norm_num),
      exp_neg_bIdx_logtwo 12, hb,
      show ((1:ℝ)/4)^12 / Real.sqrt 2 = (1/16777216:ℝ) * (Real.sqrt 2 / 2) from by
        rw [show ((1:ℝ)/4)^12 = (1/16777216:ℝ) by norm_num, div_eq_mul_inv, hinv']]
  have ht := tsq_lower
  have ht' := tsq_upper
  have hl9 := Real.log_two_gt_d9
  have hl9' := Real.log_two_lt_d9
  have hs : (1.41421356 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1.41421356:ℝ) = Real.sqrt (1.41421356^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hs' : Real.sqrt 2 ≤ 1.41421357 := by
    rw [show (1.41421357:ℝ) = Real.sqrt (1.41421357^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hD : (0:ℝ) < (49/2:ℝ)^2 + tw (Real.log 2)^2 := by positivity
  rw [show (1:ℝ)/((12:ℕ)+1/4) = (4/49:ℝ) by norm_num]
  have key : (4/49:ℝ) * (Real.log 2/2)
      - ((49/2:ℝ) * Real.log 2 / ((49/2:ℝ)^2 + tw (Real.log 2)^2)
        + 2 * tw (Real.log 2)^2 * (1 + (1/16777216:ℝ) * (Real.sqrt 2 / 2)) / ((49/2:ℝ)^2 + tw (Real.log 2)^2)^2)
      = ((4/49:ℝ) * (Real.log 2/2) * ((49/2:ℝ)^2 + tw (Real.log 2)^2)^2
          - (49/2:ℝ) * Real.log 2 * ((49/2:ℝ)^2 + tw (Real.log 2)^2)
          - 2 * tw (Real.log 2)^2 * (1 + (1/16777216:ℝ) * (Real.sqrt 2 / 2)))
        / ((49/2:ℝ)^2 + tw (Real.log 2)^2)^2 := by field_simp; ring
  rw [key, div_le_iff₀ (by positivity)]
  nlinarith [ht, ht', hl9, hl9', hs, hs', hsp, hD, tw_pos hL, mul_pos hD hD,
    sq_nonneg (tw (Real.log 2)), mul_pos (mul_pos hD hD) hD]

theorem chanLevy_13_le (hL : 0 < Real.log 2) :
    (1 / ((13:ℕ) + 1/4 : ℝ)) * (Real.log 2 / 2)
      - Cvs.WeilForm.ChannelFunctionalL2.chanInt (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 13) (Cvs.WeilForm.WindowRepresentative.rep (waveW hL))
    ≤ (133/200000 : ℝ) := by
  have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 13 = 53/2 := by rw [Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx]; norm_num
  have hsp : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hinv' : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by field_simp; linarith [hs2]
  rw [chanInt_value hL (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 13) (by rw [hb]; norm_num),
      exp_neg_bIdx_logtwo 13, hb,
      show ((1:ℝ)/4)^13 / Real.sqrt 2 = (1/67108864:ℝ) * (Real.sqrt 2 / 2) from by
        rw [show ((1:ℝ)/4)^13 = (1/67108864:ℝ) by norm_num, div_eq_mul_inv, hinv']]
  have ht := tsq_lower
  have ht' := tsq_upper
  have hl9 := Real.log_two_gt_d9
  have hl9' := Real.log_two_lt_d9
  have hs : (1.41421356 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1.41421356:ℝ) = Real.sqrt (1.41421356^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hs' : Real.sqrt 2 ≤ 1.41421357 := by
    rw [show (1.41421357:ℝ) = Real.sqrt (1.41421357^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hD : (0:ℝ) < (53/2:ℝ)^2 + tw (Real.log 2)^2 := by positivity
  rw [show (1:ℝ)/((13:ℕ)+1/4) = (4/53:ℝ) by norm_num]
  have key : (4/53:ℝ) * (Real.log 2/2)
      - ((53/2:ℝ) * Real.log 2 / ((53/2:ℝ)^2 + tw (Real.log 2)^2)
        + 2 * tw (Real.log 2)^2 * (1 + (1/67108864:ℝ) * (Real.sqrt 2 / 2)) / ((53/2:ℝ)^2 + tw (Real.log 2)^2)^2)
      = ((4/53:ℝ) * (Real.log 2/2) * ((53/2:ℝ)^2 + tw (Real.log 2)^2)^2
          - (53/2:ℝ) * Real.log 2 * ((53/2:ℝ)^2 + tw (Real.log 2)^2)
          - 2 * tw (Real.log 2)^2 * (1 + (1/67108864:ℝ) * (Real.sqrt 2 / 2)))
        / ((53/2:ℝ)^2 + tw (Real.log 2)^2)^2 := by field_simp; ring
  rw [key, div_le_iff₀ (by positivity)]
  nlinarith [ht, ht', hl9, hl9', hs, hs', hsp, hD, tw_pos hL, mul_pos hD hD,
    sq_nonneg (tw (Real.log 2)), mul_pos (mul_pos hD hD) hD]

theorem chanLevy_14_le (hL : 0 < Real.log 2) :
    (1 / ((14:ℕ) + 1/4 : ℝ)) * (Real.log 2 / 2)
      - Cvs.WeilForm.ChannelFunctionalL2.chanInt (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 14) (Cvs.WeilForm.WindowRepresentative.rep (waveW hL))
    ≤ (541/1000000 : ℝ) := by
  have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 14 = 57/2 := by rw [Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx]; norm_num
  have hsp : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hinv' : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by field_simp; linarith [hs2]
  rw [chanInt_value hL (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 14) (by rw [hb]; norm_num),
      exp_neg_bIdx_logtwo 14, hb,
      show ((1:ℝ)/4)^14 / Real.sqrt 2 = (1/268435456:ℝ) * (Real.sqrt 2 / 2) from by
        rw [show ((1:ℝ)/4)^14 = (1/268435456:ℝ) by norm_num, div_eq_mul_inv, hinv']]
  have ht := tsq_lower
  have ht' := tsq_upper
  have hl9 := Real.log_two_gt_d9
  have hl9' := Real.log_two_lt_d9
  have hs : (1.41421356 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1.41421356:ℝ) = Real.sqrt (1.41421356^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hs' : Real.sqrt 2 ≤ 1.41421357 := by
    rw [show (1.41421357:ℝ) = Real.sqrt (1.41421357^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hD : (0:ℝ) < (57/2:ℝ)^2 + tw (Real.log 2)^2 := by positivity
  rw [show (1:ℝ)/((14:ℕ)+1/4) = (4/57:ℝ) by norm_num]
  have key : (4/57:ℝ) * (Real.log 2/2)
      - ((57/2:ℝ) * Real.log 2 / ((57/2:ℝ)^2 + tw (Real.log 2)^2)
        + 2 * tw (Real.log 2)^2 * (1 + (1/268435456:ℝ) * (Real.sqrt 2 / 2)) / ((57/2:ℝ)^2 + tw (Real.log 2)^2)^2)
      = ((4/57:ℝ) * (Real.log 2/2) * ((57/2:ℝ)^2 + tw (Real.log 2)^2)^2
          - (57/2:ℝ) * Real.log 2 * ((57/2:ℝ)^2 + tw (Real.log 2)^2)
          - 2 * tw (Real.log 2)^2 * (1 + (1/268435456:ℝ) * (Real.sqrt 2 / 2)))
        / ((57/2:ℝ)^2 + tw (Real.log 2)^2)^2 := by field_simp; ring
  rw [key, div_le_iff₀ (by positivity)]
  nlinarith [ht, ht', hl9, hl9', hs, hs', hsp, hD, tw_pos hL, mul_pos hD hD,
    sq_nonneg (tw (Real.log 2)), mul_pos (mul_pos hD hD) hD]

theorem chanLevy_15_le (hL : 0 < Real.log 2) :
    (1 / ((15:ℕ) + 1/4 : ℝ)) * (Real.log 2 / 2)
      - Cvs.WeilForm.ChannelFunctionalL2.chanInt (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 15) (Cvs.WeilForm.WindowRepresentative.rep (waveW hL))
    ≤ (223/500000 : ℝ) := by
  have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 15 = 61/2 := by rw [Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx]; norm_num
  have hsp : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hinv' : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by field_simp; linarith [hs2]
  rw [chanInt_value hL (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 15) (by rw [hb]; norm_num),
      exp_neg_bIdx_logtwo 15, hb,
      show ((1:ℝ)/4)^15 / Real.sqrt 2 = (1/1073741824:ℝ) * (Real.sqrt 2 / 2) from by
        rw [show ((1:ℝ)/4)^15 = (1/1073741824:ℝ) by norm_num, div_eq_mul_inv, hinv']]
  have ht := tsq_lower
  have ht' := tsq_upper
  have hl9 := Real.log_two_gt_d9
  have hl9' := Real.log_two_lt_d9
  have hs : (1.41421356 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1.41421356:ℝ) = Real.sqrt (1.41421356^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hs' : Real.sqrt 2 ≤ 1.41421357 := by
    rw [show (1.41421357:ℝ) = Real.sqrt (1.41421357^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hD : (0:ℝ) < (61/2:ℝ)^2 + tw (Real.log 2)^2 := by positivity
  rw [show (1:ℝ)/((15:ℕ)+1/4) = (4/61:ℝ) by norm_num]
  have key : (4/61:ℝ) * (Real.log 2/2)
      - ((61/2:ℝ) * Real.log 2 / ((61/2:ℝ)^2 + tw (Real.log 2)^2)
        + 2 * tw (Real.log 2)^2 * (1 + (1/1073741824:ℝ) * (Real.sqrt 2 / 2)) / ((61/2:ℝ)^2 + tw (Real.log 2)^2)^2)
      = ((4/61:ℝ) * (Real.log 2/2) * ((61/2:ℝ)^2 + tw (Real.log 2)^2)^2
          - (61/2:ℝ) * Real.log 2 * ((61/2:ℝ)^2 + tw (Real.log 2)^2)
          - 2 * tw (Real.log 2)^2 * (1 + (1/1073741824:ℝ) * (Real.sqrt 2 / 2)))
        / ((61/2:ℝ)^2 + tw (Real.log 2)^2)^2 := by field_simp; ring
  rw [key, div_le_iff₀ (by positivity)]
  nlinarith [ht, ht', hl9, hl9', hs, hs', hsp, hD, tw_pos hL, mul_pos hD hD,
    sq_nonneg (tw (Real.log 2)), mul_pos (mul_pos hD hD) hD]

theorem chanLevy_16_le (hL : 0 < Real.log 2) :
    (1 / ((16:ℕ) + 1/4 : ℝ)) * (Real.log 2 / 2)
      - Cvs.WeilForm.ChannelFunctionalL2.chanInt (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 16) (Cvs.WeilForm.WindowRepresentative.rep (waveW hL))
    ≤ (93/250000 : ℝ) := by
  have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 16 = 65/2 := by rw [Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx]; norm_num
  have hsp : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hinv' : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by field_simp; linarith [hs2]
  rw [chanInt_value hL (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 16) (by rw [hb]; norm_num),
      exp_neg_bIdx_logtwo 16, hb,
      show ((1:ℝ)/4)^16 / Real.sqrt 2 = (1/4294967296:ℝ) * (Real.sqrt 2 / 2) from by
        rw [show ((1:ℝ)/4)^16 = (1/4294967296:ℝ) by norm_num, div_eq_mul_inv, hinv']]
  have ht := tsq_lower
  have ht' := tsq_upper
  have hl9 := Real.log_two_gt_d9
  have hl9' := Real.log_two_lt_d9
  have hs : (1.41421356 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1.41421356:ℝ) = Real.sqrt (1.41421356^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hs' : Real.sqrt 2 ≤ 1.41421357 := by
    rw [show (1.41421357:ℝ) = Real.sqrt (1.41421357^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hD : (0:ℝ) < (65/2:ℝ)^2 + tw (Real.log 2)^2 := by positivity
  rw [show (1:ℝ)/((16:ℕ)+1/4) = (4/65:ℝ) by norm_num]
  have key : (4/65:ℝ) * (Real.log 2/2)
      - ((65/2:ℝ) * Real.log 2 / ((65/2:ℝ)^2 + tw (Real.log 2)^2)
        + 2 * tw (Real.log 2)^2 * (1 + (1/4294967296:ℝ) * (Real.sqrt 2 / 2)) / ((65/2:ℝ)^2 + tw (Real.log 2)^2)^2)
      = ((4/65:ℝ) * (Real.log 2/2) * ((65/2:ℝ)^2 + tw (Real.log 2)^2)^2
          - (65/2:ℝ) * Real.log 2 * ((65/2:ℝ)^2 + tw (Real.log 2)^2)
          - 2 * tw (Real.log 2)^2 * (1 + (1/4294967296:ℝ) * (Real.sqrt 2 / 2)))
        / ((65/2:ℝ)^2 + tw (Real.log 2)^2)^2 := by field_simp; ring
  rw [key, div_le_iff₀ (by positivity)]
  nlinarith [ht, ht', hl9, hl9', hs, hs', hsp, hD, tw_pos hL, mul_pos hD hD,
    sq_nonneg (tw (Real.log 2)), mul_pos (mul_pos hD hD) hD]

theorem chanLevy_17_le (hL : 0 < Real.log 2) :
    (1 / ((17:ℕ) + 1/4 : ℝ)) * (Real.log 2 / 2)
      - Cvs.WeilForm.ChannelFunctionalL2.chanInt (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 17) (Cvs.WeilForm.WindowRepresentative.rep (waveW hL))
    ≤ (313/1000000 : ℝ) := by
  have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 17 = 69/2 := by rw [Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx]; norm_num
  have hsp : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hinv' : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by field_simp; linarith [hs2]
  rw [chanInt_value hL (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 17) (by rw [hb]; norm_num),
      exp_neg_bIdx_logtwo 17, hb,
      show ((1:ℝ)/4)^17 / Real.sqrt 2 = (1/17179869184:ℝ) * (Real.sqrt 2 / 2) from by
        rw [show ((1:ℝ)/4)^17 = (1/17179869184:ℝ) by norm_num, div_eq_mul_inv, hinv']]
  have ht := tsq_lower
  have ht' := tsq_upper
  have hl9 := Real.log_two_gt_d9
  have hl9' := Real.log_two_lt_d9
  have hs : (1.41421356 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1.41421356:ℝ) = Real.sqrt (1.41421356^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hs' : Real.sqrt 2 ≤ 1.41421357 := by
    rw [show (1.41421357:ℝ) = Real.sqrt (1.41421357^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hD : (0:ℝ) < (69/2:ℝ)^2 + tw (Real.log 2)^2 := by positivity
  rw [show (1:ℝ)/((17:ℕ)+1/4) = (4/69:ℝ) by norm_num]
  have key : (4/69:ℝ) * (Real.log 2/2)
      - ((69/2:ℝ) * Real.log 2 / ((69/2:ℝ)^2 + tw (Real.log 2)^2)
        + 2 * tw (Real.log 2)^2 * (1 + (1/17179869184:ℝ) * (Real.sqrt 2 / 2)) / ((69/2:ℝ)^2 + tw (Real.log 2)^2)^2)
      = ((4/69:ℝ) * (Real.log 2/2) * ((69/2:ℝ)^2 + tw (Real.log 2)^2)^2
          - (69/2:ℝ) * Real.log 2 * ((69/2:ℝ)^2 + tw (Real.log 2)^2)
          - 2 * tw (Real.log 2)^2 * (1 + (1/17179869184:ℝ) * (Real.sqrt 2 / 2)))
        / ((69/2:ℝ)^2 + tw (Real.log 2)^2)^2 := by field_simp; ring
  rw [key, div_le_iff₀ (by positivity)]
  nlinarith [ht, ht', hl9, hl9', hs, hs', hsp, hD, tw_pos hL, mul_pos hD hD,
    sq_nonneg (tw (Real.log 2)), mul_pos (mul_pos hD hD) hD]

theorem chanLevy_18_le (hL : 0 < Real.log 2) :
    (1 / ((18:ℕ) + 1/4 : ℝ)) * (Real.log 2 / 2)
      - Cvs.WeilForm.ChannelFunctionalL2.chanInt (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 18) (Cvs.WeilForm.WindowRepresentative.rep (waveW hL))
    ≤ (133/500000 : ℝ) := by
  have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 18 = 73/2 := by rw [Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx]; norm_num
  have hsp : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hinv' : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by field_simp; linarith [hs2]
  rw [chanInt_value hL (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 18) (by rw [hb]; norm_num),
      exp_neg_bIdx_logtwo 18, hb,
      show ((1:ℝ)/4)^18 / Real.sqrt 2 = (1/68719476736:ℝ) * (Real.sqrt 2 / 2) from by
        rw [show ((1:ℝ)/4)^18 = (1/68719476736:ℝ) by norm_num, div_eq_mul_inv, hinv']]
  have ht := tsq_lower
  have ht' := tsq_upper
  have hl9 := Real.log_two_gt_d9
  have hl9' := Real.log_two_lt_d9
  have hs : (1.41421356 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1.41421356:ℝ) = Real.sqrt (1.41421356^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hs' : Real.sqrt 2 ≤ 1.41421357 := by
    rw [show (1.41421357:ℝ) = Real.sqrt (1.41421357^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hD : (0:ℝ) < (73/2:ℝ)^2 + tw (Real.log 2)^2 := by positivity
  rw [show (1:ℝ)/((18:ℕ)+1/4) = (4/73:ℝ) by norm_num]
  have key : (4/73:ℝ) * (Real.log 2/2)
      - ((73/2:ℝ) * Real.log 2 / ((73/2:ℝ)^2 + tw (Real.log 2)^2)
        + 2 * tw (Real.log 2)^2 * (1 + (1/68719476736:ℝ) * (Real.sqrt 2 / 2)) / ((73/2:ℝ)^2 + tw (Real.log 2)^2)^2)
      = ((4/73:ℝ) * (Real.log 2/2) * ((73/2:ℝ)^2 + tw (Real.log 2)^2)^2
          - (73/2:ℝ) * Real.log 2 * ((73/2:ℝ)^2 + tw (Real.log 2)^2)
          - 2 * tw (Real.log 2)^2 * (1 + (1/68719476736:ℝ) * (Real.sqrt 2 / 2)))
        / ((73/2:ℝ)^2 + tw (Real.log 2)^2)^2 := by field_simp; ring
  rw [key, div_le_iff₀ (by positivity)]
  nlinarith [ht, ht', hl9, hl9', hs, hs', hsp, hD, tw_pos hL, mul_pos hD hD,
    sq_nonneg (tw (Real.log 2)), mul_pos (mul_pos hD hD) hD]

theorem chanLevy_19_le (hL : 0 < Real.log 2) :
    (1 / ((19:ℕ) + 1/4 : ℝ)) * (Real.log 2 / 2)
      - Cvs.WeilForm.ChannelFunctionalL2.chanInt (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 19) (Cvs.WeilForm.WindowRepresentative.rep (waveW hL))
    ≤ (57/250000 : ℝ) := by
  have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 19 = 77/2 := by rw [Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx]; norm_num
  have hsp : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hinv' : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by field_simp; linarith [hs2]
  rw [chanInt_value hL (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 19) (by rw [hb]; norm_num),
      exp_neg_bIdx_logtwo 19, hb,
      show ((1:ℝ)/4)^19 / Real.sqrt 2 = (1/274877906944:ℝ) * (Real.sqrt 2 / 2) from by
        rw [show ((1:ℝ)/4)^19 = (1/274877906944:ℝ) by norm_num, div_eq_mul_inv, hinv']]
  have ht := tsq_lower
  have ht' := tsq_upper
  have hl9 := Real.log_two_gt_d9
  have hl9' := Real.log_two_lt_d9
  have hs : (1.41421356 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1.41421356:ℝ) = Real.sqrt (1.41421356^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hs' : Real.sqrt 2 ≤ 1.41421357 := by
    rw [show (1.41421357:ℝ) = Real.sqrt (1.41421357^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hD : (0:ℝ) < (77/2:ℝ)^2 + tw (Real.log 2)^2 := by positivity
  rw [show (1:ℝ)/((19:ℕ)+1/4) = (4/77:ℝ) by norm_num]
  have key : (4/77:ℝ) * (Real.log 2/2)
      - ((77/2:ℝ) * Real.log 2 / ((77/2:ℝ)^2 + tw (Real.log 2)^2)
        + 2 * tw (Real.log 2)^2 * (1 + (1/274877906944:ℝ) * (Real.sqrt 2 / 2)) / ((77/2:ℝ)^2 + tw (Real.log 2)^2)^2)
      = ((4/77:ℝ) * (Real.log 2/2) * ((77/2:ℝ)^2 + tw (Real.log 2)^2)^2
          - (77/2:ℝ) * Real.log 2 * ((77/2:ℝ)^2 + tw (Real.log 2)^2)
          - 2 * tw (Real.log 2)^2 * (1 + (1/274877906944:ℝ) * (Real.sqrt 2 / 2)))
        / ((77/2:ℝ)^2 + tw (Real.log 2)^2)^2 := by field_simp; ring
  rw [key, div_le_iff₀ (by positivity)]
  nlinarith [ht, ht', hl9, hl9', hs, hs', hsp, hD, tw_pos hL, mul_pos hD hD,
    sq_nonneg (tw (Real.log 2)), mul_pos (mul_pos hD hD) hD]

/-- **The first twenty channel-Lévy terms sum below `1.468969`.** -/
theorem sum_chanLevy_le (hL : 0 < Real.log 2) :
    (∑ k ∈ Finset.range 20, ((1 / ((k : ℝ) + 1 / 4)) * (Real.log 2 / 2)
        - Cvs.WeilForm.ChannelFunctionalL2.chanInt (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k)
            (Cvs.WeilForm.WindowRepresentative.rep (waveW hL)))) ≤ 1468969 / 1000000 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have h0 := chanLevy_0_le hL; have h1 := chanLevy_1_le hL; have h2 := chanLevy_2_le hL
  have h3 := chanLevy_3_le hL; have h4 := chanLevy_4_le hL; have h5 := chanLevy_5_le hL
  have h6 := chanLevy_6_le hL; have h7 := chanLevy_7_le hL; have h8 := chanLevy_8_le hL
  have h9 := chanLevy_9_le hL; have h10 := chanLevy_10_le hL; have h11 := chanLevy_11_le hL
  have h12 := chanLevy_12_le hL; have h13 := chanLevy_13_le hL; have h14 := chanLevy_14_le hL
  have h15 := chanLevy_15_le hL; have h16 := chanLevy_16_le hL; have h17 := chanLevy_17_le hL
  have h18 := chanLevy_18_le hL; have h19 := chanLevy_19_le hL
  norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 ⊢
  linarith

/-- **The trial's Weil form, decomposed** (prime side `0` at `x = 2`). -/
theorem weilQW_decomp (hL : 0 < Real.log 2) :
    Cvs.WeilForm.WindowRepresentative.weilQW 2 1 (waveW hL)
      = 2 * (∫ x : ℝ, Cvs.WeilForm.WindowRepresentative.rep (waveW hL) x * Real.exp (x / 2))
            * (∫ x : ℝ, Cvs.WeilForm.WindowRepresentative.rep (waveW hL) x * Real.exp (-(x / 2)))
        + (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * selfConvolution (Cvs.WeilForm.WindowRepresentative.rep (waveW hL)) 0
          + ∫ u in Set.Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u
              * (selfConvolution (Cvs.WeilForm.WindowRepresentative.rep (waveW hL)) 0
                - selfConvolution (Cvs.WeilForm.WindowRepresentative.rep (waveW hL)) (u / 2))) := by
  rw [(Cvs.WeilForm.WindowRepresentative.weilQW_rep 2 1 (waveW hL)).1, Cvs.WeilForm.SelfConvolutionFunctional.weilForm_eq,
    Cvs.WeilForm.PrimeSideVanishesLogTwo.primeSide_eq_zero (waveW hL), sub_zero]

/-- **A crude per-channel bound**, dropping the nonnegative edge term. -/
theorem chanLevy_crude (hL : 0 < Real.log 2) (k : ℕ) :
    (1 / ((k : ℝ) + 1 / 4)) * (Real.log 2 / 2)
      - Cvs.WeilForm.ChannelFunctionalL2.chanInt (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k) (Cvs.WeilForm.WindowRepresentative.rep (waveW hL))
    ≤ Real.log 2 * tw (Real.log 2)^2 / (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k)^3 := by
  have hbpos : (0:ℝ) < Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k := by rw [Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx]; positivity
  rw [chanInt_value hL (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k) hbpos]
  have htpos : (0:ℝ) < tw (Real.log 2)^2 := pow_pos (tw_pos hL) 2
  have hbt : (0:ℝ) < (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k)^2 + tw (Real.log 2)^2 := by positivity
  have hinvb : (1:ℝ) / ((k:ℝ) + 1/4) * (Real.log 2 / 2) = Real.log 2 / Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k := by
    rw [Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx]; field_simp; ring
  rw [hinvb]
  have hedge : (0:ℝ) ≤ 2 * tw (Real.log 2)^2 * (1 + Real.exp (-(Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k) * Real.log 2))
      / ((Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k)^2 + tw (Real.log 2)^2)^2 := by positivity
  have hmain : Real.log 2 / Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k
      - Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k * Real.log 2 / ((Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k)^2 + tw (Real.log 2)^2)
      ≤ Real.log 2 * tw (Real.log 2)^2 / (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k)^3 := by
    have key : Real.log 2 / Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k
        - Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k * Real.log 2 / ((Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k)^2 + tw (Real.log 2)^2)
        = (Real.log 2 * tw (Real.log 2)^2) / (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k * ((Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k)^2 + tw (Real.log 2)^2)) := by
      field_simp; ring
    rw [key]
    gcongr
    nlinarith [hbpos, htpos, sq_nonneg (tw (Real.log 2))]
  linarith [hmain, hedge]

/-- **The partial channel sums converge to the full Lévy integral**, by dominated convergence. -/
theorem fullLevy_tendsto (hL : 0 < Real.log 2) :
    Filter.Tendsto (fun N => ∑ k ∈ Finset.range N, ((1 / ((k : ℝ) + 1 / 4)) * (Real.log 2 / 2)
        - Cvs.WeilForm.ChannelFunctionalL2.chanInt (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k)
            (Cvs.WeilForm.WindowRepresentative.rep (waveW hL)))) Filter.atTop
      (nhds (∫ u in Set.Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u
        * (selfConvolution (Cvs.WeilForm.WindowRepresentative.rep (waveW hL)) 0
          - selfConvolution (Cvs.WeilForm.WindowRepresentative.rep (waveW hL)) (u / 2)))) := by
  set g := Cvs.WeilForm.WindowRepresentative.rep (waveW hL) with hg
  set d : ℝ → ℝ := fun u => selfConvolution g 0 - selfConvolution g (u / 2) with hd
  have hpe : (fun N => ∑ k ∈ Finset.range N, ((1 / ((k : ℝ) + 1 / 4)) * (Real.log 2 / 2)
        - Cvs.WeilForm.ChannelFunctionalL2.chanInt (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k) g))
      = fun N => ∫ u in Set.Ioi (0:ℝ), Cvs.WeilForm.Archimedean.TruncatedLevyDensityBelow.densityTrunc N u * d u := by
    funext N; rw [← partialLevy_eq hL N]
  rw [hpe]
  have hcont_sc : Continuous (fun u : ℝ => selfConvolution g (u / 2)) :=
    (Cvs.WeilForm.SelfConvolutionContinuous.continuous_selfConvolution (Cvs.WeilForm.WindowRepresentative.memLp_rep _)).comp
      (continuous_id.div_const 2)
  have hbound : MeasureTheory.IntegrableOn (fun u => Cvs.WeilForm.Archimedean.LevyDensity.densityU u * d u) (Set.Ioi 0) volume := by
    have := integrableOn_levy_waveW hL; unfold Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy at this; exact this
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun u => Cvs.WeilForm.Archimedean.LevyDensity.densityU u * d u) ?_ hbound ?_ ?_
  · intro N
    refine (Continuous.aestronglyMeasurable ?_)
    have h1 : Continuous (Cvs.WeilForm.Archimedean.TruncatedLevyDensityBelow.densityTrunc N) := by
      unfold Cvs.WeilForm.Archimedean.TruncatedLevyDensityBelow.densityTrunc; exact continuous_finsetSum _ (fun k _ => by fun_prop)
    exact h1.mul (continuous_const.sub hcont_sc)
  · intro N
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u hu => ?_)
    have hdnn : 0 ≤ d u := by
      have := Cvs.WeilForm.Archimedean.ArchEnergySpectral.levy_nonneg (Cvs.WeilForm.WindowRepresentative.integrable_sq_rep (waveW hL))
        (Cvs.WeilForm.WindowRepresentative.integrable_cross_rep (waveW hL)) hu
      unfold Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy at this
      exact nonneg_of_mul_nonneg_right this (Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Cvs.WeilForm.Archimedean.TruncatedLevyDensityBelow.densityTrunc_nonneg N u) hdnn)]
    exact mul_le_mul_of_nonneg_right (Cvs.WeilForm.Archimedean.TruncatedLevyDensityBelow.densityTrunc_le N hu) hdnn
  · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u hu => ?_)
    exact (((Cvs.WeilForm.Archimedean.LevyDensity.hasSum_exp u hu).tendsto_sum_nat).mul_const (d u))

/-- **A telescoping majorant step** for the channel tail. -/
theorem tele_step (hL : 0 < Real.log 2) {k : ℕ} (hk : 1 ≤ k) :
    Real.log 2 * tw (Real.log 2)^2 / (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k)^3
      ≤ Real.log 2 * tw (Real.log 2)^2 / (4*(k:ℝ)-1)^2
        - Real.log 2 * tw (Real.log 2)^2 / (4*((k:ℝ)+1)-1)^2 := by
  have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hLt : (0:ℝ) < Real.log 2 * tw (Real.log 2)^2 := mul_pos hL (pow_pos (tw_pos hL) 2)
  have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k = (4*(k:ℝ)+1)/2 := by rw [Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx]; ring
  have h1 : (0:ℝ) < 4*(k:ℝ)-1 := by linarith
  have h3 : (0:ℝ) < 4*(k:ℝ)+3 := by linarith
  have h5 : (0:ℝ) < 4*(k:ℝ)+1 := by linarith
  have he : (4*((k:ℝ)+1)-1) = 4*(k:ℝ)+3 := by ring
  rw [hb, he, ← sub_nonneg]
  have hpoly : (4*(k:ℝ)-1)^2 * (4*(k:ℝ)+3)^2 ≤ (4*(k:ℝ)+1)^4 := by nlinarith [hk1, sq_nonneg (4*(k:ℝ)+1)]
  have key : Real.log 2 * tw (Real.log 2)^2 / (4*(k:ℝ)-1)^2
        - Real.log 2 * tw (Real.log 2)^2 / (4*(k:ℝ)+3)^2
        - Real.log 2 * tw (Real.log 2)^2 / ((4*(k:ℝ)+1)/2)^3
      = (Real.log 2 * tw (Real.log 2)^2) * (8 * ((4*(k:ℝ)+1)^4 - (4*(k:ℝ)-1)^2*(4*(k:ℝ)+3)^2))
        / ((4*(k:ℝ)-1)^2 * (4*(k:ℝ)+3)^2 * (4*(k:ℝ)+1)^3) := by field_simp; ring
  rw [key]
  apply div_nonneg
  · apply mul_nonneg hLt.le; nlinarith [hpoly]
  · positivity

/-- **The Lévy tail past channel twenty is below `23/10000`.** -/
theorem tailsum_le (hL : 0 < Real.log 2) (N : ℕ) :
    ∑ k ∈ Finset.Ico 20 N, Real.log 2 * tw (Real.log 2)^2 / (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k)^3
      ≤ 23/10000 := by
  set c := Real.log 2 * tw (Real.log 2)^2 with hc
  have hcpos : 0 < c := mul_pos hL (pow_pos (tw_pos hL) 2)
  set M : ℕ → ℝ := fun k => c / (4*(k:ℝ)-1)^2 with hM
  have hstep : ∀ k ∈ Finset.Ico 20 N, c / (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k)^3 ≤ M k - M (k+1) := by
    intro k hk
    have hk1 : 1 ≤ k := le_trans (by norm_num) (Finset.mem_Ico.mp hk).1
    have := tele_step hL hk1
    simp only [hM]
    convert this using 3
    push_cast; ring
  have htel : ∑ k ∈ Finset.Ico 20 N, (M k - M (k+1)) ≤ M 20 := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_assoc]
    rw [Finset.sum_range_sub' (fun i => M (20 + i))]
    have hpos : 0 ≤ M (20 + (N - 20)) := by simp only [hM]; positivity
    simp only [Nat.add_zero]
    linarith
  calc ∑ k ∈ Finset.Ico 20 N, c / (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k)^3
      ≤ ∑ k ∈ Finset.Ico 20 N, (M k - M (k+1)) := Finset.sum_le_sum hstep
    _ ≤ M 20 := htel
    _ ≤ 23/10000 := by
        simp only [hM]
        have ht := tsq_upper
        have hl := Real.log_two_lt_d9
        rw [hc, div_le_iff₀ (by norm_num)]
        nlinarith [ht, hl, tw_pos hL, Real.log_pos (by norm_num : (1:ℝ) < 2), pow_pos (tw_pos hL) 2]

/-- **The full Lévy integral is below the twenty-channel sum plus `23/10000`.** -/
theorem fullLevy_le (hL : 0 < Real.log 2) :
    (∫ u in Set.Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u
        * (selfConvolution (Cvs.WeilForm.WindowRepresentative.rep (waveW hL)) 0
          - selfConvolution (Cvs.WeilForm.WindowRepresentative.rep (waveW hL)) (u / 2)))
      ≤ (∑ k ∈ Finset.range 20, ((1 / ((k : ℝ) + 1 / 4)) * (Real.log 2 / 2)
          - Cvs.WeilForm.ChannelFunctionalL2.chanInt (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k)
              (Cvs.WeilForm.WindowRepresentative.rep (waveW hL)))) + 23/10000 := by
  refine le_of_tendsto (fullLevy_tendsto hL) ?_
  filter_upwards [Filter.eventually_ge_atTop 20] with N hN
  rw [← Finset.sum_range_add_sum_Ico _ hN]
  have htsum : ∑ k ∈ Finset.Ico 20 N, ((1 / ((k : ℝ) + 1 / 4)) * (Real.log 2 / 2)
      - Cvs.WeilForm.ChannelFunctionalL2.chanInt (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k) (Cvs.WeilForm.WindowRepresentative.rep (waveW hL)))
      ≤ 23/10000 := by
    calc ∑ k ∈ Finset.Ico 20 N, ((1 / ((k : ℝ) + 1 / 4)) * (Real.log 2 / 2)
          - Cvs.WeilForm.ChannelFunctionalL2.chanInt (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k) (Cvs.WeilForm.WindowRepresentative.rep (waveW hL)))
        ≤ ∑ k ∈ Finset.Ico 20 N, Real.log 2 * tw (Real.log 2)^2 / (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k)^3 :=
          Finset.sum_le_sum (fun k _ => chanLevy_crude hL k)
      _ ≤ 23/10000 := tailsum_le hL N
  linarith [htsum]

/-- **The trial level.**  The Dirichlet-mode cosine has Weil form below `(1/100)‖·‖²`. -/
theorem trial_beta (hL : 0 < Real.log 2) :
    Cvs.WeilForm.WindowRepresentative.weilQW 2 1 (waveW hL) ≤ (1/100) * ‖waveW hL‖ ^ 2 := by
  rw [weilQW_decomp hL, waveW_norm_sq hL]
  have hrank := rank1_le hL
  have hsum := sum_chanLevy_le hL
  have htail := fullLevy_le hL
  have hl9 := Real.log_two_gt_d9
  have harch2 : Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0
      * selfConvolution (Cvs.WeilForm.WindowRepresentative.rep (waveW hL)) 0 ≤ -5.368 * (Real.log 2 / 2) := by
    rw [selfConv_rep_zero hL]
    nlinarith [archSymbol_zero_upper, hl9]
  nlinarith [hrank, hsum, htail, harch2, hl9]

end Cvs.StepA.DirichletCosineTrial
