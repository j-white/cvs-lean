import Mathlib
import Cvs.WeilForm.ArchChannelWindowTerms
import Cvs.WeilForm.Archimedean.ArchSpectralDensity
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.SymbolIncrementMeasurable
import Cvs.WeilForm.Archimedean.SymbolIncrementQuadratic
import Cvs.WeilForm.AutocorrSelfConvolution
import Cvs.WeilForm.ConcreteTestIdentification
import Cvs.WeilForm.PrimeSideExplicitIndex
import Cvs.WeilForm.ProductIntegrability
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.SpectralDensityModulus
import Cvs.WeilForm.SpectralIdentification
import Cvs.WeilForm.TruncatedTestContinuous
import Cvs.WeilForm.WeilFormReflection
import Cvs.Zeta.CriticalParam
import Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly
import Cvs.Zeta.ExplicitFormula.AnalyticSideFunctional
import Cvs.Zeta.ExplicitFormula.ArchimedeanChannelEvaluated
import Cvs.Zeta.ExplicitFormula.ArchimedeanContourShift
import Cvs.Zeta.ExplicitFormula.ArchimedeanIntegrand
import Cvs.Zeta.ExplicitFormula.AutocorrelationSupport
import Cvs.Zeta.ExplicitFormula.CompactTestAdmissibility
import Cvs.Zeta.ExplicitFormula.CompactTestModulusSquared
import Cvs.Zeta.ExplicitFormula.CriticalLineDensity
import Cvs.Zeta.ExplicitFormula.DecayHypothesisShape
import Cvs.Zeta.ExplicitFormula.FirstPoleContourShift
import Cvs.Zeta.ExplicitFormula.HannWindowShifts
import Cvs.Zeta.ExplicitFormula.NonnegTestPrimeSide
import Cvs.Zeta.ExplicitFormula.PoleChannelTruncation
import Cvs.Zeta.ExplicitFormula.PrimeChannelFiniteSum
import Cvs.Zeta.ExplicitFormula.PrimeSideFiniteSum
import Cvs.Zeta.ExplicitFormula.TransformContinuityScaling
import Cvs.Zeta.ExplicitFormula.WindowTransformEntire
import Cvs.Zeta.ExplicitFormula.WindowTransformFullLine
import Cvs.Zeta.FourierShift
import Cvs.Zeta.GaussKernel.DiagonalWindows
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.IndexChangeTransport
import Cvs.Zeta.GaussKernel.MultiplicitiesAgree
import Cvs.Zeta.GaussKernel.WeightedDominator
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.GuinandWeilClassical
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.WeilPositivityStatement
import Cvs.Zeta.ZeroSideMoments

/-!
# The zero side for tests of quadratic decay

The explicit-formula chain from `DecayHypothesisShape` to `an earlier result` threads a cubic decay bound that cut cosine and
sine sums cannot meet, though every step needs only quadratic decay, since the formula sees the
square of the transform. The chain is re-run from `‖W ξ‖ ≤ C₂/‖ξ‖²`, ending in the zero-side
identity for continuous tests vanishing at the window's ends with quadratic-decay transforms.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Real Complex Function Cvs.Zeta.Explicit.Weil
open scoped FourierTransform ArithmeticFunction
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded Cvs.WeilForm.SelfConvolutionTransform Cvs.WeilForm.SelfConvolutionCosine Cvs.WeilForm.Archimedean.SymbolIncrementQuadratic
open Cvs.WeilForm.Archimedean.LevyDensity

namespace Cvs.Zeta.ExplicitFormula.QuadraticDecayZeroSide
open Cvs.ZeroCounting

/-! ### The decay lemmas from a quadratic bound -/

theorem decay_form₂ {T C0 C2 : ℝ} (hC0 : 0 ≤ C0) (hC2 : 0 ≤ C2) {W : ℂ → ℂ}
    (hplain : ∀ ξ : ℂ, |ξ.im| ≤ T → ‖W ξ‖ ≤ C0)
    (hquad : ∀ ξ : ℂ, ξ ≠ 0 → |ξ.im| ≤ T → ‖W ξ‖ ≤ C2 / ‖ξ‖ ^ 2) :
    ∀ ξ : ℂ, |ξ.im| ≤ T → ‖W ξ‖ ≤ 4 * (C0 + C2) / (1 + |ξ.re|) ^ 2 := by
  intro ξ hξ
  have habs : (0 : ℝ) ≤ |ξ.re| := abs_nonneg _
  have hden : (0 : ℝ) < (1 + |ξ.re|) ^ 2 := by positivity
  by_cases hsmall : |ξ.re| ≤ 1
  · have h4 : (1 + |ξ.re|) ^ 2 ≤ 4 := by nlinarith
    refine (hplain ξ hξ).trans ?_
    rw [le_div_iff₀ hden]
    have := mul_le_mul_of_nonneg_left h4 hC0
    nlinarith [hC2, hden]
  · rw [not_le] at hsmall
    have hbig : (1 : ℝ) < |ξ.re| := hsmall
    have hre0 : ξ.re ≠ 0 := by
      intro h; rw [h] at hbig; simp at hbig; linarith
    have hne : ξ ≠ 0 := fun h => hre0 (by rw [h]; simp)
    have hnorm : |ξ.re| ≤ ‖ξ‖ := Complex.abs_re_le_norm ξ
    have hnpos : (0 : ℝ) < ‖ξ‖ := by linarith
    refine (hquad ξ hne hξ).trans ?_
    rw [div_le_div_iff₀ (by positivity) hden]
    have h2 : (1 + |ξ.re|) ≤ 2 * |ξ.re| := by linarith
    have hsq : (1 + |ξ.re|) ^ 2 ≤ 4 * ‖ξ‖ ^ 2 := by
      calc (1 + |ξ.re|) ^ 2 ≤ (2 * |ξ.re|) ^ 2 := pow_le_pow_left₀ (by linarith) h2 2
        _ = 4 * |ξ.re| ^ 2 := by ring
        _ ≤ 4 * ‖ξ‖ ^ 2 := by
            have := pow_le_pow_left₀ habs hnorm 2
            linarith
    have h1 := mul_le_mul_of_nonneg_left hsq hC2
    have h3 : (0 : ℝ) ≤ C0 * ‖ξ‖ ^ 2 := by positivity
    nlinarith [h1, h3]

theorem sq_decay₂ {T A : ℝ} (hA : 0 ≤ A) {W : ℂ → ℂ}
    (h : ∀ ξ : ℂ, |ξ.im| ≤ T → ‖W ξ‖ ≤ A / (1 + |ξ.re|) ^ 2) :
    ∀ ξ : ℂ, |ξ.im| ≤ T → ‖W ξ * W (-ξ)‖ ≤ A ^ 2 / (1 + |ξ.re|) ^ 3 := by
  intro ξ hξ
  have hneg : |(-ξ).im| ≤ T := by simpa using hξ
  have hre : |(-ξ).re| = |ξ.re| := by simp
  have habs : (0 : ℝ) ≤ |ξ.re| := abs_nonneg _
  have hden : (0 : ℝ) < (1 + |ξ.re|) ^ 3 := by positivity
  have h1 := h ξ hξ
  have h2 := h (-ξ) hneg
  rw [hre] at h2
  rw [norm_mul]
  have hstep : ‖W ξ‖ * ‖W (-ξ)‖ ≤ (A / (1 + |ξ.re|) ^ 2) * (A / (1 + |ξ.re|) ^ 2) :=
    mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
  refine hstep.trans ?_
  have hone : (1 : ℝ) ≤ 1 + |ξ.re| := by linarith
  have h34 : (1 + |ξ.re|) ^ 3 ≤ (1 + |ξ.re|) ^ 2 * (1 + |ξ.re|) ^ 2 := by
    have : (1 + |ξ.re|) ^ 2 * (1 + |ξ.re|) ^ 2 = (1 + |ξ.re|) ^ 3 * (1 + |ξ.re|) := by ring
    rw [this]
    exact le_mul_of_one_le_right hden.le hone
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) hden]
  calc A * A * (1 + |ξ.re|) ^ 3 = A ^ 2 * (1 + |ξ.re|) ^ 3 := by ring
    _ ≤ A ^ 2 * ((1 + |ξ.re|) ^ 2 * (1 + |ξ.re|) ^ 2) :=
        mul_le_mul_of_nonneg_left h34 (sq_nonneg A)

theorem ofCritical_decay₂ {C0 C2 : ℝ} (hC0 : 0 ≤ C0) (hC2 : 0 ≤ C2) {W : ℂ → ℂ}
    (hplain : ∀ ξ : ℂ, |ξ.im| ≤ 3 / 2 → ‖W ξ‖ ≤ C0)
    (hquad : ∀ ξ : ℂ, ξ ≠ 0 → |ξ.im| ≤ 3 / 2 → ‖W ξ‖ ≤ C2 / ‖ξ‖ ^ 2) :
    ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 →
      ‖Cvs.Zeta.ofCritical (fun ξ => W ξ * W (-ξ)) z‖
        ≤ (4 * (C0 + C2)) ^ 2 / (1 + |z.im|) ^ 3 := by
  intro z h1 h2
  have hA : (0 : ℝ) ≤ 4 * (C0 + C2) := by linarith
  have hsq := sq_decay₂ (T := 3 / 2) hA (decay_form₂ hC0 hC2 hplain hquad)
    (-I * (z - 1 / 2)) (Cvs.Detection.critical_im_le h1 h2)
  rw [Cvs.Detection.critical_re] at hsq
  rw [Cvs.Zeta.ofCritical]
  exact hsq

/-- **The explicit formula for a quadratic-decay test.** -/
theorem guinand_weil_of_windowTransform₂ {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℂ}
    (hf : Continuous f) {C0 C2 : ℝ} (hC0 : 0 ≤ C0) (hC2 : 0 ≤ C2)
    (hplain : ∀ ξ : ℂ, |ξ.im| ≤ 3 / 2 → ‖Cvs.Detection.windowTransform L f ξ‖ ≤ C0)
    (hquad : ∀ ξ : ℂ, ξ ≠ 0 → |ξ.im| ≤ 3 / 2 →
      ‖Cvs.Detection.windowTransform L f ξ‖ ≤ C2 / ‖ξ‖ ^ 2) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∃ (T' : ℝ) (S : Finset ℂ) (m : ℂ → ℕ),
        T ≤ T' ∧
        (∀ ρ ∈ S, Cvs.Zeta.riemannXi ρ = 0) ∧
        (∀ ρ ∈ S, -1 < ρ.re ∧ ρ.re < 2 ∧ -T' < ρ.im ∧ ρ.im < T') ∧
        (∀ u : ℂ, Cvs.Zeta.riemannXi u = 0 → |u.im| < T' → u ∈ S) ∧
        (∀ u : ℂ, (m u : ℤ) = MeromorphicOn.divisor Cvs.Zeta.riemannXi Set.univ u) ∧
        ‖(Real.pi : ℂ) * ∑ ρ ∈ S, (m ρ : ℂ)
              * Cvs.Detection.sqTransform L f (-I * (ρ - 1 / 2))
            - Cvs.Zeta.ExplicitFormula.AnalyticSideFunctional.analyticSide (Cvs.Detection.sqTransform L f)‖
          < ε := by
  have hA : (0 : ℝ) ≤ 4 * (C0 + C2) := by linarith
  have hsq := sq_decay₂ (T := 3 / 2) hA (decay_form₂ hC0 hC2 hplain hquad)
  exact Cvs.Zeta.guinand_weil_classical (A := (4 * (C0 + C2)) ^ 2) (by positivity)
    (by positivity : (0:ℝ) ≤ (4 * (C0 + C2)) ^ 2)
    (Cvs.Detection.differentiable_sq (Cvs.Detection.differentiable_windowTransform hL hf))
    (Cvs.Detection.sq_even (Cvs.Detection.windowTransform L f))
    (ofCritical_decay₂ hC0 hC2 hplain hquad)
    (Cvs.Detection.stripDecayRe_of_decay (by positivity) hsq)

/-! ### The real-line bounds -/

theorem norm_fourier_truncate_le₂ {L : ℝ} (hL : 0 ≤ L) (f : ℝ → ℂ)
    {C0 C2 : ℝ} (hC0 : 0 ≤ C0) (hC2 : 0 ≤ C2)
    (hplain : ∀ ξ : ℂ, |ξ.im| ≤ 3 / 2 → ‖Cvs.Detection.windowTransform L f ξ‖ ≤ C0)
    (hquad : ∀ ξ : ℂ, ξ ≠ 0 → |ξ.im| ≤ 3 / 2 →
      ‖Cvs.Detection.windowTransform L f ξ‖ ≤ C2 / ‖ξ‖ ^ 2)
    (w : ℝ) :
    ‖𝓕 (Cvs.Detection.truncate L f) w‖ ≤ (4 * C0 + C2) / (1 + |w|) ^ 2 := by
  rw [Cvs.Zeta.ExplicitFormula.TransformContinuityScaling.fourier_truncate_eq hL f w]
  set ξ : ℂ := ((2 * π * w : ℝ) : ℂ) with hξ
  have him : |ξ.im| ≤ 3 / 2 := by
    rw [hξ, Complex.ofReal_im, abs_zero]
    norm_num
  have hden : (0:ℝ) < (1 + |w|) ^ 2 := by positivity
  have hWnn : 0 ≤ ‖Cvs.Detection.windowTransform L f ξ‖ := norm_nonneg _
  rw [le_div_iff₀ hden]
  rcases le_or_gt |w| 1 with hw | hw
  · have h := hplain ξ him
    have h4 : (1 + |w|) ^ 2 ≤ 4 := by nlinarith [abs_nonneg w]
    nlinarith [h, h4]
  · have hwpos : (0:ℝ) < |w| := lt_trans one_pos hw
    have hwne : w ≠ 0 := fun h => by rw [h, abs_zero] at hwpos; exact lt_irrefl 0 hwpos
    have hne : ξ ≠ 0 := by
      rw [hξ, ne_eq, Complex.ofReal_eq_zero]
      have hpi : (0:ℝ) < 2 * π := by positivity
      exact mul_ne_zero (ne_of_gt hpi) hwne
    have hnorm : ‖ξ‖ = 2 * π * |w| := by
      rw [hξ, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
    have h := hquad ξ hne him
    rw [hnorm] at h
    have hpi3 : (3:ℝ) < π := Real.pi_gt_three
    have hsqpos : (0:ℝ) < (2 * π * |w|) ^ 2 := by positivity
    have h1 : (1 + |w|) ^ 2 ≤ 4 * |w| ^ 2 := by nlinarith
    have h3 : (4:ℝ) * |w| ^ 2 ≤ (2 * π * |w|) ^ 2 := by
      have hexp : (2 * π * |w|) ^ 2 = 4 * π ^ 2 * |w| ^ 2 := by ring
      rw [hexp]
      have : (1:ℝ) ≤ π ^ 2 := by nlinarith
      nlinarith [sq_nonneg |w|]
    have hsq : (1 + |w|) ^ 2 ≤ (2 * π * |w|) ^ 2 := by linarith
    have hstep : ‖Cvs.Detection.windowTransform L f ξ‖ * (1 + |w|) ^ 2
        ≤ (C2 / (2 * π * |w|) ^ 2) * (1 + |w|) ^ 2 :=
      mul_le_mul_of_nonneg_right h hden.le
    have hkey : (C2 / (2 * π * |w|) ^ 2) * (1 + |w|) ^ 2 ≤ C2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hsqpos]
      nlinarith [hsq, hC2]
    linarith

theorem norm_sq_quartic₂ {C0 C2 : ℝ} (hC0 : 0 ≤ C0) (hC2 : 0 ≤ C2) {W : ℂ → ℂ}
    (hplain : ∀ ξ : ℂ, |ξ.im| ≤ 3 / 2 → ‖W ξ‖ ≤ C0)
    (hquad : ∀ ξ : ℂ, ξ ≠ 0 → |ξ.im| ≤ 3 / 2 → ‖W ξ‖ ≤ C2 / ‖ξ‖ ^ 2)
    (z : ℂ) (h1 : -1 ≤ z.re) (h2 : z.re ≤ 2) :
    ‖Cvs.Zeta.ofCritical (fun ξ => W ξ * W (-ξ)) z‖
      ≤ 2 * (C0 ^ 2 + C2 ^ 2) / (1 + z.im ^ 4) := by
  set ξ : ℂ := -Complex.I * (z - 1 / 2) with hξ
  have hre : ξ.re = z.im := by rw [hξ]; simp
  have him : ξ.im = -(z.re - 1 / 2) := by rw [hξ]; simp
  have himb : |ξ.im| ≤ 3 / 2 := by
    rw [him, abs_le]; constructor <;> linarith
  have himb' : |(-ξ).im| ≤ 3 / 2 := by simpa using himb
  have hge : |z.im| ≤ ‖ξ‖ := by rw [← hre]; exact Complex.abs_re_le_norm ξ
  have hval : Cvs.Zeta.ofCritical (fun ξ => W ξ * W (-ξ)) z = W ξ * W (-ξ) := rfl
  have hden : (0:ℝ) < 1 + z.im ^ 4 := by positivity
  rw [hval, norm_mul]
  have habs4 : |z.im| ^ 4 = z.im ^ 4 := by
    rw [← abs_pow, abs_of_nonneg (by positivity : (0:ℝ) ≤ z.im ^ 4)]
  rcases le_or_gt |z.im| 1 with hz | hz
  · have hb1 := hplain ξ himb
    have hb2 := hplain (-ξ) himb'
    have hq : z.im ^ 4 ≤ 1 := by
      rw [← habs4]
      exact pow_le_one₀ (abs_nonneg _) hz
    have hp : ‖W ξ‖ * ‖W (-ξ)‖ ≤ C0 ^ 2 := by
      have := mul_le_mul hb1 hb2 (norm_nonneg _) hC0
      nlinarith [this]
    rw [le_div_iff₀ hden]
    nlinarith [hp, hq, sq_nonneg C2,
      mul_nonneg (norm_nonneg (W ξ)) (norm_nonneg (W (-ξ)))]
  · have hne : ξ ≠ 0 := by
      intro hc
      rw [hc, norm_zero] at hge
      linarith
    have hne' : -ξ ≠ 0 := neg_ne_zero.mpr hne
    have hone : (1:ℝ) ≤ ‖ξ‖ := le_trans hz.le hge
    have hb1 := hquad ξ hne himb
    have hb2 := hquad (-ξ) hne' himb'
    rw [norm_neg] at hb2
    have hprod : ‖W ξ‖ * ‖W (-ξ)‖ ≤ C2 ^ 2 / ‖ξ‖ ^ 4 := by
      have h := mul_le_mul hb1 hb2 (norm_nonneg _) (by positivity)
      calc ‖W ξ‖ * ‖W (-ξ)‖ ≤ (C2 / ‖ξ‖ ^ 2) * (C2 / ‖ξ‖ ^ 2) := h
        _ = C2 ^ 2 / ‖ξ‖ ^ 4 := by rw [div_mul_div_comm]; ring_nf
    have h4 : z.im ^ 4 ≤ ‖ξ‖ ^ 4 := by
      rw [← habs4]
      exact pow_le_pow_left₀ (abs_nonneg _) hge 4
    have hfour1 : (1:ℝ) ≤ ‖ξ‖ ^ 4 := one_le_pow₀ hone
    rw [le_div_iff₀ hden]
    have hstep : ‖W ξ‖ * ‖W (-ξ)‖ * (1 + z.im ^ 4)
        ≤ (C2 ^ 2 / ‖ξ‖ ^ 4) * (1 + z.im ^ 4) :=
      mul_le_mul_of_nonneg_right hprod hden.le
    have hfrac : (C2 ^ 2 / ‖ξ‖ ^ 4) * (1 + z.im ^ 4) ≤ 2 * (C0 ^ 2 + C2 ^ 2) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [h4, hfour1, sq_nonneg C0, sq_nonneg C2]
    linarith

/-- **The zero side is summable** for a quadratic-decay test. -/
theorem summable_sqTransform_zeroSide₂ {L : ℝ} {f : ℝ → ℂ} {C0 C2 : ℝ}
    (hC0 : 0 ≤ C0) (hC2 : 0 ≤ C2)
    (hplain : ∀ ξ : ℂ, |ξ.im| ≤ 3 / 2 →
      ‖Cvs.Detection.windowTransform L f ξ‖ ≤ C0)
    (hquad : ∀ ξ : ℂ, ξ ≠ 0 → |ξ.im| ≤ 3 / 2 →
      ‖Cvs.Detection.windowTransform L f ξ‖ ≤ C2 / ‖ξ‖ ^ 2) :
    Summable fun rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet =>
      (Cvs.Criterion.divisorWeight rho : ℝ)
        * (Cvs.Detection.sqTransform L f (Cvs.ZeroCounting.zPoint rho)).re := by
  refine Summable.of_norm_bounded
    (Cvs.Criterion.summable_divisorWeight_quartic.mul_left (2 * (C0 ^ 2 + C2 ^ 2)))
    fun rho => ?_
  have hstrip := Cvs.Zeta.GaussKernel.AdmissibleKernel.abs_re_sub_half_le rho
  rw [abs_le] at hstrip
  have h1 : (-1:ℝ) ≤ ((rho : ℂ)).re := by linarith [hstrip.1]
  have h2 : ((rho : ℂ)).re ≤ 2 := by linarith [hstrip.2]
  have hbound := norm_sq_quartic₂ hC0 hC2 hplain hquad (rho : ℂ) h1 h2
  have hval : Cvs.Zeta.ofCritical
      (fun ξ => Cvs.Detection.windowTransform L f ξ * Cvs.Detection.windowTransform L f (-ξ))
      ((rho : ℂ)) = Cvs.Detection.sqTransform L f (Cvs.ZeroCounting.zPoint rho) := rfl
  rw [hval] at hbound
  have hre := Complex.abs_re_le_norm (Cvs.Detection.sqTransform L f (Cvs.ZeroCounting.zPoint rho))
  have hw : (0:ℝ) ≤ (Cvs.Criterion.divisorWeight rho : ℝ) := Nat.cast_nonneg _
  have hden : (0:ℝ) < 1 + ((rho : ℂ)).im ^ 4 := by positivity
  rw [Real.norm_eq_abs, abs_mul, Nat.abs_cast]
  have hstep : |(Cvs.Detection.sqTransform L f (Cvs.ZeroCounting.zPoint rho)).re|
      ≤ 2 * (C0 ^ 2 + C2 ^ 2) / (1 + ((rho : ℂ)).im ^ 4) := le_trans hre hbound
  calc (Cvs.Criterion.divisorWeight rho : ℝ)
        * |(Cvs.Detection.sqTransform L f (Cvs.ZeroCounting.zPoint rho)).re|
      ≤ (Cvs.Criterion.divisorWeight rho : ℝ)
          * (2 * (C0 ^ 2 + C2 ^ 2) / (1 + ((rho : ℂ)).im ^ 4)) :=
        mul_le_mul_of_nonneg_left hstep hw
    _ = 2 * (C0 ^ 2 + C2 ^ 2)
          * ((Cvs.Criterion.divisorWeight rho : ℝ) * (1 / (1 + ((rho : ℂ)).im ^ 4))) := by
        field_simp

/-! ### The channels -/

theorem fourierReal_sqTransform_eq₂ {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℝ}
    (hf : Continuous (cf f)) (h0 : cf f 0 = 0) (hLz : cf f L = 0)
    {C0 C2 : ℝ} (hC0 : 0 ≤ C0) (hC2 : 0 ≤ C2)
    (hplain : ∀ ξ : ℂ, |ξ.im| ≤ 3 / 2 →
      ‖Cvs.Detection.windowTransform L (cf f) ξ‖ ≤ C0)
    (hquad : ∀ ξ : ℂ, ξ ≠ 0 → |ξ.im| ≤ 3 / 2 →
      ‖Cvs.Detection.windowTransform L (cf f) ξ‖ ≤ C2 / ‖ξ‖ ^ 2)
    (t : ℝ) :
    Cvs.Zeta.fourierReal (Cvs.Detection.sqTransform L (cf f)) t
      = ((Real.pi : ℝ) : ℂ)
        * ((selfConvolution (Set.indicator (Set.Ioc 0 L) f) t
            + selfConvolution (Set.indicator (Set.Ioc 0 L) f) (-t) : ℝ) : ℂ) := by
  have hbd := norm_fourier_truncate_le₂ hL (cf f) hC0 hC2 hplain hquad
  have hCnn : (0:ℝ) ≤ 4 * C0 + C2 := by linarith
  have hac : Cvs.Detection.autocorr L (cf f) (-t)
      = ((selfConvolution (Set.indicator (Set.Ioc 0 L) f) t : ℝ) : ℂ) := by
    rw [show (cf f) = (fun s : ℝ => ((f s : ℝ) : ℂ)) from rfl,
      Cvs.Detection.autocorr_ofReal, Cvs.WeilForm.AutocorrSelfConvolution.autocorrR_eq_selfConvolution,
      Cvs.WeilForm.WeilFormReflection.selfConvolution_neg]
  rw [Cvs.Detection.fourierReal_sqTransform hL hf h0 hLz hCnn hbd t, hac,
    Cvs.WeilForm.WeilFormReflection.selfConvolution_neg]
  push_cast
  ring

theorem prime_channel_eq₂ {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℝ}
    (hf : Continuous (cf f)) (h0 : cf f 0 = 0) (hLz : cf f L = 0)
    {C0 C2 : ℝ} (hC0 : 0 ≤ C0) (hC2 : 0 ≤ C2)
    (hplain : ∀ ξ : ℂ, |ξ.im| ≤ 3 / 2 →
      ‖Cvs.Detection.windowTransform L (cf f) ξ‖ ≤ C0)
    (hquad : ∀ ξ : ℂ, ξ ≠ 0 → |ξ.im| ≤ 3 / 2 →
      ‖Cvs.Detection.windowTransform L (cf f) ξ‖ ≤ C2 / ‖ξ‖ ^ 2) :
    (Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly.primeSide (Cvs.Detection.sqTransform L (cf f))).re
      = π * ∑ n ∈ Finset.range ⌈Real.exp L⌉₊,
          (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1/2) : ℝ))
            * (selfConvolution (Set.indicator (Set.Ioc 0 L) f) (Real.log n)
              + selfConvolution (Set.indicator (Set.Ioc 0 L) f) (-(Real.log n))) := by
  have hbd := norm_fourier_truncate_le₂ hL (cf f) hC0 hC2 hplain hquad
  have hCnn : (0:ℝ) ≤ 4 * C0 + C2 := by linarith
  have hterm : ∀ n ∈ Finset.range ⌈Real.exp L⌉₊,
      (ArithmeticFunction.vonMangoldt n : ℂ) * (((n : ℝ) ^ (-(1/2) : ℝ) : ℝ) : ℂ)
          * Cvs.Zeta.fourierReal (Cvs.Detection.sqTransform L (cf f)) (Real.log n)
        = (((ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1/2) : ℝ))
            * (π * (selfConvolution (Set.indicator (Set.Ioc 0 L) f) (Real.log n)
              + selfConvolution (Set.indicator (Set.Ioc 0 L) f)
                  (-(Real.log n)))) : ℝ) : ℂ) := by
    intro n _
    rw [fourierReal_sqTransform_eq₂ hL hf h0 hLz hC0 hC2 hplain hquad (Real.log n)]
    push_cast
    ring
  rw [Cvs.Detection.primeSide_eq_sum hL hf h0 hLz hCnn hbd,
    Finset.sum_congr rfl hterm, ← Complex.ofReal_sum, Complex.ofReal_re, Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => by ring

theorem integrable_fourier_sq₂ {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℝ}
    (hint : Integrable (Cvs.Detection.truncate L (cf f)))
    {C0 C2 : ℝ} (hC0 : 0 ≤ C0) (hC2 : 0 ≤ C2)
    (hplain : ∀ ξ : ℂ, |ξ.im| ≤ 3 / 2 →
      ‖Cvs.Detection.windowTransform L (cf f) ξ‖ ≤ C0)
    (hquad : ∀ ξ : ℂ, ξ ≠ 0 → |ξ.im| ≤ 3 / 2 →
      ‖Cvs.Detection.windowTransform L (cf f) ξ‖ ≤ C2 / ‖ξ‖ ^ 2) :
    Integrable fun ξ : ℝ =>
      ‖𝓕 (cf (Set.indicator (Set.Ioc 0 L) f)) ξ‖ ^ 2 := by
  have hbd := norm_fourier_truncate_le₂ hL (cf f) hC0 hC2 hplain hquad
  have hCnn : (0:ℝ) ≤ 4 * C0 + C2 := by linarith
  rw [Cvs.WeilForm.SpectralDensityModulus.cf_indicator_eq_truncate L f]
  have hdom : Integrable fun ξ : ℝ =>
      (4 * C0 + C2) ^ 2 * (1 + ‖ξ‖) ^ (-(4:ℝ)) :=
    (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 4)
      (by simp)).const_mul _
  refine Integrable.mono' hdom ?_ ?_
  · have hcont : Continuous (𝓕 (Cvs.Detection.truncate L (cf f))) :=
      VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        (innerSL ℝ).continuous₂ hint
    exact (hcont.norm.pow 2).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun ξ => ?_
    have hnn : (0:ℝ) < 1 + |ξ| := by positivity
    have h := hbd ξ
    have hsq : ‖𝓕 (Cvs.Detection.truncate L (cf f)) ξ‖ ^ 2
        ≤ ((4 * C0 + C2) / (1 + |ξ|) ^ 2) ^ 2 := by
      have := norm_nonneg (𝓕 (Cvs.Detection.truncate L (cf f)) ξ)
      nlinarith [h, this]
    have hrw : ((4 * C0 + C2) / (1 + |ξ|) ^ 2) ^ 2
        = (4 * C0 + C2) ^ 2 * (1 + ‖ξ‖) ^ (-(4:ℝ)) := by
      rw [Real.norm_eq_abs, div_pow,
        show ((1 + |ξ|) ^ 2) ^ 2 = (1 + |ξ|) ^ (4:ℕ) by ring,
        ← Real.rpow_natCast (1 + |ξ|) 4, div_eq_mul_inv,
        ← Real.rpow_neg (by positivity)]
      norm_num
    rw [Real.norm_of_nonneg (by positivity), ← hrw]
    exact hsq

theorem specDensity_le₂ {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℝ} {C0 C2 : ℝ}
    (hC0 : 0 ≤ C0) (hC2 : 0 ≤ C2)
    (hplain : ∀ ξ : ℂ, |ξ.im| ≤ 3 / 2 →
      ‖Cvs.Detection.windowTransform L (cf f) ξ‖ ≤ C0)
    (hquad : ∀ ξ : ℂ, ξ ≠ 0 → |ξ.im| ≤ 3 / 2 →
      ‖Cvs.Detection.windowTransform L (cf f) ξ‖ ≤ C2 / ‖ξ‖ ^ 2)
    (t : ℝ) :
    Cvs.WeilForm.SelfConvolutionCosine.specDensity (Set.indicator (Set.Ioc 0 L) f) t
      ≤ (4 * C0 + C2) ^ 2 / (2 * π) / (1 + |t| / (2 * π)) ^ 4 := by
  have hbd := norm_fourier_truncate_le₂ hL (cf f) hC0 hC2 hplain hquad
  have hCnn : (0:ℝ) ≤ 4 * C0 + C2 := by linarith
  have hpi : (0:ℝ) < 2 * π := by positivity
  unfold Cvs.WeilForm.SelfConvolutionCosine.specDensity
  rw [Cvs.WeilForm.SpectralDensityModulus.cf_indicator_eq_truncate L f]
  have habs : |t / (2 * π)| = |t| / (2 * π) := by rw [abs_div, abs_of_pos hpi]
  have h := hbd (t / (2 * π))
  rw [habs] at h
  have hnn := norm_nonneg (𝓕 (Cvs.Detection.truncate L (cf f)) (t / (2 * π)))
  have hsq : ‖𝓕 (Cvs.Detection.truncate L (cf f)) (t / (2 * π))‖ ^ 2
      ≤ (4 * C0 + C2) ^ 2 / (1 + |t| / (2 * π)) ^ 4 := by
    have hstep := pow_le_pow_left₀ hnn h 2
    rw [div_pow, show ((1 + |t| / (2 * π)) ^ 2) ^ 2 = (1 + |t| / (2 * π)) ^ 4 by ring]
      at hstep
    exact hstep
  have hsq' := (le_div_iff₀ (by positivity : (0:ℝ) < (1 + |t| / (2 * π)) ^ 4)).mp hsq
  rw [div_div, div_le_div_iff₀ hpi (by positivity)]
  rw [show (cf f) = (fun s : ℝ => ((f s : ℝ) : ℂ)) from rfl] at hsq'
  nlinarith [mul_le_mul_of_nonneg_right hsq' hpi.le]

theorem integrable_specDensity_mul_arch₂ {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℝ}
    (hint : Integrable (Cvs.Detection.truncate L (cf f)))
    {C0 C2 : ℝ} (hC0 : 0 ≤ C0) (hC2 : 0 ≤ C2)
    (hplain : ∀ ξ : ℂ, |ξ.im| ≤ 3 / 2 →
      ‖Cvs.Detection.windowTransform L (cf f) ξ‖ ≤ C0)
    (hquad : ∀ ξ : ℂ, ξ ≠ 0 → |ξ.im| ≤ 3 / 2 →
      ‖Cvs.Detection.windowTransform L (cf f) ξ‖ ≤ C2 / ‖ξ‖ ^ 2) :
    Integrable fun t : ℝ =>
      Cvs.WeilForm.SelfConvolutionCosine.specDensity (Set.indicator (Set.Ioc 0 L) f) t
        * (archSymbol t - archSymbol 0) := by
  have hpi : (0:ℝ) < 2 * π := by positivity
  have hR : ((2 * π)⁻¹ : ℝ) ≠ 0 := inv_ne_zero (ne_of_gt hpi)
  set A : ℝ := (4 * C0 + C2) ^ 2 / (2 * π) with hA
  set K : ℝ := A * levyMass * (2 + π ^ 2 / 2) with hK
  have hdom : Integrable fun t : ℝ => K * (1 + ‖(2 * π)⁻¹ * t‖) ^ (-(2:ℝ)) :=
    (((integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2)
      (by simp)).comp_mul_left' hR)).const_mul K
  have hFc : Continuous (𝓕 (Cvs.Detection.truncate L (cf f))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hint
  have hWc : Measurable (Cvs.WeilForm.SelfConvolutionCosine.specDensity
      (Set.indicator (Set.Ioc 0 L) f)) := by
    unfold Cvs.WeilForm.SelfConvolutionCosine.specDensity
    rw [Cvs.WeilForm.SpectralDensityModulus.cf_indicator_eq_truncate L f]
    exact ((hFc.comp (continuous_id.div_const (2 * π))).norm.pow 2).measurable.div_const _
  refine Integrable.mono' hdom
    (hWc.aestronglyMeasurable.mul
      Cvs.WeilForm.Archimedean.SymbolIncrementMeasurable.stronglyMeasurable_archSymbol_sub.aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun t => ?_
  set x : ℝ := |t| / (2 * π) with hx
  have hx0 : 0 ≤ x := by positivity
  have hnorm : ‖(2 * π)⁻¹ * t‖ = x := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (2 * π)⁻¹), hx,
      inv_mul_eq_div]
  have hrpow : (1 + ‖(2 * π)⁻¹ * t‖) ^ (-(2:ℝ)) = ((1 + x) ^ 2)⁻¹ := by
    rw [hnorm, Real.rpow_neg (by positivity), ← Real.rpow_natCast (1 + x) 2]
    norm_num
  have hWle := specDensity_le₂ hL hC0 hC2 hplain hquad t
  have hWnn := Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg
    (Set.indicator (Set.Ioc 0 L) f) t
  have hAnn := Cvs.WeilForm.Archimedean.SymbolIncrementQuadratic.archSymbol_sub_nonneg t
  have hAle := Cvs.WeilForm.Archimedean.SymbolIncrementQuadratic.archSymbol_sub_le t
  have hmass := levyMass_nonneg
  have htx : t ^ 2 = (2 * π) ^ 2 * x ^ 2 := by
    rw [hx, div_pow, sq_abs]
    field_simp
  have hquad' : 2 + t ^ 2 / 8 ≤ (2 + π ^ 2 / 2) * (1 + x) ^ 2 := by
    rw [htx]
    nlinarith [sq_nonneg x, hx0, Real.pi_pos, sq_nonneg π]
  have hden : (0:ℝ) < (1 + x) ^ 2 := by positivity
  have hden4 : (0:ℝ) < (1 + x) ^ 4 := by positivity
  rw [Real.norm_of_nonneg (mul_nonneg hWnn hAnn), hrpow]
  have hstep : Cvs.WeilForm.SelfConvolutionCosine.specDensity (Set.indicator (Set.Ioc 0 L) f) t
      * (archSymbol t - archSymbol 0)
      ≤ (A / (1 + x) ^ 4) * ((2 + π ^ 2 / 2) * (1 + x) ^ 2 * levyMass) := by
    refine mul_le_mul hWle ?_ hAnn (by positivity)
    calc archSymbol t - archSymbol 0 ≤ (2 + t ^ 2 / 8) * levyMass := hAle
      _ ≤ (2 + π ^ 2 / 2) * (1 + x) ^ 2 * levyMass :=
          mul_le_mul_of_nonneg_right hquad' hmass
  refine le_trans hstep (le_of_eq ?_)
  rw [hK]
  have hne : ((1 + x) : ℝ) ≠ 0 := by positivity
  field_simp

/-! ### The identity -/

/-- **The window form is the analytic side**, for a quadratic-decay test, on the same
integrability inputs as `an earlier result`. -/
theorem weilForm_eq_analyticSide₂ {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℝ}
    (hf : Continuous (cf f)) (h0 : cf f 0 = 0) (hLz : cf f L = 0)
    {C0 C2 : ℝ} (hC0 : 0 ≤ C0) (hC2 : 0 ≤ C2)
    (hplain : ∀ ξ : ℂ, |ξ.im| ≤ 3 / 2 →
      ‖Cvs.Detection.windowTransform L (cf f) ξ‖ ≤ C0)
    (hquad : ∀ ξ : ℂ, ξ ≠ 0 → |ξ.im| ≤ 3 / 2 →
      ‖Cvs.Detection.windowTransform L (cf f) ξ‖ ≤ C2 / ‖ξ‖ ^ 2)
    {P R : ℕ} (hP : Real.exp L ≤ P) (hR : L ≤ R * Real.log 2)
    (hFint : Integrable (Set.indicator (Set.Ioc 0 L) f))
    (hgint : Integrable fun u : ℝ =>
      ((selfConvolution (Set.indicator (Set.Ioc 0 L) f) u : ℝ) : ℂ))
    (hcont : Continuous fun u : ℝ =>
      ((selfConvolution (Set.indicator (Set.Ioc 0 L) f) u : ℝ) : ℂ))
    (hFsq : Integrable fun ξ : ℝ =>
      ‖𝓕 (cf (Set.indicator (Set.Ioc 0 L) f)) ξ‖ ^ 2)
    (hWi : Integrable (specDensity (Set.indicator (Set.Ioc 0 L) f)))
    (hWA : Integrable fun t : ℝ =>
      specDensity (Set.indicator (Set.Ioc 0 L) f) t * (archSymbol t - archSymbol 0))
    (hprod : Integrable (Function.uncurry fun u t : ℝ =>
        Cvs.WeilForm.Archimedean.LevyDensity.densityU u
          * ((1 - Real.cos (t / 2 * u)) * specDensity (Set.indicator (Set.Ioc 0 L) f) t))
      ((volume.restrict (Ioi (0:ℝ))).prod volume)) :
    π * Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Set.indicator (Set.Ioc 0 L) f)
      = (Cvs.Zeta.ExplicitFormula.AnalyticSideFunctional.analyticSide (Cvs.Detection.sqTransform L (cf f))).re := by
  have hd : Differentiable ℂ (Cvs.Detection.sqTransform L (cf f)) :=
    Cvs.Detection.differentiable_sq (Cvs.Detection.differentiable_windowTransform hL hf)
  have hAnn : (0:ℝ) ≤ (4 * (C0 + C2)) ^ 2 := by positivity
  have hdec := ofCritical_decay₂ hC0 hC2 hplain hquad
  have hrho := Cvs.Detection.ofCritical_sqTransform_half L f
  have hg : ∀ v : ℝ, selfConvolution (Set.indicator (Set.Ioc 0 L) f) v
      = ∫ t : ℝ, specDensity (Set.indicator (Set.Ioc 0 L) f) t * Real.cos (t * v) :=
    fun v => Cvs.WeilForm.SelfConvolutionCosine.selfConvolution_eq_cosIntegral hFint hgint hFsq
      hcont.continuousAt
  have harch := Cvs.WeilForm.Archimedean.ArchSpectralDensity.arch_of_spectral hWi hg hWA hprod
  have hpole : ((∫ y : ℝ, Cvs.Zeta.ExplicitFormula.FirstPoleContourShift.poleIntegrand
          (Cvs.Detection.sqTransform L (cf f)) (2 + (y : ℝ) * I))
        + ∫ y : ℝ, Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly.poleTwo
          (Cvs.Detection.sqTransform L (cf f)) (2 + (y : ℝ) * I)).re
      = π * (2 * (∫ s : ℝ, Set.indicator (Set.Ioc 0 L) f s * Real.exp (s / 2))
        * ∫ s : ℝ, Set.indicator (Set.Ioc 0 L) f s * Real.exp (-(s / 2))) :=
    Cvs.Zeta.ExplicitFormula.PoleChannelTruncation.pole_channel_truncate hL hd hAnn hdec hrho
  have harchline : (∫ y : ℝ, Cvs.Zeta.ExplicitFormula.ArchimedeanContourShift.archIntegrand
          (Cvs.Detection.sqTransform L (cf f)) (2 + (y : ℝ) * I)).re
      = ∫ y : ℝ, Cvs.Detection.archScore y
          * ‖Cvs.Detection.windowTransform L (cf f) ((y : ℝ))‖ ^ 2 :=
    Cvs.Zeta.ExplicitFormula.ArchimedeanChannelEvaluated.arch_channel_window_line hAnn hd hdec hrho
  have hprime := prime_channel_eq₂ hL hf h0 hLz hC0 hC2 hplain hquad
  have hcomb : Cvs.Zeta.ExplicitFormula.AnalyticSideFunctional.analyticSide (Cvs.Detection.sqTransform L (cf f))
      = ((∫ y : ℝ, Cvs.Zeta.ExplicitFormula.FirstPoleContourShift.poleIntegrand
            (Cvs.Detection.sqTransform L (cf f)) (2 + (y : ℝ) * I))
          + (∫ y : ℝ, Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly.poleTwo
            (Cvs.Detection.sqTransform L (cf f)) (2 + (y : ℝ) * I))
          + (∫ y : ℝ, Cvs.Zeta.ExplicitFormula.ArchimedeanContourShift.archIntegrand
            (Cvs.Detection.sqTransform L (cf f)) (2 + (y : ℝ) * I)))
        - Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly.primeSide (Cvs.Detection.sqTransform L (cf f)) := rfl
  rw [Cvs.WeilForm.PrimeSideExplicitIndex.weilForm_eq_range hL hP hR f, harch, hcomb,
    Complex.sub_re, Complex.add_re, hpole, harchline,
    Cvs.WeilForm.ArchChannelWindowTerms.arch_channel_eq hL f, hprime]
  ring

/-- **The window form is the analytic side**, for a continuous test vanishing at the ends with
a quadratic-decay transform. -/
theorem weilForm_eq_analyticSide'₂ {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hfc : Continuous f) (h0 : f 0 = 0) (hLz : f L = 0)
    {C0 C2 : ℝ} (hC0 : 0 ≤ C0) (hC2 : 0 ≤ C2)
    (hplain : ∀ ξ : ℂ, |ξ.im| ≤ 3 / 2 →
      ‖Cvs.Detection.windowTransform L (cf f) ξ‖ ≤ C0)
    (hquad : ∀ ξ : ℂ, ξ ≠ 0 → |ξ.im| ≤ 3 / 2 →
      ‖Cvs.Detection.windowTransform L (cf f) ξ‖ ≤ C2 / ‖ξ‖ ^ 2)
    {P R : ℕ} (hP : Real.exp L ≤ P) (hR : L ≤ R * Real.log 2) :
    π * Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Set.indicator (Set.Ioc (0:ℝ) L) f)
      = (Cvs.Zeta.ExplicitFormula.AnalyticSideFunctional.analyticSide (Cvs.Detection.sqTransform L (cf f))).re := by
  have hint := Cvs.WeilForm.SpectralIdentification.integrable_truncate hL hfc h0 hLz
  have hFsq := integrable_fourier_sq₂ hL.le hint hC0 hC2 hplain hquad
  have hWA := integrable_specDensity_mul_arch₂ hL.le hint hC0 hC2 hplain hquad
  refine weilForm_eq_analyticSide₂ hL.le
    (Complex.continuous_ofReal.comp hfc) (by simp [cf, h0]) (by simp [cf, hLz])
    hC0 hC2 hplain hquad hP hR
    (Cvs.WeilForm.TruncatedTestContinuous.integrable_indicator hL hfc h0 hLz)
    (Cvs.WeilForm.TruncatedTestContinuous.integrable_selfConvolution hL hfc h0 hLz)
    (Cvs.WeilForm.TruncatedTestContinuous.continuous_selfConvolution hL hfc h0 hLz)
    hFsq
    (Cvs.WeilForm.ProductIntegrability.integrable_specDensity hFsq)
    hWA
    (Cvs.WeilForm.ProductIntegrability.integrable_prod_of_arch
      (specDensity_nonneg (Set.indicator (Set.Ioc 0 L) f))
      (Cvs.WeilForm.SpectralIdentification.measurable_specDensity hL hfc h0 hLz) hWA)

/-- **The window form equals the zero sum to any accuracy**, for a quadratic-decay test. -/
theorem weilForm_sub_zeroSum_lt₂ {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hfc : Continuous f) (h0 : f 0 = 0) (hLz : f L = 0)
    {C0 C2 : ℝ} (hC0 : 0 ≤ C0) (hC2 : 0 ≤ C2)
    (hplain : ∀ ξ : ℂ, |ξ.im| ≤ 3 / 2 →
      ‖Cvs.Detection.windowTransform L (cf f) ξ‖ ≤ C0)
    (hquad : ∀ ξ : ℂ, ξ ≠ 0 → |ξ.im| ≤ 3 / 2 →
      ‖Cvs.Detection.windowTransform L (cf f) ξ‖ ≤ C2 / ‖ξ‖ ^ 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∃ (T' : ℝ) (S : Finset ℂ) (m : ℂ → ℕ),
        T ≤ T' ∧
        (∀ ρ ∈ S, Cvs.Zeta.riemannXi ρ = 0) ∧
        (∀ ρ ∈ S, -1 < ρ.re ∧ ρ.re < 2 ∧ -T' < ρ.im ∧ ρ.im < T') ∧
        (∀ u : ℂ, Cvs.Zeta.riemannXi u = 0 → |u.im| < T' → u ∈ S) ∧
        (∀ u : ℂ, (m u : ℤ) = MeromorphicOn.divisor Cvs.Zeta.riemannXi Set.univ u) ∧
        |π * (∑ ρ ∈ S, (m ρ : ℂ)
              * Cvs.Detection.sqTransform L (cf f) (-I * (ρ - 1 / 2))).re
            - π * Cvs.WeilForm.SelfConvolutionFunctional.weilForm ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊
                (Set.indicator (Set.Ioc (0:ℝ) L) f)|
          < ε := by
  obtain ⟨T₀, hT₀⟩ := guinand_weil_of_windowTransform₂ hL.le (f := cf f)
    (Complex.continuous_ofReal.comp hfc) hC0 hC2 hplain hquad ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  obtain ⟨T', S, m, h1, h2, h3, h4, h5, hnorm⟩ := hT₀ T hT
  refine ⟨T', S, m, h1, h2, h3, h4, h5, ?_⟩
  have hre := Complex.abs_re_le_norm
    ((Real.pi : ℂ) * ∑ ρ ∈ S, (m ρ : ℂ)
        * Cvs.Detection.sqTransform L (cf f) (-I * (ρ - 1 / 2))
      - Cvs.Zeta.ExplicitFormula.AnalyticSideFunctional.analyticSide (Cvs.Detection.sqTransform L (cf f)))
  rw [Complex.sub_re, Complex.re_ofReal_mul,
    ← weilForm_eq_analyticSide'₂ hL hfc h0 hLz hC0 hC2 hplain hquad
      (Cvs.WeilForm.ConcreteTestIdentification.le_ceil_exp L) (Cvs.WeilForm.ConcreteTestIdentification.le_ceil_log L)] at hre
  linarith [hre, hnorm]

/-- **The zero side is the window form**, for a continuous test vanishing at the ends with a
quadratic-decay transform. -/
theorem weilForm_eq_kernelZeroSide₂ {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hfc : Continuous f) (h0 : f 0 = 0) (hLz : f L = 0)
    {C0 C2 : ℝ} (hC0 : 0 ≤ C0) (hC2 : 0 ≤ C2)
    (hplain : ∀ ξ : ℂ, |ξ.im| ≤ 3 / 2 →
      ‖Cvs.Detection.windowTransform L (cf f) ξ‖ ≤ C0)
    (hquad : ∀ ξ : ℂ, ξ ≠ 0 → |ξ.im| ≤ 3 / 2 →
      ‖Cvs.Detection.windowTransform L (cf f) ξ‖ ≤ C2 / ‖ξ‖ ^ 2)
    (lam a : ℝ) :
    Cvs.ZeroCounting.kernelZeroSide (Cvs.Detection.sqTransform L (cf f)) lam a
      = Cvs.WeilForm.SelfConvolutionFunctional.weilForm ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊
          (Set.indicator (Set.Ioc (0:ℝ) L) f) := by
  classical
  unfold Cvs.ZeroCounting.kernelZeroSide
  refine Cvs.Criterion.tsum_eq_of_formula_shape
    (summable_sqTransform_zeroSide₂ hC0 hC2 hplain hquad)
    Cvs.Criterion.height ?_
  intro ε hε
  have hpi : (0:ℝ) < π := Real.pi_pos
  obtain ⟨T₀, hT₀⟩ := weilForm_sub_zeroSum_lt₂ hL hfc h0 hLz hC0 hC2 hplain hquad (π * ε)
    (by positivity)
  refine ⟨T₀, fun T hT => ?_⟩
  obtain ⟨T', S, m, hTT', hzero, _hbox, hcov, hm, herr⟩ := hT₀ T hT
  refine ⟨T', hTT', S.subtype (· ∈ Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet),
    fun rho hrho => Cvs.Criterion.absorbing_transport hcov rho hrho, ?_⟩
  set F : ℂ → ℝ := fun z => (m z : ℝ)
    * (Cvs.Detection.sqTransform L (cf f) (-Complex.I * (z - 1 / 2))).re with hF
  have htrans : (∑ rho ∈ S.subtype (· ∈ Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet),
        (Cvs.Criterion.divisorWeight rho : ℝ)
          * (Cvs.Detection.sqTransform L (cf f) (Cvs.ZeroCounting.zPoint rho)).re)
      = ∑ rho ∈ S, F rho := by
    rw [← Cvs.Criterion.sum_transport hzero F]
    refine Finset.sum_congr rfl fun rho _ => ?_
    simp only [hF]
    rw [Cvs.Criterion.formula_weight_eq hm rho]
    rfl
  have hsum : (∑ ρ ∈ S, (m ρ : ℂ)
        * Cvs.Detection.sqTransform L (cf f) (-Complex.I * (ρ - 1 / 2))).re
      = ∑ ρ ∈ S, F ρ := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    simp only [hF]
    rw [show ((m ρ : ℂ)) = (((m ρ : ℕ) : ℝ) : ℂ) by push_cast; ring,
      Complex.re_ofReal_mul]
  rw [htrans, ← hsum]
  rw [abs_lt] at herr ⊢
  constructor
  · nlinarith [herr.1, hpi]
  · nlinarith [herr.2, hpi]

end Cvs.Zeta.ExplicitFormula.QuadraticDecayZeroSide
