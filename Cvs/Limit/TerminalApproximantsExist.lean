import Mathlib
import Cvs.Finite.WindowedModeSumDomain
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.EvenBottomAttained
import Cvs.WeilForm.FormBoundedBelowInfimum
import Cvs.WeilForm.ModeSumsFormDenseEven
import Cvs.WeilForm.Mollify.AeSymmetryEnough
import Cvs.WeilForm.Mollify.ComposedApproximant
import Cvs.WeilForm.Mollify.ContinuousApproximation
import Cvs.WeilForm.Mollify.MollifySmooth
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.WeilFormNullSets
import Cvs.WeilForm.WindowConstraintSet

/-!
# The terminal's approximants exist

    for every `ε > 0` there is an even-sector mode sum whose form is within `ε` of the bottom

so the sequence `an earlier result` quantifies over is not an empty promise.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Filter Cvs.Zeta.Explicit.Weil

namespace Cvs.Limit.TerminalApproximantsExist

variable {L : ℝ}

/-- **The composed approximants are smooth and symmetric.** -/
theorem exists_evenApprox (hL : 0 < L) (P R : ℕ) {η : ℝ → ℝ}
    (hη : η ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L) (hηm : Measurable η)
    (hsymm : (fun x : ℝ => η (L - x)) =ᵐ[(volume : Measure ℝ)] η) :
    ∃ Ξ : ℕ → ℝ → ℝ,
      (∀ n, Ξ n ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L) ∧
      (∀ n, ∀ x : ℝ, Ξ n (L - x) = Ξ n x) ∧
      (∀ n, ContDiff ℝ 2 (Ξ n)) ∧
      Filter.Tendsto (fun n : ℕ => Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Ξ n)) Filter.atTop
        (nhds (Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R η)) := by
  obtain ⟨Ξ, hmemΞ, _, _, hformΞ, hshape⟩ :=
    Cvs.WeilForm.Mollify.ContinuousApproximation.exists_windowApprox hL P R hη hηm
  refine ⟨Ξ, hmemΞ, ?_, ?_, hformΞ⟩
  · intro n x
    obtain ⟨c, m, hcm⟩ := hshape n
    rw [hcm]
    simp only
    rw [Cvs.WeilForm.Mollify.AeSymmetryEnough.pre_even_of_ae hL hsymm m x]
  · intro n
    obtain ⟨c, m, hcm⟩ := hshape n
    rw [hcm]
    exact contDiff_const.mul
      (Cvs.WeilForm.Mollify.MollifySmooth.contDiff_conv
        (Cvs.WeilForm.Mollify.ComposedApproximant.memLp_shifted hη.1 L m) (Cvs.WeilForm.Mollify.ComposedApproximant.shift_pos hL m))

/-- **An even-sector mode sum of nearly minimal form exists.** -/
theorem exists_modeSum_close (hL : 0 < L) (P R : ℕ) {lam : ℝ}
    (hlam : IsGLB (Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R ''
      Cvs.WeilForm.EvenBottomAttained.evenWindowSet L) lam) {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset ℕ) (a : ℕ → ℝ),
      Cvs.Finite.WindowedModeSumDomain.windowMode L s a ∈ Cvs.WeilForm.EvenBottomAttained.evenWindowSet L ∧
      |Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Cvs.Finite.WindowedModeSumDomain.windowMode L s a) - lam| < ε := by
  -- the minimiser, in a measurable representative
  obtain ⟨lam', η₀, hη₀, hlam', hη₀v⟩ := Cvs.WeilForm.FormBoundedBelowInfimum.exists_even_minimiser hL P R
  have hlameq : lam' = lam := IsGLB.unique hlam' hlam
  rw [hlameq] at hη₀v
  obtain ⟨η, hηwin, hηm, hη₀η, hηform⟩ :=
    Cvs.WeilForm.WeilFormNullSets.exists_measurable_rep P R hη₀.1
  have hηsymm : (fun x : ℝ => η (L - x)) =ᵐ[(volume : Measure ℝ)] η := by
    have hmp : QuasiMeasurePreserving (fun x : ℝ => L - x)
        (volume : Measure ℝ) (volume : Measure ℝ) :=
      (Measure.measurePreserving_sub_left (volume : Measure ℝ) L).quasiMeasurePreserving
    have h1 : (fun x : ℝ => η (L - x)) =ᵐ[(volume : Measure ℝ)] fun x : ℝ => η₀ (L - x) :=
      hmp.ae hη₀η.symm
    exact (h1.trans hη₀.2).trans hη₀η
  -- smooth even approximants of the minimiser
  obtain ⟨Ξ, hmemΞ, hsymΞ, hcdΞ, hformΞ⟩ := exists_evenApprox hL P R hηwin hηm hηsymm
  rw [hηform, hη₀v] at hformΞ
  obtain ⟨n, hn⟩ := Metric.tendsto_atTop.mp hformΞ (ε / 2) (by linarith)
  have hng := hn n le_rfl
  rw [Real.dist_eq] at hng
  -- mode sums of that approximant
  set g : ℝ → ℝ := Ξ n with hg
  have hgd : ∀ x : ℝ, HasDerivAt g (deriv g x) x := fun x =>
    ((hcdΞ n).differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hg'c : Continuous (deriv g) := (hcdΞ n).continuous_deriv (by norm_num)
  obtain ⟨S, A, hSmem, _, hSform⟩ := Cvs.WeilForm.ModeSumsFormDenseEven.exists_modeApprox hL P R
    hgd hg'c (hmemΞ n).2.1 (hsymΞ n) (hmemΞ n).2.2.1 (hmemΞ n).2.2.2
  obtain ⟨k, hk⟩ := Metric.tendsto_atTop.mp hSform (ε / 2) (by linarith)
  have hkg := hk k le_rfl
  rw [Real.dist_eq] at hkg
  refine ⟨S k, A k, hSmem k, ?_⟩
  have := abs_sub_abs_le_abs_sub
    (Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Cvs.Finite.WindowedModeSumDomain.windowMode L (S k) (A k)))
    (Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R g)
  calc |Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Cvs.Finite.WindowedModeSumDomain.windowMode L (S k) (A k)) - lam|
      ≤ |Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Cvs.Finite.WindowedModeSumDomain.windowMode L (S k) (A k))
          - Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R g|
        + |Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R g - lam| := by
        have := abs_sub_le
          (Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Cvs.Finite.WindowedModeSumDomain.windowMode L (S k) (A k)))
          (Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R g) lam
        exact this
    _ < ε := by rw [hg] at hng ⊢; linarith

end Cvs.Limit.TerminalApproximantsExist
