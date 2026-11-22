import Mathlib
import Cvs.Finite.DiscreteStepACertificate
import Cvs.Finite.ModeSumFormDomain
import Cvs.Finite.ModeSumPairValues
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Limit.OffAxesLimit
import Cvs.Limit.ZeroFreeApproximantsRH
import Cvs.Upstream.FourierLaplace
import Cvs.WeilForm.CentredWindowTranslate
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.TransformNowhereLocallyZero

/-!
# The discrete spine: finite certificates along a sequence and discrete step (b) give RH
Every mode-sum transform is entire (`differentiable_modeSum`). If at each scale `L n` and mode
count `N n` the CvS matrix admits `Cvs.Finite.DiscreteStepACertificate`'s finite certificate, the discrete minimisers'
transforms are zero-free off the axes; if a nonzero rescaling of them converges locally
uniformly to `Ξ`, `Cvs.Limit.ZeroFreeApproximantsRH` gives RH (`riemannHypothesis_of_discrete`). Step (a) enters only
through finite matrix inequalities.
-/

noncomputable section

open Real Matrix Filter Topology MeasureTheory

namespace Cvs.Limit.DiscreteSpine

/-- **The transform of any mode sum is entire.** -/
theorem differentiable_modeSum {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 < L) (mode : ι → ℤ)
    (xi : ι → ℝ) :
    Differentiable ℂ (FourierLaplace.fourierLaplace
      (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi))) := by
  have hsupp : ∀ s ∉ Set.Ioc (0:ℝ) L, Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi s = 0 :=
    fun s hs => Cvs.Finite.ModeSumPairValues.modeSum_eq_zero_of_notMem L mode xi hs
  have hmem : MemLp (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi) 2 (MeasureTheory.volume) :=
    Cvs.Finite.ModeSumFormDomain.memLp_two_of_bounded (Cvs.Finite.ModeSumPairValues.measurable_modeSum L mode xi)
      (Cvs.Finite.ModeSumPairValues.abs_modeSum_le L mode xi) (fun s hs => hsupp s hs)
  have hint := Cvs.WeilForm.CentredWindowTranslate.integrable_of_support hL.le hmem hsupp
  exact FourierLaplace.differentiable_fourierLaplace_of_integrable hint.ofReal
    (Cvs.WeilForm.TransformNowhereLocallyZero.hasCompactSupport_cf hsupp)

open Cvs.Finite.SymmetricModeSet in
/-- The finite certificate of discrete step (a) at scale `L`, primes `P`, powers `R`, `N` modes. -/
def Cert (P R : ℕ) (L : ℝ) (N : ℕ) : Prop :=
  ∃ (w : Idx N → ℝ) (t : ℝ),
    w ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ w) < t * (w ⬝ᵥ w)
    ∧ (∀ o : Idx N → ℝ, (∀ i, o (negI N i) = -o i) →
        t * (o ⬝ᵥ o) ≤ o ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ o))
    ∧ (∀ v : Idx N → ℝ, (∀ i, v (negI N i) = v i) → v ⬝ᵥ w = 0 →
        t * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v))
    ∧ t ≤ Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) none none

/-- The discrete minimiser's transform at a scale. -/
def dtransform (P R : ℕ) {L : ℝ} (hL : 0 < L) (N : ℕ) : ℂ → ℂ :=
  FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf
    (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (Cvs.Finite.SymmetricModeSet.mode N)
      (Cvs.Finite.SymmetricModeSet.xiD P R L hL N)))

/-- **Zero-freeness from the certificate.** -/
theorem dtransform_ne_zero {P R : ℕ} {L : ℝ} (hL : 0 < L) {N : ℕ} (h : Cert P R L N) :
    ∀ z ∈ Cvs.Limit.OffAxesLimit.offAxes, dtransform P R hL N z ≠ 0 := by
  obtain ⟨w, t, hw, hodd, hperp, hconst⟩ := h
  exact Cvs.Finite.DiscreteStepACertificate.zeroFree_of_cert hL P R N hw hodd hperp hconst

/-- **The discrete spine.** Finite certificates at every scale of a sequence, and a nonzero
rescaling of the discrete transforms converging locally uniformly to `Ξ`, give RH. -/
theorem riemannHypothesis_of_discrete {L : ℕ → ℝ} (hL : ∀ n, 0 < L n) (P R N : ℕ → ℕ)
    (hcert : ∀ n, Cert (P n) (R n) (L n) (N n))
    (hB : ∃ c : ℕ → ℂ, (∀ n, c n ≠ 0) ∧
      TendstoLocallyUniformlyOn (fun n z => c n * dtransform (P n) (R n) (hL n) (N n) z)
        Cvs.Limit.ZeroFreeApproximantsRH.Xi atTop (Set.univ : Set ℂ)) :
    RiemannHypothesis := by
  obtain ⟨c, hc, hconv⟩ := hB
  refine Cvs.Limit.ZeroFreeApproximantsRH.riemannHypothesis_of_convergence'
    (fun n z => c n * dtransform (P n) (R n) (hL n) (N n) z) (fun n => ?_) (fun n z hz => ?_) hconv
  · exact (differentiable_const (c n)).mul (differentiable_modeSum (hL n) _ _)
  · exact mul_ne_zero (hc n) (dtransform_ne_zero (hL n) (hcert n) z hz)

end Cvs.Limit.DiscreteSpine
