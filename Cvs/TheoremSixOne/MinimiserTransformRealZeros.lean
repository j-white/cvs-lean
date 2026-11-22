import Mathlib
import Cvs.Composition.SpineStepsAB
import Cvs.Finite.DiscreteTwoGap
import Cvs.Finite.DisplacementIdentity
import Cvs.Finite.DividedDifferenceCommutator
import Cvs.Finite.ModeSumFormDomain
import Cvs.Finite.PairFormDividedDifference
import Cvs.Finite.SecularRootsReal
import Cvs.Finite.ShiftedDiagonalSimplicity
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Limit.ConstantMinimiserLink
import Cvs.Limit.HurwitzRealZerosL2Limit
import Cvs.Limit.ModeSumsToMinimiser
import Cvs.Limit.OffAxesLimit
import Cvs.Limit.StepAZeroFreeMinimiser
import Cvs.StepA.StepAPredicate
import Cvs.Upstream.FourierLaplace
import Cvs.Upstream.Hurwitz
import Cvs.Upstream.SymmetricMatrixBottom
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.CentredWindowTranslate
import Cvs.WeilForm.EvenBottomAttained
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.FormSignInvariant
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.IsolationFromSimplicity
import Cvs.WeilForm.MinimisingSequenceConverges
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.TransformNowhereLocallyZero
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowConstraintSet
import Cvs.WeilForm.WindowReflectionSymmetry
import Cvs.WeilForm.WindowRepresentative

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Theorem 6.1 for `QW_λ`: under Step A every zero of the minimiser's transform is real

Connes' Theorem 6.1 (arXiv:2602.04022 §6.1, after Connes–van Suijlekom) applied to the truncated Weil
form: if its bottom is simple with even minimiser `η`, the Fourier transform of `η`, recentred to
`[−L/2, L/2]`, has only real zeros. The Hurwitz step and the secular step need only `Im z ≠ 0`.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real MeasureTheory Set Cvs.Zeta.Explicit.Weil Matrix Filter Topology

namespace Cvs.TheoremSixOne.MinimiserTransformRealZeros

/-- The plane off the real axis. -/
def nonReal : Set ℂ := {z : ℂ | z.im ≠ 0}

theorem isOpen_nonReal : IsOpen nonReal :=
  isOpen_compl_singleton.preimage Complex.continuous_im

theorem offAxes_subset_nonReal : Cvs.Limit.OffAxesLimit.offAxes ⊆ nonReal := fun _ hz => hz.2

/-- **Zero-freeness off the real axis survives the `L²` limit.** -/
theorem ne_zero_of_approx {L : ℝ} (hL : 0 < L) {ξ : ℝ → ℝ} {Ξ : ℕ → ℝ → ℝ}
    (hξ : MemLp ξ 2 (volume : Measure ℝ)) (hξs : ∀ s ∉ Set.Ioc (0:ℝ) L, ξ s = 0)
    (hξn : (∫ x : ℝ, ξ x ^ 2) = 1)
    (hΞ : ∀ k, MemLp (Ξ k) 2 (volume : Measure ℝ))
    (hΞs : ∀ k, ∀ s ∉ Set.Ioc (0:ℝ) L, Ξ k s = 0)
    (hfree : ∀ k, ∀ z ∈ nonReal,
      FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf (Ξ k)) z ≠ 0)
    (hconv : Tendsto (fun k => ∫ x : ℝ, (Ξ k x - ξ x) ^ 2) atTop (nhds 0)) :
    ∀ z ∈ nonReal, FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf ξ) z ≠ 0 := by
  intro z₀ hz₀
  refine Cvs.Upstream.Hurwitz.ne_zero_of_zeroFree_of_tendstoLocallyUniformlyOn
    isOpen_nonReal hz₀ (fun k => ?_) hfree ?_ ?_
  · have hint : Integrable (Ξ k) (volume : Measure ℝ) :=
      Cvs.WeilForm.CentredWindowTranslate.integrable_of_support hL.le (hΞ k) (hΞs k)
    exact (FourierLaplace.differentiable_fourierLaplace_of_integrable hint.ofReal
      (Cvs.WeilForm.TransformNowhereLocallyZero.hasCompactSupport_cf (hΞs k))).differentiableOn
  · exact (Cvs.Limit.HurwitzRealZerosL2Limit.tendstoLocallyUniformly_transforms hL.le hξ hΞ hξs hΞs
      hconv).mono (Set.subset_univ _)
  · exact Cvs.WeilForm.TransformNowhereLocallyZero.not_eventually_zero hL.le hξ hξs hξn z₀

section Finite

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open Cvs.Finite.DividedDifferenceCommutator Cvs.Finite.TruncationZeroFreeOffAxes in
/-- **A divided-difference truncation's transform is zero-free off the real axis**, for a
`ddMatrix` whose shifted bottom is a simple eigenvalue. -/
theorem zeroFree_nonReal {L : ℝ} (hL : 0 < L) {a b pos : ι → ℝ} {mode : ι → ℤ} {neg : ι → ι}
    {lam : ℝ} {xi : ι → ℝ}
    (hposinj : Function.Injective pos) (hinv : Function.Involutive neg)
    (hmode : ∀ i, mode (neg i) = -mode i) (hb : ∀ i, b (neg i) = -b i)
    (hxieven : ∀ i, xi (neg i) = xi i)
    (hpos : ∀ i, pos i = omega L mode i)
    (hQpsd : ∀ v : ι → ℝ, 0 ≤ v ⬝ᵥ (ddMatrix (Cvs.Finite.ShiftedDiagonalSimplicity.shiftDiag a lam) b pos *ᵥ v))
    (hQxi : ddMatrix (Cvs.Finite.ShiftedDiagonalSimplicity.shiftDiag a lam) b pos *ᵥ xi = 0)
    (hnorm : ∑ i, xi i = 1)
    (hkerline : ∀ v : ι → ℝ, ddMatrix a b pos *ᵥ v = lam • v → ∃ c : ℝ, v = c • xi)
    (hne : ∃ j, xi j * pos j ≠ 0) :
    ∀ z ∈ nonReal,
      FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf (modeSum L mode xi)) z ≠ 0 := by
  intro z him hzero
  have him : z.im ≠ 0 := him
  have hne0 : ∀ i, ((omega L mode i : ℝ) : ℂ) + z ≠ 0 := by
    intro i hc
    exact him (by simpa using congrArg Complex.im hc)
  rw [fourierLaplace_modeSum hL hinv hmode hxieven z hne0] at hzero
  have hpre : Complex.exp (Complex.I * z * (L : ℂ)) - 1 ≠ 0 :=
    sub_ne_zero.mpr (Cvs.Limit.ConstantMinimiserLink.exp_I_mul_ne_one hL him)
  have hsecular : ∑ i, (xi i : ℂ) / (((omega L mode i : ℝ) : ℂ) + z) = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd (div_eq_zero_iff.mp h |>.resolve_right Complex.I_ne_zero) hpre
    · exact h
  have hsum : ∑ j, (xi j : ℂ) / (((pos j : ℝ) : ℂ) - (-z)) = 0 := by
    rw [← hsecular]
    exact Finset.sum_congr rfl fun i _ => by rw [hpos i]; ring_nf
  have hroot := Cvs.Finite.SecularRootsReal.root_im_eq_zero hposinj hinv hb hxieven hQpsd hQxi hnorm
    ((Cvs.Finite.ShiftedDiagonalSimplicity.kerline_shift_iff a b pos lam xi).mpr hkerline) hne hsum
  exact him (by simpa using hroot)

end Finite

/-- **Step (a) at mode order `N`**: the discrete minimiser's transform is zero-free off the real
axis. -/
theorem zeroFree_of_stepA_N {L : ℝ} (hL : 0 < L) (P R : ℕ) {lam mu : ℝ}
    {η : Cvs.WeilForm.FormDomain.formDomain hL.le}
    (heven : Cvs.WeilForm.WindowReflectionSymmetry.reflD hL.le η = η)
    (hiso : ∀ v : Cvs.WeilForm.FormDomain.formDomain hL.le, (inner ℝ η v : ℝ) = 0 →
      mu * ‖v‖ ^ 2 ≤ Cvs.WeilForm.WindowRepresentative.weilQW P R (v : Cvs.WeilForm.WeilFormOnWindowL2.window L))
    (N : ℕ) (hlt : Cvs.Finite.SymmetricModeSet.lamD P R L hL N < mu)
    (hconst : Cvs.Finite.SymmetricModeSet.lamD P R L hL N
      < Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) none none)
    (hsum : ∑ i, Cvs.Finite.SymmetricModeSet.xiD P R L hL N i ≠ 0) :
    ∀ z ∈ nonReal,
      FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf
        (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (Cvs.Finite.SymmetricModeSet.mode N)
          (Cvs.Finite.SymmetricModeSet.xiD P R L hL N))) z ≠ 0 := by
  have _hlam : lam = lam := rfl
  obtain ⟨hxi1, hge, hxi⟩ := Cvs.Finite.SymmetricModeSet.xiD_spec P R L hL N
  set M := Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) with hM
  set xi := Cvs.Finite.SymmetricModeSet.xiD P R L hL N with hxidef
  set lamD := Cvs.Finite.SymmetricModeSet.lamD P R L hL N with hlamD
  have hinj := Cvs.Finite.SymmetricModeSet.mode_injective N
  have hinv := Cvs.Finite.SymmetricModeSet.negI_involutive N
  have hmode := Cvs.Finite.SymmetricModeSet.mode_negI N
  have hsymm := Cvs.Finite.TruncationQuadraticForm.M_symm hL P R hinj
  have hA := Cvs.Finite.TruncationQuadraticForm.M_neg_neg hL P R hinj hmode
  have hgap : ∀ o : Cvs.Finite.SymmetricModeSet.Idx N → ℝ,
      (∀ i, o (Cvs.Finite.SymmetricModeSet.negI N i) = -o i) → o ≠ 0 →
      lamD * (o ⬝ᵥ o) < o ⬝ᵥ (M *ᵥ o) := by
    intro o hodd hne
    have h1 := Cvs.Finite.DiscreteTwoGap.odd_gap_of_stepA hL P R (lam := lam) heven hiso hinj hinv
      hmode hodd
    have hpos : 0 < o ⬝ᵥ o := lt_of_le_of_ne (Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' o)
      (fun h => hne (dotProduct_self_eq_zero.mp h.symm))
    calc lamD * (o ⬝ᵥ o) < mu * (o ⬝ᵥ o) := mul_lt_mul_of_pos_right hlt hpos
      _ ≤ o ⬝ᵥ (M *ᵥ o) := h1
  have hxieven : ∀ i, xi (Cvs.Finite.SymmetricModeSet.negI N i) = xi i := by
    have ho := Cvs.Upstream.SymmetricMatrixBottom.oddPart_eq_zero_of_gap hsymm hinv hA hge hgap hxi
    intro i
    have := congrFun ho i
    simp only [Cvs.Finite.TruncationQuadraticForm.oddPart, Pi.zero_apply] at this
    linarith
  have hker : ∀ v, M *ᵥ v = lamD • v → ∃ c : ℝ, v = c • xi :=
    Cvs.Upstream.SymmetricMatrixBottom.kerline_of_even hsymm hinv hA hge hgap
      (Cvs.Finite.DiscreteTwoGap.even_kerline_of_stepA hL P R hiso hinj hinv hmode hlt hxi1 hxieven hxi)
  have hne : ∃ j, xi j * Cvs.Finite.TruncationZeroFreeOffAxes.omega L (Cvs.Finite.SymmetricModeSet.mode N) j ≠ 0 :=
    Cvs.Finite.DisplacementIdentity.xiD_ne hL P R N hconst
  set c : ℝ := (∑ i, xi i)⁻¹ with hc
  have hc0 : c ≠ 0 := inv_ne_zero hsum
  set xi' : Cvs.Finite.SymmetricModeSet.Idx N → ℝ := c • xi with hxi'
  have hnorm : ∑ i, xi' i = 1 := by
    simp only [hxi', Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    exact inv_mul_cancel₀ hsum
  have hxieven' : ∀ i, xi' (Cvs.Finite.SymmetricModeSet.negI N i) = xi' i := by
    intro i; simp only [hxi', Pi.smul_apply, hxieven i]
  have hQpsd : ∀ v : Cvs.Finite.SymmetricModeSet.Idx N → ℝ, 0 ≤ v ⬝ᵥ (Cvs.Finite.DividedDifferenceCommutator.ddMatrix
      (Cvs.Finite.ShiftedDiagonalSimplicity.shiftDiag
        (fun k => Cvs.Finite.PairFormDividedDifference.aval P R L (Cvs.Finite.SymmetricModeSet.mode N k)) lamD)
      (fun k => Cvs.Finite.PairFormDividedDifference.bval P R L (Cvs.Finite.SymmetricModeSet.mode N k))
      (Cvs.Finite.TruncationZeroFreeOffAxes.omega L (Cvs.Finite.SymmetricModeSet.mode N)) *ᵥ v) := by
    intro v
    rw [Cvs.Upstream.SymmetricMatrixBottom.dotProduct_shiftDiag]
    change 0 ≤ v ⬝ᵥ (M *ᵥ v) - lamD * (v ⬝ᵥ v)
    linarith [hge v]
  have hQxi : Cvs.Finite.DividedDifferenceCommutator.ddMatrix
      (Cvs.Finite.ShiftedDiagonalSimplicity.shiftDiag
        (fun k => Cvs.Finite.PairFormDividedDifference.aval P R L (Cvs.Finite.SymmetricModeSet.mode N k)) lamD)
      (fun k => Cvs.Finite.PairFormDividedDifference.bval P R L (Cvs.Finite.SymmetricModeSet.mode N k))
      (Cvs.Finite.TruncationZeroFreeOffAxes.omega L (Cvs.Finite.SymmetricModeSet.mode N)) *ᵥ xi' = 0 := by
    rw [Cvs.Upstream.SymmetricMatrixBottom.shiftDiag_mulVec_eq_zero_iff]
    change M *ᵥ xi' = lamD • xi'
    rw [hxi', Matrix.mulVec_smul, hxi, smul_comm]
  have hkerline' : ∀ v : Cvs.Finite.SymmetricModeSet.Idx N → ℝ, Cvs.Finite.DividedDifferenceCommutator.ddMatrix
      (fun k => Cvs.Finite.PairFormDividedDifference.aval P R L (Cvs.Finite.SymmetricModeSet.mode N k))
      (fun k => Cvs.Finite.PairFormDividedDifference.bval P R L (Cvs.Finite.SymmetricModeSet.mode N k))
      (Cvs.Finite.TruncationZeroFreeOffAxes.omega L (Cvs.Finite.SymmetricModeSet.mode N)) *ᵥ v = lamD • v →
      ∃ d : ℝ, v = d • xi' := by
    intro v hv
    obtain ⟨d, hd⟩ := hker v hv
    refine ⟨d * (∑ i, xi i), ?_⟩
    rw [hd, hxi', smul_smul, hc, mul_assoc, mul_inv_cancel₀ hsum, mul_one]
  have hne' : ∃ j, xi' j * Cvs.Finite.TruncationZeroFreeOffAxes.omega L (Cvs.Finite.SymmetricModeSet.mode N) j ≠ 0 := by
    obtain ⟨j, hj⟩ := hne
    refine ⟨j, ?_⟩
    simp only [hxi', Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact mul_ne_zero hc0 hj
  have hb : ∀ i, (fun k => Cvs.Finite.PairFormDividedDifference.bval P R L (Cvs.Finite.SymmetricModeSet.mode N k))
      (Cvs.Finite.SymmetricModeSet.negI N i)
      = -(fun k => Cvs.Finite.PairFormDividedDifference.bval P R L (Cvs.Finite.SymmetricModeSet.mode N k)) i := by
    intro i
    simp only []
    rw [hmode, Cvs.Finite.PairFormDividedDifference.bval_neg]
  have hz := zeroFree_nonReal hL (Cvs.Finite.DisplacementIdentity.omega_injective hL hinj) hinv hmode hb
    hxieven' (fun _ => rfl) hQpsd hQxi hnorm hkerline' hne'
  intro z hz'
  have h := hz z hz'
  rw [hxi', Cvs.Finite.ModeSumFormDomain.modeSum_smul, Cvs.Finite.DisplacementIdentity.fourierLaplace_cf_const_mul]
    at h
  exact (mul_ne_zero_iff.mp h).2

/-- **The normalised discrete minimiser's transform is zero-free off the real axis.** -/
theorem Xi_zeroFree {L : ℝ} (hL : 0 < L) (P R : ℕ) {lam mu : ℝ}
    {η : Cvs.WeilForm.FormDomain.formDomain hL.le}
    (heven : Cvs.WeilForm.WindowReflectionSymmetry.reflD hL.le η = η)
    (hiso : ∀ v : Cvs.WeilForm.FormDomain.formDomain hL.le, (inner ℝ η v : ℝ) = 0 →
      mu * ‖v‖ ^ 2 ≤ Cvs.WeilForm.WindowRepresentative.weilQW P R (v : Cvs.WeilForm.WeilFormOnWindowL2.window L))
    (N : ℕ) (hlt : Cvs.Finite.SymmetricModeSet.lamD P R L hL N < mu)
    (hconst : Cvs.Finite.SymmetricModeSet.lamD P R L hL N
      < Cvs.Finite.TruncationQuadraticForm.M P R L (Cvs.Finite.SymmetricModeSet.mode N) none none) :
    ∀ z ∈ nonReal,
      FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf
        (Cvs.Limit.StepAZeroFreeMinimiser.Xi P R L hL N)) z ≠ 0 := by
  intro z hz
  have h := zeroFree_of_stepA_N hL P R (lam := lam) heven hiso N hlt hconst
    (Cvs.Finite.DisplacementIdentity.sum_xiD_ne_zero hL P R (lam := lam) heven hiso N hlt hconst) z hz
  unfold Cvs.Limit.StepAZeroFreeMinimiser.Xi
  rw [Cvs.Finite.ModeSumFormDomain.modeSum_smul, Cvs.Finite.DisplacementIdentity.fourierLaplace_cf_const_mul]
  refine mul_ne_zero ?_ h
  exact_mod_cast inv_ne_zero (Real.sqrt_pos.mpr hL).ne'

/-- **Step (a) at a scale, minimiser not the constant**: the normalised minimiser's transform has
no zeros off the real axis. -/
theorem zeroFree_normRep_of_stepA_of_lt {L : ℝ} (hL : 0 < L) (P R : ℕ) {lam : ℝ}
    {η : Cvs.WeilForm.FormDomain.formDomain hL.le}
    (h : Cvs.StepA.StepAPredicate.StepA
      (fun v : Cvs.WeilForm.FormDomain.formDomain hL.le =>
        Cvs.WeilForm.WindowRepresentative.weilQW P R (v : Cvs.WeilForm.WeilFormOnWindowL2.window L))
      (Cvs.WeilForm.WindowReflectionSymmetry.reflD hL.le) lam η)
    (hc : lam < Cvs.Finite.PairFormDividedDifference.aval P R L 0) :
    ∀ z ∈ nonReal,
      FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf
        (Cvs.Limit.ModeSumsToMinimiser.normRep η)) z ≠ 0 := by
  obtain ⟨mu, hmu, hiso⟩ := h.isolated
  have hglb := Cvs.Limit.ModeSumsToMinimiser.isGLB_of_stepA hL P R h
  obtain ⟨N₀, hN₀⟩ := Cvs.Limit.StepAZeroFreeMinimiser.eventually_conditions hL P R hglb hmu hc
  have hbot : ∀ g ∈ Cvs.WeilForm.EvenBottomAttained.evenWindowSet L,
      lam ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R g :=
    fun g hg => hglb.1 ⟨g, hg, rfl⟩
  set Ξ : ℕ → ℝ → ℝ := fun k => Cvs.Limit.StepAZeroFreeMinimiser.Xi P R L hL (k + N₀) with hΞ
  have hΞmem : ∀ k, Ξ k ∈ Cvs.WeilForm.EvenBottomAttained.evenWindowSet L :=
    fun k => Cvs.Limit.StepAZeroFreeMinimiser.Xi_mem hL P R (lam := lam) h.even hiso _ (hN₀ _ (by omega)).1
  have hΞform : ∀ k, Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Ξ k)
      = Cvs.Finite.SymmetricModeSet.lamD P R L hL (k + N₀) :=
    fun k => Cvs.Limit.StepAZeroFreeMinimiser.weilForm_Xi hL P R (lam := lam) h.even hiso _
      (hN₀ _ (by omega)).1
  have htend : Tendsto (fun k => Cvs.Finite.SymmetricModeSet.lamD P R L hL (k + N₀)) atTop (𝓝 lam) := by
    rw [tendsto_order]
    constructor
    · intro a ha
      refine Filter.Eventually.of_forall fun k => lt_of_lt_of_le ha ?_
      exact Cvs.Finite.SymmetricModeSet.lam_le_lamD P R hL hbot _
        (Cvs.Finite.DisplacementIdentity.xiD_even hL P R (lam := lam) h.even hiso _ (hN₀ _ (by omega)).1)
    · intro b hb
      obtain ⟨N₁, hN₁⟩ := Cvs.Finite.SymmetricModeSet.lamD_lt_of_glb P R hL hglb (ε := b - lam)
        (by linarith)
      rw [Filter.eventually_atTop]
      refine ⟨N₁, fun k hk => ?_⟩
      have := hN₁ (k + N₀) (by omega)
      linarith
  have hΞv : Tendsto (fun k => Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Ξ k)) atTop (𝓝 lam) := by
    refine htend.congr fun k => ?_
    rw [hΞform]
  obtain ⟨φ, -, hconv⟩ := Cvs.WeilForm.MinimisingSequenceConverges.exists_subseq_tendsto_minimiser hL.le P R hglb
    hΞmem hΞv (Cvs.Limit.ModeSumsToMinimiser.unique_of_stepA hL P R h)
  have hξ := Cvs.Limit.ModeSumsToMinimiser.normRep_mem_evenWindowSet hL.le η h.nonzero h.even
  have hfree : ∀ k, ∀ z ∈ nonReal,
      FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf (Ξ (φ k))) z ≠ 0 :=
    fun k => Xi_zeroFree hL P R (lam := lam) h.even hiso _ (hN₀ _ (by omega)).1
      (hN₀ _ (by omega)).2
  rcases hconv with hconv | hconv
  · exact ne_zero_of_approx hL hξ.1.1 hξ.1.2.1 hξ.1.2.2.1
      (fun k => (hΞmem (φ k)).1.1) (fun k => (hΞmem (φ k)).1.2.1) hfree hconv
  · refine ne_zero_of_approx hL hξ.1.1 hξ.1.2.1 hξ.1.2.2.1
      (Ξ := fun k x => -Ξ (φ k) x) (fun k => (hΞmem (φ k)).1.1.neg)
      (fun k s hs => by simp only [(hΞmem (φ k)).1.2.1 s hs, neg_zero]) ?_ hconv
    intro k z hz
    rw [Cvs.WeilForm.FormSignInvariant.fourierLaplace_neg]
    exact neg_ne_zero.mpr (hfree k z hz)

/-- **The constant minimiser**: its transform has no zeros off the real axis. -/
theorem zeroFree_normRep_of_const {L : ℝ} (hL : 0 < L) (P R : ℕ) {lam : ℝ}
    {η : Cvs.WeilForm.FormDomain.formDomain hL.le}
    (h : Cvs.StepA.StepAPredicate.StepA
      (fun v : Cvs.WeilForm.FormDomain.formDomain hL.le =>
        Cvs.WeilForm.WindowRepresentative.weilQW P R (v : Cvs.WeilForm.WeilFormOnWindowL2.window L))
      (Cvs.WeilForm.WindowReflectionSymmetry.reflD hL.le) lam η)
    (hc : lam = Cvs.Finite.PairFormDividedDifference.aval P R L 0) :
    ∀ z ∈ nonReal,
      FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf
        (Cvs.Limit.ModeSumsToMinimiser.normRep η)) z ≠ 0 := by
  set g := Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (Cvs.Finite.SymmetricModeSet.mode 0)
    (Cvs.Limit.ConstantMinimiserLink.constVec (Real.sqrt L)⁻¹) with hg
  have hu := Cvs.Limit.ModeSumsToMinimiser.unique_of_stepA hL P R h g (Cvs.Limit.ConstantMinimiserLink.const_mem hL)
    (by rw [hg, Cvs.Limit.ConstantMinimiserLink.weilForm_const hL, hc])
  intro z hz
  have him : z.im ≠ 0 := hz
  have hz0 : z ≠ 0 := fun h0 => him (by rw [h0]; rfl)
  have hFL : FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf g) z ≠ 0 := by
    rw [hg, Cvs.Limit.ConstantMinimiserLink.fourierLaplace_const hL _ hz0]
    refine mul_ne_zero (div_ne_zero (sub_ne_zero.mpr (Cvs.Limit.ConstantMinimiserLink.exp_I_mul_ne_one hL him))
      Complex.I_ne_zero) (div_ne_zero ?_ hz0)
    exact_mod_cast inv_ne_zero (Real.sqrt_pos.mpr hL).ne'
  rcases hu with hae | hae
  · rw [← Cvs.Limit.ConstantMinimiserLink.fourierLaplace_cf_congr_ae hae z]; exact hFL
  · rw [Cvs.Limit.ConstantMinimiserLink.fourierLaplace_cf_congr_ae hae z,
      Cvs.WeilForm.FormSignInvariant.fourierLaplace_neg] at hFL
    exact fun h0 => hFL (by rw [h0, neg_zero])

/-- **Step (a) at a scale gives a minimiser transform with no zeros off the real axis.** -/
theorem zeroFree_normRep_of_stepA {L : ℝ} (hL : 0 < L) (P R : ℕ) {lam : ℝ}
    {η : Cvs.WeilForm.FormDomain.formDomain hL.le}
    (h : Cvs.StepA.StepAPredicate.StepA
      (fun v : Cvs.WeilForm.FormDomain.formDomain hL.le =>
        Cvs.WeilForm.WindowRepresentative.weilQW P R (v : Cvs.WeilForm.WeilFormOnWindowL2.window L))
      (Cvs.WeilForm.WindowReflectionSymmetry.reflD hL.le) lam η) :
    ∀ z ∈ nonReal,
      FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf
        (Cvs.Limit.ModeSumsToMinimiser.normRep η)) z ≠ 0 := by
  have hglb := Cvs.Limit.ModeSumsToMinimiser.isGLB_of_stepA hL P R h
  have hle : lam ≤ Cvs.Finite.PairFormDividedDifference.aval P R L 0 := by
    have := hglb.1 ⟨_, Cvs.Limit.ConstantMinimiserLink.const_mem hL, rfl⟩
    rwa [Cvs.Limit.ConstantMinimiserLink.weilForm_const hL] at this
  rcases hle.lt_or_eq with hlt | heq
  · exact zeroFree_normRep_of_stepA_of_lt hL P R h hlt
  · exact zeroFree_normRep_of_const hL P R h heq

/-- **Connes' Step A** for the truncated Weil form at scale `L`, as stated in §6.6: the bottom
`lam` of the form is attained at a nonzero `η`, it is simple, and its eigenvector is even. -/
structure ConnesStepA {L : ℝ} (hL : 0 < L) (P R : ℕ) (lam : ℝ)
    (η : Cvs.WeilForm.FormDomain.formDomain hL.le) : Prop where
  bottom : ∀ v : Cvs.WeilForm.FormDomain.formDomain hL.le,
    lam * ‖v‖ ^ 2 ≤ Cvs.WeilForm.WindowRepresentative.weilQW P R (v : Cvs.WeilForm.WeilFormOnWindowL2.window L)
  attains : Cvs.WeilForm.WindowRepresentative.weilQW P R (η : Cvs.WeilForm.WeilFormOnWindowL2.window L) = lam * ‖η‖ ^ 2
  nonzero : η ≠ 0
  simple : ∀ v : Cvs.WeilForm.FormDomain.formDomain hL.le,
    Cvs.WeilForm.WindowRepresentative.weilQW P R (v : Cvs.WeilForm.WeilFormOnWindowL2.window L) = lam * ‖v‖ ^ 2 →
      ∃ c : ℝ, v = c • η
  even : Cvs.WeilForm.WindowReflectionSymmetry.reflD hL.le η = η

/-- **Connes' Step A gives the isolated form**: a simple bottom of the truncated Weil form is
isolated. -/
theorem ConnesStepA.stepA {L : ℝ} {hL : 0 < L} {P R : ℕ} {lam : ℝ}
    {η : Cvs.WeilForm.FormDomain.formDomain hL.le} (h : ConnesStepA hL P R lam η) :
    Cvs.StepA.StepAPredicate.StepA
      (fun v : Cvs.WeilForm.FormDomain.formDomain hL.le =>
        Cvs.WeilForm.WindowRepresentative.weilQW P R (v : Cvs.WeilForm.WeilFormOnWindowL2.window L))
      (Cvs.WeilForm.WindowReflectionSymmetry.reflD hL.le) lam η := by
  obtain ⟨mu, hgap, hperp⟩ := Cvs.WeilForm.IsolationFromSimplicity.isolated_of_simple hL P R h.bottom h.nonzero
    h.simple
  exact Cvs.WeilForm.FormDomain.stepA_weil hL.le P R h.bottom h.attains h.nonzero h.simple hgap hperp
    h.even

/-- The minimiser recentred to `[−L/2, L/2]`, Connes' `θ_x` in the additive variable. -/
def centred {L : ℝ} (hL : 0 < L) (η : Cvs.WeilForm.FormDomain.formDomain hL.le) : ℝ → ℝ :=
  fun y => Cvs.Limit.ModeSumsToMinimiser.normRep η (y + L / 2)

/-- **Recentring multiplies the transform by a phase**: `θ̂(z) = e^{−izL/2} η̂(z)`. -/
theorem fourierLaplace_centred {L : ℝ} (hL : 0 < L) (η : Cvs.WeilForm.FormDomain.formDomain hL.le)
    (z : ℂ) :
    FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf (centred hL η)) z
      = Complex.exp (-(Complex.I * z * ((L / 2 : ℝ) : ℂ)))
        * FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf
          (Cvs.Limit.ModeSumsToMinimiser.normRep η)) z := by
  unfold FourierLaplace.fourierLaplace
  set f := Cvs.Limit.ModeSumsToMinimiser.normRep η
  have hshift := MeasureTheory.integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun t : ℝ => (Cvs.WeilForm.SelfConvolutionTransform.cf f t) *
      Complex.exp (Complex.I * z * ((t - L / 2 : ℝ) : ℂ))) (L / 2)
  simp only [add_sub_cancel_right] at hshift
  rw [← integral_const_mul]
  unfold centred
  simp only [Cvs.WeilForm.SelfConvolutionTransform.cf] at hshift ⊢
  rw [hshift]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only []
  rw [show Complex.I * z * ((t - L / 2 : ℝ) : ℂ)
      = Complex.I * z * (t : ℂ) + -(Complex.I * z * ((L / 2 : ℝ) : ℂ)) by push_cast; ring,
    Complex.exp_add]
  ring

/-- **Theorem 6.1 for `QW_λ`** (Connes, after Connes–van Suijlekom): under Step A, every zero of
the Fourier transform of the recentred minimiser is real. -/
theorem im_eq_zero_of_centred_eq_zero {L : ℝ} (hL : 0 < L) (P R : ℕ) {lam : ℝ}
    {η : Cvs.WeilForm.FormDomain.formDomain hL.le} (h : ConnesStepA hL P R lam η) {z : ℂ}
    (hz : FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf (centred hL η)) z = 0) :
    z.im = 0 := by
  by_contra him
  rw [fourierLaplace_centred hL η z] at hz
  exact (mul_ne_zero (Complex.exp_ne_zero _)
    (zeroFree_normRep_of_stepA hL P R h.stepA z him)) hz

/-- **Theorem 6.1 for `QW_λ`, uncentred form**: under Step A, every zero of the Fourier transform
of the normalised minimiser on `(0, L]` is real. -/
theorem im_eq_zero_of_transform_eq_zero {L : ℝ} (hL : 0 < L) (P R : ℕ) {lam : ℝ}
    {η : Cvs.WeilForm.FormDomain.formDomain hL.le} (h : ConnesStepA hL P R lam η) {z : ℂ}
    (hz : Cvs.Composition.SpineStepsAB.transform hL η z = 0) : z.im = 0 := by
  by_contra him
  exact zeroFree_normRep_of_stepA hL P R h.stepA z him hz

end Cvs.TheoremSixOne.MinimiserTransformRealZeros
