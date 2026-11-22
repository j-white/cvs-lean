import Mathlib
import Cvs.Finite.EvenMinimisers
import Cvs.Finite.EvenSectorZeroSide
import Cvs.Finite.OddEigenvectorResolvent
import Cvs.Finite.ParitySectorDefect
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.StepA.EvenBelowOdd
import Cvs.StepA.OddAboveDisplacement
import Cvs.Upstream.SymmetricMatrixBottom
import Cvs.WeilForm.ConcreteTestIdentification
import Cvs.WeilForm.CouplingAngle
import Cvs.WeilForm.MatrixPSDCriterion
import Cvs.WeilForm.MellinZeroSum
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Zeta.ExplicitFormula.CompactTestAdmissibility
import Cvs.Zeta.ExplicitFormula.CompactTestModulusSquared
import Cvs.Zeta.ExplicitFormula.HannWindowShifts
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.WeightedRateLemma
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroSideMoments

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# RH and step (a): under RH, `OddAbove` is the odd bottom's transform being nonzero at some zero ordinate, when `Ω_h` lies below every zero ordinate

Under RH every defect term is `m_ρ (Ω_h² − γ²)‖Ŵ_x(γ)‖² ≤ 0` when `Ω_h = |o|/|xdiv o|` lies below every
zero ordinate, and the odd form is `∑ m_ρ ‖Ŵ_o(γ)‖²`. So for an odd bottom eigenpair `(μ, o)` with
`Ω_h < |γ_ρ|` for every `ρ`: `OddAbove ↔ 0 < μ ↔ Ŵ_o(γ_ρ) ≠ 0` for some zero `ρ`.
-/

noncomputable section

open Matrix Real Cvs.Finite.SymmetricModeSet Cvs.Finite.OddEigenvectorResolvent Cvs.Finite.EvenMinimisers
open Cvs.StepA.OddAboveDisplacement Cvs.Finite.ParitySectorDefect Cvs.StepA.EvenBelowOdd Cvs.WeilForm.SelfConvolutionTransform

namespace Cvs.StepA.OddAboveUnderRH
open Cvs.ZeroCounting

variable {L : ℝ} {N : ℕ}

/-! ### The forms under RH -/

/-- **Under RH the even bottom is nonnegative.** -/
theorem evLam_nonneg_of_RH (hRH : RiemannHypothesis) (hL : 0 < L) (N : ℕ) :
    0 ≤ evLam ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L hL N := by
  obtain ⟨-, he1, -, heeig⟩ := evMin_spec ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ hL N
  have hpsd := Cvs.WeilForm.MatrixPSDCriterion.posSemidef_of_rh hRH hL (Cvs.WeilForm.ConcreteTestIdentification.le_ceil_exp L)
    (Cvs.WeilForm.ConcreteTestIdentification.le_ceil_log L) (mode_injective N) (negI_involutive N) (mode_negI N)
  have h := hpsd.dotProduct_mulVec_nonneg (evMin ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L hL N)
  rw [star_trivial, heeig, dotProduct_smul, smul_eq_mul, he1, mul_one] at h
  exact h

/-- On the critical line the zero-side term of a real test `f` is `m_ρ‖Ŵ_f(γ)‖²`. -/
theorem sqTerm_of_re (L : ℝ) (f : ℝ → ℝ) {rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet}
    (h : (rho : ℂ).re = 1 / 2) :
    (Cvs.Criterion.divisorWeight rho : ℝ)
        * (Cvs.Detection.sqTransform L (cf f) (Cvs.ZeroCounting.zPoint rho)).re
      = (Cvs.Criterion.divisorWeight rho : ℝ)
        * ‖Cvs.Detection.windowTransform L (cf f) (((rho : ℂ).im : ℝ) : ℂ)‖ ^ 2 := by
  rw [Cvs.ZeroCounting.zPoint_of_re_eq_half h]
  have hs := Cvs.Detection.sqTransform_real L f ((rho : ℂ).im)
  change Cvs.Detection.sqTransform L (cf _) _ = _ at hs
  rw [hs, Complex.ofReal_re]
  rfl

/-! ### The division vector under RH -/

/-- **Under RH the defect at `Ω_h²` is negative** when `Ω_h < |γ_ρ|` for every zero and the odd form is
positive: `Ω_h²·xᵀMx < oᵀMo`. -/
theorem omegaSq_mul_evenForm_lt_of_RH (hRH : RiemannHypothesis) (hL : 0 < L) {o : Idx N → ℝ}
    (hodd : ∀ i, o (negI N i) = -o i) (hpos : 0 < o ⬝ᵥ (MX L N *ᵥ o))
    (hΩ : ∀ rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet, omegaSq L N o < ((rho : ℂ).im) ^ 2) :
    omegaSq L N o * (xdiv L N o ⬝ᵥ (MX L N *ᵥ xdiv L N o)) < o ⬝ᵥ (MX L N *ᵥ o) := by
  have hre := Cvs.WeilForm.CouplingAngle.re_eq_half_of_rh hRH
  -- a zero at which the division vector's transform does not vanish
  obtain ⟨rho₀, hrho₀⟩ : ∃ rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet,
      Cvs.Detection.windowTransform L (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) (xdiv L N o)))
        (((rho : ℂ).im : ℝ) : ℂ) ≠ 0 := by
    by_contra hall
    push Not at hall
    have h0 : L * (o ⬝ᵥ (MX L N *ᵥ o)) = 0 := by
      rw [oddForm_zeroSide hL hodd]
      have : ∀ rho, bTerm L N o rho = 0 := fun rho => by rw [bTerm_of_re L N o (hre rho), hall rho]; simp
      exact (tsum_congr this).trans tsum_zero
    have : 0 < L * (o ⬝ᵥ (MX L N *ᵥ o)) := mul_pos hL hpos
    linarith
  have hle : ∀ rho, tTerm L N o (omegaSq L N o) rho ≤ (0 : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet → ℝ) rho := by
    intro rho
    rw [tTerm_of_re L N o _ (hre rho)]
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _)
      (mul_nonpos_of_nonpos_of_nonneg (by linarith [hΩ rho]) (sq_nonneg _))
  have hlt : tTerm L N o (omegaSq L N o) rho₀ < (0 : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet → ℝ) rho₀ := by
    rw [tTerm_of_re L N o _ (hre rho₀), Pi.zero_apply]
    have hw : (0 : ℝ) < (Cvs.Criterion.divisorWeight rho₀ : ℝ) := by
      exact_mod_cast Cvs.Criterion.one_le_divisorWeight rho₀
    exact mul_neg_of_pos_of_neg hw
      (mul_neg_of_neg_of_pos (by linarith [hΩ rho₀]) (pow_pos (norm_pos_iff.mpr hrho₀) 2))
  have hneg : ∑' rho, tTerm L N o (omegaSq L N o) rho < 0 := by
    have := hasSum_lt hle hlt (summable_tTerm hL hodd _).hasSum hasSum_zero
    exact (summable_tTerm hL hodd _).hasSum.tsum_eq ▸ this
  rw [← defect_eq hL hodd] at hneg
  have := (mul_neg_iff.mp hneg).resolve_right (fun h => by linarith [h.1])
  linarith [this.2]

/-! ### The even bottom under RH -/

/-- **Under RH the even bottom is strictly below the Rayleigh quotient of every odd vector with
positive form and `Ω_h` below every zero ordinate.** -/
theorem evLam_mul_lt_of_RH (hRH : RiemannHypothesis) (hL : 0 < L) {o : Idx N → ℝ}
    (hodd : ∀ i, o (negI N i) = -o i) (hpos : 0 < o ⬝ᵥ (MX L N *ᵥ o))
    (hΩ : ∀ rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet, omegaSq L N o < ((rho : ℂ).im) ^ 2) :
    evLam ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L hL N * (o ⬝ᵥ o) < o ⬝ᵥ (MX L N *ᵥ o) := by
  have hne : o ≠ 0 := by rintro rfl; simp at hpos
  obtain ⟨-, -, hemin, -⟩ := evMin_spec ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ hL N
  have hx := hemin (xdiv L N o) (xdiv_even hL N hodd)
  have hd := omegaSq_mul_evenForm_lt_of_RH hRH hL hodd hpos hΩ
  have ha := omegaSq_mul hL hodd hne
  have ha0 := omegaSq_nonneg L N o
  rw [← ha]
  nlinarith [mul_le_mul_of_nonneg_left hx ha0]

/-! ### Step (a) under RH -/

/-- **RH gives step (a)** from an odd bottom eigenpair `(μ, o)` with `0 < μ` and `Ω_h = |o|/|xdiv o|`
below every zero ordinate. -/
theorem oddAbove_of_RH (hRH : RiemannHypothesis) (hL : 0 < L) {μ : ℝ} {o : Idx N → ℝ}
    (hodd : ∀ i, o (negI N i) = -o i) (hne : o ≠ 0) (hMo : MX L N *ᵥ o = μ • o)
    (hbot : ∀ v : Idx N → ℝ, (∀ i, v (negI N i) = -v i) → μ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (MX L N *ᵥ v))
    (hμ : 0 < μ)
    (hΩ : ∀ rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet, omegaSq L N o < ((rho : ℂ).im) ^ 2) :
    OddAbove ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L hL N := by
  have ho : 0 < o ⬝ᵥ o := lt_of_le_of_ne (Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' o)
    (fun h => hne (dotProduct_self_eq_zero.mp h.symm))
  have hoo : o ⬝ᵥ (MX L N *ᵥ o) = μ * (o ⬝ᵥ o) := by rw [hMo, dotProduct_smul, smul_eq_mul]
  have h := evLam_mul_lt_of_RH hRH hL hodd (by rw [hoo]; positivity) hΩ
  rw [hoo] at h
  exact oddAbove_of_evLam_lt hL hbot (lt_of_mul_lt_mul_right h ho.le)

/-- A vector with `|o|² < c²·|xdiv o|²` is nonzero. -/
theorem ne_zero_of_lt_sq_mul {c : ℝ} {o : Idx N → ℝ}
    (hΩ : o ⬝ᵥ o < c ^ 2 * (xdiv L N o ⬝ᵥ xdiv L N o)) : o ≠ 0 := by
  rintro rfl
  rw [xdiv_zero] at hΩ
  simp at hΩ

/-- **Below a common gap** `0 ≤ c ≤ |γ_ρ|`, `|o|² < c²·|xdiv o|²` puts `Ω_h²` below every squared
zero ordinate. -/
theorem omegaSq_lt_of_gap (hL : 0 < L) {o : Idx N → ℝ} (hodd : ∀ i, o (negI N i) = -o i) {c : ℝ}
    (hc : 0 ≤ c) (hgap : ∀ rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet, c ≤ |(rho : ℂ).im|)
    (hΩ : o ⬝ᵥ o < c ^ 2 * (xdiv L N o ⬝ᵥ xdiv L N o))
    (rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet) : omegaSq L N o < ((rho : ℂ).im) ^ 2 := by
  have hc2 : c ^ 2 ≤ ((rho : ℂ).im) ^ 2 := by
    rw [← sq_abs ((rho : ℂ).im)]; exact pow_le_pow_left₀ hc (hgap rho) 2
  exact lt_of_lt_of_le ((omegaSq_lt_iff hL hodd (ne_zero_of_lt_sq_mul hΩ) _).mpr hΩ) hc2

/-- **Under RH, step (a) is the positivity of the odd bottom**, for an odd bottom eigenpair `(μ, o)`
with `Ω_h` below every zero ordinate. -/
theorem oddAbove_iff_pos_of_RH (hRH : RiemannHypothesis) (hL : 0 < L) {μ : ℝ} {o : Idx N → ℝ}
    (hodd : ∀ i, o (negI N i) = -o i) (hne : o ≠ 0) (hMo : MX L N *ᵥ o = μ • o)
    (hbot : ∀ v : Idx N → ℝ, (∀ i, v (negI N i) = -v i) → μ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (MX L N *ᵥ v))
    (hΩ : ∀ rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet, omegaSq L N o < ((rho : ℂ).im) ^ 2) :
    OddAbove ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L hL N ↔ 0 < μ :=
  ⟨fun h => lt_of_le_of_lt (evLam_nonneg_of_RH hRH hL N) (evLam_lt_of_oddAbove h hodd hne hMo),
    fun hμ => oddAbove_of_RH hRH hL hodd hne hMo hbot hμ hΩ⟩

end Cvs.StepA.OddAboveUnderRH
