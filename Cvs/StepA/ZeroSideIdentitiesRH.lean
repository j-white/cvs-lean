import Mathlib
import Cvs.Finite.DivisionVector
import Cvs.Finite.EvenSectorZeroSide
import Cvs.Finite.OddDivisionPolynomial
import Cvs.Finite.OddEigenvectorResolvent
import Cvs.Finite.OddSectorZeroSide
import Cvs.Finite.ParitySectorDefect
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.WeilForm.CouplingAngle
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Zeta.ExplicitFormula.ExponentialSumTransform
import Cvs.Zeta.ExplicitFormula.HannWindowShifts
import Cvs.Zeta.ExplicitFormula.WindowTransformByParts
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
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
# The two zero-side identities on `H_W` under RH

Under RH, for odd `v` with division vector `x`, `L·vᵀMv = ∑ m_ρ γ_ρ² ‖Ŵ_x(γ_ρ)‖²`, and when also
`ω·v = 0`, `L·(W²v)ᵀMv = ∑ m_ρ γ_ρ⁴ ‖Ŵ_x(γ_ρ)‖²`. So if `Ŵ_x` vanishes at every ordinate with
`γ² < Λ`, then `Λ·vᵀMv ≤ (W²v)ᵀMv`.
-/

noncomputable section

open Matrix Real

namespace Cvs.Finite.OddDisplacementPencil
open Cvs.ZeroCounting
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.Finite.SymmetricModeSet (Idx mode negI)
open Cvs.Finite.OddEigenvectorResolvent (xdiv om)
open Cvs.Finite.ParitySectorDefect (MX)

variable {L : ℝ} {N : ℕ}

/-- The window transform of the division vector of `v`, at the ordinate of `ρ`. -/
abbrev Wdiv (L : ℝ) (N : ℕ) (v : Idx N → ℝ) (ρ : nonTrivialZeroSet) : ℂ :=
  Cvs.Detection.windowTransform L
    (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) (xdiv L N v)))
    (((ρ : ℂ).im : ℝ) : ℂ)

/-- **The odd form over the zeros under RH**: `L·vᵀMv = ∑ m_ρ γ_ρ² ‖Ŵ_x(γ_ρ)‖²`. -/
theorem hasSum_zeroSide (hRH : RiemannHypothesis) (hL : 0 < L) {v : Idx N → ℝ}
    (hv : ∀ i, v (negI N i) = -v i) :
    HasSum (fun ρ : nonTrivialZeroSet =>
        (Cvs.Criterion.divisorWeight ρ : ℝ) * ((ρ : ℂ).im ^ 2 * ‖Wdiv L N v ρ‖ ^ 2))
      (L * (v ⬝ᵥ (MX L N *ᵥ v))) := by
  have hs := Cvs.Finite.ParitySectorDefect.summable_odd hL hv
  have he : (fun ρ : nonTrivialZeroSet =>
      (Cvs.Criterion.divisorWeight ρ : ℝ) * ((ρ : ℂ).im ^ 2 * ‖Wdiv L N v ρ‖ ^ 2))
      = Cvs.Finite.ParitySectorDefect.bTerm L N v := funext fun ρ =>
    (Cvs.Finite.ParitySectorDefect.bTerm_of_re L N v (Cvs.WeilForm.CouplingAngle.re_eq_half_of_rh hRH ρ)).symm
  rw [he, Cvs.Finite.ParitySectorDefect.oddForm_zeroSide hL hv]
  exact hs.hasSum

/-- `xdiv` is linear: `xdiv (u + c•v) = xdiv u + c•xdiv v`. -/
private theorem xdiv_add_smul (u v : Idx N → ℝ) (c : ℝ) :
    xdiv L N (u + c • v) = xdiv L N u + c • xdiv L N v := by
  funext i
  rcases i with _ | j
  · simp only [xdiv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_div, mul_div_assoc,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  · simp only [xdiv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_div, mul_div_assoc]

/-- For `ω·v = 0`, the division vector of `W²v` is `ω² ⊙ xdiv v`. -/
private theorem xdiv_om_sq_mul (hL : 0 < L) {v : Idx N → ℝ} (hη : om L N ⬝ᵥ v = 0) :
    xdiv L N (fun i => om L N i ^ 2 * v i) = fun i => om L N i ^ 2 * xdiv L N v i := by
  funext i
  rcases i with _ | j
  · have h := hη
    simp only [dotProduct, Fintype.sum_option, Cvs.Finite.OddEigenvectorResolvent.om_none, zero_mul,
      zero_add] at h
    have hs : ∀ k : Fin N × Bool, om L N (some k) ^ 2 * v (some k) / om L N (some k)
        = om L N (some k) * v (some k) := fun k => by
      field_simp [Cvs.Finite.OddEigenvectorResolvent.om_some_ne hL N k]
    simp only [xdiv, Cvs.Finite.OddEigenvectorResolvent.om_none, hs]
    rw [h]
    ring
  · simp only [xdiv, mul_div_assoc]

/-- The window transform of a cosine polynomial is linear in the coefficients. -/
private theorem windowTransform_cosPoly_add_smul (x y : Idx N → ℝ) (c : ℝ) (ξ : ℂ) :
    Cvs.Detection.windowTransform L
        (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) (x + c • y))) ξ
      = Cvs.Detection.windowTransform L
          (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) x)) ξ
        + (c : ℂ) * Cvs.Detection.windowTransform L
          (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) y)) ξ := by
  have hf : Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) (x + c • y))
      = fun s => Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) x) s
        + (c : ℂ) * Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) y) s := by
    funext s
    simp only [Cvs.WeilForm.SelfConvolutionTransform.cf, Cvs.Finite.EvenSectorZeroSide.cosPoly, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib, mul_assoc]
    push_cast
    rw [Finset.mul_sum]
  have hcx : Continuous (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) x)) :=
    Complex.continuous_ofReal.comp (Cvs.Finite.EvenSectorZeroSide.continuous_cosPoly L (mode N) x)
  have hcy : Continuous fun s =>
      (c : ℂ) * Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) y) s :=
    continuous_const.mul
      (Complex.continuous_ofReal.comp (Cvs.Finite.EvenSectorZeroSide.continuous_cosPoly L (mode N) y))
  rw [hf, Cvs.Detection.windowTransform_add L hcx hcy, Cvs.Detection.windowTransform_const_mul]

/-- For odd `v`, the transform of the cosine polynomial of `ω² ⊙ xdiv v` is `ξ²` times that of
`xdiv v`, at every `ξ ∈ ℂ` (two integrations by parts). -/
private theorem windowTransform_cosPoly_om_sq_mul (hL : 0 < L) {v : Idx N → ℝ}
    (hv : ∀ i, v (negI N i) = -v i) (ξ : ℂ) :
    Cvs.Detection.windowTransform L
        (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N)
          (fun i => om L N i ^ 2 * xdiv L N v i))) ξ
      = ξ ^ 2 * Cvs.Detection.windowTransform L
          (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) (xdiv L N v))) ξ := by
  set x := xdiv L N v with hx
  set g := Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N)
    (fun i => om L N i ^ 2 * x i)) with hg
  have h2 : Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.EvenSectorZeroSide.cosPoly'' L (mode N) x)
      = fun s => -g s := by
    funext s
    simp only [hg, Cvs.WeilForm.SelfConvolutionTransform.cf, Cvs.Finite.EvenSectorZeroSide.cosPoly'',
      Cvs.Finite.EvenSectorZeroSide.cosPoly, om]
    push_cast
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hd1 : ∀ s ∈ Set.uIcc (0 : ℝ) L,
      HasDerivAt (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) x))
        (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.EvenSectorZeroSide.cosPoly' L (mode N) x) s) s :=
    fun s _ => (Cvs.Finite.EvenSectorZeroSide.hasDerivAt_cosPoly L (mode N) x s).ofReal_comp
  have hd2 : ∀ s ∈ Set.uIcc (0 : ℝ) L,
      HasDerivAt (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.EvenSectorZeroSide.cosPoly' L (mode N) x))
        (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.EvenSectorZeroSide.cosPoly'' L (mode N) x) s) s :=
    fun s _ => (Cvs.Finite.EvenSectorZeroSide.hasDerivAt_cosPoly' L (mode N) x s).ofReal_comp
  have hc1 : Continuous (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.EvenSectorZeroSide.cosPoly' L (mode N) x)) :=
    Complex.continuous_ofReal.comp (Cvs.Finite.EvenSectorZeroSide.continuous_cosPoly' L (mode N) x)
  have hc2 : Continuous (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.EvenSectorZeroSide.cosPoly'' L (mode N) x)) :=
    Complex.continuous_ofReal.comp (Cvs.Finite.EvenSectorZeroSide.continuous_cosPoly'' L (mode N) x)
  have h0 : Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) x) 0 = 0 := by
    simp [Cvs.WeilForm.SelfConvolutionTransform.cf, hx, Cvs.Finite.DivisionVector.cosPoly_xdiv_zero]
  have hL0 : Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) x) L = 0 := by
    simp [Cvs.WeilForm.SelfConvolutionTransform.cf, hx, Cvs.Finite.DivisionVector.cosPoly_xdiv_L hL]
  have h0' : Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.EvenSectorZeroSide.cosPoly' L (mode N) x) 0 = 0 := by
    simp [Cvs.WeilForm.SelfConvolutionTransform.cf, Cvs.Finite.EvenSectorZeroSide.cosPoly']
  have hL' : Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.EvenSectorZeroSide.cosPoly' L (mode N) x) L = 0 := by
    simp [Cvs.WeilForm.SelfConvolutionTransform.cf, hx, Cvs.Finite.DivisionVector.cosPoly'_xdiv hL hv,
      Cvs.Finite.OddSectorZeroSide.sinePoly_L hL]
  have hneg : ∀ η : ℂ, Cvs.Detection.windowTransform L
      (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.EvenSectorZeroSide.cosPoly'' L (mode N) x)) η
        = -Cvs.Detection.windowTransform L g η := by
    intro η
    rw [h2]
    have := Cvs.Detection.windowTransform_const_mul L (-1) g η
    simpa using this
  rcases eq_or_ne ξ 0 with rfl | hξ
  · have h := Cvs.Finite.DivisionVector.windowTransform_zero_of_hasDerivAt hd2 hc2
    rw [h0', hL', sub_zero, hneg] at h
    rw [neg_eq_zero.mp h]
    ring
  · rw [Cvs.Detection.windowTransform_ibp_two hd1 hd2 hc1 hc2 h0 hL0 h0' hL' hξ, hneg]
    field_simp
    rw [Complex.I_sq]
    ring

/-- For odd `v ⊥ ω`, the division transform of `W²v + c•v` at `γ_ρ` is `(γ_ρ² + c)` times that
of `v`. -/
private theorem Wdiv_om_sq_add_smul (hL : 0 < L) {v : Idx N → ℝ}
    (hv : ∀ i, v (negI N i) = -v i) (hη : om L N ⬝ᵥ v = 0) (c : ℝ) (ρ : nonTrivialZeroSet) :
    Wdiv L N ((fun i => om L N i ^ 2 * v i) + c • v) ρ
      = ((((ρ : ℂ).im ^ 2 + c : ℝ)) : ℂ) * Wdiv L N v ρ := by
  simp only [Wdiv]
  rw [xdiv_add_smul, windowTransform_cosPoly_add_smul, xdiv_om_sq_mul hL hη,
    windowTransform_cosPoly_om_sq_mul hL hv]
  push_cast
  ring

-- H_fix Step 2 (`X_{W²g} = t² X_g` on `H_W`, with Cvs.Finite.ParitySectorDefect.oddForm_zeroSide and bTerm_of_re)
/-- **The `W²`-pencil over the zeros under RH**: for odd `v` with `ω·v = 0`,
`L·(W²v)ᵀMv = ∑ m_ρ γ_ρ⁴ ‖Ŵ_x(γ_ρ)‖²`. -/
theorem hasSum_W2_zeroSide (hRH : RiemannHypothesis) (hL : 0 < L) {v : Idx N → ℝ}
    (hv : ∀ i, v (negI N i) = -v i) (hη : om L N ⬝ᵥ v = 0) :
    HasSum (fun ρ : nonTrivialZeroSet =>
        (Cvs.Criterion.divisorWeight ρ : ℝ) * ((ρ : ℂ).im ^ 4 * ‖Wdiv L N v ρ‖ ^ 2))
      (L * ((fun i => om L N i ^ 2 * v i) ⬝ᵥ (MX L N *ᵥ v))) := by
  set u : Idx N → ℝ := fun i => om L N i ^ 2 * v i with hu
  have hu_odd : ∀ i, u (negI N i) = -u i := fun i => by simp only [hu, om_negI, hv]; ring
  have hw : ∀ c : ℝ, ∀ i, (u + c • v) (negI N i) = -(u + c • v) i := fun c i => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu_odd, hv]; ring
  have hp := hasSum_zeroSide hRH hL (hw 1)
  have hm := hasSum_zeroSide hRH hL (hw (-1))
  have hMT : (MX L N)ᵀ = MX L N := by
    ext i j
    rw [Matrix.transpose_apply]
    exact Cvs.Finite.TruncationQuadraticForm.M_symm hL _ _ (Cvs.Finite.SymmetricModeSet.mode_injective N) j i
  have hsymm : v ⬝ᵥ (MX L N *ᵥ u) = u ⬝ᵥ (MX L N *ᵥ v) := by
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hMT, dotProduct_comm]
  convert (hp.sub hm).div_const 4 using 1
  · funext ρ
    rw [Wdiv_om_sq_add_smul hL hv hη, Wdiv_om_sq_add_smul hL hv hη, norm_mul, norm_mul,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow,
      sq_abs, sq_abs]
    ring
  · simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_eq_mul, hsymm]
    ring

/-- **The deflation inequality under RH**: for odd `v ⊥ ω` whose division transform vanishes at
every ordinate with `γ² < Λ`, `Λ·vᵀMv ≤ (W²v)ᵀMv`. -/
theorem mul_dotProduct_le_of_vanish (hRH : RiemannHypothesis) (hL : 0 < L) {v : Idx N → ℝ}
    (hv : ∀ i, v (negI N i) = -v i) (hη : om L N ⬝ᵥ v = 0) {Λ : ℝ}
    (hvan : ∀ ρ : nonTrivialZeroSet, (ρ : ℂ).im ^ 2 < Λ → Wdiv L N v ρ = 0) :
    Λ * (v ⬝ᵥ (MX L N *ᵥ v)) ≤ (fun i => om L N i ^ 2 * v i) ⬝ᵥ (MX L N *ᵥ v) := by
  have h2 := (hasSum_zeroSide hRH hL hv).mul_left Λ
  have h4 := hasSum_W2_zeroSide hRH hL hv hη
  have hle := hasSum_le (fun ρ => ?_) h2 h4
  · have h' : L * (Λ * (v ⬝ᵥ (MX L N *ᵥ v)))
        ≤ L * ((fun i => om L N i ^ 2 * v i) ⬝ᵥ (MX L N *ᵥ v)) := by
      calc L * (Λ * (v ⬝ᵥ (MX L N *ᵥ v))) = Λ * (L * (v ⬝ᵥ (MX L N *ᵥ v))) := by ring
        _ ≤ _ := hle
    exact le_of_mul_le_mul_left h' hL
  · by_cases hρ : (ρ : ℂ).im ^ 2 < Λ
    · simp [hvan ρ hρ]
    · push Not at hρ
      have hm : 0 ≤ (Cvs.Criterion.divisorWeight ρ : ℝ) * ‖Wdiv L N v ρ‖ ^ 2 := by positivity
      calc Λ * ((Cvs.Criterion.divisorWeight ρ : ℝ) * ((ρ : ℂ).im ^ 2 * ‖Wdiv L N v ρ‖ ^ 2))
          = ((Cvs.Criterion.divisorWeight ρ : ℝ) * ‖Wdiv L N v ρ‖ ^ 2) * (Λ * (ρ : ℂ).im ^ 2) := by
            ring
        _ ≤ ((Cvs.Criterion.divisorWeight ρ : ℝ) * ‖Wdiv L N v ρ‖ ^ 2)
              * ((ρ : ℂ).im ^ 2 * (ρ : ℂ).im ^ 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hρ (sq_nonneg _)) hm
        _ = (Cvs.Criterion.divisorWeight ρ : ℝ) * ((ρ : ℂ).im ^ 4 * ‖Wdiv L N v ρ‖ ^ 2) := by ring

end Cvs.Finite.OddDisplacementPencil
