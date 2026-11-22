import Mathlib
import Cvs.Approximant.ConnesVectorFirstRung
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.Finite.CentredCosineNyquist
import Cvs.Finite.EvenSectorZeroSide
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Route.EigenvectorCoordinateCompression
import Cvs.Route.EvenBulkFloorSandwich
import Cvs.Route.GroundRouteJointGap
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.RungFlagConnesHyperplane
import Cvs.StepA.WindowGeneratorZeros
import Cvs.Upstream.SymmetricMatrixBottom
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.Zeta.ExplicitFormula.HannWindowShifts
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
# The graded residual of Connes' vector, exactly, by tails and by zeros

For even `ξ, η`, `L·ξᵀMη = ∑_ρ m_ρ Re(Φ_ξ(z_ρ)Φ_η(z_ρ))`, so `L⟪T y, z⟫` is the zero-side pairing of `y, z`. For even
`y`, `L√(α⬝α)⟪T v̂, y⟫ = −weilθ(τ, modeTest y) − QW(connesTruncError, modeMap y)`, `τ = connesTail x`. Hence the graded
residual `∑_{j≥2}⟪eⱼ,T v̂⟫²/gⱼ + ‖P_{R₁(N)ᗮ}T v̂‖²/b` equals these pairings on the rung flag and on the bulk part of `T v̂`.
-/

noncomputable section

open Real Matrix
open scoped InnerProductSpace

namespace Cvs.Route.ConnesGradedResidual
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet (Idx mode negI)
open Cvs.Route.GroundRouteJointGap (evenSub Meven)
open Cvs.Route.L1FloorFromBulkD0 (D0idx)
open Cvs.Approximant.ConnesVectorFirstRung (vhat)
open Cvs.Route.RungFlagConnesHyperplane (gradedDual gradedResid rungFlag)
open Cvs.Finite.CentredCosineNyquist (PhiC)
open Cvs.Finite.EvenSectorZeroSide (cosPoly)

/-! ### The zero side of the bilinear form -/

section ZeroSide

variable {ι : Type*} [Fintype ι]

/-- For reflection-even cosine polynomials, `W_ξ(z) W_η(−z) = Φ_ξ(z) Φ_η(z)` at every `z ∈ ℂ`. -/
theorem windowTransform_mul_neg_eq_PhiC_mul (L : ℝ) (mode : ι → ℤ) (ξ η : ι → ℝ) (z : ℂ) :
    Cvs.Detection.windowTransform L (Cvs.WeilForm.SelfConvolutionTransform.cf (cosPoly L mode ξ)) z
        * Cvs.Detection.windowTransform L (Cvs.WeilForm.SelfConvolutionTransform.cf (cosPoly L mode η)) (-z)
      = PhiC L (cosPoly L mode ξ) z * PhiC L (cosPoly L mode η) z := by
  have h1 := Cvs.Finite.CentredCosineNyquist.PhiC_eq_windowTransform (Cvs.Finite.CentredCosineNyquist.cosPoly_reflect L mode ξ)
    ((Cvs.Finite.EvenSectorZeroSide.continuous_cosPoly L mode ξ).intervalIntegrable 0 L) z
  have h2 := Cvs.Finite.CentredCosineNyquist.PhiC_eq_windowTransform (Cvs.Finite.CentredCosineNyquist.cosPoly_reflect L mode η)
    ((Cvs.Finite.EvenSectorZeroSide.continuous_cosPoly L mode η).intervalIntegrable 0 L) (-z)
  rw [Cvs.Finite.CentredCosineNyquist.PhiC_neg] at h2
  have he : Complex.exp (z * ((L : ℂ) / 2) * Complex.I) * Complex.exp (-z * ((L : ℂ) / 2) * Complex.I) = 1 := by
    rw [← Complex.exp_add, show z * ((L : ℂ) / 2) * Complex.I + -z * ((L : ℂ) / 2) * Complex.I = 0 by ring,
      Complex.exp_zero]
  rw [h1, h2]
  linear_combination (-(Cvs.Detection.windowTransform L (Cvs.WeilForm.SelfConvolutionTransform.cf (cosPoly L mode ξ)) z
    * Cvs.Detection.windowTransform L (Cvs.WeilForm.SelfConvolutionTransform.cf (cosPoly L mode η)) (-z))) * he

/-- **The bilinear form is the zero-side pairing**: for reflection-even `ξ, η`,
`L·ξᵀMη = ∑_ρ m_ρ Re(Φ_ξ(z_ρ) Φ_η(z_ρ))`. -/
theorem bilin_eq_zeroSide [DecidableEq ι] {L : ℝ} (hL : 0 < L) {mode : ι → ℤ}
    (hinj : Function.Injective mode) {neg : ι → ι} (hinv : Function.Involutive neg)
    (hmode : ∀ i, mode (neg i) = -mode i) {ξ η : ι → ℝ} (hξ : ∀ i, ξ (neg i) = ξ i)
    (hη : ∀ i, η (neg i) = η i) :
    L * (ξ ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L mode *ᵥ η))
      = ∑' rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet, (Cvs.Criterion.divisorWeight rho : ℝ)
          * (PhiC L (cosPoly L mode ξ) (Cvs.ZeroCounting.zPoint rho)
            * PhiC L (cosPoly L mode η) (Cvs.ZeroCounting.zPoint rho)).re := by
  have h := Cvs.StepA.WindowGeneratorZeros.two_mul_bilinear_eq_zeroSide hL hinj hinv hmode hξ hη
  have hre : ∀ a b : ℂ, (a * b + b * a).re = 2 * (a * b).re := fun a b => by
    rw [mul_comm b a, Complex.add_re]; ring
  simp only [windowTransform_mul_neg_eq_PhiC_mul, hre] at h
  have h2 : ∀ rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet, (Cvs.Criterion.divisorWeight rho : ℝ)
      * (2 * (PhiC L (cosPoly L mode ξ) (Cvs.ZeroCounting.zPoint rho)
        * PhiC L (cosPoly L mode η) (Cvs.ZeroCounting.zPoint rho)).re)
      = 2 * ((Cvs.Criterion.divisorWeight rho : ℝ) * (PhiC L (cosPoly L mode ξ) (Cvs.ZeroCounting.zPoint rho)
        * PhiC L (cosPoly L mode η) (Cvs.ZeroCounting.zPoint rho)).re) := fun rho => by ring
  rw [tsum_congr h2, tsum_mul_left] at h
  linarith

end ZeroSide

/-! ### The window form at truncation `N` -/

section Window

variable {x : ℕ}

/-- **The window form over the zeros**: `L⟪T y, z⟫ = ∑_ρ m_ρ Re(Φ_y(z_ρ) Φ_z(z_ρ))` on the even sector. -/
theorem inner_formN_eq_zeroSide (hx1 : (1 : ℝ) < x) (N : ℕ) (y z : evenSub N) :
    Real.log x * ⟪Cvs.Route.EvenBulkFloorSandwich.formN hx1 N y, z⟫_ℝ
      = ∑' rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet, (Cvs.Criterion.divisorWeight rho : ℝ)
          * (PhiC (Real.log x) (cosPoly (Real.log x) (mode N) (WithLp.ofLp (y : EuclideanSpace ℝ (Idx N))))
              (Cvs.ZeroCounting.zPoint rho)
            * PhiC (Real.log x) (cosPoly (Real.log x) (mode N) (WithLp.ofLp (z : EuclideanSpace ℝ (Idx N))))
              (Cvs.ZeroCounting.zPoint rho)).re := by
  have hx0 : 0 < x := by exact_mod_cast zero_lt_one.trans hx1
  have hL := Real.log_pos hx1
  have h := bilin_eq_zeroSide hL (Cvs.Finite.SymmetricModeSet.mode_injective N)
    (Cvs.Finite.SymmetricModeSet.negI_involutive N) (Cvs.Finite.SymmetricModeSet.mode_negI N) y.2 z.2
  have hM : Cvs.Finite.TruncationQuadraticForm.M ⌈Real.exp (Real.log x)⌉₊ ⌈Real.log x / Real.log 2⌉₊ (Real.log x) (mode N)
      = Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x) (mode N) :=
    Cvs.Route.EigenvectorCoordinateCompression.MX_log_natCast hx0 N
  rw [hM] at h
  rw [Cvs.Route.GroundRouteJointGap.inner_evenSub, Cvs.Route.GroundRouteJointGap.ofLp_Meven, dotProduct_comm (Cvs.Finite.TruncationQuadraticForm.M _ _ _ _ *ᵥ _),
    Cvs.Upstream.SymmetricMatrixBottom.dotProduct_mulVec_comm
      (Cvs.Finite.TruncationQuadraticForm.M_symm hL _ _ (Cvs.Finite.SymmetricModeSet.mode_injective N)), h]

/-- Connes' column: `−weilθ(connesTail x, modeTest y) − QW(connesTruncError, modeMap y)` for `y` in the even sector. -/
def connesCol (hx : 80 ≤ 2 * π * x) (N : ℕ) (y : evenSub N) : ℝ :=
  -Cvs.WeilForm.ThetaSpaceParseval.weilθ (Cvs.Approximant.CosineColumnTailPairing.connesTail x) (Cvs.Approximant.CosineColumnTailPairing.modeTest x N (WithLp.ofLp (y : EuclideanSpace ℝ (Idx N))))
    - Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x) (Cvs.Approximant.CosineColumnTailPairing.connesTruncError hx N)
      (Cvs.Approximant.CosineColumnTailPairing.modeMap (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N (WithLp.ofLp (y : EuclideanSpace ℝ (Idx N))))

/-- **Connes' column in tail form**: `L√(α⬝α)⟪T v̂, y⟫ = connesCol y`, `α = connesCoef x N ≠ 0`. -/
theorem inner_formN_vhat_eq_connesCol (hx : 80 ≤ 2 * π * x) (N : ℕ)
    (hs : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) (y : evenSub N) :
    Real.log x * √(Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N)
        * ⟪Cvs.Route.EvenBulkFloorSandwich.formN (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N (vhat x N), y⟫_ℝ = connesCol hx N y := by
  have hx1 := Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx
  have hL := Real.log_pos hx1
  have hq : 0 < √(Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N) :=
    Real.sqrt_pos.2 (lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg _) (Ne.symm hs))
  have hcol := Cvs.Approximant.CosineColumnTailPairing.connes_column_eq_tail_truncation hx N _ y.2
  have hv : WithLp.ofLp ((vhat x N : evenSub N) : EuclideanSpace ℝ (Idx N))
      = (√(Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N))⁻¹ • Cvs.Approximant.ConnesVectorRealScale.connesCoef x N := by
    show Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x = _
    unfold Cvs.Approximant.ConnesVectorRealScale.connesVec
    simp only [if_neg hs]
  rw [Cvs.Route.GroundRouteJointGap.inner_evenSub, Cvs.Route.GroundRouteJointGap.ofLp_Meven, dotProduct_comm (Cvs.Finite.TruncationQuadraticForm.M _ _ _ _ *ᵥ _),
    Cvs.Upstream.SymmetricMatrixBottom.dotProduct_mulVec_comm
      (Cvs.Finite.TruncationQuadraticForm.M_symm hL _ _ (Cvs.Finite.SymmetricModeSet.mode_injective N)), hv, smul_dotProduct,
    smul_eq_mul, connesCol, ← hcol]
  field_simp

private theorem norm_sq_starProjection_eq_inner {N : ℕ} (K : Submodule ℝ (evenSub N)) [K.HasOrthogonalProjection]
    (u : evenSub N) : ‖K.starProjection u‖ ^ 2 = ⟪u, K.starProjection u⟫_ℝ := by
  rw [← real_inner_self_eq_norm_sq, Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem u)]

/-- **The graded residual in tail form**: with `ℓ = L√(α⬝α)`, `ℓ²·R = ∑_{j≥2} connesCol(eⱼ)²/gⱼ + ℓ·connesCol(P T v̂)/b`,
`P = P_{R₁(N)ᗮ}`. -/
theorem gradedResid_eq_connesCol (hx : 80 ≤ 2 * π * x) (N : ℕ)
    (hs : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) (g : Cvs.Approximant.SpineSubspace.SF x → ℝ) (b : ℝ) :
    (Real.log x * √(Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N)) ^ 2
        * gradedResid (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N g b
      = ∑ j : D0idx x, connesCol hx N (rungFlag x N j.1) ^ 2 / g j.1
        + Real.log x * √(Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N)
          * connesCol hx N ((Cvs.Route.EvenBulkFloorSandwich.R1N x N)ᗮ.starProjection
            (Cvs.Route.EvenBulkFloorSandwich.formN (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N (vhat x N))) / b := by
  set ℓ := Real.log x * √(Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N)
  set u := Cvs.Route.EvenBulkFloorSandwich.formN (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N (vhat x N)
  have hc := inner_formN_vhat_eq_connesCol hx N hs
  unfold gradedResid gradedDual
  rw [norm_sq_starProjection_eq_inner, ← hc, mul_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hc, real_inner_comm]
    ring
  · ring

/-- **The graded residual over the zeros**: `L²·R = ∑_{j≥2} Z(eⱼ)²/gⱼ + L·Z(P T v̂)/b`, `Z(y) = ∑_ρ m_ρ Re(Φ_{v̂}Φ_y)(z_ρ)`
and `P = P_{R₁(N)ᗮ}`. -/
theorem gradedResid_eq_zeroSide (hx1 : (1 : ℝ) < x) (N : ℕ) (g : Cvs.Approximant.SpineSubspace.SF x → ℝ) (b : ℝ) :
    Real.log x ^ 2 * gradedResid hx1 N g b
      = ∑ j : D0idx x, (∑' rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet, (Cvs.Criterion.divisorWeight rho : ℝ)
            * (PhiC (Real.log x) (cosPoly (Real.log x) (mode N)
                (WithLp.ofLp ((vhat x N : evenSub N) : EuclideanSpace ℝ (Idx N)))) (Cvs.ZeroCounting.zPoint rho)
              * PhiC (Real.log x) (cosPoly (Real.log x) (mode N)
                (WithLp.ofLp ((rungFlag x N j.1 : evenSub N) : EuclideanSpace ℝ (Idx N))))
                  (Cvs.ZeroCounting.zPoint rho)).re) ^ 2 / g j.1
        + Real.log x * (∑' rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet, (Cvs.Criterion.divisorWeight rho : ℝ)
            * (PhiC (Real.log x) (cosPoly (Real.log x) (mode N)
                (WithLp.ofLp ((vhat x N : evenSub N) : EuclideanSpace ℝ (Idx N)))) (Cvs.ZeroCounting.zPoint rho)
              * PhiC (Real.log x) (cosPoly (Real.log x) (mode N)
                (WithLp.ofLp (((Cvs.Route.EvenBulkFloorSandwich.R1N x N)ᗮ.starProjection (Cvs.Route.EvenBulkFloorSandwich.formN hx1 N (vhat x N)) : evenSub N) :
                  EuclideanSpace ℝ (Idx N)))) (Cvs.ZeroCounting.zPoint rho)).re) / b := by
  have hz := inner_formN_eq_zeroSide hx1 N (vhat x N)
  unfold gradedResid gradedDual
  rw [norm_sq_starProjection_eq_inner, ← hz, mul_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hz, real_inner_comm]
    ring
  · ring

end Window

end Cvs.Route.ConnesGradedResidual
