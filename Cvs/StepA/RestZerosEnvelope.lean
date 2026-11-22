import Mathlib
import Cvs.Finite.SymmetricModeSet
import Cvs.StepA.ModePolynomialFarEnvelope
import Cvs.StepA.QuadrupleParitySectors
import Cvs.StepA.TopQuadruple
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
# The rest of the off-line zeros, bounded by the band-limited envelope

For any set `S` of zeros and `L > 0`, `∑'_S m_ρ pairE(ξ, z_ρ) ≥ −(∑'_S m_ρ envE(z_ρ))·L‖ξ‖²` and
`∑'_S m_ρ pairO(o, z_ρ) ≤ (∑'_S m_ρ envO(z_ρ))·L‖o‖²`. On `S = offLine ∖ quad σ` the two envelope sums
`restBE`, `restBO` are nonnegative rest bounds for the even and odd sectors around `quad σ`, so
`W·trialBound + restBO + onLineBound < W·lamE − restBE` makes `OddAbove` fail at `(L, N)`.
-/

noncomputable section

open Real MeasureTheory Matrix

namespace Cvs.StepA.RestZerosEnvelope
open Cvs.ZeroCounting

open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.Finite.SymmetricModeSet (Idx negI)
open Cvs.StepA.TopQuadruple (offLine quad quadWeight pairE pairO)
open Cvs.StepA.ModePolynomialFarEnvelope (envE envO)

/-! ### Any set of zeros -/

/-- For `L > 0`, every `ξ` and every set `S` of zeros,
`−(∑'_S m_ρ envE(L, N, z_ρ))·L‖ξ‖² ≤ ∑'_S m_ρ pairE(L, N, ξ, z_ρ)`. -/
theorem neg_tsum_envE_mul_le {L : ℝ} (hL : 0 < L) (N : ℕ) (ξ : Idx N → ℝ)
    (S : Set nonTrivialZeroSet) :
    -((∑' ρ : S, (Cvs.Criterion.divisorWeight ρ : ℝ) * envE L N (Cvs.ZeroCounting.zPoint ρ))
        * (L * (ξ ⬝ᵥ ξ)))
      ≤ ∑' ρ : S, (Cvs.Criterion.divisorWeight ρ : ℝ) * pairE L N ξ (Cvs.ZeroCounting.zPoint ρ) := by
  have hs1 : Summable fun ρ : S =>
      (Cvs.Criterion.divisorWeight ρ : ℝ) * envE L N (Cvs.ZeroCounting.zPoint ρ) :=
    (Cvs.StepA.ModePolynomialFarEnvelope.summable_envE hL N).subtype (· ∈ S)
  have hs2 : Summable fun ρ : S =>
      (Cvs.Criterion.divisorWeight ρ : ℝ) * pairE L N ξ (Cvs.ZeroCounting.zPoint ρ) :=
    (Cvs.StepA.QuadrupleParitySectors.summable_pairE hL N ξ).subtype (· ∈ S)
  rw [← tsum_mul_right, ← tsum_neg]
  refine Summable.tsum_le_tsum (fun ρ => ?_) (hs1.mul_right _).neg hs2
  have h : -(envE L N (Cvs.ZeroCounting.zPoint ρ) * (L * (ξ ⬝ᵥ ξ)))
      ≤ pairE L N ξ (Cvs.ZeroCounting.zPoint ρ) :=
    Cvs.StepA.ModePolynomialFarEnvelope.neg_envE_mul_le_sq_sub_sq hL N ξ _
  have hm : (0 : ℝ) ≤ (Cvs.Criterion.divisorWeight ρ : ℝ) := Nat.cast_nonneg _
  calc -((Cvs.Criterion.divisorWeight ρ : ℝ) * envE L N (Cvs.ZeroCounting.zPoint ρ)
          * (L * (ξ ⬝ᵥ ξ)))
      = (Cvs.Criterion.divisorWeight ρ : ℝ)
          * -(envE L N (Cvs.ZeroCounting.zPoint ρ) * (L * (ξ ⬝ᵥ ξ))) := by ring
    _ ≤ (Cvs.Criterion.divisorWeight ρ : ℝ) * pairE L N ξ (Cvs.ZeroCounting.zPoint ρ) :=
        mul_le_mul_of_nonneg_left h hm

/-- For `L > 0`, every `o` and every set `S` of zeros,
`∑'_S m_ρ pairO(L, N, o, z_ρ) ≤ (∑'_S m_ρ envO(L, N, z_ρ))·L‖o‖²`. -/
theorem tsum_pairO_le_tsum_envO_mul {L : ℝ} (hL : 0 < L) (N : ℕ) (o : Idx N → ℝ)
    (S : Set nonTrivialZeroSet) :
    ∑' ρ : S, (Cvs.Criterion.divisorWeight ρ : ℝ) * pairO L N o (Cvs.ZeroCounting.zPoint ρ)
      ≤ (∑' ρ : S, (Cvs.Criterion.divisorWeight ρ : ℝ) * envO L N (Cvs.ZeroCounting.zPoint ρ))
          * (L * (o ⬝ᵥ o)) := by
  have hs1 : Summable fun ρ : S =>
      (Cvs.Criterion.divisorWeight ρ : ℝ) * envO L N (Cvs.ZeroCounting.zPoint ρ) :=
    (Cvs.StepA.ModePolynomialFarEnvelope.summable_envO hL N).subtype (· ∈ S)
  have hs2 : Summable fun ρ : S =>
      (Cvs.Criterion.divisorWeight ρ : ℝ) * pairO L N o (Cvs.ZeroCounting.zPoint ρ) :=
    (Cvs.StepA.QuadrupleParitySectors.summable_pairO hL N o).subtype (· ∈ S)
  rw [← tsum_mul_right]
  refine Summable.tsum_le_tsum (fun ρ => ?_) hs2 (hs1.mul_right _)
  have h : pairO L N o (Cvs.ZeroCounting.zPoint ρ)
      ≤ envO L N (Cvs.ZeroCounting.zPoint ρ) * (L * (o ⬝ᵥ o)) :=
    Cvs.StepA.ModePolynomialFarEnvelope.sq_sub_sq_le_envO_mul hL N o _
  have hm : (0 : ℝ) ≤ (Cvs.Criterion.divisorWeight ρ : ℝ) := Nat.cast_nonneg _
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left h hm

/-! ### The rest of the zeros off the line -/

end Cvs.StepA.RestZerosEnvelope
