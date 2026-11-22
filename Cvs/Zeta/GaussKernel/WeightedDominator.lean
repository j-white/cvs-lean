import Mathlib
import Cvs.Zeta.CompletedZeroIndex
import Cvs.Zeta.ExplicitFormula.SquaredKernelFormula
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.DivisorWeightExpansion
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZetaZeroWindows

/-!
# The weighted dominator at the zeros
-/

namespace Cvs.Criterion

open Cvs.Zeta.GaussKernel.AdmissibleKernel Cvs.GaussKernel

/-- **The quartic sum at the divisor weight**, over the criterion's index. -/
theorem summable_divisorWeight_quartic :
    Summable fun rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet =>
      (Cvs.Criterion.divisorWeight rho : ℝ) * (1 / (1 + ((rho : ℂ).im) ^ 4)) := by
  have h := Cvs.Criterion.summable_weighted_of_sigma
    (g := fun rho : Cvs.Zeta.Explicit.Venue.nontrivialRiemannZetaZeros =>
      1 / (1 + ((Cvs.Zeta.Explicit.Venue.nontrivialZetaZeroValue rho).im) ^ 4))
    Cvs.Zeta.GaussKernel.AdmissibleKernel.summable_quartic_index
  rw [← Cvs.Criterion.zeroEquiv.summable_iff]
  refine h.congr fun rho => ?_
  simp only [Function.comp_apply, Cvs.Criterion.divisorWeight, Equiv.symm_apply_apply,
    Cvs.Criterion.coe_zeroEquiv]

/-- **The shifted bumps are quartically dominated.**  The constant depends on `a`, not on the
zero. -/
theorem bumps_le_quartic {lam₀ : ℝ} (hlam : 0 < lam₀) (a : ℝ) {γ δ : ℝ}
    (hδ : |δ| ≤ 1 / 2) :
    Real.exp (lam₀ * (δ ^ 2 - (γ - a) ^ 2)) + Real.exp (lam₀ * (δ ^ 2 - (γ + a) ^ 2))
        + 2 * Real.exp (lam₀ * (δ ^ 2 - γ ^ 2 - a ^ 2))
      ≤ (4 * Real.exp (lam₀ / 4 + lam₀ * a ^ 2) * (1 + 8 / lam₀ ^ 2))
          * (1 / (1 + γ ^ 4)) := by
  have hd : δ ^ 2 ≤ 1 / 4 := by nlinarith [abs_nonneg δ, sq_abs δ]
  have hQ := Cvs.Zeta.SquaredKernel.exp_neg_le_quartic hlam γ
  have hE : (0 : ℝ) < Real.exp (lam₀ / 4 + lam₀ * a ^ 2) := Real.exp_pos _
  -- each bump is below `E · e^{−λ₀γ²/2}`
  have key : ∀ u : ℝ, u ≤ lam₀ / 4 + lam₀ * a ^ 2 - lam₀ * γ ^ 2 / 2 →
      Real.exp u
        ≤ Real.exp (lam₀ / 4 + lam₀ * a ^ 2) * ((1 + 8 / lam₀ ^ 2) * (1 / (1 + γ ^ 4))) := by
    intro u hu
    calc Real.exp u ≤ Real.exp (lam₀ / 4 + lam₀ * a ^ 2 - lam₀ * γ ^ 2 / 2) :=
          Real.exp_le_exp.mpr hu
      _ = Real.exp (lam₀ / 4 + lam₀ * a ^ 2) * Real.exp (-(lam₀ * γ ^ 2 / 2)) := by
          rw [← Real.exp_add]; ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left hQ hE.le
  have h1 : lam₀ * (δ ^ 2 - (γ - a) ^ 2) ≤ lam₀ / 4 + lam₀ * a ^ 2 - lam₀ * γ ^ 2 / 2 := by
    nlinarith [sq_nonneg (γ - 2 * a), hlam.le]
  have h2 : lam₀ * (δ ^ 2 - (γ + a) ^ 2) ≤ lam₀ / 4 + lam₀ * a ^ 2 - lam₀ * γ ^ 2 / 2 := by
    nlinarith [sq_nonneg (γ + 2 * a), hlam.le]
  have h3 : lam₀ * (δ ^ 2 - γ ^ 2 - a ^ 2) ≤ lam₀ / 4 + lam₀ * a ^ 2 - lam₀ * γ ^ 2 / 2 := by
    nlinarith [sq_nonneg γ, sq_nonneg a, hlam.le]
  have b1 := key _ h1
  have b2 := key _ h2
  have b3 := key _ h3
  have hq0 : (0 : ℝ) ≤ (1 + 8 / lam₀ ^ 2) * (1 / (1 + γ ^ 4)) := by positivity
  nlinarith [hE, hq0]

/-- **The tail hypothesis of, at the divisor weight.** -/
theorem summable_weighted_bumps {lam₀ : ℝ} (hlam : 0 < lam₀) (a : ℝ) :
    Summable fun rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet => (Cvs.Criterion.divisorWeight rho : ℝ) *
      (Real.exp (lam₀ * ((del rho) ^ 2 - ((gam rho) - a) ^ 2))
        + Real.exp (lam₀ * ((del rho) ^ 2 - ((gam rho) + a) ^ 2))
        + 2 * Real.exp (lam₀ * ((del rho) ^ 2 - (gam rho) ^ 2 - a ^ 2))) := by
  refine Summable.of_nonneg_of_le (fun rho => by positivity) (fun rho => ?_)
    ((summable_divisorWeight_quartic).mul_left
      (4 * Real.exp (lam₀ / 4 + lam₀ * a ^ 2) * (1 + 8 / lam₀ ^ 2)))
  have hb := bumps_le_quartic hlam a (γ := gam rho) (δ := del rho) (del_bdd rho)
  have hw : (0 : ℝ) ≤ (Cvs.Criterion.divisorWeight rho : ℝ) := Nat.cast_nonneg _
  calc (Cvs.Criterion.divisorWeight rho : ℝ) *
        (Real.exp (lam₀ * ((del rho) ^ 2 - ((gam rho) - a) ^ 2))
          + Real.exp (lam₀ * ((del rho) ^ 2 - ((gam rho) + a) ^ 2))
          + 2 * Real.exp (lam₀ * ((del rho) ^ 2 - (gam rho) ^ 2 - a ^ 2)))
      ≤ (Cvs.Criterion.divisorWeight rho : ℝ) *
          ((4 * Real.exp (lam₀ / 4 + lam₀ * a ^ 2) * (1 + 8 / lam₀ ^ 2))
            * (1 / (1 + (gam rho) ^ 4))) := mul_le_mul_of_nonneg_left hb hw
    _ = (4 * Real.exp (lam₀ / 4 + lam₀ * a ^ 2) * (1 + 8 / lam₀ ^ 2))
          * ((Cvs.Criterion.divisorWeight rho : ℝ) * (1 / (1 + ((rho : ℂ).im) ^ 4))) := by
        rw [gam]; ring

end Cvs.Criterion
