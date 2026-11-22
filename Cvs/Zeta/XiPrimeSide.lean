import Mathlib
import Cvs.Zeta.XiVertical

/-!
# The prime side: interchanging the von Mangoldt sum with the vertical integral

`Cvs.Zeta.XiHorizontal` kills the horizontal sides of the rung-7 contour;
`Cvs.Zeta.XiVerticalLimit` shows the vertical converges.
-/

open Complex Real MeasureTheory LSeries ArithmeticFunction
open scoped LSeries.notation

namespace Cvs.Zeta

/-- The contour's right-hand vertical, parameterised by height. -/
noncomputable def vline (y : ℝ) : ℂ := (2 : ℂ) + y * I

@[simp] theorem vline_re (y : ℝ) : (vline y).re = 2 := by simp [vline]

/-- The Dirichlet terms have constant modulus along the line. -/
theorem norm_term_vline (n : ℕ) (y : ℝ) :
    ‖term (fun k => (Λ k : ℂ)) (vline y) n‖ = ‖term (fun k => (Λ k : ℂ)) (2 : ℂ) n‖ := by
  rw [norm_term_eq, norm_term_eq, vline_re]
  simp

theorem continuous_vline : Continuous vline := by unfold vline; fun_prop

theorem continuous_term_vline (n : ℕ) :
    Continuous fun y : ℝ => term (fun k => (Λ k : ℂ)) (vline y) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simpa using continuous_const
  · have hn0 : ((n : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have : NeZero ((n : ℂ)) := ⟨hn0⟩
    simp only [term, if_neg hn]
    refine continuous_const.div ((continuous_const_cpow (n : ℂ)).comp continuous_vline) ?_
    intro y
    exact fun h => hn0 ((Complex.cpow_eq_zero_iff _ _).mp h).1

/-! ### The interchange -/

theorem integrable_term_vline {φ : ℂ → ℂ}
    (hφi : Integrable fun y : ℝ => φ (vline y)) (n : ℕ) :
    Integrable fun y : ℝ => term (fun k => (Λ k : ℂ)) (vline y) n * φ (vline y) :=
  hφi.bdd_mul (continuous_term_vline n).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => le_of_eq (norm_term_vline n y))

theorem integral_norm_term_vline (φ : ℂ → ℂ) (n : ℕ) :
    (∫ y : ℝ, ‖term (fun k => (Λ k : ℂ)) (vline y) n * φ (vline y)‖)
      = ‖term (fun k => (Λ k : ℂ)) (2 : ℂ) n‖ * ∫ y : ℝ, ‖φ (vline y)‖ := by
  simp_rw [norm_mul, norm_term_vline]
  exact integral_const_mul _ _

theorem summable_integral_norm_term_vline (φ : ℂ → ℂ) :
    Summable fun n : ℕ =>
      ∫ y : ℝ, ‖term (fun k => (Λ k : ℂ)) (vline y) n * φ (vline y)‖ := by
  simp_rw [integral_norm_term_vline]
  exact (summable_norm_term_vonMangoldt (by simp)).mul_right _

/-- The Dirichlet series, summed along the line. -/
theorem tsum_term_vline (y : ℝ) :
    ∑' n : ℕ, term (fun k => (Λ k : ℂ)) (vline y) n = - logDeriv riemannZeta (vline y) := by
  have h : logDeriv riemannZeta (vline y) = - LSeries (fun k => (Λ k : ℂ)) (vline y) := by
    rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simp), logDeriv_apply, neg_div, neg_neg]
  rw [h, neg_neg]
  rfl

/-- **The prime side.** Along `Re s = 2` the vertical integral of `(ζ'/ζ)·φ` is exactly `−Σ_n Λ(n)
∫ n^{−s} φ(s)`: the sum and the integral may be interchanged. -/
theorem integral_logDeriv_riemannZeta_vline {φ : ℂ → ℂ}
    (hφi : Integrable fun y : ℝ => φ (vline y)) :
    (∫ y : ℝ, logDeriv riemannZeta (vline y) * φ (vline y))
      = - ∑' n : ℕ, ∫ y : ℝ, term (fun k => (Λ k : ℂ)) (vline y) n * φ (vline y) := by
  have hsum := integral_tsum_of_summable_integral_norm
    (F := fun (n : ℕ) (y : ℝ) => term (fun k => (Λ k : ℂ)) (vline y) n * φ (vline y))
    (fun n => integrable_term_vline hφi n) (summable_integral_norm_term_vline φ)
  have hpt : ∀ y : ℝ, (∑' n : ℕ, term (fun k => (Λ k : ℂ)) (vline y) n * φ (vline y))
      = - (logDeriv riemannZeta (vline y) * φ (vline y)) := by
    intro y
    rw [tsum_mul_right, tsum_term_vline]
    ring
  rw [hsum]
  simp_rw [hpt]
  rw [integral_neg, neg_neg]

/-- The same, with the von Mangoldt weight pulled out — the explicit formula's prime side in the
shape it is usually written: ∫ (ζ'/ζ)(s)·φ(s) = − Σ_n Λ(n) ∫ n^{−s}·φ(s), `s = 2 + iy`. -/
theorem integral_logDeriv_riemannZeta_vline_prime {φ : ℂ → ℂ}
    (hφi : Integrable fun y : ℝ => φ (vline y)) :
    (∫ y : ℝ, logDeriv riemannZeta (vline y) * φ (vline y))
      = - ∑' n : ℕ, (Λ n : ℂ) * ∫ y : ℝ, ((n : ℂ) ^ (-(vline y))) * φ (vline y) := by
  rw [integral_logDeriv_riemannZeta_vline hφi]
  congr 1
  refine tsum_congr fun n => ?_
  have hterm : ∀ y : ℝ, term (fun k => (Λ k : ℂ)) (vline y) n * φ (vline y)
      = (Λ n : ℂ) * (((n : ℂ) ^ (-(vline y))) * φ (vline y)) := by
    intro y
    rw [term_def₀ (by simp) (vline y) n]
    ring
  simp_rw [hterm]
  exact integral_const_mul _ _

end Cvs.Zeta
