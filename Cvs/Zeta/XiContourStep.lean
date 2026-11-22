import Mathlib
import Cvs.Zeta.RectWinding
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.XiHorizontal

/-!
# The contour argument at finite height, with the four sides named

`rectBoundaryIntegral` is a definition; unfolding it at the corners `−1 − iT'` and `2 + iT'`
gives the four sides explicitly.
-/

open Complex

namespace Cvs.Zeta

/-- **The zero sum equals the two vertical integrals, up to the horizontal error.** This is the
contour argument at finite height, with the four sides named. -/
theorem norm_verticals_sub_zero_sum_le {T T' K M : ℝ} {φ : ℂ → ℂ} {S : Finset ℂ} {m : ℂ → ℕ}
    (hK : 0 ≤ K)
    (hbound : ∀ z : ℂ, ‖z - (2 + (T' : ℂ) * I)‖ ≤ (12 : ℝ) / 4 → z.im = T' →
      riemannZeta z ≠ 0 → ‖logDeriv riemannXi z‖ ≤ K * (1 + Real.log |T|) ^ 2)
    (hζ : ∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta ((x : ℂ) + T' * I) ≠ 0)
    (hφp : ∀ x ∈ Set.uIcc (-1 : ℝ) 2, ‖φ ((x : ℂ) + T' * I)‖ ≤ M)
    (hφn : ∀ x ∈ Set.uIcc (-1 : ℝ) 2, ‖φ ((x : ℂ) - T' * I)‖ ≤ M)
    (heq : rectBoundaryIntegral (fun u => logDeriv riemannXi u * φ u)
        (-1 - (T' : ℂ) * I) (2 + (T' : ℂ) * I)
      = 2 * (Real.pi : ℂ) * I * ∑ ρ ∈ S, (m ρ : ℂ) * φ ρ) :
    ‖I * (∫ y in (-T')..T', logDeriv riemannXi ((2 : ℂ) + (y : ℂ) * I) * φ ((2 : ℂ) + (y : ℂ) * I))
        - I * (∫ y in (-T')..T',
            logDeriv riemannXi ((-1 : ℂ) + (y : ℂ) * I) * φ ((-1 : ℂ) + (y : ℂ) * I))
        - 2 * (Real.pi : ℂ) * I * ∑ ρ ∈ S, (m ρ : ℂ) * φ ρ‖
      ≤ 6 * (K * (1 + Real.log |T|) ^ 2 * M) := by
  rw [rectBoundaryIntegral] at heq
  norm_num at heq
  simp only [← sub_eq_add_neg] at heq
  have h1 := norm_horizontal_integral_le (T := T) (T' := T') (K := K) (M := M) (φ := φ)
    hK hbound hφp hζ
  have h2 := norm_horizontal_integral_le_neg (T := T) (T' := T') (K := K) (M := M) (φ := φ)
    hK hbound hφn hζ
  have hkey :
      I * (∫ y in (-T')..T',
            logDeriv riemannXi ((2 : ℂ) + (y : ℂ) * I) * φ ((2 : ℂ) + (y : ℂ) * I))
        - I * (∫ y in (-T')..T',
            logDeriv riemannXi ((-1 : ℂ) + (y : ℂ) * I) * φ ((-1 : ℂ) + (y : ℂ) * I))
        - 2 * (Real.pi : ℂ) * I * ∑ ρ ∈ S, (m ρ : ℂ) * φ ρ
      = (∫ x in (-1 : ℝ)..2,
            logDeriv riemannXi ((x : ℂ) + T' * I) * φ ((x : ℂ) + T' * I))
        - (∫ x in (-1 : ℝ)..2,
            logDeriv riemannXi ((x : ℂ) - T' * I) * φ ((x : ℂ) - T' * I)) := by
    linear_combination heq
  rw [hkey]
  refine le_trans (norm_sub_le _ _) ?_
  linarith

end Cvs.Zeta
