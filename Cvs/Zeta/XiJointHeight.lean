import Mathlib
import Cvs.Zeta.RectWinding
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.XiCollar
import Cvs.Zeta.XiLogSqFull
import Cvs.Zeta.XiRectangleZeroSum
import Cvs.Zeta.ZeroFreeHeightGen
import Cvs.Zeta.ZetaLineNonvanishing

/-!
# One height for both sides of the contour

The obstacle to the limit was that `rect_zero_sum_riemannXi` and
`exists_norm_logDeriv_riemannXi_le_log_sq` each minted their own `T'`, from different
constructions, and could not be composed.
-/

open Complex Metric

namespace Cvs.Zeta

/-- **One height serving both sides of the contour argument.** At a single `T' ∈ [T, T+1]`: * the
boundary integral over `[−1,2] × [−T',T']` equals `2πi Σ_ρ m_ρ φ(ρ)`, the sum over *all* zeros
with `|Im| < T'`; and * `‖ξ'/ξ‖ ≤ K(1 + log|T|)²` on the horizontal segment at height `T'`. -/
theorem exists_joint_height (r : ℝ) (hr : 0 < r) (hr3 : 3 ≤ r) (k : ℕ) (hk : 1 ≤ k)
    (hkr : 2 * (r + 1) ≤ (k : ℝ) + 3 / 2) {φ : ℂ → ℂ} (hφ : Differentiable ℂ φ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, 2 * (r + 1) + 6 ≤ T →
      ∃ (T' : ℝ) (S : Finset ℂ) (m : ℂ → ℕ),
        T ≤ T' ∧ T' ≤ T + 1 ∧
        (∀ ρ ∈ S, riemannXi ρ = 0) ∧
        (∀ ρ ∈ S, -1 < ρ.re ∧ ρ.re < 2 ∧ -T' < ρ.im ∧ ρ.im < T') ∧
        (∀ u : ℂ, riemannXi u = 0 → |u.im| < T' → u ∈ S) ∧
        (∀ u : ℂ, (m u : ℤ) = MeromorphicOn.divisor riemannXi Set.univ u) ∧
        (∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta ((x : ℂ) + T' * I) ≠ 0) ∧
        (∀ z : ℂ, ‖z - (2 + (T' : ℂ) * I)‖ ≤ r / 4 → z.im = T' → riemannZeta z ≠ 0 →
          ‖logDeriv riemannXi z‖ ≤ K * (1 + Real.log |T|) ^ 2) ∧
        rectBoundaryIntegral (fun u => logDeriv riemannXi u * φ u)
            (-1 - (T' : ℂ) * I) (2 + (T' : ℂ) * I)
          = 2 * (Real.pi : ℂ) * I * ∑ ρ ∈ S, (m ρ : ℂ) * φ ρ := by
  obtain ⟨Kf, hKf0, hKf⟩ := exists_zero_free_height' (r + 1) (by linarith) k hk hkr
  obtain ⟨K, hK0, hK⟩ := norm_logDeriv_riemannXi_le_log_sq_of_height r hr k hk hkr Kf hKf0
  refine ⟨K, hK0, fun T hT => ?_⟩
  have hTpos : (0 : ℝ) < T := by linarith
  have hTabs : |T| = T := abs_of_pos hTpos
  have hT1 : (1 : ℝ) ≤ |T| := by rw [hTabs]; linarith
  have hlog : 0 ≤ Real.log |T| := Real.log_nonneg hT1
  obtain ⟨T', hT'1, hT'2, hfree⟩ := hKf T (by rw [hTabs]; linarith)
  set gap : ℝ := 1 / (2 * (Kf * (1 + Real.log |T|) + 2)) with hgapdef
  have hden : (0 : ℝ) < 2 * (Kf * (1 + Real.log |T|) + 2) := by nlinarith
  have hgap0 : 0 < gap := by rw [hgapdef]; positivity
  have hgap1 : gap ≤ 1 := by
    rw [hgapdef, div_le_one hden]
    nlinarith
  have hcollar := collar_of_zeta_gap (T := T) (T' := T') (gap := gap) (r := r + 1)
    (by linarith) hgap1 hT'1 hT'2 (by linarith) hfree
  obtain ⟨S, m, hS0, hSin, hScap, hSmult, heq⟩ :=
    rect_zero_sum_of_collar (by linarith) hgap0 hgap1 hcollar hφ
  exact ⟨T', S, m, hT'1, hT'2, hS0, hSin, hScap, hSmult,
    zeta_ne_zero_on_collar_line (by linarith) hgap0 hcollar,
    hK T (by rw [hTabs]; linarith) T' hT'1 hT'2 hfree, heq⟩

end Cvs.Zeta
