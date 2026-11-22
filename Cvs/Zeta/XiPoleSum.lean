import Mathlib
import Cvs.Zeta.RiemannXi

/-!
# From `ξ'/ξ` minus its poles to `ξ'/ξ`

`Cvs.Zeta.exists_logDeriv_riemannXi_bound_at_height` controls `ξ'/ξ` *minus* its nearby poles.
-/

open Complex Real Finset

namespace Cvs.Zeta

/-- **The pole sum, on a height that keeps its distance.** `Σ_σ m_σ/(z − (c+σ))` is at most `(Σ_σ
m_σ)/gap` once every pole is at distance `≥ gap`. -/
theorem norm_sum_poles_le {S : Finset ℂ} {m : ℂ → ℕ} {c z : ℂ} {N gap : ℝ}
    (hgap : 0 < gap) (hd : ∀ σ ∈ S, gap ≤ ‖z - (c + σ)‖)
    (hN : (∑ σ ∈ S, (m σ : ℝ)) ≤ N) :
    ‖∑ σ ∈ S, (m σ : ℂ) / (z - (c + σ))‖ ≤ N / gap := by
  refine (norm_sum_le _ _).trans ?_
  have hstep : ∀ σ ∈ S, ‖(m σ : ℂ) / (z - (c + σ))‖ ≤ (m σ : ℝ) / gap := by
    intro σ hσ
    rw [norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hgap (hd σ hσ)
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.sum_div]
  gcongr

/-- **`ξ'/ξ` itself, on a height whose poles are far.** The Landau bound controls `ξ'/ξ` *minus*
its nearby poles; adding the pole sum back costs `(Σ m_σ)/gap`. -/
theorem norm_logDeriv_riemannXi_le_of_gap {K : ℝ} {T : ℝ}
    {S : Finset ℂ} {m : ℂ → ℕ} {z : ℂ} {N gap : ℝ} (hgap : 0 < gap)
    (hlandau : ‖logDeriv riemannXi z
        - ∑ σ ∈ S, (m σ : ℂ) / (z - ((2 + T * I) + σ))‖ ≤ K * (1 + Real.log |T|))
    (hd : ∀ σ ∈ S, gap ≤ ‖z - ((2 + T * I) + σ)‖)
    (hN : (∑ σ ∈ S, (m σ : ℝ)) ≤ N) :
    ‖logDeriv riemannXi z‖ ≤ K * (1 + Real.log |T|) + N / gap := by
  have hpole := norm_sum_poles_le hgap hd hN
  have hsplit : ‖logDeriv riemannXi z‖
      ≤ ‖logDeriv riemannXi z - ∑ σ ∈ S, (m σ : ℂ) / (z - ((2 + T * I) + σ))‖
        + ‖∑ σ ∈ S, (m σ : ℂ) / (z - ((2 + T * I) + σ))‖ := by
    simpa using norm_add_le
      (logDeriv riemannXi z - ∑ σ ∈ S, (m σ : ℂ) / (z - ((2 + T * I) + σ)))
      (∑ σ ∈ S, (m σ : ℂ) / (z - ((2 + T * I) + σ)))
  linarith

end Cvs.Zeta
