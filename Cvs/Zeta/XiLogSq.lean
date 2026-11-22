import Mathlib
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.XiPoleSum

/-!
# `ξ'/ξ = O(log²T)` on a zero-free horizontal line

The two halves finally meet.
-/

open Complex Real Set Metric Finset

namespace Cvs.Zeta

/-- **A zero-free height keeps the Landau poles away, on its own horizontal line.** -/
theorem gap_of_zero_free {c : ℂ} {r gap T' : ℝ} {S : Finset ℂ}
    (hc : c = 2 + (T' : ℂ) * I)
    (hfree : ∀ w : ℂ, w ∈ closedBall c r → riemannZeta w = 0 → gap ≤ |T' - w.im|)
    (hS : ∀ σ ∈ S, ‖σ‖ ≤ r ∧ riemannZeta (c + σ) = 0)
    {z : ℂ} (hz : z.im = T') :
    ∀ σ ∈ S, gap ≤ ‖z - (c + σ)‖ := by
  intro σ hσ
  obtain ⟨hσr, hσ0⟩ := hS σ hσ
  have hmem : c + σ ∈ closedBall c r := by
    rw [mem_closedBall, dist_eq_norm]
    simpa using hσr
  have hgap := hfree (c + σ) hmem hσ0
  have hcim : c.im = T' := by rw [hc]; simp
  have him : (c + σ).im = T' + σ.im := by rw [Complex.add_im, hcim]
  rw [him] at hgap
  have habs : |T' - (T' + σ.im)| = |σ.im| := by
    rw [show T' - (T' + σ.im) = -σ.im by ring, abs_neg]
  rw [habs] at hgap
  refine le_trans hgap ?_
  have h1 : |(z - (c + σ)).im| ≤ ‖z - (c + σ)‖ := Complex.abs_im_le_norm _
  have h2 : (z - (c + σ)).im = -σ.im := by
    rw [Complex.sub_im, him, hz]; ring
  rw [h2, abs_neg] at h1
  exact h1

/-- **`ξ'/ξ = O(log²T)` on a zero-free horizontal line.** The Landau bound gives `O(log T)` for
`ξ'/ξ` minus its nearby poles; on a line whose distance to every zero ordinate is `gap`, the
pole sum costs `N/gap`. -/
theorem norm_logDeriv_riemannXi_le_of_zero_free
    {r gap T' N K : ℝ} {S : Finset ℂ} {m : ℂ → ℕ} {z : ℂ}
    (hgap : 0 < gap)
    (hfree : ∀ w : ℂ, w ∈ closedBall (2 + (T' : ℂ) * I) r → riemannZeta w = 0 →
      gap ≤ |T' - w.im|)
    (hS : ∀ σ ∈ S, ‖σ‖ ≤ r ∧ riemannZeta ((2 + (T' : ℂ) * I) + σ) = 0)
    (hz : z.im = T')
    (hlandau : ‖logDeriv riemannXi z
        - ∑ σ ∈ S, (m σ : ℂ) / (z - ((2 + (T' : ℂ) * I) + σ))‖ ≤ K * (1 + Real.log |T'|))
    (hN : (∑ σ ∈ S, (m σ : ℝ)) ≤ N) :
    ‖logDeriv riemannXi z‖ ≤ K * (1 + Real.log |T'|) + N / gap :=
  norm_logDeriv_riemannXi_le_of_gap hgap hlandau
    (gap_of_zero_free rfl hfree hS hz) hN

end Cvs.Zeta
