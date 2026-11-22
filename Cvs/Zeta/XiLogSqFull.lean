import Mathlib
import Cvs.Zeta.CountTransfer
import Cvs.Zeta.HeightShift
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.XiLogDerivHeight
import Cvs.Zeta.XiLogSq
import Cvs.Zeta.ZetaPolyGrowth
import Cvs.Zeta.ZetaZeroCountGen

/-!
# `ξ'/ξ = O(log²T)`, hypothesis-free

`Cvs.Zeta.XiLogSq` proves the bound but takes the zero-freeness, the zero-set of the Landau
factorisation, and the `T` versus `T'` bookkeeping as hypotheses.
-/

open Complex Real Set Metric Finset

namespace Cvs.Zeta

theorem riemannZeta_eq_zero_of_riemannZeta₁ {w : ℂ} (hw : w ≠ 1)
    (h : riemannZeta₁ w = 0) : riemannZeta w = 0 := by
  rw [riemannZeta₁_eq_mul hw] at h
  rcases mul_eq_zero.mp h with h1 | h1
  · exact absurd (sub_eq_zero.mp h1) hw
  · exact h1

/-- **`ξ'/ξ = O(log²T)`, with the height supplied by the caller.**
`exists_norm_logDeriv_riemannXi_le_log_sq` below mints its own `T'` from
`exists_zero_free_height'`. -/
theorem norm_logDeriv_riemannXi_le_log_sq_of_height (r : ℝ) (hr : 0 < r) (k : ℕ) (hk : 1 ≤ k)
    (hkr : 2 * (r + 1) ≤ (k : ℝ) + 3 / 2) (Kf : ℝ) (hKf0 : 0 ≤ Kf) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, 2 * (r + 1) + 6 ≤ |T| →
      ∀ T' : ℝ, T ≤ T' → T' ≤ T + 1 →
        (∀ z : ℂ, z ∈ Metric.closedBall (2 + (T : ℂ) * I) (r + 1) → riemannZeta z = 0 →
            1 / (2 * (Kf * (1 + Real.log |T|) + 2)) ≤ |T' - z.im|) →
        ∀ z : ℂ, ‖z - (2 + (T' : ℂ) * I)‖ ≤ r / 4 → z.im = T' → riemannZeta z ≠ 0 →
          ‖logDeriv riemannXi z‖ ≤ K * (1 + Real.log |T|) ^ 2 := by
  have hrk : 2 * r ≤ (k : ℝ) + 3 / 2 := by linarith
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_logDeriv_riemannXi_bound_at_height hr k hk hrk
  obtain ⟨Kc, hKc0, hKc⟩ := exists_zero_count_riemannZeta_ball' r hr k hk hrk
  have hl2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  refine ⟨K₁ * (1 + Real.log 2) + 2 * Kc * (1 + Real.log 2) * (Kf + 2), by positivity, ?_⟩
  intro T hT T' hT'1 hT'2 hfree
  have hT1 : (1 : ℝ) ≤ |T| := by linarith
  have hL : 0 ≤ Real.log |T| := Real.log_nonneg hT1
  have hTT' : |T' - T| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hTlow : |T| - 1 ≤ |T'| := by
    have h := abs_sub_abs_le_abs_sub T T'
    rw [abs_sub_comm T T'] at h
    linarith
  have hT'abs : 2 * r + 1 ≤ |T'| := by linarith
  have hT'4 : 2 * r + 4 ≤ |T'| := by linarith
  have hlogT' : Real.log |T'| ≤ Real.log 2 + Real.log |T| := log_abs_shift_le hT1 hTT'
  have hlogT'0 : 0 ≤ Real.log |T'| := Real.log_nonneg (by linarith)
  intro z hz hzim hζ
  -- Landau at height `T'`
  obtain ⟨S, m, hSr, hcount, hSzero, hbound⟩ := hK₁ T' hT'4
  -- the poles are zeros of `ζ`
  -- points of the disc are far from the real axis, hence never `1`
  have hne1 : ∀ σ ∈ S, (2 + (T' : ℂ) * I) + σ ≠ 1 := by
    intro σ hσ hc
    have him : ((2 + (T' : ℂ) * I) + σ).im = T' + σ.im := by simp
    have hσim : |σ.im| ≤ r := le_trans (Complex.abs_im_le_norm σ) (hSr σ hσ)
    have h1 : (T' + σ.im) = 0 := by rw [← him, hc]; simp
    have habs := abs_le.mp hσim
    have : |T'| ≤ r := by
      rcases le_or_gt 0 T' with h | h
      · rw [abs_of_nonneg h]; linarith [habs.1, habs.2]
      · rw [abs_of_neg h]; linarith [habs.1, habs.2]
    linarith
  have hSz : ∀ σ ∈ S, ‖σ‖ ≤ r ∧ riemannZeta ((2 + (T' : ℂ) * I) + σ) = 0 :=
    fun σ hσ => ⟨hSr σ hσ,
      riemannZeta_eq_zero_of_riemannZeta₁ (hne1 σ hσ) (hSzero σ hσ)⟩
  -- the ball avoids the pole, so the count transfers
  have hpole : (1 : ℂ) ∉ closedBall (2 + (T' : ℂ) * I) r := by
    intro hc
    have := one_le_abs_im_of_mem_ball (T := T') (R := r) (by linarith) hc
    simp at this
    linarith
  have hN : (∑ σ ∈ S, (m σ : ℝ)) ≤ Kc * (1 + Real.log |T'|) := by
    have h1 := count_transfer hpole hcount
    have h2 := hKc T' hT'abs
    have hcast : (∑ σ ∈ S, (m σ : ℝ)) = ((∑ σ ∈ S, (m σ : ℤ) : ℤ) : ℝ) := by push_cast; ring
    rw [hcast, h1]
    exact h2
  -- `z` is not one of the poles, since it is not a zero
  have hzS : (z - (2 + (T' : ℂ) * I)) ∉ S := by
    intro hc
    exact hζ (by simpa using (hSz _ hc).2)
  -- the gap, transferred to the shifted ball
  set gap : ℝ := 1 / (2 * (Kf * (1 + Real.log |T|) + 2)) with hgapdef
  have hgap0 : 0 < gap := by rw [hgapdef]; positivity
  have hfree' := zero_free_shift hTT' (le_refl (r + 1)) hfree
  have hmain := norm_logDeriv_riemannXi_le_of_zero_free hgap0 hfree' hSz hzim
    (hbound z hz hzS hζ) hN
  refine hmain.trans ?_
  -- the arithmetic
  have hstep : (1 : ℝ) + Real.log |T'| ≤ (1 + Real.log 2) * (1 + Real.log |T|) := by
    nlinarith [hlogT', hL, hl2]
  have hinv : Kc * (1 + Real.log |T'|) / gap
      = Kc * (1 + Real.log |T'|) * (2 * (Kf * (1 + Real.log |T|) + 2)) := by
    rw [hgapdef]
    field_simp
  rw [hinv]
  have hone : (1 : ℝ) ≤ 1 + Real.log |T| := by linarith
  have hKf' : Kf * (1 + Real.log |T|) + 2 ≤ (Kf + 2) * (1 + Real.log |T|) := by nlinarith
  have hL'0 : (0 : ℝ) ≤ 1 + Real.log |T'| := by linarith
  have hlog2' : (0 : ℝ) ≤ 1 + Real.log 2 := by linarith
  calc K₁ * (1 + Real.log |T'|)
        + Kc * (1 + Real.log |T'|) * (2 * (Kf * (1 + Real.log |T|) + 2))
      ≤ K₁ * ((1 + Real.log 2) * (1 + Real.log |T|))
        + Kc * ((1 + Real.log 2) * (1 + Real.log |T|))
          * (2 * ((Kf + 2) * (1 + Real.log |T|))) := by
        gcongr
    _ = K₁ * (1 + Real.log 2) * (1 + Real.log |T|)
        + 2 * Kc * (1 + Real.log 2) * (Kf + 2) * (1 + Real.log |T|) ^ 2 := by ring
    _ ≤ (K₁ * (1 + Real.log 2) + 2 * Kc * (1 + Real.log 2) * (Kf + 2))
          * (1 + Real.log |T|) ^ 2 := by
        have hLsq : (1 + Real.log |T|) ≤ (1 + Real.log |T|) ^ 2 := by nlinarith
        have hc : (0 : ℝ) ≤ K₁ * (1 + Real.log 2) := mul_nonneg hK₁0 hlog2'
        nlinarith [mul_le_mul_of_nonneg_left hLsq hc]

end Cvs.Zeta
