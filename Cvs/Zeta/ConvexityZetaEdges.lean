import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Cvs.Zeta.ConvexityEdgeMinusHalf

/-!
# The entire part, and the edges at `ζ`
-/

open Complex

namespace Cvs.ArchScore

/-- `|s - 1| ≥ |Im s|`, so the pole term is small away from the real axis. -/
theorem norm_sub_one_ge (s : ℂ) : |s.im| ≤ ‖s - 1‖ := by
  have h1 : |(s - 1).im| ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
  have h2 : (s - 1).im = s.im := by simp
  rwa [h2] at h1

/-- **The pole term is bounded off the real axis.** -/
theorem norm_pole_le {s : ℂ} (h : 1 ≤ |s.im|) : ‖(s - (1 : ℂ))⁻¹‖ ≤ 1 := by
  have hge : (1 : ℝ) ≤ ‖s - 1‖ := le_trans h (norm_sub_one_ge s)
  have hne : s - (1 : ℂ) ≠ 0 := by
    intro hc
    rw [hc, norm_zero] at hge; linarith
  rw [norm_inv]
  rw [inv_le_one_iff₀]
  right; exact hge

/-- **The entire part inherits the edge bounds**, with the pole removed. -/
theorem norm_zeta₀_le {s : ℂ} (h : 1 ≤ |s.im|) {C : ℝ}
    (hz : ‖riemannZeta s‖ ≤ C) : ‖riemannZeta₀ s‖ ≤ C + 1 := by
  have hs1 : s ≠ 1 := by
    intro hc
    rw [hc] at h; simp at h; linarith
  have heq := riemannZeta_eq_inv_sub_add hs1
  have : riemannZeta₀ s = riemannZeta s - (s - 1)⁻¹ := by rw [heq]; ring
  rw [this]
  calc ‖riemannZeta s - (s - 1)⁻¹‖ ≤ ‖riemannZeta s‖ + ‖(s - (1:ℂ))⁻¹‖ := norm_sub_le _ _
    _ ≤ C + 1 := add_le_add hz (norm_pole_le h)

/-- **And `ζ` is recovered from it**, with the pole term costing at most `1`. -/
theorem norm_zeta_le_of_zeta₀ {s : ℂ} (h : 1 ≤ |s.im|) {C : ℝ}
    (hz : ‖riemannZeta₀ s‖ ≤ C) : ‖riemannZeta s‖ ≤ C + 1 := by
  have hs1 : s ≠ 1 := by
    intro hc
    rw [hc] at h; simp at h; linarith
  rw [riemannZeta_eq_inv_sub_add hs1]
  calc ‖(s - 1)⁻¹ + riemannZeta₀ s‖ ≤ ‖(s - (1:ℂ))⁻¹‖ + ‖riemannZeta₀ s‖ := norm_add_le _ _
    _ ≤ 1 + C := add_le_add (norm_pole_le h) hz
    _ = C + 1 := by ring

/-- **The far edge for the entire part**, from `ConvexityEdgeMinusHalf`.  `ζ₀` at `σ = -1/2` is linear in the
height. -/
theorem zeta₀_edge_neg_half {t : ℝ} (ht : 1 ≤ |t|) {C₀ : ℝ}
    (hC₀ : ‖riemannZeta ((3 : ℂ) / 2 - (t : ℂ) * I)‖ ≤ C₀) (hC₀0 : 0 ≤ C₀) :
    ‖riemannZeta₀ ((-1 : ℂ) / 2 + (t : ℂ) * I)‖
      ≤ Real.pi⁻¹ * ((1 + |t|) / 2) * C₀ + 1 := by
  have htne : t ≠ 0 := by
    intro hc; rw [hc] at ht; simp at ht; linarith
  have heq := Cvs.ArchScore.zeta_neg_half_eq t htne
  have hnorm : ‖((-1 : ℂ) / 2 + (t : ℂ) * I) / 2‖ ≤ (1 + |t|) / 2 := by
    rw [norm_div]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2]
    have hle : ‖(-1 : ℂ) / 2 + (t : ℂ) * I‖ ≤ 1 + |t| := by
      refine le_trans (norm_add_le _ _) ?_
      have hA : ‖(-1 : ℂ) / 2‖ ≤ 1 := by
        rw [norm_div]; simp; norm_num
      have hB : ‖(t : ℂ) * I‖ = |t| := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      rw [hB]; linarith
    linarith
  have him : |((-1 : ℂ) / 2 + (t : ℂ) * I).im| = |t| := by simp
  refine norm_zeta₀_le (by rw [him]; exact ht) ?_
  rw [heq]
  have hpi : (0:ℝ) < Real.pi⁻¹ := by positivity
  calc Real.pi⁻¹ * ‖((-1 : ℂ) / 2 + (t : ℂ) * I) / 2‖
        * ‖riemannZeta ((3 : ℂ) / 2 - (t : ℂ) * I)‖
      ≤ Real.pi⁻¹ * ((1 + |t|) / 2) * C₀ := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hnorm hpi.le) hC₀ (norm_nonneg _) ?_
        positivity

end Cvs.ArchScore
