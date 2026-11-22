import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Cvs.Zeta.ConvexityNearEdgeParams
import Cvs.Zeta.ConvexityZetaEdges

/-!
# The edge constants for the convexity ladder

`ConvexityZetaEdges.zeta₀_edge_neg_half` and `ConvexityNearEdgeParams.zeta₀_edge_three_halves` both take the bound on `ζ` at
the near edge as a *hypothesis* `C₀`.
-/

open Complex

namespace Cvs.ZetaGrowth

/-- The value of the Dirichlet series at the near edge `σ = 3/2`. -/
noncomputable def zetaEdge : ℝ := ∑' n : ℕ, 1 / (n : ℝ) ^ (3 / 2 : ℝ)

theorem zetaEdge_nonneg : 0 ≤ zetaEdge :=
  tsum_nonneg (fun n => by positivity)

/-- **`ζ` on a vertical line right of `1` is dominated by the real point.**  Termwise: the
Dirichlet series converges absolutely and `‖n^{-s}‖ = n^{-σ}`, so the height contributes
nothing. -/
theorem norm_zeta_le_tsum {s : ℂ} (h : 1 < s.re) :
    ‖riemannZeta s‖ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ s.re := by
  have hre0 : (0 : ℝ) < s.re := by linarith
  have hs0 : s ≠ 0 := by
    intro hc; rw [hc] at h; simp at h; linarith
  have hn : ∀ n : ℕ, ‖1 / (n : ℂ) ^ s‖ = 1 / (n : ℝ) ^ s.re := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [Complex.zero_cpow hs0, Real.zero_rpow hre0.ne']
    · rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hpos]
  have hsum : Summable (fun n : ℕ => 1 / (n : ℝ) ^ s.re) :=
    Real.summable_one_div_nat_rpow.mpr h
  have hsum' : Summable (fun n : ℕ => ‖1 / (n : ℂ) ^ s‖) :=
    hsum.congr (fun n => (hn n).symm)
  rw [zeta_eq_tsum_one_div_nat_cpow h]
  calc ‖∑' n : ℕ, 1 / (n : ℂ) ^ s‖ ≤ ∑' n : ℕ, ‖1 / (n : ℂ) ^ s‖ :=
        norm_tsum_le_tsum_norm hsum'
    _ = ∑' n : ℕ, 1 / (n : ℝ) ^ s.re := tsum_congr hn

theorem norm_zeta_edge_add (t : ℝ) :
    ‖riemannZeta ((3 : ℂ) / 2 + (t : ℂ) * I)‖ ≤ zetaEdge := by
  have hre : ((3 : ℂ) / 2 + (t : ℂ) * I).re = 3 / 2 := by simp
  have h := norm_zeta_le_tsum (s := (3 : ℂ) / 2 + (t : ℂ) * I) (by rw [hre]; norm_num)
  rwa [hre] at h

theorem norm_zeta_edge_sub (t : ℝ) :
    ‖riemannZeta ((3 : ℂ) / 2 - (t : ℂ) * I)‖ ≤ zetaEdge := by
  have hre : ((3 : ℂ) / 2 - (t : ℂ) * I).re = 3 / 2 := by simp
  have h := norm_zeta_le_tsum (s := (3 : ℂ) / 2 - (t : ℂ) * I) (by rw [hre]; norm_num)
  rwa [hre] at h

/-- **The near edge, with the constant supplied.** -/
theorem zeta₀_edge_right {t : ℝ} (ht : 1 ≤ |t|) :
    ‖riemannZeta₀ ((3 : ℂ) / 2 + (t : ℂ) * I)‖ ≤ zetaEdge + 1 :=
  Cvs.ArchScore.zeta₀_edge_three_halves ht (norm_zeta_edge_add t)

/-- **The far edge, with the constant supplied.**  Linear in the height, via `ConvexityEdgeMinusHalf`'s
Stirling-free reflection. -/
theorem zeta₀_edge_left {t : ℝ} (ht : 1 ≤ |t|) :
    ‖riemannZeta₀ ((-1 : ℂ) / 2 + (t : ℂ) * I)‖
      ≤ Real.pi⁻¹ * ((1 + |t|) / 2) * zetaEdge + 1 :=
  Cvs.ArchScore.zeta₀_edge_neg_half ht (norm_zeta_edge_sub t) zetaEdge_nonneg

end Cvs.ZetaGrowth
