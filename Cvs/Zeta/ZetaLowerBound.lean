import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues

/-!
# `ζ` is bounded below on the line `Re s = 2`

Jensen's formula applied at centre `2 + iT` produces the term `- log ‖ζ(2 + iT)‖`, and the
unit-window zero count is `O(log T)` only if that term is bounded independently of `T`.
-/

open Complex Real Set

namespace Cvs.Zeta

/-- On the line `Re s = 2` the Dirichlet series is dominated by its first term: `‖ζ(s)‖ ≥ 1 -
(ζ(2) - 1) = 2 - π²/6 > 0`, uniformly in `Im s`. -/
theorem norm_riemannZeta_ge_of_re_eq_two {s : ℂ} (hs : s.re = 2) :
    2 - Real.pi ^ 2 / 6 ≤ ‖riemannZeta s‖ := by
  have hs1 : 1 < s.re := by rw [hs]; norm_num
  have hsum : LSeriesSummable 1 s := LSeriesSummable_one_iff.mpr hs1
  -- the termwise norms are exactly the `ζ(2)` summand
  have hnorm : ∀ n : ℕ, ‖LSeries.term 1 s n‖ = (1 : ℝ) / (n : ℝ) ^ 2 := by
    intro n
    rw [LSeries.norm_term_eq, hs]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [if_neg hn]
      simp
  have hz2 : ∑' n : ℕ, ‖LSeries.term 1 s n‖ = Real.pi ^ 2 / 6 := by
    rw [tsum_congr hnorm]
    exact hasSum_zeta_two.tsum_eq
  -- split off the `n = 1` term, which is `1`
  have hone : ‖LSeries.term 1 s 1‖ = 1 := by rw [hnorm 1]; norm_num
  have hsplit : LSeries 1 s
      = LSeries.term 1 s 1 + ∑' n : ℕ, ite (n = 1) 0 (LSeries.term 1 s n) :=
    hsum.tsum_eq_add_tsum_ite 1
  have hsummableN : Summable fun n : ℕ => ‖LSeries.term 1 s n‖ := hsum.norm
  have hb : ∀ n : ℕ, ‖ite (n = 1) 0 (LSeries.term 1 s n)‖
      = ite (n = 1) 0 ‖LSeries.term 1 s n‖ := by
    intro n
    rcases eq_or_ne n 1 with rfl | hn
    · simp
    · simp [hn]
  -- the tail is small
  have htail : ‖∑' n : ℕ, ite (n = 1) 0 (LSeries.term 1 s n)‖ ≤ Real.pi ^ 2 / 6 - 1 := by
    have hsN : Summable fun n : ℕ => ‖ite (n = 1) 0 (LSeries.term 1 s n)‖ := by
      refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hsummableN
      rw [hb]; split
      · exact norm_nonneg _
      · exact le_rfl
    refine (norm_tsum_le_tsum_norm hsN).trans ?_
    rw [tsum_congr hb]
    have hsp := hsummableN.tsum_eq_add_tsum_ite 1
    rw [hz2, hone] at hsp
    linarith
  -- assemble
  rw [← LSeries_one_eq_riemannZeta hs1, hsplit]
  have hone' : LSeries.term 1 s 1 = 1 := by simp [LSeries.term]
  rw [hone']
  have := norm_sub_norm_le (1 : ℂ) (-(∑' n : ℕ, ite (n = 1) 0 (LSeries.term 1 s n)))
  simp only [norm_one, norm_neg, sub_neg_eq_add] at this
  linarith [this, htail]

/-- The same bound with the numerics discharged: `‖ζ(s)‖ ≥ 1/3` on `Re s = 2`.
In particular `ζ` does not vanish there, and `log ‖ζ(s)‖ ≥ -log 3`. -/
theorem one_third_le_norm_riemannZeta_of_re_eq_two {s : ℂ} (hs : s.re = 2) :
    (1 : ℝ) / 3 ≤ ‖riemannZeta s‖ := by
  refine le_trans ?_ (norm_riemannZeta_ge_of_re_eq_two hs)
  nlinarith [Real.pi_lt_d2, Real.pi_gt_three]

theorem riemannZeta_ne_zero_of_re_eq_two {s : ℂ} (hs : s.re = 2) :
    riemannZeta s ≠ 0 := by
  intro h
  have := one_third_le_norm_riemannZeta_of_re_eq_two hs
  rw [h, norm_zero] at this
  linarith

end Cvs.Zeta
