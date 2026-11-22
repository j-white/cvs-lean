import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.CosineTransformSignLaw
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.SlepianEvenOrdering

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Slepian's sign rule

The finite cosine transform eigenvalue of the even rung of index `k` (the prolate `h_{2k}`) has sign `(−1)^k`:
`0 < (−1)^k muR c k`. From `CosineTransformSignLaw`'s `0 < μ g(0)g(1)` and `EdgeCentreSign`'s `0 < g(0)g(1) ↔ k` even.
-/

noncomputable section

open Real Set

namespace Cvs.Prolate.SlepianSignRule

open Cvs.Prolate.EvenRungsByIndex

/-- **The sign by index, both parities**: an even angular eigenfunction of the finite cosine transform has
`0 < (−1)^k μ`, `k` the number of even levels below its own. -/
theorem neg_one_pow_mul_mu_pos {g g₁ g₂ : ℝ → ℝ} {c χ μ : ℝ} (hc : 0 < c)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0)
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, Cvs.L2a.AngularProlateTailPositive.psi c g s = μ * g s) :
    0 < (-1 : ℝ) ^ (Cvs.Prolate.EdgeCentreSign.evenSpec (Cvs.Prolate.RegularSolutionEdge.sqC c) ∩ Iio χ).ncard * μ := by
  have hχ0 := Cvs.Prolate.SlepianEvenOrdering.nonneg_of_mem_evenSpec c
    (Cvs.Prolate.EdgeCentreSign.mem_evenSpec_of_angular hg hg₁ hang heven hg0)
  have hm := Cvs.Prolate.CosineTransformSignLaw.mu_sign hc hχ0 hg hg₁ hg₂c hang heven hg0 hμ
  have he := Cvs.Prolate.EdgeCentreSign.edge_centre_pos_iff hg hg₁ hang heven hg0
  rcases Nat.even_or_odd (Cvs.Prolate.EdgeCentreSign.evenSpec (Cvs.Prolate.RegularSolutionEdge.sqC c) ∩ Iio χ).ncard
    with hk | hk
  · rw [hk.neg_one_pow, one_mul]
    exact (pos_iff_pos_of_mul_pos hm).mpr (he.mpr hk)
  · rw [hk.neg_one_pow, neg_one_mul, neg_pos]
    have hp : ¬ 0 < g 0 * g 1 := fun h => (Nat.not_even_iff_odd.mpr hk) (he.mp h)
    have hp' : g 0 * g 1 ≤ 0 := not_lt.mp hp
    by_contra hμn
    have hμn' : 0 ≤ μ := not_lt.mp hμn
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hμn' hp']

/-- **Slepian's sign rule**: `0 < (−1)^k muR c k` for every even rung index `k` that exists. -/
theorem neg_one_pow_mul_muR_pos {c : ℝ} {k : ℕ} (hc : 0 < c) (h : ∃ χ, IsLevelIdx c k χ) :
    0 < (-1 : ℝ) ^ k * muR c k := by
  obtain ⟨hg, hg₁, hg₂c, hang, heven, -⟩ := rung_spec h
  have := neg_one_pow_mul_mu_pos hc hg hg₁ hg₂c hang heven (rung_ne_zero h) (psi_rung h)
  rwa [(lev_spec h).2] at this

/-- **Odd index, negative eigenvalue**: `muR c k < 0` for odd `k`. -/
theorem muR_neg_of_odd {c : ℝ} {k : ℕ} (hc : 0 < c) (h : ∃ χ, IsLevelIdx c k χ) (hk : Odd k) :
    muR c k < 0 := by
  have := neg_one_pow_mul_muR_pos hc h
  rw [hk.neg_one_pow, neg_one_mul, neg_pos] at this
  exact this

end Cvs.Prolate.SlepianSignRule
