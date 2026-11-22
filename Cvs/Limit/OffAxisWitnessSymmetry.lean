import Mathlib
import Cvs.Limit.OffAxesLimit
import Cvs.Upstream.OffAxisFourQuadrants

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# One witness off the axes gives one in every quadrant, by symmetry

For a function that is even and conjugate-symmetric off both coordinate axes, a single point there
at which it does not vanish yields such a point in each of the four quadrants of `Cvs.Upstream.OffAxisFourQuadrants.quad`,
since `w`, `-w`, `conj w` and `-conj w` realise all four pairs of signs.
-/

noncomputable section

open Complex

namespace Cvs.Limit.OffAxisWitnessSymmetry

open Cvs.Limit.OffAxesLimit
open Cvs.Upstream.OffAxisFourQuadrants

/-- The off-axis set is closed under negation. -/
theorem neg_mem_offAxes {z : ℂ} (hz : z ∈ offAxes) : -z ∈ offAxes :=
  ⟨by rw [Complex.neg_re]; exact neg_ne_zero.mpr hz.1,
   by rw [Complex.neg_im]; exact neg_ne_zero.mpr hz.2⟩

/-- The off-axis set is closed under conjugation. -/
theorem conj_mem_offAxes {z : ℂ} (hz : z ∈ offAxes) : (starRingEnd ℂ) z ∈ offAxes :=
  ⟨by rw [Complex.conj_re]; exact hz.1,
   by rw [Complex.conj_im]; exact neg_ne_zero.mpr hz.2⟩

/-- An even, conjugate-symmetric function non-zero somewhere off the axes is non-zero at a point
of every quadrant. -/
theorem exists_quad_of_symm {f : ℂ → ℂ}
    (heven : ∀ z ∈ offAxes, f (-z) = f z)
    (hconj : ∀ z ∈ offAxes, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z))
    {w₀ : ℂ} (hw₀ : w₀ ∈ offAxes) (hfw₀ : f w₀ ≠ 0)
    {s t : ℝ} (hs : s ≠ 0) (ht : t ≠ 0) :
    ∃ w ∈ quad s t, f w ≠ 0 := by
  have hcw : (starRingEnd ℂ) (f w₀) ≠ 0 := by simpa using hfw₀
  have hsa : s * w₀.re ≠ 0 := mul_ne_zero hs hw₀.1
  have htb : t * w₀.im ≠ 0 := mul_ne_zero ht hw₀.2
  rcases lt_or_gt_of_ne hsa with hsa' | hsa' <;>
    rcases lt_or_gt_of_ne htb with htb' | htb'
  · -- both signs wrong: negate, which flips both parts and fixes `f` by evenness
    refine ⟨-w₀, ⟨?_, ?_⟩, ?_⟩
    · rw [Complex.neg_re, mul_neg]; linarith
    · rw [Complex.neg_im, mul_neg]; linarith
    · rw [heven w₀ hw₀]; exact hfw₀
  · -- real part wrong, imaginary part right: negate the conjugate
    refine ⟨-(starRingEnd ℂ) w₀, ⟨?_, ?_⟩, ?_⟩
    · rw [Complex.neg_re, Complex.conj_re, mul_neg]; linarith
    · rw [Complex.neg_im, Complex.conj_im, neg_neg]; exact htb'
    · rw [heven _ (conj_mem_offAxes hw₀), hconj w₀ hw₀]; exact hcw
  · -- real part right, imaginary part wrong: conjugate
    refine ⟨(starRingEnd ℂ) w₀, ⟨?_, ?_⟩, ?_⟩
    · rw [Complex.conj_re]; exact hsa'
    · rw [Complex.conj_im, mul_neg]; linarith
    · rw [hconj w₀ hw₀]; exact hcw
  · exact ⟨w₀, ⟨hsa', htb'⟩, hfw₀⟩

end Cvs.Limit.OffAxisWitnessSymmetry
