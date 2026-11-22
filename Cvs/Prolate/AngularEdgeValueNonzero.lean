import Mathlib
import Cvs.Prolate.CosineTransformEigenRelation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The edge value is nonzero: an angular solution vanishing at `s = 1` vanishes on `[−1, 1]`

At `s = 1` the angular equation forces `g'(1) = 0`; the flux `(1 − s²)g'` then has derivative `(c²s² − χ)g`, so on
`[1 − δ, 1]` both `|g'|` and `|g|/δ` are at most `(c² + |χ|)·max|g|`, which forces `g = 0` there once `δ` is small.
Cvs.Prolate.CosineTransformEigenRelation.eq_zero_of_initial spreads the zero data from an interior point to `[−1, 1]`.
-/

namespace Cvs.Prolate.AngularEdgeValueNonzero

open Real Set

/-- **Edge uniqueness**: a `C²` angular solution on `[−1, 1]` with `g(1) = 0` vanishes on `[−1, 1]`. -/
theorem eq_zero_of_edge {c χ : ℝ} {g g₁ g₂ : ℝ → ℝ}
    (hg : ∀ s ∈ Icc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ Icc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (he : ∀ s ∈ Icc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (h1 : g 1 = 0) :
    ∀ s ∈ Icc (-1 : ℝ) 1, g s = 0 := by
  have hm1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  -- the equation at `s = 1` forces `g'(1) = 0`
  have h11 : g₁ 1 = 0 := by have := he 1 hm1; rw [h1] at this; linarith
  set K := c ^ 2 + |χ| with hK
  have hK0 : 0 ≤ K := by positivity
  set δ := 1 / (2 * (K + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδK : K * δ ≤ 1 / 2 := by
    rw [hδ, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hδ1 : δ ≤ 1 / 2 := by
    rw [hδ, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  set s₁ := 1 - δ with hs₁
  set I := Icc s₁ 1 with hI
  have hIsub : ∀ s ∈ I, s ∈ Icc (-1 : ℝ) 1 := fun s hs => ⟨by linarith [hs.1], hs.2⟩
  have hIne : I.Nonempty := ⟨1, by rw [hI]; exact ⟨by linarith, le_rfl⟩⟩
  have h1I : (1 : ℝ) ∈ I := ⟨by linarith, le_rfl⟩
  -- the point of `I` where `|g|` is largest
  have hgc : ContinuousOn (fun s => |g s|) I :=
    fun s hs => (hg s (hIsub s hs)).continuousAt.continuousWithinAt.abs
  obtain ⟨s', hs', hmax⟩ := isCompact_Icc.exists_isMaxOn hIne hgc
  set M := |g s'| with hM
  have hgM : ∀ s ∈ I, |g s| ≤ M := fun s hs => hmax hs
  have hM0 : 0 ≤ M := abs_nonneg _
  -- the flux bound `|(1 − s²) g'(s)| ≤ K M (1 − s)`
  have hflux : ∀ s ∈ I, |(1 - s ^ 2) * g₁ s| ≤ K * M * (1 - s) := by
    intro s hs
    have hF : ∀ x ∈ I, HasDerivWithinAt (fun x => (1 - x ^ 2) * g₁ x) ((c ^ 2 * x ^ 2 - χ) * g x) I x := by
      intro x hx
      have hp : HasDerivAt (fun s : ℝ => 1 - s ^ 2) (-(2 * x)) x := by
        simpa using ((hasDerivAt_pow 2 x).const_sub 1)
      refine ((hp.mul (hg₁ x (hIsub x hx))).congr_deriv ?_).hasDerivWithinAt
      linear_combination he x (hIsub x hx)
    have hbd : ∀ x ∈ I, ‖(c ^ 2 * x ^ 2 - χ) * g x‖ ≤ K * M := by
      intro x hx
      have hx2 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
      rw [Real.norm_eq_abs, abs_mul]
      have hcx : |c ^ 2 * x ^ 2 - χ| ≤ K := by
        calc |c ^ 2 * x ^ 2 - χ| ≤ |c ^ 2 * x ^ 2| + |χ| := abs_sub _ _
          _ ≤ K := by rw [abs_of_nonneg (by positivity), hK]; nlinarith [sq_nonneg c]
      exact mul_le_mul hcx (hgM x hx) (abs_nonneg _) hK0
    have := (convex_Icc s₁ 1).norm_image_sub_le_of_norm_hasDerivWithin_le hF hbd hs h1I
    simp only [Real.norm_eq_abs, one_pow, sub_self, zero_mul, zero_sub, abs_neg] at this
    rwa [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s)] at this
  -- hence `|g'| ≤ K M` on `I`
  have hder : ∀ s ∈ I, |g₁ s| ≤ K * M := by
    intro s hs
    rcases eq_or_lt_of_le hs.2 with h | h
    · rw [h, h11, abs_zero]; positivity
    · have hs0 : 0 ≤ s := by linarith [hs.1]
      have hf := hflux s hs
      rw [abs_mul, abs_of_nonneg (by nlinarith [hs.2] : (0 : ℝ) ≤ 1 - s ^ 2)] at hf
      have h1s : 0 < 1 - s := by linarith
      have : (1 - s) * |g₁ s| ≤ (1 - s) * (K * M) := by
        nlinarith [mul_nonneg (mul_nonneg h1s.le hs0) (abs_nonneg (g₁ s))]
      exact le_of_mul_le_mul_left this h1s
  -- hence `|g| ≤ K M δ ≤ M / 2` on `I`, so `M = 0`
  have hgval : ∀ s ∈ I, |g s| ≤ K * M * δ := by
    intro s hs
    have := (convex_Icc s₁ 1).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x hx => (hg x (hIsub x hx)).hasDerivWithinAt) (fun x hx => hder x hx) hs h1I
    simp only [Real.norm_eq_abs, h1, zero_sub, abs_neg] at this
    rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s)] at this
    calc |g s| ≤ K * M * (1 - s) := this
      _ ≤ K * M * δ := mul_le_mul_of_nonneg_left (by linarith [hs.1]) (by positivity)
  have hMz : M = 0 := by
    have := hgval s' hs'
    rw [← hM] at this
    have : K * M * δ ≤ M / 2 := by nlinarith
    linarith
  -- zero data at an interior point
  set s₀ := 1 - δ / 2 with hs₀
  have hs₀I : s₀ ∈ I := ⟨by linarith, by linarith⟩
  have hs₀Ioo : s₀ ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hz0 : g s₀ = 0 := abs_eq_zero.1 (le_antisymm (hMz ▸ hgM s₀ hs₀I) (abs_nonneg _))
  have hz1 : g₁ s₀ = 0 := abs_eq_zero.1 (le_antisymm (by simpa [hMz] using hder s₀ hs₀I) (abs_nonneg _))
  have hIoo : ∀ s ∈ Ioo (-1 : ℝ) 1, s ∈ Icc (-1 : ℝ) 1 := fun s hs => Ioo_subset_Icc_self hs
  have hz := Cvs.Prolate.CosineTransformEigenRelation.eq_zero_of_initial (fun s hs => hg s (hIoo s hs)) (fun s hs => hg₁ s (hIoo s hs))
    (fun s hs => he s (hIoo s hs)) hs₀Ioo hz0 hz1
  have hcont : ContinuousOn g (Icc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  have heq : EqOn g (fun _ => (0 : ℝ)) (Icc (-1) 1) :=
    EqOn.of_subset_closure hz hcont continuousOn_const Ioo_subset_Icc_self (by rw [closure_Ioo (by norm_num)])
  exact fun s hs => heq hs

/-- **The edge value is nonzero**: a `C²` angular solution on `[−1, 1]`, nonzero at some point there, has
`g(1) ≠ 0`. -/
theorem edge_ne_zero {c χ s₀ : ℝ} {g g₁ g₂ : ℝ → ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (he : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hs₀ : s₀ ∈ Icc (-1 : ℝ) 1) (hg0 : g s₀ ≠ 0) :
    g 1 ≠ 0 := by
  have hI : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  rw [hI] at hg hg₁ he
  exact fun h1 => hg0 (eq_zero_of_edge hg hg₁ he h1 s₀ hs₀)

end Cvs.Prolate.AngularEdgeValueNonzero
