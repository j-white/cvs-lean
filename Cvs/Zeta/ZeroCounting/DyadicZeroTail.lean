import Mathlib
import Cvs.Zeta.CompletedZeroIndex
import Cvs.Zeta.ZeroCounting.DyadicZeroBlock
import Cvs.Zeta.ZetaZeroWindows

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The tail, assembled over dyadic blocks

Iterating `Cvs.Zeta.ZeroCounting.DyadicZeroBlock` from `H` to `2^n H` bounds the whole tail by one explicit sum, each term the
block's left value against the count's price for that block.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real Cvs.Zeta.Explicit.Venue

open scoped Classical

namespace Cvs.Zeta.ZeroCounting.DyadicZeroTail
open Cvs.ZeroFree

/-- Nested windows split a difference in two. -/
theorem sum_sdiff_split {α : Type*} [DecidableEq α] {A B C : Finset α}
    (hAB : A ⊆ B) (hBC : B ⊆ C) (g : α → ℝ) :
    ∑ x ∈ C \ A, g x = ∑ x ∈ C \ B, g x + ∑ x ∈ B \ A, g x := by
  have h1 := Finset.sum_sdiff (f := g) hAB
  have h2 := Finset.sum_sdiff (f := g) hBC
  have h3 := Finset.sum_sdiff (f := g) (hAB.trans hBC)
  linarith

/-- **The tail over `n` dyadic blocks.** -/
theorem tail_le {H : ℝ} (hH : 9 + Real.exp 1 ≤ 2 * H) {f : ℝ → ℝ}
    (hf : ∀ a b : ℝ, H ≤ a → a ≤ b → f b ≤ f a)
    (hf0 : ∀ t : ℝ, H ≤ t → 0 ≤ f t) (n : ℕ) :
    ∑ rho ∈ nontrivialZetaZeroWindowFinset ((2:ℝ) ^ n * H) \
        nontrivialZetaZeroWindowFinset H,
        (completedZetaZeroMultiplicity rho : ℝ) * f |(nontrivialZetaZeroValue rho).im|
      ≤ ∑ j ∈ Finset.range n,
          f ((2:ℝ) ^ j * H) * (8 * ((2:ℝ) ^ j * H) * Real.log (2 * ((2:ℝ) ^ j * H))) := by
  have hH0 : (0:ℝ) ≤ H := by nlinarith [Real.exp_pos 1]
  induction n with
  | zero => simp
  | succ n ih =>
      have hpow : (1:ℝ) ≤ (2:ℝ) ^ n := one_le_pow₀ (by norm_num)
      have hHn : H ≤ (2:ℝ) ^ n * H := by nlinarith
      have hsucc : (2:ℝ) ^ (n + 1) * H = 2 * ((2:ℝ) ^ n * H) := by ring
      have hsub1 : nontrivialZetaZeroWindowFinset H ⊆
          nontrivialZetaZeroWindowFinset ((2:ℝ) ^ n * H) :=
        Cvs.Zeta.ZeroCounting.DyadicZeroBlock.window_subset hHn
      have hsub2 : nontrivialZetaZeroWindowFinset ((2:ℝ) ^ n * H) ⊆
          nontrivialZetaZeroWindowFinset ((2:ℝ) ^ (n + 1) * H) := by
        refine Cvs.Zeta.ZeroCounting.DyadicZeroBlock.window_subset ?_
        rw [hsucc]; nlinarith
      rw [sum_sdiff_split hsub1 hsub2, Finset.sum_range_succ]
      have hblockH : 9 + Real.exp 1 ≤ 2 * ((2:ℝ) ^ n * H) := by nlinarith
      have hfn : ∀ t : ℝ, (2:ℝ) ^ n * H ≤ t → f t ≤ f ((2:ℝ) ^ n * H) :=
        fun t ht => hf _ t hHn ht
      have hfn0 : (0:ℝ) ≤ f ((2:ℝ) ^ n * H) := hf0 _ hHn
      have hblock := Cvs.Zeta.ZeroCounting.DyadicZeroBlock.block_le_count hblockH hfn hfn0
      rw [hsucc]
      linarith [ih, hblock]

end Cvs.Zeta.ZeroCounting.DyadicZeroTail
