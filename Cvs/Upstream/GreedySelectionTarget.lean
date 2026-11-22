import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Greedy selection against a nondecreasing target

Scanning a finite `P ⊆ ℝ` upward and keeping `p` exactly when fewer than `Φ(p)` points are kept below it gives `S ⊆ P`
with `#S(−∞, y] ≤ Φ(y) + 1`; if every increment of `Φ` is at most that of `G` and `P` counts like `G` up to `E`, then
`#S(−∞, y] ≥ Φ(y) − 2E`.
-/

noncomputable section

open Finset

namespace Cvs.Upstream.GreedySelectionTarget

/-- The count `#{p ∈ P : p ≤ y}`. -/
def cnt (P : Finset ℝ) (y : ℝ) : ℕ := (P.filter (· ≤ y)).card

theorem cnt_eq_card {T : Finset ℝ} {y : ℝ} (h : ∀ x ∈ T, x ≤ y) : cnt T y = T.card := by
  unfold cnt; rw [filter_true_of_mem h]

theorem cnt_insert_of_lt {T : Finset ℝ} {p y : ℝ} (hy : y < p) : cnt (insert p T) y = cnt T y := by
  classical
  unfold cnt; rw [filter_insert, if_neg (not_le.mpr hy)]

/-- **Greedy selection**: `S ⊆ P` with `#S(−∞, y] ≤ Φ(y) + 1`; below every `y` either nothing was rejected or some
rejected `ρ ≤ y` has `Φ(ρ) + #P(ρ, y] ≤ #S(−∞, y]`; and every rejected `p` has `Φ(p) ≤ #S(−∞, p)`. -/
theorem exists_greedy (P : Finset ℝ) {Φ : ℝ → ℝ} (hΦ : Monotone Φ) (hΦ0 : ∀ y, 0 ≤ Φ y) :
    ∃ S ⊆ P, (∀ y, (cnt S y : ℝ) ≤ Φ y + 1) ∧
      (∀ y, cnt S y = cnt P y ∨ ∃ ρ ∈ P, ρ ≤ y ∧ ρ ∉ S ∧ Φ ρ + (cnt P y : ℝ) - cnt P ρ ≤ cnt S y) ∧
      (∀ p ∈ P, p ∉ S → Φ p ≤ ((S.filter (· < p)).card : ℝ)) := by
  classical
  induction P using Finset.induction_on_max with
  | empty => exact ⟨∅, subset_refl _, fun y => by simp [cnt]; linarith [hΦ0 y], fun y => Or.inl (by simp [cnt]),
      fun p hp => absurd hp (Finset.notMem_empty p)⟩
  | insert p P' hlt ih =>
    obtain ⟨S', hS', h1, h2, h3⟩ := ih
    have hpP' : p ∉ P' := fun h => lt_irrefl p (hlt p h)
    have hpS' : p ∉ S' := fun h => hpP' (hS' h)
    have hS'lt : ∀ x ∈ S', x < p := fun x hx => hlt x (hS' hx)
    have cP : ∀ y, p ≤ y → cnt (insert p P') y = P'.card + 1 := fun y hy => by
      rw [cnt_eq_card fun x hx => ?_, card_insert_of_notMem hpP']
      rcases mem_insert.mp hx with rfl | hx
      · exact hy
      · exact (hlt x hx).le.trans hy
    have cP' : ∀ y, p ≤ y → cnt P' y = P'.card := fun y hy => cnt_eq_card fun x hx => (hlt x hx).le.trans hy
    have cS' : ∀ y, p ≤ y → cnt S' y = S'.card := fun y hy => cnt_eq_card fun x hx => (hS'lt x hx).le.trans hy
    have hρlt : ∀ ρ ∈ P', cnt (insert p P') ρ = cnt P' ρ := fun ρ hρ => cnt_insert_of_lt (hlt ρ hρ)
    have hfS' : (S'.filter (· < p)).card = S'.card := by rw [filter_true_of_mem hS'lt]
    by_cases hsel : (S'.card : ℝ) < Φ p
    · -- keep `p`
      refine ⟨insert p S', insert_subset_insert p hS', fun y => ?_, fun y => ?_, fun q hq hqS => ?_⟩
      · rcases lt_or_ge y p with hy | hy
        · rw [cnt_insert_of_lt hy]; exact h1 y
        · rw [cnt_eq_card fun x hx => ?_, card_insert_of_notMem hpS']
          · push_cast; linarith [hΦ hy]
          · rcases mem_insert.mp hx with rfl | hx
            · exact hy
            · exact (hS'lt x hx).le.trans hy
      · rcases lt_or_ge y p with hy | hy
        · rw [cnt_insert_of_lt hy, cnt_insert_of_lt hy]
          rcases h2 y with h | ⟨ρ, hρ, hρy, hρS, hb⟩
          · exact Or.inl h
          · refine Or.inr ⟨ρ, mem_insert_of_mem hρ, hρy, fun h => ?_, by rw [hρlt ρ hρ]; exact hb⟩
            rcases mem_insert.mp h with rfl | h
            · exact lt_irrefl _ (hρy.trans_lt hy)
            · exact hρS h
        · have hcS : cnt (insert p S') y = S'.card + 1 := by
            rw [cnt_eq_card fun x hx => ?_, card_insert_of_notMem hpS']
            rcases mem_insert.mp hx with rfl | hx
            · exact hy
            · exact (hS'lt x hx).le.trans hy
          rw [hcS, cP y hy]
          rcases h2 p with h | ⟨ρ, hρ, hρy, hρS, hb⟩
          · left; rw [← cS' p le_rfl, h, cP' p le_rfl]
          · right
            refine ⟨ρ, mem_insert_of_mem hρ, hρy.trans hy, fun h => ?_, ?_⟩
            · rcases mem_insert.mp h with rfl | h
              · exact hpP' hρ
              · exact hρS h
            · rw [hρlt ρ hρ]; rw [cS' p le_rfl, cP' p le_rfl] at hb; push_cast; linarith
      · rcases mem_insert.mp hq with rfl | hq
        · exact absurd (mem_insert_self _ _) hqS
        · have hqS' : q ∉ S' := fun h => hqS (mem_insert_of_mem h)
          have hfil : (insert p S').filter (· < q) = S'.filter (· < q) := by
            rw [filter_insert, if_neg (not_lt.mpr (hlt q hq).le)]
          rw [hfil]; exact h3 q hq hqS'
    · -- reject `p`
      push Not at hsel
      refine ⟨S', (hS').trans (subset_insert p P'), fun y => h1 y, fun y => ?_, fun q hq hqS => ?_⟩
      · rcases lt_or_ge y p with hy | hy
        · rw [cnt_insert_of_lt hy]
          rcases h2 y with h | ⟨ρ, hρ, hρy, hρS, hb⟩
          · exact Or.inl h
          · exact Or.inr ⟨ρ, mem_insert_of_mem hρ, hρy, hρS, by rw [hρlt ρ hρ]; exact hb⟩
        · right
          refine ⟨p, mem_insert_self _ _, hy, hpS', ?_⟩
          rw [cP y hy, cP p le_rfl, cS' y hy]; linarith
      · rcases mem_insert.mp hq with rfl | hq
        · rw [hfS']; exact hsel
        · exact h3 q hq hqS

end Cvs.Upstream.GreedySelectionTarget

end
