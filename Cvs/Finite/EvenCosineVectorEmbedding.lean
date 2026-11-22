import Mathlib
import Cvs.Approximant.ConnesTailWeightedEnergy
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Finite.SymmetricModeSet
import Cvs.WeilForm.EvenBoundaryKernelBound
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.WeilFormOnWindowL2

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Exact embeddings of finite even cosine vectors

The retained cosine coefficients preserve the represented form class and
coefficient square norm when embedded into any larger signed mode set.
-/

noncomputable section

open Real Finset

namespace Cvs.Finite.EvenCosineVectorEmbedding
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet (Idx negI)

/-- The positive coefficient sequence of a finite signed vector, extended by zero. -/
def positiveCoef (N : ℕ) (f : Idx N → ℝ) (k : ℕ) : ℝ :=
  if hk : k < N then f (some (⟨k, hk⟩, true)) else 0

/-- The unsigned cosine sequence representing a finite reflection-even vector. -/
def scalarCoef (N : ℕ) (f : Idx N → ℝ) : ℕ → ℝ
  | 0 => f none
  | k + 1 => 2 * positiveCoef N f k

/-- A finite even cosine vector embedded by its retained scalar coefficients. -/
def embed (N J : ℕ) (f : Idx N → ℝ) : Idx J → ℝ :=
  Cvs.Finite.SymmetricModeSet.coeff J (range (N + 1)) (scalarCoef N f)

theorem embed_even (N J : ℕ) (f : Idx N → ℝ) (i : Idx J) :
    embed N J f (negI J i) = embed N J f i := Cvs.Finite.SymmetricModeSet.coeff_even J _ _ i

theorem embed_none (N J : ℕ) (f : Idx N → ℝ) : embed N J f none = f none := by
  simp [embed, Cvs.Finite.SymmetricModeSet.coeff, scalarCoef]

theorem embed_some (N J : ℕ) (f : Idx N → ℝ) (k : Fin J) (b : Bool) :
    embed N J f (some (k, b)) = positiveCoef N f k.val := by
  simp only [embed, Cvs.Finite.SymmetricModeSet.coeff, mem_range, scalarCoef]
  by_cases hk : k.val < N
  · rw [if_pos (by omega)]
    ring
  · rw [if_neg (by omega)]
    simp [positiveCoef, hk]

/-- Scalar reconstruction is exact for every finite reflection-even vector. -/
theorem coeff_self (N : ℕ) (f : Idx N → ℝ)
    (heven : ∀ i, f (negI N i) = f i) :
    Cvs.Finite.SymmetricModeSet.coeff N (range (N + 1)) (scalarCoef N f) = f := by
  change embed N N f = f
  funext i
  rcases i with _ | ⟨k, b⟩
  · exact embed_none N N f
  · rw [embed_some]
    simp only [positiveCoef, dif_pos k.isLt]
    cases b
    · exact (Cvs.WeilForm.EvenBoundaryKernelBound.idx_even_pair N f heven k).symm
    · rfl

/-- A larger mode set represents exactly the same form-domain vector. -/
theorem modeMap_embed {x : ℕ} (hx0 : (0 : ℝ) < x) {N J : ℕ} (hNJ : N ≤ J)
    (f : Idx N → ℝ) (heven : ∀ i, f (negI N i) = f i) :
    Cvs.Approximant.CosineColumnTailPairing.modeMap hx0 J (embed N J f) = Cvs.Approximant.CosineColumnTailPairing.modeMap hx0 N f := by
  have h := Cvs.Approximant.ConnesTailWeightedEnergy.modeMap_coeff_eq hx0 N J (range (N + 1)) (scalarCoef N f)
    subset_rfl (range_mono (by omega))
  rw [coeff_self N f heven] at h
  exact h

/-- Zero extension preserves the positive coefficient square sum. -/
theorem sum_positiveCoef_sq {N J : ℕ} (hNJ : N ≤ J) (f : Idx N → ℝ) :
    (∑ k : Fin J, positiveCoef N f k.val ^ 2) =
      ∑ k : Fin N, f (some (k, true)) ^ 2 := by
  have hN : (∑ k : Fin N, positiveCoef N f k.val ^ 2) =
      ∑ k : Fin N, f (some (k, true)) ^ 2 := by
    apply sum_congr rfl
    intro k _
    simp [positiveCoef, k.isLt]
  rw [← hN, Fin.sum_univ_eq_sum_range (fun k => positiveCoef N f k ^ 2) J,
    Fin.sum_univ_eq_sum_range (fun k => positiveCoef N f k ^ 2) N]
  symm
  apply sum_subset (range_mono hNJ)
  intro k _ hk
  simp only [mem_range, not_lt] at hk
  simp [positiveCoef, not_lt.mpr hk]

/-- Embedding into a larger order preserves the complete signed coefficient norm. -/
theorem sum_embed_sq {N J : ℕ} (hNJ : N ≤ J) (f : Idx N → ℝ)
    (heven : ∀ i, f (negI N i) = f i) :
    (∑ i : Idx J, embed N J f i ^ 2) = ∑ i : Idx N, f i ^ 2 := by
  rw [Cvs.WeilForm.EvenBoundaryKernelBound.idx_even_sq J _ (embed_even N J f),
    Cvs.WeilForm.EvenBoundaryKernelBound.idx_even_sq N _ heven, embed_none]
  simp_rw [embed_some]
  rw [sum_positiveCoef_sq hNJ]

/-- Retained arbitrary cosine coefficients and the actual omitted Connes coefficients are disjoint. -/
theorem tailCoef_disjoint (x N J : ℕ) (f : Idx N → ℝ) (i : Idx J) :
    embed N J f i * Cvs.Approximant.ConnesTailWeightedEnergy.tailCoef x N J i = 0 := by
  rcases i with _ | ⟨k, b⟩
  · rw [Cvs.Approximant.ConnesTailWeightedEnergy.tailCoef_none, mul_zero]
  · rw [embed_some, Cvs.Approximant.ConnesTailWeightedEnergy.tailCoef_some]
    by_cases hk : k.val < N
    · rw [if_neg (by omega), mul_zero]
    · simp [positiveCoef, hk]

end Cvs.Finite.EvenCosineVectorEmbedding
