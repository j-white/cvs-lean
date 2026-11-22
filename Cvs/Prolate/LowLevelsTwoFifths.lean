import Mathlib
import Cvs.L2a.ProlateFamilyQuarterDeep
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.EvenLevelIndexLemma
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RegularSolutionEdge

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The low levels lie below `(2/5)c²`

`ProlateFamilyQuarterDeep`'s Sturm comparison with `sin(cξ/2)/√(1 − ξ²)`, run at the level `(2/5)c²` on `[0, 2/5]`, gives `⌊c/5π⌋` zeros of
the regular solution, hence `⌊c/5π⌋` even levels below `(2/5)c²` (Cvs.Prolate.EvenLevelIndexLemma). For `c ≥ 15π` the level of index `2`
(`h₄`) is below `(2/5)c²`: the angular forbidden region of `h₄` contains `[3/4, 1]`.
-/

noncomputable section

open Real Set Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.RegularSolutionEdge Cvs.Prolate.EdgeCentreSign Cvs.Prolate.EvenLevelIndexLemma Cvs.Prolate.EvenRungsByIndex Cvs.L2a.ProlateFamilyQuarterDeep

namespace Cvs.Prolate.LowLevelsTwoFifths

/-- The comparison potential dominates `c²ξ² − (2/5)c²` on `[0, 2/5]`. -/
theorem sub_lt_rS' {c ξ : ℝ} (h0 : 0 ≤ ξ) (h1 : ξ ≤ 2 / 5) :
    c ^ 2 * ξ ^ 2 - 2 / 5 * c ^ 2 < rS c ξ := by
  have hp : 21 / 25 ≤ 1 - ξ ^ 2 := by nlinarith
  have hq : 0 ≤ ξ ^ 2 / (1 - ξ ^ 2) := div_nonneg (sq_nonneg ξ) (by linarith)
  have hξ2 : ξ ^ 2 ≤ 4 / 25 := by nlinarith
  unfold rS
  nlinarith [sq_nonneg c, mul_le_mul_of_nonneg_left hξ2 (sq_nonneg c)]

/-- **`⌊c/5π⌋` zeros of the regular solution at `(2/5)c²`**, for `c > 0`. -/
theorem hasZeros_two_fifths {c : ℝ} (hc0 : 0 < c) :
    Cvs.Prolate.EvenLevelIndexLemma.HasZeros (sqC c) (2 / 5 * c ^ 2) ⌊c / (5 * π)⌋₊ := by
  set K := ⌊c / (5 * π)⌋₊ with hKdef
  have hK : (K : ℝ) ≤ c / (5 * π) := Nat.floor_le (by positivity)
  set ζ : ℕ → ℝ := fun k => 2 * π * k / c with hζdef
  have hζ0 : ∀ k, 0 ≤ ζ k := fun k => by simp only [hζdef]; positivity
  have hζK : ∀ k ≤ K, ζ k ≤ 2 / 5 := by
    intro k hk
    have hk' : (k : ℝ) ≤ c / (5 * π) := le_trans (by exact_mod_cast hk) hK
    simp only [hζdef]
    rw [div_le_iff₀ hc0]
    have : 2 * π * (k : ℝ) ≤ 2 * π * (c / (5 * π)) := mul_le_mul_of_nonneg_left hk' (by positivity)
    have e : 2 * π * (c / (5 * π)) = 2 / 5 * c := by field_simp
    linarith
  have hζlt : ∀ k, ζ k < ζ (k + 1) := fun k => by
    simp only [hζdef]
    apply div_lt_div_of_pos_right _ hc0
    push_cast
    nlinarith [Real.pi_pos]
  have hζθ : ∀ k, c / 2 * ζ k = (k : ℝ) * π := fun k => by
    simp only [hζdef]; field_simp
  have hzζ : ∀ k, zS c (ζ k) = 0 := fun k => by
    simp only [zS, hζθ, Real.sin_nat_mul_pi, zero_div]
  have hz : ∀ i : Fin K, ∃ x ∈ Ioo (ζ i) (ζ (i + 1)), regSol (sqC c) (2 / 5 * c ^ 2) x = 0 := by
    intro i
    have hα0 := hζ0 i
    have hβ := hζK (i + 1) (by omega)
    have hlo : ∀ ξ ∈ Icc (ζ i) (ζ (i + 1)), -1 < ξ := fun ξ hξ => by linarith [hξ.1]
    have hhi : ∀ ξ ∈ Icc (ζ i) (ζ (i + 1)), ξ < 1 := fun ξ hξ => by linarith [hξ.2]
    refine exists_zero_of_comparison (Q := fun ξ => sqC c ξ) (R := rS c)
      (U := regU (sqC c) (2 / 5 * c ^ 2)) (χ := 2 / 5 * c ^ 2) (z := zS c) (Z := fS c) (by linarith)
      (hζlt i) (by linarith) (fun ξ hξ => ?_) (fun ξ hξ => ?_) (fun ξ hξ => ?_) (fun ξ hξ => ?_) (hzζ i)
      (by exact_mod_cast hzζ (i + 1)) (fun ξ hξ => ?_) (fun ξ hξ => ?_)
    · have hp : pP ξ ≠ 0 := by
        have := hlo ξ hξ; have := hhi ξ hξ; unfold pP; nlinarith
      have h := hasDerivAt_regSol (sqC c) (2 / 5 * c ^ 2) (hlo ξ hξ)
      rwa [← pP_mul_regV (sqC c) (2 / 5 * c ^ 2) (hlo ξ hξ), mul_div_cancel_left₀ _ hp]
    · exact hasDerivAt_regU (sqC c) (2 / 5 * c ^ 2) (hlo ξ hξ)
    · exact hasDerivAt_zS c (hlo ξ hξ) (hhi ξ hξ)
    · exact hasDerivAt_fS c (hlo ξ hξ) (hhi ξ hξ)
    · have hp : 0 < 1 - ξ ^ 2 := by
        have := hlo ξ (Ioo_subset_Icc_self hξ); have := hhi ξ (Ioo_subset_Icc_self hξ); nlinarith
      refine div_ne_zero (fun hs => ?_) (Real.sqrt_pos.2 hp).ne'
      obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hs
      have hl1 : c / 2 * ζ i < c / 2 * ξ := mul_lt_mul_of_pos_left hξ.1 (by positivity)
      have hl2 : c / 2 * ξ < c / 2 * ζ (i + 1) := mul_lt_mul_of_pos_left hξ.2 (by positivity)
      rw [hζθ, ← hn] at hl1
      rw [hζθ, ← hn] at hl2
      have h1 : ((i : ℕ) : ℝ) < n := lt_of_mul_lt_mul_right (by simpa using hl1) pi_pos.le
      have h2 : (n : ℝ) < ((i : ℕ) : ℝ) + 1 := by
        have : (n : ℝ) * π < (((i : ℕ) : ℝ) + 1) * π := by simpa using hl2
        exact lt_of_mul_lt_mul_right this pi_pos.le
      have h1' : ((i : ℕ) : ℤ) < n := by exact_mod_cast h1
      have h2' : n < ((i : ℕ) : ℤ) + 1 := by exact_mod_cast h2
      omega
    · exact sub_lt_rS' (by linarith [hξ.1]) (by linarith [hξ.2])
  choose x hxI hx0 using hz
  refine ⟨x, fun i j hij => ?_, fun i => ⟨?_, ?_⟩, hx0⟩
  · have hij' : (i : ℕ) + 1 ≤ j := hij
    have h1 : ζ ((i : ℕ) + 1) ≤ ζ j := by
      simp only [hζdef]
      apply div_le_div_of_nonneg_right _ hc0.le
      have : (((i : ℕ) + 1 : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hij'
      push_cast at this ⊢
      nlinarith [Real.pi_pos]
    linarith [(hxI i).2, (hxI j).1]
  · linarith [(hxI i).1, hζ0 i]
  · linarith [(hxI i).2, hζK ((i : ℕ) + 1) (by omega)]

/-- **The level of `h₄` lies below `(2/5)c²`** for `c ≥ 15π`. -/
theorem lev_two_lt {c : ℝ} (hc : 15 * π ≤ c) : lev c 2 < 2 / 5 * c ^ 2 ∧ ∃ χ, IsLevelIdx c 2 χ := by
  have hc0 : 0 < c := lt_of_lt_of_le (by positivity) hc
  have h3 : 3 ≤ ⌊c / (5 * π)⌋₊ := by
    rw [Nat.le_floor_iff (by positivity), le_div_iff₀ (by positivity)]
    push_cast; linarith
  have hcount := le_ncard_evenSpec (hasZeros_two_fifths hc0)
  obtain ⟨χ, hχ, hidx⟩ := exists_isLevelIdx_of_lt_ncard (c := c) (χ := 2 / 5 * c ^ 2) (k := 2) (by omega)
  have he := (lev_spec ⟨χ, hidx⟩).unique hidx
  exact ⟨he ▸ hχ, χ, hidx⟩

end Cvs.Prolate.LowLevelsTwoFifths
