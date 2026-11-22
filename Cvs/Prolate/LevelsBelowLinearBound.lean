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
# The levels lie below `2π(k + 1)c`

`ProlateFamilyQuarterDeep`'s Sturm comparison with `sin(wξ/2)/√(1 − ξ²)` at a free frequency `w`: if `c²ξ² − Λ < R_w(ξ)` up to the
`K`-th zero `2πK/w < 1`, the regular solution at `Λ` has `K` zeros in `(0, 1)`. At `w² = 4πKc`, `Λ = 2πKc`, the
`K`-th zero is `√(πK/c)` and the comparison holds there; so for `π(k + 1) < c` the level of index `k` exists and lies
below `2π(k + 1)c`, linear in `c`.
-/

noncomputable section

open Real Set Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.RegularSolutionEdge Cvs.Prolate.EvenLevelIndexLemma Cvs.Prolate.EvenRungsByIndex Cvs.L2a.ProlateFamilyQuarterDeep

namespace Cvs.Prolate.LevelsBelowLinearBound

/-- **Zeros from a comparison frequency**: if `0 < w`, `2πK/w < 1` and `c²ξ² − Λ < R_w(ξ)` on `[0, 2πK/w]`, the
regular solution at `Λ` has `K` zeros in `(0, 1)`. -/
theorem hasZeros_of_freq {c w Λ : ℝ} {K : ℕ} (hw : 0 < w) (hK1 : 2 * π * K / w < 1)
    (hR : ∀ ξ, 0 ≤ ξ → ξ ≤ 2 * π * K / w → c ^ 2 * ξ ^ 2 - Λ < rS w ξ) :
    HasZeros (sqC c) Λ K := by
  set ζ : ℕ → ℝ := fun k => 2 * π * k / w with hζdef
  have hζ0 : ∀ k, 0 ≤ ζ k := fun k => by simp only [hζdef]; positivity
  have hζK : ∀ k ≤ K, ζ k ≤ ζ K := fun k hk => by
    simp only [hζdef]
    apply div_le_div_of_nonneg_right _ hw.le
    have : (k : ℝ) ≤ K := by exact_mod_cast hk
    nlinarith [Real.pi_pos]
  have hζlt : ∀ k, ζ k < ζ (k + 1) := fun k => by
    simp only [hζdef]
    apply div_lt_div_of_pos_right _ hw
    push_cast
    nlinarith [Real.pi_pos]
  have hζθ : ∀ k, w / 2 * ζ k = (k : ℝ) * π := fun k => by
    simp only [hζdef]; field_simp
  have hzζ : ∀ k, zS w (ζ k) = 0 := fun k => by
    simp only [zS, hζθ, Real.sin_nat_mul_pi, zero_div]
  have hz : ∀ i : Fin K, ∃ x ∈ Ioo (ζ i) (ζ (i + 1)), regSol (sqC c) Λ x = 0 := by
    intro i
    have hα0 := hζ0 i
    have hβ := hζK (i + 1) (by omega)
    have hlo : ∀ ξ ∈ Icc (ζ i) (ζ (i + 1)), -1 < ξ := fun ξ hξ => by linarith [hξ.1]
    have hhi : ∀ ξ ∈ Icc (ζ i) (ζ (i + 1)), ξ < 1 := fun ξ hξ => by linarith [hξ.2]
    refine exists_zero_of_comparison (Q := fun ξ => sqC c ξ) (R := rS w)
      (U := regU (sqC c) Λ) (χ := Λ) (z := zS w) (Z := fS w) (by linarith)
      (hζlt i) (by linarith) (fun ξ hξ => ?_) (fun ξ hξ => ?_) (fun ξ hξ => ?_) (fun ξ hξ => ?_) (hzζ i)
      (by exact_mod_cast hzζ (i + 1)) (fun ξ hξ => ?_) (fun ξ hξ => ?_)
    · have hp : pP ξ ≠ 0 := by
        have := hlo ξ hξ; have := hhi ξ hξ; unfold pP; nlinarith
      have h := hasDerivAt_regSol (sqC c) Λ (hlo ξ hξ)
      rwa [← pP_mul_regV (sqC c) Λ (hlo ξ hξ), mul_div_cancel_left₀ _ hp]
    · exact hasDerivAt_regU (sqC c) Λ (hlo ξ hξ)
    · exact hasDerivAt_zS w (hlo ξ hξ) (hhi ξ hξ)
    · exact hasDerivAt_fS w (hlo ξ hξ) (hhi ξ hξ)
    · have hp : 0 < 1 - ξ ^ 2 := by
        have := hlo ξ (Ioo_subset_Icc_self hξ); have := hhi ξ (Ioo_subset_Icc_self hξ); nlinarith
      refine div_ne_zero (fun hs => ?_) (Real.sqrt_pos.2 hp).ne'
      obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hs
      have hl1 : w / 2 * ζ i < w / 2 * ξ := mul_lt_mul_of_pos_left hξ.1 (by positivity)
      have hl2 : w / 2 * ξ < w / 2 * ζ (i + 1) := mul_lt_mul_of_pos_left hξ.2 (by positivity)
      rw [hζθ, ← hn] at hl1
      rw [hζθ, ← hn] at hl2
      have h1 : ((i : ℕ) : ℝ) < n := lt_of_mul_lt_mul_right (by simpa using hl1) pi_pos.le
      have h2 : (n : ℝ) < ((i : ℕ) : ℝ) + 1 := by
        have : (n : ℝ) * π < (((i : ℕ) : ℝ) + 1) * π := by simpa using hl2
        exact lt_of_mul_lt_mul_right this pi_pos.le
      have h1' : ((i : ℕ) : ℤ) < n := by exact_mod_cast h1
      have h2' : n < ((i : ℕ) : ℤ) + 1 := by exact_mod_cast h2
      omega
    · exact hR ξ (by linarith [hξ.1]) (by have := hζK (i + 1) (by omega); simp only [hζdef] at this ⊢
                                          push_cast at this; linarith [hξ.2])
  choose x hxI hx0 using hz
  refine ⟨x, fun i j hij => ?_, fun i => ⟨?_, ?_⟩, hx0⟩
  · have hij' : (i : ℕ) + 1 ≤ j := hij
    have h1 : ζ ((i : ℕ) + 1) ≤ ζ j := by
      simp only [hζdef]
      apply div_le_div_of_nonneg_right _ hw.le
      have : (((i : ℕ) + 1 : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hij'
      push_cast at this ⊢
      nlinarith [Real.pi_pos]
    linarith [(hxI i).2, (hxI j).1]
  · linarith [(hxI i).1, hζ0 i]
  · have := hζK ((i : ℕ) + 1) (by omega)
    have hK' : ζ K < 1 := hK1
    linarith [(hxI i).2]

/-- **`K` zeros at `Λ = 2πKc`** for `0 < K`, `πK < c`. -/
theorem hasZeros_lin {c : ℝ} {K : ℕ} (hK : 0 < K) (hc : π * K < c) : HasZeros (sqC c) (2 * π * K * c) K := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hc0 : 0 < c := lt_trans (by positivity) hc
  set w := 2 * √(π * K * c) with hwd
  have hw : 0 < w := by positivity
  have hw2 : w ^ 2 = 4 * (π * K * c) := by rw [hwd, mul_pow, Real.sq_sqrt (by positivity)]; ring
  have hζ2 : (2 * π * K / w) ^ 2 = π * K / c := by
    rw [div_pow, hw2]; field_simp; ring
  have hζ0 : 0 ≤ 2 * π * K / w := by positivity
  refine hasZeros_of_freq hw ?_ fun ξ h0 h1 => ?_
  · have : (2 * π * K / w) ^ 2 < 1 := by rw [hζ2, div_lt_one hc0]; exact hc
    nlinarith
  · have hξ2 : ξ ^ 2 ≤ π * K / c := hζ2 ▸ pow_le_pow_left₀ h0 h1 2
    have hξ1 : ξ ^ 2 < 1 := lt_of_le_of_lt hξ2 (by rw [div_lt_one hc0]; exact hc)
    have hq : 0 ≤ ξ ^ 2 / (1 - ξ ^ 2) := div_nonneg (sq_nonneg ξ) (by linarith)
    have hcξ : c ^ 2 * ξ ^ 2 ≤ π * K * c := by
      have := mul_le_mul_of_nonneg_left hξ2 (sq_nonneg c)
      rw [show c ^ 2 * (π * K / c) = π * K * c by field_simp] at this
      exact this
    unfold rS
    rw [hw2]
    nlinarith [sq_nonneg ξ, mul_nonneg (mul_nonneg Real.pi_pos.le hK0.le) hc0.le]

/-- **The level of index `k` exists and lies below `2π(k + 1)c`** for `π(k + 1) < c`. -/
theorem lev_lt_lin {c : ℝ} {k : ℕ} (hc : π * (k + 1) < c) :
    lev c k < 2 * π * (k + 1) * c ∧ ∃ χ, IsLevelIdx c k χ := by
  have hz := hasZeros_lin (c := c) (K := k + 1) (Nat.succ_pos k) (by push_cast; exact hc)
  have hcount := le_ncard_evenSpec hz
  obtain ⟨χ, hχ, hidx⟩ := exists_isLevelIdx_of_lt_ncard (c := c) (χ := 2 * π * ((k + 1 : ℕ) : ℝ) * c) (k := k)
    (by omega)
  have he := (lev_spec ⟨χ, hidx⟩).unique hidx
  push_cast at hχ
  exact ⟨he ▸ hχ, χ, hidx⟩

end Cvs.Prolate.LevelsBelowLinearBound
