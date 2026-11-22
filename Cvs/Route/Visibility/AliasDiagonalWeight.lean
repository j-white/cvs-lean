import Mathlib
import Cvs.Route.Visibility.AliasWindowCornerCut

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The diagonal weight of the AL-R alias tail: `W̃_K(s) ≤ 19/20` for every `K` and `s`

`W̃_K(s) = Σ_{k=3}^{K} ρ(s/k)/k + (ρ(1 − τ))(s/3)/3 + (ρ(1 − τ))(s/4)/4`.  On `[0, 12]` only `k ≤ 25` contribute
and Cvs.Route.Visibility.AliasWindowCornerCut bounds the sum; for `s ≥ 12` the corner terms vanish and `Σ_{s/(11/10) < k < 25s/12} 1/k ≤ log(b/a) < 19/20`
by comparison with `∫dt/t`.
-/

noncomputable section

open Real Finset

namespace Cvs.Route.Visibility.AliasDiagonalWeight

open Cvs.Route.Visibility.AliasWindowCornerCut (rho tau rho_nonneg rho_le_one rho_eq_zero_of_le rho_eq_zero_of_ge F F_le_of_mem)

/-- **The diagonal weight** `W̃_K(s) = Σ_{k=3}^{K} ρ(s/k)/k + (ρ(1 − τ))(s/3)/3 + (ρ(1 − τ))(s/4)/4`. -/
def wDiag (K : ℕ) (s : ℝ) : ℝ :=
  ∑ k ∈ Icc 3 K, rho (s / k) / k + rho (s / 3) * (1 - tau (s / 3)) / 3 + rho (s / 4) * (1 - tau (s / 4)) / 4

/-- `W̃_K(s) = 0` for `s ≤ 36/25`. -/
theorem wDiag_eq_zero {K : ℕ} {s : ℝ} (hs : s ≤ 36 / 25) : wDiag K s = 0 := by
  unfold wDiag
  have hk : ∀ k ∈ Icc 3 K, rho (s / k) / k = 0 := by
    intro k hk
    have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.1 hk).1
    rw [rho_eq_zero_of_le ((div_le_iff₀ (by linarith)).2 (by nlinarith)), zero_div]
  rw [Finset.sum_eq_zero hk, rho_eq_zero_of_le (by linarith), rho_eq_zero_of_le (by linarith)]
  ring

/-- On `[0, 12]` the window sum over `3 ≤ k ≤ K` is at most the one over `3 ≤ k ≤ 25`. -/
theorem sum_le_F_part {K : ℕ} {s : ℝ} (h12 : s ≤ 12) :
    ∑ k ∈ Icc 3 K, rho (s / k) / k ≤ ∑ i ∈ range 23, rho (s / ((i : ℝ) + 3)) / ((i : ℝ) + 3) := by
  set f : ℕ → ℝ := fun k => rho (s / k) / k
  have hf0 : ∀ k, 0 ≤ f k := fun k => div_nonneg (rho_nonneg _) (Nat.cast_nonneg _)
  have hz : ∀ k ∈ Icc 3 K, f k ≠ 0 → k ≤ 25 := by
    intro k _ hk
    by_contra h
    have h26 : (26 : ℝ) ≤ k := by exact_mod_cast (by omega : 26 ≤ k)
    exact hk (by
      simp only [f]
      rw [rho_eq_zero_of_le ((div_le_iff₀ (by linarith)).2 (by nlinarith)), zero_div])
  rw [← Finset.sum_filter_of_ne hz]
  have hsub : (Icc 3 K).filter (· ≤ 25) ⊆ Icc 3 25 := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk ⊢
    omega
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => hf0 k).trans_eq ?_
  rw [show Icc 3 25 = Ico 3 26 from rfl, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [f]
  push_cast
  rw [add_comm (3 : ℝ)]

/-- **`W̃_K ≤ 19/20` on `[0, 12]`.** -/
theorem wDiag_le_of_le {K : ℕ} {s : ℝ} (h0 : 0 ≤ s) (h12 : s ≤ 12) : wDiag K s ≤ 19 / 20 := by
  have h := F_le_of_mem h0 h12
  have hs := sum_le_F_part (K := K) h12
  unfold wDiag
  unfold F at h
  linarith

/-- `log(b/a) < 19/20` once `b ≤ (253/100)a`. -/
theorem log_lt_of_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : b ≤ 253 / 100 * a) : log (b / a) < 19 / 20 := by
  rw [Real.log_lt_iff_lt_exp (by positivity)]
  have he := Real.sum_le_exp_of_nonneg (x := 19 / 20) (by norm_num) 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at he
  norm_num at he
  rw [div_lt_iff₀ ha]
  nlinarith

/-- **`W̃_K ≤ 19/20` from `12` on**: the corner terms vanish and the window sum is a harmonic block. -/
theorem wDiag_le_of_ge {K : ℕ} {s : ℝ} (h12 : 12 ≤ s) : wDiag K s ≤ 19 / 20 := by
  set a := ⌊s * (10 / 11)⌋₊
  set b := ⌊s * (25 / 12)⌋₊
  have hs0 : 0 ≤ s := by linarith
  have ha : s * (10 / 11) - 1 < a := Nat.sub_one_lt_floor _
  have hb : (b : ℝ) ≤ s * (25 / 12) := Nat.floor_le (by positivity)
  have ha1 : 1 ≤ a := Nat.le_floor (by norm_num; linarith)
  have hab : a ≤ b := Nat.floor_le_floor (by nlinarith)
  -- the corner terms vanish
  have hc3 : 1 - tau (s / 3) = 0 := Cvs.Route.Visibility.AliasWindowCornerCut.one_sub_tau_eq_zero (by linarith)
  have hc4 : 1 - tau (s / 4) = 0 := Cvs.Route.Visibility.AliasWindowCornerCut.one_sub_tau_eq_zero (by linarith)
  -- each term is supported on `a < k ≤ b`
  have hterm : ∀ k ∈ Icc 3 K, rho (s / k) / k ≤ if k ∈ Ico (a + 1) (b + 1) then 1 / (k : ℝ) else 0 := by
    intro k hk
    have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.1 hk).1
    have hk0 : (0 : ℝ) < k := by linarith
    split_ifs with hm
    · exact div_le_div_of_nonneg_right (rho_le_one _) hk0.le
    · refine le_of_eq ?_
      simp only [Finset.mem_Ico, not_and_or, not_le, not_lt] at hm
      rcases hm with hm | hm
      · -- `k ≤ a`, so `s/k ≥ 11/10`
        have : (k : ℝ) ≤ a := by exact_mod_cast (by omega : k ≤ a)
        have hfl : (a : ℝ) ≤ s * (10 / 11) := Nat.floor_le (by positivity)
        rw [rho_eq_zero_of_ge ((le_div_iff₀ hk0).2 (by linarith)), zero_div]
      · -- `k > b`, so `s/k ≤ 12/25`
        have : (b : ℝ) + 1 ≤ k := by exact_mod_cast hm
        have hfl : s * (25 / 12) < b + 1 := Nat.lt_floor_add_one _
        rw [rho_eq_zero_of_le ((div_le_iff₀ hk0).2 (by linarith)), zero_div]
  have hsum : ∑ k ∈ Icc 3 K, rho (s / k) / k ≤ ∑ k ∈ Ico (a + 1) (b + 1), 1 / (k : ℝ) := by
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => (Finset.mem_filter.1 hk).2) fun k _ _ => ?_
    positivity
  -- comparison with `∫ dt/t`
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha1
  have hint : ∑ k ∈ Ico (a + 1) (b + 1), 1 / (k : ℝ) ≤ log ((b : ℝ) / a) := by
    have hA : AntitoneOn (fun t : ℝ => 1 / t) (Set.Icc (a : ℝ) b) := by
      intro u hu v hv huv
      exact one_div_le_one_div_of_le (ha0.trans_le hu.1) huv
    have h := hA.sum_le_integral_Ico hab
    rw [integral_one_div_of_pos ha0 (by exact_mod_cast (Nat.lt_of_lt_of_le ha1 hab))] at h
    rw [← Finset.sum_Ico_add' (fun k : ℕ => 1 / (k : ℝ)) a b 1]
    simpa using h
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (Nat.lt_of_lt_of_le ha1 hab)
  have hlog := log_lt_of_le ha0 hb0 (by nlinarith)
  unfold wDiag
  rw [hc3, hc4]
  linarith

/-- **The diagonal weight** `W̃_K(s) ≤ 19/20` for every `K` and every `s`. -/
theorem wDiag_le (K : ℕ) (s : ℝ) : wDiag K s ≤ 19 / 20 := by
  rcases le_total s 0 with h | h
  · rw [wDiag_eq_zero (by linarith)]; norm_num
  rcases le_total s 12 with h' | h'
  · exact wDiag_le_of_le h h'
  · exact wDiag_le_of_ge h'

end Cvs.Route.Visibility.AliasDiagonalWeight
