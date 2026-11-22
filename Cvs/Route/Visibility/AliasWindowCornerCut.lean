import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The AL-R window `ρ`, the corner cut `τ`, and the diagonal weight `W̃ ≤ 19/20`

`ρ = 1` on `[1/2, 1]`, linear on `[12/25, 1/2]` and `[1, 11/10]`, `0` off `(12/25, 11/10)`; `τ = 0` below `3/5`,
linear on `[3/5, 13/20]`, `1` above.  The diagonal weight of the alias tail with the `{3, 4}` corner split by AM–GM is
`W̃_K(s) = Σ_{k=3}^{K} ρ(s/k)/k + (ρ(1 − τ))(s/3)/3 + (ρ(1 − τ))(s/4)/4`, and `W̃_K(s) ≤ 19/20` for every `K` and `s`,
with equality at `s = 3`.
-/

noncomputable section

open Real Finset

namespace Cvs.Route.Visibility.AliasWindowCornerCut

/-! ### The window and the corner cut -/

/-- The window `ρ(θ) = max(0, min(1, 50(θ − 12/25), 10(11/10 − θ)))`. -/
def rho (θ : ℝ) : ℝ := max 0 (min 1 (min ((θ - 12 / 25) * 50) ((11 / 10 - θ) * 10)))

/-- The corner cut `τ(θ) = max(0, min(1, 20(θ − 3/5)))`. -/
def tau (θ : ℝ) : ℝ := max 0 (min 1 ((θ - 3 / 5) * 20))

/-- `ρ ≥ 0`. -/
theorem rho_nonneg (θ : ℝ) : 0 ≤ rho θ := le_max_left _ _

/-- `ρ ≤ 1`. -/
theorem rho_le_one (θ : ℝ) : rho θ ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

/-- `ρ = 1` on `[1/2, 1]`. -/
theorem rho_eq_one {θ : ℝ} (h1 : 1 / 2 ≤ θ) (h2 : θ ≤ 1) : rho θ = 1 := by
  unfold rho
  rw [min_eq_left (le_min (by linarith) (by linarith)), max_eq_right zero_le_one]

/-- `ρ = 0` at and below `12/25`. -/
theorem rho_eq_zero_of_le {θ : ℝ} (h : θ ≤ 12 / 25) : rho θ = 0 := by
  unfold rho
  refine max_eq_left ?_
  exact (min_le_right _ _).trans ((min_le_left _ _).trans (by linarith))

/-- `ρ = 0` at and above `11/10`. -/
theorem rho_eq_zero_of_ge {θ : ℝ} (h : 11 / 10 ≤ θ) : rho θ = 0 := by
  unfold rho
  refine max_eq_left ?_
  exact (min_le_right _ _).trans ((min_le_right _ _).trans (by linarith))

/-- `ρ(θ) ≤ 50(θ − 12/25)` from `12/25` on. -/
theorem rho_le_left {θ : ℝ} (h : 12 / 25 ≤ θ) : rho θ ≤ (θ - 12 / 25) * 50 :=
  max_le (by linarith) ((min_le_right _ _).trans (min_le_left _ _))

/-- `ρ(θ) ≤ 10(11/10 − θ)` up to `11/10`. -/
theorem rho_le_right {θ : ℝ} (h : θ ≤ 11 / 10) : rho θ ≤ (11 / 10 - θ) * 10 :=
  max_le (by linarith) ((min_le_right _ _).trans (min_le_right _ _))

/-- `0 ≤ 1 − τ ≤ 1`. -/
theorem one_sub_tau_mem (θ : ℝ) : 0 ≤ 1 - tau θ ∧ 1 - tau θ ≤ 1 := by
  unfold tau
  constructor
  · have : max 0 (min 1 ((θ - 3 / 5) * 20)) ≤ 1 := max_le zero_le_one (min_le_left _ _)
    linarith
  · have : 0 ≤ max 0 (min 1 ((θ - 3 / 5) * 20)) := le_max_left _ _
    linarith

/-- `1 − τ = 0` from `13/20` on. -/
theorem one_sub_tau_eq_zero {θ : ℝ} (h : 13 / 20 ≤ θ) : 1 - tau θ = 0 := by
  unfold tau
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]; ring

/-- `1 − τ(θ) ≤ 20(13/20 − θ)` up to `13/20`. -/
theorem one_sub_tau_le {θ : ℝ} (h : θ ≤ 13 / 20) : 1 - tau θ ≤ (13 / 20 - θ) * 20 := by
  unfold tau
  have : min 1 ((θ - 3 / 5) * 20) = (θ - 3 / 5) * 20 := min_eq_right (by linarith)
  rw [this]
  have := le_max_right 0 ((θ - 3 / 5) * 20)
  linarith

/-! ### One term of the diagonal weight -/

section Terms

variable {s k : ℝ}

/-- A term below the window vanishes. -/
theorem term_zero_low (hk : 0 < k) (h : s ≤ 12 / 25 * k) : rho (s / k) / k = 0 := by
  rw [rho_eq_zero_of_le ((div_le_iff₀ hk).2 (by linarith)), zero_div]

/-- A term above the window vanishes. -/
theorem term_zero_high (hk : 0 < k) (h : 11 / 10 * k ≤ s) : rho (s / k) / k = 0 := by
  rw [rho_eq_zero_of_ge ((le_div_iff₀ hk).2 (by linarith)), zero_div]

/-- A term is at most `1/k`. -/
theorem term_le_one (hk : 0 < k) (s : ℝ) : rho (s / k) / k ≤ 1 / k :=
  div_le_div_of_nonneg_right (rho_le_one _) hk.le

/-- A term on the left ramp. -/
theorem term_le_left (hk : 0 < k) (h : 12 / 25 * k ≤ s) : rho (s / k) / k ≤ (s - 12 / 25 * k) * 50 / k ^ 2 := by
  have := rho_le_left ((le_div_iff₀ hk).2 (by linarith) : 12 / 25 ≤ s / k)
  calc rho (s / k) / k ≤ (s / k - 12 / 25) * 50 / k := div_le_div_of_nonneg_right this hk.le
    _ = (s - 12 / 25 * k) * 50 / k ^ 2 := by field_simp

/-- A term on the right ramp. -/
theorem term_le_right (hk : 0 < k) (h : s ≤ 11 / 10 * k) : rho (s / k) / k ≤ (11 / 10 * k - s) * 10 / k ^ 2 := by
  have := rho_le_right ((div_le_iff₀ hk).2 (by linarith) : s / k ≤ 11 / 10)
  calc rho (s / k) / k ≤ (11 / 10 - s / k) * 10 / k := div_le_div_of_nonneg_right this hk.le
    _ = (11 / 10 * k - s) * 10 / k ^ 2 := by field_simp

/-- A corner term is at most the window term. -/
theorem corner_le_rho (hk : 0 < k) (s : ℝ) : rho (s / k) * (1 - tau (s / k)) / k ≤ rho (s / k) / k := by
  refine div_le_div_of_nonneg_right ?_ hk.le
  exact mul_le_of_le_one_right (rho_nonneg _) (one_sub_tau_mem _).2

/-- A corner term vanishes from `13k/20` on. -/
theorem corner_zero (hk : 0 < k) (h : 13 / 20 * k ≤ s) : rho (s / k) * (1 - tau (s / k)) / k = 0 := by
  rw [one_sub_tau_eq_zero ((le_div_iff₀ hk).2 (by linarith)), mul_zero, zero_div]

/-- A corner term on the cut ramp. -/
theorem corner_le_mid (hk : 0 < k) (h : s ≤ 13 / 20 * k) :
    rho (s / k) * (1 - tau (s / k)) / k ≤ (13 / 20 * k - s) * 20 / k ^ 2 := by
  have h1 := one_sub_tau_le ((div_le_iff₀ hk).2 (by linarith) : s / k ≤ 13 / 20)
  have h0 := (one_sub_tau_mem (s / k)).1
  have hr := rho_le_one (s / k)
  have hr0 := rho_nonneg (s / k)
  have : rho (s / k) * (1 - tau (s / k)) ≤ (13 / 20 - s / k) * 20 :=
    (mul_le_of_le_one_left h0 hr).trans h1
  calc rho (s / k) * (1 - tau (s / k)) / k ≤ (13 / 20 - s / k) * 20 / k := div_le_div_of_nonneg_right this hk.le
    _ = (13 / 20 * k - s) * 20 / k ^ 2 := by field_simp

end Terms

/-! ### The diagonal weight on `[0, 12]` -/

/-- The diagonal weight truncated at `k = 25`. -/
def F (s : ℝ) : ℝ :=
  ∑ i ∈ range 23, rho (s / ((i : ℝ) + 3)) / ((i : ℝ) + 3) + rho (s / 3) * (1 - tau (s / 3)) / 3
    + rho (s / 4) * (1 - tau (s / 4)) / 4

/-- `F` written out term by term. -/
theorem F_eq (s : ℝ) : F s = rho (s / 3) / 3 + rho (s / 4) / 4 + rho (s / 5) / 5 + rho (s / 6) / 6
    + rho (s / 7) / 7 + rho (s / 8) / 8 + rho (s / 9) / 9 + rho (s / 10) / 10 + rho (s / 11) / 11
    + rho (s / 12) / 12 + rho (s / 13) / 13 + rho (s / 14) / 14 + rho (s / 15) / 15 + rho (s / 16) / 16
    + rho (s / 17) / 17 + rho (s / 18) / 18 + rho (s / 19) / 19 + rho (s / 20) / 20 + rho (s / 21) / 21
    + rho (s / 22) / 22 + rho (s / 23) / 23 + rho (s / 24) / 24 + rho (s / 25) / 25
    + rho (s / 3) * (1 - tau (s / 3)) / 3 + rho (s / 4) * (1 - tau (s / 4)) / 4 := by
  simp only [F, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- `F ≤ 19/20` on `[0, 36/25]`. -/
theorem F_le_0 {s : ℝ} (_h1 : (0:ℝ) ≤ s) (_h2 : s ≤ (36/25:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_low (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 6) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 7) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 8) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 9) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 10) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 11) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 12) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 13) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 14) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 15) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 16) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 17) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_le_rho (k := 3) (by norm_num) s
  have := corner_le_rho (k := 4) (by norm_num) s
  linarith

/-- `F ≤ 19/20` on `[36/25, 3/2]`. -/
theorem F_le_1 {s : ℝ} (_h1 : (36/25:ℝ) ≤ s) (_h2 : s ≤ (3/2:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_le_left (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 6) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 7) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 8) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 9) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 10) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 11) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 12) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 13) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 14) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 15) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 16) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 17) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_le_rho (k := 3) (by norm_num) s
  have := corner_le_rho (k := 4) (by norm_num) s
  linarith

/-- `F ≤ 19/20` on `[3/2, 9/5]`. -/
theorem F_le_2 {s : ℝ} (_h1 : (3/2:ℝ) ≤ s) (_h2 : s ≤ (9/5:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_le_one (k := 3) (by norm_num) s
  have := term_zero_low (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 6) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 7) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 8) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 9) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 10) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 11) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 12) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 13) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 14) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 15) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 16) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 17) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_le_rho (k := 3) (by norm_num) s
  have := corner_le_rho (k := 4) (by norm_num) s
  linarith

/-- `F ≤ 19/20` on `[9/5, 48/25]`. -/
theorem F_le_3 {s : ℝ} (_h1 : (9/5:ℝ) ≤ s) (_h2 : s ≤ (48/25:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_le_one (k := 3) (by norm_num) s
  have := term_zero_low (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 6) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 7) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 8) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 9) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 10) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 11) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 12) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 13) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 14) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 15) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 16) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 17) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_le_mid (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_le_rho (k := 4) (by norm_num) s
  linarith

/-- `F ≤ 19/20` on `[48/25, 39/20]`. -/
theorem F_le_4 {s : ℝ} (_h1 : (48/25:ℝ) ≤ s) (_h2 : s ≤ (39/20:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_le_one (k := 3) (by norm_num) s
  have := term_le_left (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 6) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 7) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 8) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 9) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 10) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 11) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 12) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 13) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 14) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 15) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 16) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 17) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_le_mid (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_le_rho (k := 4) (by norm_num) s
  linarith

/-- `F ≤ 19/20` on `[39/20, 2]`. -/
theorem F_le_5 {s : ℝ} (_h1 : (39/20:ℝ) ≤ s) (_h2 : s ≤ (2:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_le_one (k := 3) (by norm_num) s
  have := term_le_left (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 6) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 7) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 8) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 9) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 10) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 11) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 12) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 13) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 14) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 15) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 16) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 17) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_le_rho (k := 4) (by norm_num) s
  linarith

/-- `F ≤ 19/20` on `[2, 12/5]`. -/
theorem F_le_6 {s : ℝ} (_h1 : (2:ℝ) ≤ s) (_h2 : s ≤ (12/5:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_le_one (k := 3) (by norm_num) s
  have := term_le_one (k := 4) (by norm_num) s
  have := term_zero_low (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 6) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 7) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 8) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 9) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 10) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 11) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 12) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 13) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 14) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 15) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 16) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 17) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_le_rho (k := 4) (by norm_num) s
  linarith

/-- `F ≤ 19/20` on `[12/5, 5/2]`. -/
theorem F_le_7 {s : ℝ} (_h1 : (12/5:ℝ) ≤ s) (_h2 : s ≤ (5/2:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_le_one (k := 3) (by norm_num) s
  have := term_le_one (k := 4) (by norm_num) s
  have := term_le_left (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 6) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 7) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 8) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 9) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 10) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 11) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 12) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 13) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 14) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 15) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 16) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 17) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_le_mid (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[5/2, 13/5]`. -/
theorem F_le_8 {s : ℝ} (_h1 : (5/2:ℝ) ≤ s) (_h2 : s ≤ (13/5:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_le_one (k := 3) (by norm_num) s
  have := term_le_one (k := 4) (by norm_num) s
  have := term_le_one (k := 5) (by norm_num) s
  have := term_zero_low (s := s) (k := 6) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 7) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 8) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 9) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 10) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 11) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 12) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 13) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 14) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 15) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 16) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 17) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_le_mid (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[13/5, 72/25]`. -/
theorem F_le_9 {s : ℝ} (_h1 : (13/5:ℝ) ≤ s) (_h2 : s ≤ (72/25:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_le_one (k := 3) (by norm_num) s
  have := term_le_one (k := 4) (by norm_num) s
  have := term_le_one (k := 5) (by norm_num) s
  have := term_zero_low (s := s) (k := 6) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 7) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 8) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 9) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 10) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 11) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 12) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 13) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 14) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 15) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 16) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 17) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[72/25, 3]`. -/
theorem F_le_10 {s : ℝ} (_h1 : (72/25:ℝ) ≤ s) (_h2 : s ≤ (3:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_le_one (k := 3) (by norm_num) s
  have := term_le_one (k := 4) (by norm_num) s
  have := term_le_one (k := 5) (by norm_num) s
  have := term_le_left (s := s) (k := 6) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 7) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 8) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 9) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 10) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 11) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 12) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 13) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 14) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 15) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 16) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 17) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[3, 33/10]`. -/
theorem F_le_11 {s : ℝ} (_h1 : (3:ℝ) ≤ s) (_h2 : s ≤ (33/10:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_le_right (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_le_one (k := 4) (by norm_num) s
  have := term_le_one (k := 5) (by norm_num) s
  have := term_le_one (k := 6) (by norm_num) s
  have := term_zero_low (s := s) (k := 7) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 8) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 9) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 10) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 11) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 12) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 13) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 14) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 15) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 16) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 17) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[33/10, 84/25]`. -/
theorem F_le_12 {s : ℝ} (_h1 : (33/10:ℝ) ≤ s) (_h2 : s ≤ (84/25:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_le_one (k := 4) (by norm_num) s
  have := term_le_one (k := 5) (by norm_num) s
  have := term_le_one (k := 6) (by norm_num) s
  have := term_zero_low (s := s) (k := 7) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 8) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 9) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 10) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 11) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 12) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 13) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 14) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 15) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 16) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 17) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[84/25, 7/2]`. -/
theorem F_le_13 {s : ℝ} (_h1 : (84/25:ℝ) ≤ s) (_h2 : s ≤ (7/2:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_le_one (k := 4) (by norm_num) s
  have := term_le_one (k := 5) (by norm_num) s
  have := term_le_one (k := 6) (by norm_num) s
  have := term_le_left (s := s) (k := 7) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 8) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 9) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 10) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 11) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 12) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 13) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 14) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 15) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 16) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 17) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[7/2, 96/25]`. -/
theorem F_le_14 {s : ℝ} (_h1 : (7/2:ℝ) ≤ s) (_h2 : s ≤ (96/25:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_le_one (k := 4) (by norm_num) s
  have := term_le_one (k := 5) (by norm_num) s
  have := term_le_one (k := 6) (by norm_num) s
  have := term_le_one (k := 7) (by norm_num) s
  have := term_zero_low (s := s) (k := 8) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 9) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 10) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 11) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 12) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 13) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 14) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 15) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 16) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 17) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[96/25, 4]`. -/
theorem F_le_15 {s : ℝ} (_h1 : (96/25:ℝ) ≤ s) (_h2 : s ≤ (4:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_le_one (k := 4) (by norm_num) s
  have := term_le_one (k := 5) (by norm_num) s
  have := term_le_one (k := 6) (by norm_num) s
  have := term_le_one (k := 7) (by norm_num) s
  have := term_le_left (s := s) (k := 8) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 9) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 10) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 11) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 12) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 13) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 14) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 15) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 16) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 17) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[4, 108/25]`. -/
theorem F_le_16 {s : ℝ} (_h1 : (4:ℝ) ≤ s) (_h2 : s ≤ (108/25:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_le_right (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_le_one (k := 5) (by norm_num) s
  have := term_le_one (k := 6) (by norm_num) s
  have := term_le_one (k := 7) (by norm_num) s
  have := term_le_one (k := 8) (by norm_num) s
  have := term_zero_low (s := s) (k := 9) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 10) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 11) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 12) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 13) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 14) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 15) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 16) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 17) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[108/25, 22/5]`. -/
theorem F_le_17 {s : ℝ} (_h1 : (108/25:ℝ) ≤ s) (_h2 : s ≤ (22/5:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_le_right (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_le_one (k := 5) (by norm_num) s
  have := term_le_one (k := 6) (by norm_num) s
  have := term_le_one (k := 7) (by norm_num) s
  have := term_le_one (k := 8) (by norm_num) s
  have := term_le_left (s := s) (k := 9) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 10) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 11) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 12) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 13) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 14) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 15) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 16) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 17) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[22/5, 9/2]`. -/
theorem F_le_18 {s : ℝ} (_h1 : (22/5:ℝ) ≤ s) (_h2 : s ≤ (9/2:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_le_one (k := 5) (by norm_num) s
  have := term_le_one (k := 6) (by norm_num) s
  have := term_le_one (k := 7) (by norm_num) s
  have := term_le_one (k := 8) (by norm_num) s
  have := term_le_left (s := s) (k := 9) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 10) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 11) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 12) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 13) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 14) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 15) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 16) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 17) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[9/2, 24/5]`. -/
theorem F_le_19 {s : ℝ} (_h1 : (9/2:ℝ) ≤ s) (_h2 : s ≤ (24/5:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_le_one (k := 5) (by norm_num) s
  have := term_le_one (k := 6) (by norm_num) s
  have := term_le_one (k := 7) (by norm_num) s
  have := term_le_one (k := 8) (by norm_num) s
  have := term_le_one (k := 9) (by norm_num) s
  have := term_zero_low (s := s) (k := 10) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 11) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 12) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 13) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 14) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 15) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 16) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 17) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[24/5, 5]`. -/
theorem F_le_20 {s : ℝ} (_h1 : (24/5:ℝ) ≤ s) (_h2 : s ≤ (5:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_le_one (k := 5) (by norm_num) s
  have := term_le_one (k := 6) (by norm_num) s
  have := term_le_one (k := 7) (by norm_num) s
  have := term_le_one (k := 8) (by norm_num) s
  have := term_le_one (k := 9) (by norm_num) s
  have := term_le_left (s := s) (k := 10) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 11) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 12) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 13) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 14) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 15) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 16) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 17) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[5, 132/25]`. -/
theorem F_le_21 {s : ℝ} (_h1 : (5:ℝ) ≤ s) (_h2 : s ≤ (132/25:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_le_right (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_le_one (k := 6) (by norm_num) s
  have := term_le_one (k := 7) (by norm_num) s
  have := term_le_one (k := 8) (by norm_num) s
  have := term_le_one (k := 9) (by norm_num) s
  have := term_le_one (k := 10) (by norm_num) s
  have := term_zero_low (s := s) (k := 11) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 12) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 13) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 14) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 15) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 16) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 17) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[132/25, 11/2]`. -/
theorem F_le_22 {s : ℝ} (_h1 : (132/25:ℝ) ≤ s) (_h2 : s ≤ (11/2:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_le_right (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_le_one (k := 6) (by norm_num) s
  have := term_le_one (k := 7) (by norm_num) s
  have := term_le_one (k := 8) (by norm_num) s
  have := term_le_one (k := 9) (by norm_num) s
  have := term_le_one (k := 10) (by norm_num) s
  have := term_le_left (s := s) (k := 11) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 12) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 13) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 14) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 15) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 16) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 17) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[11/2, 144/25]`. -/
theorem F_le_23 {s : ℝ} (_h1 : (11/2:ℝ) ≤ s) (_h2 : s ≤ (144/25:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_le_one (k := 6) (by norm_num) s
  have := term_le_one (k := 7) (by norm_num) s
  have := term_le_one (k := 8) (by norm_num) s
  have := term_le_one (k := 9) (by norm_num) s
  have := term_le_one (k := 10) (by norm_num) s
  have := term_le_one (k := 11) (by norm_num) s
  have := term_zero_low (s := s) (k := 12) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 13) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 14) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 15) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 16) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 17) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[144/25, 6]`. -/
theorem F_le_24 {s : ℝ} (_h1 : (144/25:ℝ) ≤ s) (_h2 : s ≤ (6:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_le_one (k := 6) (by norm_num) s
  have := term_le_one (k := 7) (by norm_num) s
  have := term_le_one (k := 8) (by norm_num) s
  have := term_le_one (k := 9) (by norm_num) s
  have := term_le_one (k := 10) (by norm_num) s
  have := term_le_one (k := 11) (by norm_num) s
  have := term_le_left (s := s) (k := 12) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 13) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 14) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 15) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 16) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 17) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[6, 156/25]`. -/
theorem F_le_25 {s : ℝ} (_h1 : (6:ℝ) ≤ s) (_h2 : s ≤ (156/25:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_le_right (s := s) (k := 6) (by norm_num) (by linarith)
  have := term_le_one (k := 7) (by norm_num) s
  have := term_le_one (k := 8) (by norm_num) s
  have := term_le_one (k := 9) (by norm_num) s
  have := term_le_one (k := 10) (by norm_num) s
  have := term_le_one (k := 11) (by norm_num) s
  have := term_le_one (k := 12) (by norm_num) s
  have := term_zero_low (s := s) (k := 13) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 14) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 15) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 16) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 17) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[156/25, 13/2]`. -/
theorem F_le_26 {s : ℝ} (_h1 : (156/25:ℝ) ≤ s) (_h2 : s ≤ (13/2:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_le_right (s := s) (k := 6) (by norm_num) (by linarith)
  have := term_le_one (k := 7) (by norm_num) s
  have := term_le_one (k := 8) (by norm_num) s
  have := term_le_one (k := 9) (by norm_num) s
  have := term_le_one (k := 10) (by norm_num) s
  have := term_le_one (k := 11) (by norm_num) s
  have := term_le_one (k := 12) (by norm_num) s
  have := term_le_left (s := s) (k := 13) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 14) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 15) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 16) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 17) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[13/2, 33/5]`. -/
theorem F_le_27 {s : ℝ} (_h1 : (13/2:ℝ) ≤ s) (_h2 : s ≤ (33/5:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_le_right (s := s) (k := 6) (by norm_num) (by linarith)
  have := term_le_one (k := 7) (by norm_num) s
  have := term_le_one (k := 8) (by norm_num) s
  have := term_le_one (k := 9) (by norm_num) s
  have := term_le_one (k := 10) (by norm_num) s
  have := term_le_one (k := 11) (by norm_num) s
  have := term_le_one (k := 12) (by norm_num) s
  have := term_le_one (k := 13) (by norm_num) s
  have := term_zero_low (s := s) (k := 14) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 15) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 16) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 17) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[33/5, 168/25]`. -/
theorem F_le_28 {s : ℝ} (_h1 : (33/5:ℝ) ≤ s) (_h2 : s ≤ (168/25:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 6) (by norm_num) (by linarith)
  have := term_le_one (k := 7) (by norm_num) s
  have := term_le_one (k := 8) (by norm_num) s
  have := term_le_one (k := 9) (by norm_num) s
  have := term_le_one (k := 10) (by norm_num) s
  have := term_le_one (k := 11) (by norm_num) s
  have := term_le_one (k := 12) (by norm_num) s
  have := term_le_one (k := 13) (by norm_num) s
  have := term_zero_low (s := s) (k := 14) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 15) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 16) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 17) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[168/25, 7]`. -/
theorem F_le_29 {s : ℝ} (_h1 : (168/25:ℝ) ≤ s) (_h2 : s ≤ (7:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 6) (by norm_num) (by linarith)
  have := term_le_one (k := 7) (by norm_num) s
  have := term_le_one (k := 8) (by norm_num) s
  have := term_le_one (k := 9) (by norm_num) s
  have := term_le_one (k := 10) (by norm_num) s
  have := term_le_one (k := 11) (by norm_num) s
  have := term_le_one (k := 12) (by norm_num) s
  have := term_le_one (k := 13) (by norm_num) s
  have := term_le_left (s := s) (k := 14) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 15) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 16) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 17) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[7, 36/5]`. -/
theorem F_le_30 {s : ℝ} (_h1 : (7:ℝ) ≤ s) (_h2 : s ≤ (36/5:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 6) (by norm_num) (by linarith)
  have := term_le_right (s := s) (k := 7) (by norm_num) (by linarith)
  have := term_le_one (k := 8) (by norm_num) s
  have := term_le_one (k := 9) (by norm_num) s
  have := term_le_one (k := 10) (by norm_num) s
  have := term_le_one (k := 11) (by norm_num) s
  have := term_le_one (k := 12) (by norm_num) s
  have := term_le_one (k := 13) (by norm_num) s
  have := term_le_one (k := 14) (by norm_num) s
  have := term_zero_low (s := s) (k := 15) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 16) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 17) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[36/5, 15/2]`. -/
theorem F_le_31 {s : ℝ} (_h1 : (36/5:ℝ) ≤ s) (_h2 : s ≤ (15/2:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 6) (by norm_num) (by linarith)
  have := term_le_right (s := s) (k := 7) (by norm_num) (by linarith)
  have := term_le_one (k := 8) (by norm_num) s
  have := term_le_one (k := 9) (by norm_num) s
  have := term_le_one (k := 10) (by norm_num) s
  have := term_le_one (k := 11) (by norm_num) s
  have := term_le_one (k := 12) (by norm_num) s
  have := term_le_one (k := 13) (by norm_num) s
  have := term_le_one (k := 14) (by norm_num) s
  have := term_le_left (s := s) (k := 15) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 16) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 17) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[15/2, 192/25]`. -/
theorem F_le_32 {s : ℝ} (_h1 : (15/2:ℝ) ≤ s) (_h2 : s ≤ (192/25:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 6) (by norm_num) (by linarith)
  have := term_le_right (s := s) (k := 7) (by norm_num) (by linarith)
  have := term_le_one (k := 8) (by norm_num) s
  have := term_le_one (k := 9) (by norm_num) s
  have := term_le_one (k := 10) (by norm_num) s
  have := term_le_one (k := 11) (by norm_num) s
  have := term_le_one (k := 12) (by norm_num) s
  have := term_le_one (k := 13) (by norm_num) s
  have := term_le_one (k := 14) (by norm_num) s
  have := term_le_one (k := 15) (by norm_num) s
  have := term_zero_low (s := s) (k := 16) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 17) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[192/25, 77/10]`. -/
theorem F_le_33 {s : ℝ} (_h1 : (192/25:ℝ) ≤ s) (_h2 : s ≤ (77/10:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 6) (by norm_num) (by linarith)
  have := term_le_right (s := s) (k := 7) (by norm_num) (by linarith)
  have := term_le_one (k := 8) (by norm_num) s
  have := term_le_one (k := 9) (by norm_num) s
  have := term_le_one (k := 10) (by norm_num) s
  have := term_le_one (k := 11) (by norm_num) s
  have := term_le_one (k := 12) (by norm_num) s
  have := term_le_one (k := 13) (by norm_num) s
  have := term_le_one (k := 14) (by norm_num) s
  have := term_le_one (k := 15) (by norm_num) s
  have := term_le_left (s := s) (k := 16) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 17) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[77/10, 8]`. -/
theorem F_le_34 {s : ℝ} (_h1 : (77/10:ℝ) ≤ s) (_h2 : s ≤ (8:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 6) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 7) (by norm_num) (by linarith)
  have := term_le_one (k := 8) (by norm_num) s
  have := term_le_one (k := 9) (by norm_num) s
  have := term_le_one (k := 10) (by norm_num) s
  have := term_le_one (k := 11) (by norm_num) s
  have := term_le_one (k := 12) (by norm_num) s
  have := term_le_one (k := 13) (by norm_num) s
  have := term_le_one (k := 14) (by norm_num) s
  have := term_le_one (k := 15) (by norm_num) s
  have := term_le_left (s := s) (k := 16) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 17) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[8, 204/25]`. -/
theorem F_le_35 {s : ℝ} (_h1 : (8:ℝ) ≤ s) (_h2 : s ≤ (204/25:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 6) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 7) (by norm_num) (by linarith)
  have := term_le_right (s := s) (k := 8) (by norm_num) (by linarith)
  have := term_le_one (k := 9) (by norm_num) s
  have := term_le_one (k := 10) (by norm_num) s
  have := term_le_one (k := 11) (by norm_num) s
  have := term_le_one (k := 12) (by norm_num) s
  have := term_le_one (k := 13) (by norm_num) s
  have := term_le_one (k := 14) (by norm_num) s
  have := term_le_one (k := 15) (by norm_num) s
  have := term_le_one (k := 16) (by norm_num) s
  have := term_zero_low (s := s) (k := 17) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[204/25, 17/2]`. -/
theorem F_le_36 {s : ℝ} (_h1 : (204/25:ℝ) ≤ s) (_h2 : s ≤ (17/2:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 6) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 7) (by norm_num) (by linarith)
  have := term_le_right (s := s) (k := 8) (by norm_num) (by linarith)
  have := term_le_one (k := 9) (by norm_num) s
  have := term_le_one (k := 10) (by norm_num) s
  have := term_le_one (k := 11) (by norm_num) s
  have := term_le_one (k := 12) (by norm_num) s
  have := term_le_one (k := 13) (by norm_num) s
  have := term_le_one (k := 14) (by norm_num) s
  have := term_le_one (k := 15) (by norm_num) s
  have := term_le_one (k := 16) (by norm_num) s
  have := term_le_left (s := s) (k := 17) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[17/2, 216/25]`. -/
theorem F_le_37 {s : ℝ} (_h1 : (17/2:ℝ) ≤ s) (_h2 : s ≤ (216/25:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 6) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 7) (by norm_num) (by linarith)
  have := term_le_right (s := s) (k := 8) (by norm_num) (by linarith)
  have := term_le_one (k := 9) (by norm_num) s
  have := term_le_one (k := 10) (by norm_num) s
  have := term_le_one (k := 11) (by norm_num) s
  have := term_le_one (k := 12) (by norm_num) s
  have := term_le_one (k := 13) (by norm_num) s
  have := term_le_one (k := 14) (by norm_num) s
  have := term_le_one (k := 15) (by norm_num) s
  have := term_le_one (k := 16) (by norm_num) s
  have := term_le_one (k := 17) (by norm_num) s
  have := term_zero_low (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[216/25, 44/5]`. -/
theorem F_le_38 {s : ℝ} (_h1 : (216/25:ℝ) ≤ s) (_h2 : s ≤ (44/5:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 6) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 7) (by norm_num) (by linarith)
  have := term_le_right (s := s) (k := 8) (by norm_num) (by linarith)
  have := term_le_one (k := 9) (by norm_num) s
  have := term_le_one (k := 10) (by norm_num) s
  have := term_le_one (k := 11) (by norm_num) s
  have := term_le_one (k := 12) (by norm_num) s
  have := term_le_one (k := 13) (by norm_num) s
  have := term_le_one (k := 14) (by norm_num) s
  have := term_le_one (k := 15) (by norm_num) s
  have := term_le_one (k := 16) (by norm_num) s
  have := term_le_one (k := 17) (by norm_num) s
  have := term_le_left (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[44/5, 9]`. -/
theorem F_le_39 {s : ℝ} (_h1 : (44/5:ℝ) ≤ s) (_h2 : s ≤ (9:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 6) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 7) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 8) (by norm_num) (by linarith)
  have := term_le_one (k := 9) (by norm_num) s
  have := term_le_one (k := 10) (by norm_num) s
  have := term_le_one (k := 11) (by norm_num) s
  have := term_le_one (k := 12) (by norm_num) s
  have := term_le_one (k := 13) (by norm_num) s
  have := term_le_one (k := 14) (by norm_num) s
  have := term_le_one (k := 15) (by norm_num) s
  have := term_le_one (k := 16) (by norm_num) s
  have := term_le_one (k := 17) (by norm_num) s
  have := term_le_left (s := s) (k := 18) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[9, 228/25]`. -/
theorem F_le_40 {s : ℝ} (_h1 : (9:ℝ) ≤ s) (_h2 : s ≤ (228/25:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 6) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 7) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 8) (by norm_num) (by linarith)
  have := term_le_right (s := s) (k := 9) (by norm_num) (by linarith)
  have := term_le_one (k := 10) (by norm_num) s
  have := term_le_one (k := 11) (by norm_num) s
  have := term_le_one (k := 12) (by norm_num) s
  have := term_le_one (k := 13) (by norm_num) s
  have := term_le_one (k := 14) (by norm_num) s
  have := term_le_one (k := 15) (by norm_num) s
  have := term_le_one (k := 16) (by norm_num) s
  have := term_le_one (k := 17) (by norm_num) s
  have := term_le_one (k := 18) (by norm_num) s
  have := term_zero_low (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[228/25, 19/2]`. -/
theorem F_le_41 {s : ℝ} (_h1 : (228/25:ℝ) ≤ s) (_h2 : s ≤ (19/2:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 6) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 7) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 8) (by norm_num) (by linarith)
  have := term_le_right (s := s) (k := 9) (by norm_num) (by linarith)
  have := term_le_one (k := 10) (by norm_num) s
  have := term_le_one (k := 11) (by norm_num) s
  have := term_le_one (k := 12) (by norm_num) s
  have := term_le_one (k := 13) (by norm_num) s
  have := term_le_one (k := 14) (by norm_num) s
  have := term_le_one (k := 15) (by norm_num) s
  have := term_le_one (k := 16) (by norm_num) s
  have := term_le_one (k := 17) (by norm_num) s
  have := term_le_one (k := 18) (by norm_num) s
  have := term_le_left (s := s) (k := 19) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[19/2, 48/5]`. -/
theorem F_le_42 {s : ℝ} (_h1 : (19/2:ℝ) ≤ s) (_h2 : s ≤ (48/5:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 6) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 7) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 8) (by norm_num) (by linarith)
  have := term_le_right (s := s) (k := 9) (by norm_num) (by linarith)
  have := term_le_one (k := 10) (by norm_num) s
  have := term_le_one (k := 11) (by norm_num) s
  have := term_le_one (k := 12) (by norm_num) s
  have := term_le_one (k := 13) (by norm_num) s
  have := term_le_one (k := 14) (by norm_num) s
  have := term_le_one (k := 15) (by norm_num) s
  have := term_le_one (k := 16) (by norm_num) s
  have := term_le_one (k := 17) (by norm_num) s
  have := term_le_one (k := 18) (by norm_num) s
  have := term_le_one (k := 19) (by norm_num) s
  have := term_zero_low (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[48/5, 99/10]`. -/
theorem F_le_43 {s : ℝ} (_h1 : (48/5:ℝ) ≤ s) (_h2 : s ≤ (99/10:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 6) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 7) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 8) (by norm_num) (by linarith)
  have := term_le_right (s := s) (k := 9) (by norm_num) (by linarith)
  have := term_le_one (k := 10) (by norm_num) s
  have := term_le_one (k := 11) (by norm_num) s
  have := term_le_one (k := 12) (by norm_num) s
  have := term_le_one (k := 13) (by norm_num) s
  have := term_le_one (k := 14) (by norm_num) s
  have := term_le_one (k := 15) (by norm_num) s
  have := term_le_one (k := 16) (by norm_num) s
  have := term_le_one (k := 17) (by norm_num) s
  have := term_le_one (k := 18) (by norm_num) s
  have := term_le_one (k := 19) (by norm_num) s
  have := term_le_left (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[99/10, 10]`. -/
theorem F_le_44 {s : ℝ} (_h1 : (99/10:ℝ) ≤ s) (_h2 : s ≤ (10:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 6) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 7) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 8) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 9) (by norm_num) (by linarith)
  have := term_le_one (k := 10) (by norm_num) s
  have := term_le_one (k := 11) (by norm_num) s
  have := term_le_one (k := 12) (by norm_num) s
  have := term_le_one (k := 13) (by norm_num) s
  have := term_le_one (k := 14) (by norm_num) s
  have := term_le_one (k := 15) (by norm_num) s
  have := term_le_one (k := 16) (by norm_num) s
  have := term_le_one (k := 17) (by norm_num) s
  have := term_le_one (k := 18) (by norm_num) s
  have := term_le_one (k := 19) (by norm_num) s
  have := term_le_left (s := s) (k := 20) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[10, 252/25]`. -/
theorem F_le_45 {s : ℝ} (_h1 : (10:ℝ) ≤ s) (_h2 : s ≤ (252/25:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 6) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 7) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 8) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 9) (by norm_num) (by linarith)
  have := term_le_right (s := s) (k := 10) (by norm_num) (by linarith)
  have := term_le_one (k := 11) (by norm_num) s
  have := term_le_one (k := 12) (by norm_num) s
  have := term_le_one (k := 13) (by norm_num) s
  have := term_le_one (k := 14) (by norm_num) s
  have := term_le_one (k := 15) (by norm_num) s
  have := term_le_one (k := 16) (by norm_num) s
  have := term_le_one (k := 17) (by norm_num) s
  have := term_le_one (k := 18) (by norm_num) s
  have := term_le_one (k := 19) (by norm_num) s
  have := term_le_one (k := 20) (by norm_num) s
  have := term_zero_low (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[252/25, 21/2]`. -/
theorem F_le_46 {s : ℝ} (_h1 : (252/25:ℝ) ≤ s) (_h2 : s ≤ (21/2:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 6) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 7) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 8) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 9) (by norm_num) (by linarith)
  have := term_le_right (s := s) (k := 10) (by norm_num) (by linarith)
  have := term_le_one (k := 11) (by norm_num) s
  have := term_le_one (k := 12) (by norm_num) s
  have := term_le_one (k := 13) (by norm_num) s
  have := term_le_one (k := 14) (by norm_num) s
  have := term_le_one (k := 15) (by norm_num) s
  have := term_le_one (k := 16) (by norm_num) s
  have := term_le_one (k := 17) (by norm_num) s
  have := term_le_one (k := 18) (by norm_num) s
  have := term_le_one (k := 19) (by norm_num) s
  have := term_le_one (k := 20) (by norm_num) s
  have := term_le_left (s := s) (k := 21) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[21/2, 264/25]`. -/
theorem F_le_47 {s : ℝ} (_h1 : (21/2:ℝ) ≤ s) (_h2 : s ≤ (264/25:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 6) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 7) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 8) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 9) (by norm_num) (by linarith)
  have := term_le_right (s := s) (k := 10) (by norm_num) (by linarith)
  have := term_le_one (k := 11) (by norm_num) s
  have := term_le_one (k := 12) (by norm_num) s
  have := term_le_one (k := 13) (by norm_num) s
  have := term_le_one (k := 14) (by norm_num) s
  have := term_le_one (k := 15) (by norm_num) s
  have := term_le_one (k := 16) (by norm_num) s
  have := term_le_one (k := 17) (by norm_num) s
  have := term_le_one (k := 18) (by norm_num) s
  have := term_le_one (k := 19) (by norm_num) s
  have := term_le_one (k := 20) (by norm_num) s
  have := term_le_one (k := 21) (by norm_num) s
  have := term_zero_low (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[264/25, 11]`. -/
theorem F_le_48 {s : ℝ} (_h1 : (264/25:ℝ) ≤ s) (_h2 : s ≤ (11:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 6) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 7) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 8) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 9) (by norm_num) (by linarith)
  have := term_le_right (s := s) (k := 10) (by norm_num) (by linarith)
  have := term_le_one (k := 11) (by norm_num) s
  have := term_le_one (k := 12) (by norm_num) s
  have := term_le_one (k := 13) (by norm_num) s
  have := term_le_one (k := 14) (by norm_num) s
  have := term_le_one (k := 15) (by norm_num) s
  have := term_le_one (k := 16) (by norm_num) s
  have := term_le_one (k := 17) (by norm_num) s
  have := term_le_one (k := 18) (by norm_num) s
  have := term_le_one (k := 19) (by norm_num) s
  have := term_le_one (k := 20) (by norm_num) s
  have := term_le_one (k := 21) (by norm_num) s
  have := term_le_left (s := s) (k := 22) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[11, 276/25]`. -/
theorem F_le_49 {s : ℝ} (_h1 : (11:ℝ) ≤ s) (_h2 : s ≤ (276/25:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 6) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 7) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 8) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 9) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 10) (by norm_num) (by linarith)
  have := term_le_right (s := s) (k := 11) (by norm_num) (by linarith)
  have := term_le_one (k := 12) (by norm_num) s
  have := term_le_one (k := 13) (by norm_num) s
  have := term_le_one (k := 14) (by norm_num) s
  have := term_le_one (k := 15) (by norm_num) s
  have := term_le_one (k := 16) (by norm_num) s
  have := term_le_one (k := 17) (by norm_num) s
  have := term_le_one (k := 18) (by norm_num) s
  have := term_le_one (k := 19) (by norm_num) s
  have := term_le_one (k := 20) (by norm_num) s
  have := term_le_one (k := 21) (by norm_num) s
  have := term_le_one (k := 22) (by norm_num) s
  have := term_zero_low (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[276/25, 23/2]`. -/
theorem F_le_50 {s : ℝ} (_h1 : (276/25:ℝ) ≤ s) (_h2 : s ≤ (23/2:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 6) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 7) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 8) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 9) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 10) (by norm_num) (by linarith)
  have := term_le_right (s := s) (k := 11) (by norm_num) (by linarith)
  have := term_le_one (k := 12) (by norm_num) s
  have := term_le_one (k := 13) (by norm_num) s
  have := term_le_one (k := 14) (by norm_num) s
  have := term_le_one (k := 15) (by norm_num) s
  have := term_le_one (k := 16) (by norm_num) s
  have := term_le_one (k := 17) (by norm_num) s
  have := term_le_one (k := 18) (by norm_num) s
  have := term_le_one (k := 19) (by norm_num) s
  have := term_le_one (k := 20) (by norm_num) s
  have := term_le_one (k := 21) (by norm_num) s
  have := term_le_one (k := 22) (by norm_num) s
  have := term_le_left (s := s) (k := 23) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[23/2, 288/25]`. -/
theorem F_le_51 {s : ℝ} (_h1 : (23/2:ℝ) ≤ s) (_h2 : s ≤ (288/25:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 6) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 7) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 8) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 9) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 10) (by norm_num) (by linarith)
  have := term_le_right (s := s) (k := 11) (by norm_num) (by linarith)
  have := term_le_one (k := 12) (by norm_num) s
  have := term_le_one (k := 13) (by norm_num) s
  have := term_le_one (k := 14) (by norm_num) s
  have := term_le_one (k := 15) (by norm_num) s
  have := term_le_one (k := 16) (by norm_num) s
  have := term_le_one (k := 17) (by norm_num) s
  have := term_le_one (k := 18) (by norm_num) s
  have := term_le_one (k := 19) (by norm_num) s
  have := term_le_one (k := 20) (by norm_num) s
  have := term_le_one (k := 21) (by norm_num) s
  have := term_le_one (k := 22) (by norm_num) s
  have := term_le_one (k := 23) (by norm_num) s
  have := term_zero_low (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith

/-- `F ≤ 19/20` on `[288/25, 12]`. -/
theorem F_le_52 {s : ℝ} (_h1 : (288/25:ℝ) ≤ s) (_h2 : s ≤ (12:ℝ)) : F s ≤ 19 / 20 := by
  rw [F_eq]
  have := term_zero_high (s := s) (k := 3) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 4) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 5) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 6) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 7) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 8) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 9) (by norm_num) (by linarith)
  have := term_zero_high (s := s) (k := 10) (by norm_num) (by linarith)
  have := term_le_right (s := s) (k := 11) (by norm_num) (by linarith)
  have := term_le_one (k := 12) (by norm_num) s
  have := term_le_one (k := 13) (by norm_num) s
  have := term_le_one (k := 14) (by norm_num) s
  have := term_le_one (k := 15) (by norm_num) s
  have := term_le_one (k := 16) (by norm_num) s
  have := term_le_one (k := 17) (by norm_num) s
  have := term_le_one (k := 18) (by norm_num) s
  have := term_le_one (k := 19) (by norm_num) s
  have := term_le_one (k := 20) (by norm_num) s
  have := term_le_one (k := 21) (by norm_num) s
  have := term_le_one (k := 22) (by norm_num) s
  have := term_le_one (k := 23) (by norm_num) s
  have := term_le_left (s := s) (k := 24) (by norm_num) (by linarith)
  have := term_zero_low (s := s) (k := 25) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 3) (by norm_num) (by linarith)
  have := corner_zero (s := s) (k := 4) (by norm_num) (by linarith)
  linarith
/-- **`F ≤ 19/20` on `[0, 12]`.** -/
theorem F_le_of_mem {s : ℝ} (h1 : 0 ≤ s) (h2 : s ≤ 12) : F s ≤ 19 / 20 := by
  rcases le_total s (36/25:ℝ) with h | h
  · exact F_le_0 (by linarith) h
  rcases le_total s (3/2:ℝ) with h | h
  · exact F_le_1 (by linarith) h
  rcases le_total s (9/5:ℝ) with h | h
  · exact F_le_2 (by linarith) h
  rcases le_total s (48/25:ℝ) with h | h
  · exact F_le_3 (by linarith) h
  rcases le_total s (39/20:ℝ) with h | h
  · exact F_le_4 (by linarith) h
  rcases le_total s (2:ℝ) with h | h
  · exact F_le_5 (by linarith) h
  rcases le_total s (12/5:ℝ) with h | h
  · exact F_le_6 (by linarith) h
  rcases le_total s (5/2:ℝ) with h | h
  · exact F_le_7 (by linarith) h
  rcases le_total s (13/5:ℝ) with h | h
  · exact F_le_8 (by linarith) h
  rcases le_total s (72/25:ℝ) with h | h
  · exact F_le_9 (by linarith) h
  rcases le_total s (3:ℝ) with h | h
  · exact F_le_10 (by linarith) h
  rcases le_total s (33/10:ℝ) with h | h
  · exact F_le_11 (by linarith) h
  rcases le_total s (84/25:ℝ) with h | h
  · exact F_le_12 (by linarith) h
  rcases le_total s (7/2:ℝ) with h | h
  · exact F_le_13 (by linarith) h
  rcases le_total s (96/25:ℝ) with h | h
  · exact F_le_14 (by linarith) h
  rcases le_total s (4:ℝ) with h | h
  · exact F_le_15 (by linarith) h
  rcases le_total s (108/25:ℝ) with h | h
  · exact F_le_16 (by linarith) h
  rcases le_total s (22/5:ℝ) with h | h
  · exact F_le_17 (by linarith) h
  rcases le_total s (9/2:ℝ) with h | h
  · exact F_le_18 (by linarith) h
  rcases le_total s (24/5:ℝ) with h | h
  · exact F_le_19 (by linarith) h
  rcases le_total s (5:ℝ) with h | h
  · exact F_le_20 (by linarith) h
  rcases le_total s (132/25:ℝ) with h | h
  · exact F_le_21 (by linarith) h
  rcases le_total s (11/2:ℝ) with h | h
  · exact F_le_22 (by linarith) h
  rcases le_total s (144/25:ℝ) with h | h
  · exact F_le_23 (by linarith) h
  rcases le_total s (6:ℝ) with h | h
  · exact F_le_24 (by linarith) h
  rcases le_total s (156/25:ℝ) with h | h
  · exact F_le_25 (by linarith) h
  rcases le_total s (13/2:ℝ) with h | h
  · exact F_le_26 (by linarith) h
  rcases le_total s (33/5:ℝ) with h | h
  · exact F_le_27 (by linarith) h
  rcases le_total s (168/25:ℝ) with h | h
  · exact F_le_28 (by linarith) h
  rcases le_total s (7:ℝ) with h | h
  · exact F_le_29 (by linarith) h
  rcases le_total s (36/5:ℝ) with h | h
  · exact F_le_30 (by linarith) h
  rcases le_total s (15/2:ℝ) with h | h
  · exact F_le_31 (by linarith) h
  rcases le_total s (192/25:ℝ) with h | h
  · exact F_le_32 (by linarith) h
  rcases le_total s (77/10:ℝ) with h | h
  · exact F_le_33 (by linarith) h
  rcases le_total s (8:ℝ) with h | h
  · exact F_le_34 (by linarith) h
  rcases le_total s (204/25:ℝ) with h | h
  · exact F_le_35 (by linarith) h
  rcases le_total s (17/2:ℝ) with h | h
  · exact F_le_36 (by linarith) h
  rcases le_total s (216/25:ℝ) with h | h
  · exact F_le_37 (by linarith) h
  rcases le_total s (44/5:ℝ) with h | h
  · exact F_le_38 (by linarith) h
  rcases le_total s (9:ℝ) with h | h
  · exact F_le_39 (by linarith) h
  rcases le_total s (228/25:ℝ) with h | h
  · exact F_le_40 (by linarith) h
  rcases le_total s (19/2:ℝ) with h | h
  · exact F_le_41 (by linarith) h
  rcases le_total s (48/5:ℝ) with h | h
  · exact F_le_42 (by linarith) h
  rcases le_total s (99/10:ℝ) with h | h
  · exact F_le_43 (by linarith) h
  rcases le_total s (10:ℝ) with h | h
  · exact F_le_44 (by linarith) h
  rcases le_total s (252/25:ℝ) with h | h
  · exact F_le_45 (by linarith) h
  rcases le_total s (21/2:ℝ) with h | h
  · exact F_le_46 (by linarith) h
  rcases le_total s (264/25:ℝ) with h | h
  · exact F_le_47 (by linarith) h
  rcases le_total s (11:ℝ) with h | h
  · exact F_le_48 (by linarith) h
  rcases le_total s (276/25:ℝ) with h | h
  · exact F_le_49 (by linarith) h
  rcases le_total s (23/2:ℝ) with h | h
  · exact F_le_50 (by linarith) h
  rcases le_total s (288/25:ℝ) with h | h
  · exact F_le_51 (by linarith) h
  exact F_le_52 (by linarith) h2

end Cvs.Route.Visibility.AliasWindowCornerCut
