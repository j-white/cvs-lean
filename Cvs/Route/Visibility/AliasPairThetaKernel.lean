import Mathlib
import Cvs.Route.Visibility.AliasTailThroughWindow
import Cvs.Route.Visibility.AliasWindowCornerCut

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The `θ`-kernel of the alias pairs: `β_k`, `Λ_k`, the Neumann ratio and the window corners

`β_k = k²/(k²θ² − 1)`, `Λ_k = k² + β_k/2`, `Λ_k − Λ_l = (k² − l²)(1 − π_kπ_l/2)`; on `θ ≥ 12/25` the ratio
`q_{kl} = (β_k + β_l)/(2|Λ_k − Λ_l|)` is at most `3/4` off `{3, 4}` (and on it for `θ ≥ 3/5`), `λ_k = √Λ_k` are
`1/3`-separated, and `ρ`, `τ`, `ρτ` are differentiable off their corners with `|ρ′| ≤ 50`, `|(ρτ)′| ≤ 70`.
-/

noncomputable section

namespace Cvs.Route.Visibility.AliasPairThetaKernel
open Cvs.ZeroCounting

open Real Set Filter Topology
open Cvs.Route.Visibility.AliasWindowCornerCut (rho tau rho_nonneg rho_le_one rho_eq_one rho_eq_zero_of_le rho_eq_zero_of_ge)
open Cvs.Route.Visibility.AliasTailThroughWindow (rhoT continuous_rho continuous_tau)

/-- `β_k(θ) = k²/(k²θ² − 1)`. -/
def bet (k : ℕ) (θ : ℝ) : ℝ := (k : ℝ) ^ 2 / ((k : ℝ) ^ 2 * θ ^ 2 - 1)

/-- `π_k(θ) = 1/(k²θ² − 1)`. -/
def piK (k : ℕ) (θ : ℝ) : ℝ := 1 / ((k : ℝ) ^ 2 * θ ^ 2 - 1)

/-- `Λ_k(θ) = k² + β_k(θ)/2`. -/
def Lam (k : ℕ) (θ : ℝ) : ℝ := (k : ℝ) ^ 2 + bet k θ / 2

/-- `m²θ₀² − 1 ≤ k²θ² − 1` for `m ≤ k`, `θ₀ ≤ θ`. -/
theorem sq_mul_sq_sub_one_pos {k m : ℕ} {θ θ₀ : ℝ} (hmk : m ≤ k) (hθ₀ : 0 ≤ θ₀) (hθ : θ₀ ≤ θ)
    (_h : 1 < (m : ℝ) ^ 2 * θ₀ ^ 2) : (m : ℝ) ^ 2 * θ₀ ^ 2 - 1 ≤ (k : ℝ) ^ 2 * θ ^ 2 - 1 := by
  have hm : (m : ℝ) ≤ k := by exact_mod_cast hmk
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h1 : (m : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 := pow_le_pow_left₀ hm0 hm 2
  have h2 : θ₀ ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ hθ₀ hθ 2
  nlinarith [sq_nonneg θ₀, sq_nonneg (m : ℝ)]

/-- **Monotonicity of `β`**: `β_k(θ) ≤ m²/(m²θ₀² − 1)` for `m ≤ k` and `θ₀ ≤ θ` with `m²θ₀² > 1`. -/
theorem bet_le {k m : ℕ} {θ θ₀ : ℝ} (hmk : m ≤ k) (hθ₀ : 0 ≤ θ₀) (hθ : θ₀ ≤ θ)
    (h : 1 < (m : ℝ) ^ 2 * θ₀ ^ 2) : bet k θ ≤ (m : ℝ) ^ 2 / ((m : ℝ) ^ 2 * θ₀ ^ 2 - 1) := by
  have hle := sq_mul_sq_sub_one_pos hmk hθ₀ hθ h
  have hm : (m : ℝ) ≤ k := by exact_mod_cast hmk
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h1 : (m : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 := pow_le_pow_left₀ hm0 hm 2
  have h2 : θ₀ ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ hθ₀ hθ 2
  unfold bet
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (m : ℝ)) (sq_nonneg (k : ℝ))) (sub_nonneg.mpr h2)]

/-- **Monotonicity of `π`**: `π_k(θ) ≤ 1/(m²θ₀² − 1)`. -/
theorem piK_le {k m : ℕ} {θ θ₀ : ℝ} (hmk : m ≤ k) (hθ₀ : 0 ≤ θ₀) (hθ : θ₀ ≤ θ)
    (h : 1 < (m : ℝ) ^ 2 * θ₀ ^ 2) : piK k θ ≤ 1 / ((m : ℝ) ^ 2 * θ₀ ^ 2 - 1) := by
  have hle := sq_mul_sq_sub_one_pos hmk hθ₀ hθ h
  unfold piK
  exact one_div_le_one_div_of_le (by linarith) hle

/-- `β_k > 0` when `k²θ² > 1`. -/
theorem bet_pos {k : ℕ} {θ : ℝ} (hk : 0 < k) (h : 1 < (k : ℝ) ^ 2 * θ ^ 2) : 0 < bet k θ := by
  unfold bet; have : (0 : ℝ) < k := by exact_mod_cast hk
  exact div_pos (by positivity) (by linarith)

/-- `π_k > 0` when `k²θ² > 1`. -/
theorem piK_pos {k : ℕ} {θ : ℝ} (h : 1 < (k : ℝ) ^ 2 * θ ^ 2) : 0 < piK k θ := by
  unfold piK; exact div_pos one_pos (by linarith)

/-- **The level gap**: `Λ_k − Λ_l = (k² − l²)(1 − π_kπ_l/2)`. -/
theorem Lam_sub {k l : ℕ} {θ : ℝ} (hk : 1 < (k : ℝ) ^ 2 * θ ^ 2) (hl : 1 < (l : ℝ) ^ 2 * θ ^ 2) :
    Lam k θ - Lam l θ = ((k : ℝ) ^ 2 - (l : ℝ) ^ 2) * (1 - piK k θ * piK l θ / 2) := by
  have h1 : (k : ℝ) ^ 2 * θ ^ 2 - 1 ≠ 0 := by linarith
  have h2 : (l : ℝ) ^ 2 * θ ^ 2 - 1 ≠ 0 := by linarith
  unfold Lam bet piK
  have key : (k : ℝ) ^ 2 * ((l : ℝ) ^ 2 * θ ^ 2 - 1) - (l : ℝ) ^ 2 * ((k : ℝ) ^ 2 * θ ^ 2 - 1)
      = (l : ℝ) ^ 2 - (k : ℝ) ^ 2 := by ring
  have h2' : θ ^ 2 * (l : ℝ) ^ 2 - 1 ≠ 0 := by linarith
  have h1' : θ ^ 2 * (k : ℝ) ^ 2 - 1 ≠ 0 := by linarith
  field_simp
  linear_combination (-1 : ℝ) * key

/-- **The `θ`-derivative of `β`**: `β_k′ = −2θβ_k²`. -/
theorem hasDerivAt_bet {k : ℕ} {θ : ℝ} (h : (k : ℝ) ^ 2 * θ ^ 2 - 1 ≠ 0) :
    HasDerivAt (bet k) (-2 * θ * bet k θ ^ 2) θ := by
  have hd : HasDerivAt (fun θ : ℝ => (k : ℝ) ^ 2 * θ ^ 2 - 1) ((k : ℝ) ^ 2 * (2 * θ)) θ := by
    simpa using ((hasDerivAt_pow 2 θ).const_mul ((k : ℝ) ^ 2)).sub_const 1
  have := (hasDerivAt_const θ ((k : ℝ) ^ 2)).div hd h
  refine this.congr_deriv ?_
  unfold bet
  field_simp
  ring

/-- The Neumann ratio `q_{kl} = (β_k + β_l)/(2|Λ_k − Λ_l|)`. -/
def qK (k l : ℕ) (θ : ℝ) : ℝ := (bet k θ + bet l θ) / (2 * |Lam k θ - Lam l θ|)

/-- `q_{kl} = q_{lk}`. -/
theorem qK_comm (k l : ℕ) (θ : ℝ) : qK k l θ = qK l k θ := by
  unfold qK; rw [add_comm, abs_sub_comm]

/-- `k²θ² > 1` for `k ≥ 3`, `θ ≥ 12/25`. -/
theorem one_lt_of {k : ℕ} (hk : 3 ≤ k) {θ : ℝ} (hθ : 12 / 25 ≤ θ) : 1 < (k : ℝ) ^ 2 * θ ^ 2 := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : (9 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have h2 : (144 / 625 : ℝ) ≤ θ ^ 2 := by nlinarith
  nlinarith

/-- A sufficient condition for `q_{kl} ≤ 3/4` with `k < l`. -/
theorem qK_le_of_lt {k l : ℕ} {θ : ℝ} (hk : 1 < (k : ℝ) ^ 2 * θ ^ 2) (hl : 1 < (l : ℝ) ^ 2 * θ ^ 2)
    {U V P D₀ : ℝ} (hu : bet k θ ≤ U) (hv : bet l θ ≤ V) (hP : piK k θ * piK l θ ≤ P)
    (hD : D₀ ≤ (l : ℝ) ^ 2 - (k : ℝ) ^ 2) (hD0 : 0 < D₀) (hP1 : P ≤ 1)
    (hkey : U + V ≤ 3 / 2 * D₀ * (1 - P / 2)) : qK k l θ ≤ 3 / 4 := by
  have hp0 : 0 ≤ piK k θ * piK l θ := mul_nonneg (piK_pos hk).le (piK_pos hl).le
  have hgap : D₀ * (1 - P / 2) ≤ |Lam k θ - Lam l θ| := by
    rw [Lam_sub hk hl, abs_mul, abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    have : 1 - P / 2 ≤ 1 - piK k θ * piK l θ / 2 := by linarith
    calc D₀ * (1 - P / 2) ≤ ((l : ℝ) ^ 2 - (k : ℝ) ^ 2) * (1 - piK k θ * piK l θ / 2) :=
          mul_le_mul hD this (by linarith) (by linarith)
      _ = -((k : ℝ) ^ 2 - (l : ℝ) ^ 2) * (1 - piK k θ * piK l θ / 2) := by ring
  have hpos : 0 < D₀ * (1 - P / 2) := mul_pos hD0 (by linarith)
  unfold qK
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- **The Neumann ratio is at most `3/4`** on every pair other than `{3, 4}` for `θ ≥ 12/25`, and on `{3, 4}` for
`θ ≥ 3/5`. -/
theorem qK_le {k l : ℕ} (hk : 3 ≤ k) (hl : 3 ≤ l) (hkl : k ≠ l) {θ : ℝ} (hθ : 12 / 25 ≤ θ)
    (h34 : ¬(k = 3 ∧ l = 4) ∧ ¬(k = 4 ∧ l = 3) ∨ 3 / 5 ≤ θ) : qK k l θ ≤ 3 / 4 := by
  -- reduce to `k < l`
  wlog hlt : k < l generalizing k l
  · rw [qK_comm]
    refine this hl hk hkl.symm ?_ (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hkl))
    rcases h34 with h | h
    · exact Or.inl ⟨fun h' => h.2 ⟨h'.2, h'.1⟩, fun h' => h.1 ⟨h'.2, h'.1⟩⟩
    · exact Or.inr h
  have hk1 := one_lt_of hk hθ
  have hl1 := one_lt_of hl hθ
  have hθ0 : (0 : ℝ) ≤ 12 / 25 := by norm_num
  have hk' : (k : ℝ) + 1 ≤ l := by exact_mod_cast hlt
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  rcases (show k = 3 ∨ k = 4 ∨ 5 ≤ k by omega) with rfl | rfl | h5
  · rcases (show l = 4 ∨ 5 ≤ l by omega) with rfl | h5
    · have hθ' : 3 / 5 ≤ θ := by
        rcases h34 with h | h
        · exact absurd ⟨rfl, rfl⟩ h.1
        · exact h
      refine qK_le_of_lt hk1 hl1 (U := 225 / 56) (V := 400 / 119) (P := 25 / 56 * (25 / 119)) (D₀ := 7)
        ?_ ?_ ?_ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · have := bet_le (le_refl 3) (by norm_num) hθ' (by norm_num); norm_num at this ⊢; linarith
      · have := bet_le (le_refl 4) (by norm_num) hθ' (by norm_num); norm_num at this ⊢; linarith
      · have h1 := piK_le (le_refl 3) (by norm_num) hθ' (by norm_num)
        have h2 := piK_le (le_refl 4) (by norm_num) hθ' (by norm_num)
        norm_num at h1 h2
        exact mul_le_mul h1 h2 (piK_pos hl1).le (by norm_num)
    · have hl5 : (5 : ℝ) ≤ l := by exact_mod_cast h5
      refine qK_le_of_lt hk1 hl1 (U := 5625 / 671) (V := 625 / 119) (P := 625 / 671 * (25 / 119)) (D₀ := 16)
        ?_ ?_ ?_ (by push_cast; nlinarith) (by norm_num) (by norm_num) (by norm_num)
      · have := bet_le (le_refl 3) hθ0 hθ (by norm_num); norm_num at this ⊢; linarith
      · have := bet_le h5 hθ0 hθ (by norm_num); norm_num at this ⊢; linarith
      · have h1 := piK_le (le_refl 3) hθ0 hθ (by norm_num)
        have h2 := piK_le h5 hθ0 hθ (by norm_num)
        norm_num at h1 h2
        exact mul_le_mul h1 h2 (piK_pos hl1).le (by norm_num)
  · rcases (show l = 5 ∨ 6 ≤ l by omega) with rfl | h6
    · refine qK_le_of_lt hk1 hl1 (U := 10000 / 1679) (V := 625 / 119) (P := 625 / 1679 * (25 / 119)) (D₀ := 9)
        ?_ ?_ ?_ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · have := bet_le (le_refl 4) hθ0 hθ (by norm_num); norm_num at this ⊢; linarith
      · have := bet_le (le_refl 5) hθ0 hθ (by norm_num); norm_num at this ⊢; linarith
      · have h1 := piK_le (le_refl 4) hθ0 hθ (by norm_num)
        have h2 := piK_le (le_refl 5) hθ0 hθ (by norm_num)
        norm_num at h1 h2
        exact mul_le_mul h1 h2 (piK_pos hl1).le (by norm_num)
    · have hl6 : (6 : ℝ) ≤ l := by exact_mod_cast h6
      refine qK_le_of_lt hk1 hl1 (U := 10000 / 1679) (V := 10000 / 1679) (P := 625 / 1679 * (625 / 1679))
        (D₀ := 20) ?_ ?_ ?_ (by push_cast; nlinarith) (by norm_num) (by norm_num) (by norm_num)
      · have := bet_le (le_refl 4) hθ0 hθ (by norm_num); norm_num at this ⊢; linarith
      · have := bet_le (show 4 ≤ l by omega) hθ0 hθ (by norm_num); norm_num at this ⊢; linarith
      · have h1 := piK_le (le_refl 4) hθ0 hθ (by norm_num)
        have h2 := piK_le (show 4 ≤ l by omega) hθ0 hθ (by norm_num)
        norm_num at h1 h2
        exact mul_le_mul h1 h2 (piK_pos hl1).le (by norm_num)
  · have hk5 : (5 : ℝ) ≤ k := by exact_mod_cast h5
    refine qK_le_of_lt hk1 hl1 (U := 625 / 119) (V := 625 / 119) (P := 25 / 119 * (25 / 119))
      (D₀ := 11) ?_ ?_ ?_ (by nlinarith) (by norm_num) (by norm_num) (by norm_num)
    · have := bet_le h5 hθ0 hθ (by norm_num); norm_num at this ⊢; linarith
    · have := bet_le (show 5 ≤ l by omega) hθ0 hθ (by norm_num); norm_num at this ⊢; linarith
    · have h1 := piK_le h5 hθ0 hθ (by norm_num)
      have h2 := piK_le (show 5 ≤ l by omega) hθ0 hθ (by norm_num)
      norm_num at h1 h2
      exact mul_le_mul h1 h2 (piK_pos hl1).le (by norm_num)

/-- `0 < β_k ≤ 5625/671` for `k ≥ 3`, `θ ≥ 12/25`. -/
theorem bet_mem {k : ℕ} (hk : 3 ≤ k) {θ : ℝ} (hθ : 12 / 25 ≤ θ) : 0 < bet k θ ∧ bet k θ ≤ 5625 / 671 := by
  refine ⟨bet_pos (by omega) (one_lt_of hk hθ), ?_⟩
  have := bet_le hk (by norm_num) hθ (by norm_num); norm_num at this ⊢; linarith

/-- `0 < π_k ≤ 625/671` for `k ≥ 3`, `θ ≥ 12/25`. -/
theorem piK_mem {k : ℕ} (hk : 3 ≤ k) {θ : ℝ} (hθ : 12 / 25 ≤ θ) : 0 < piK k θ ∧ piK k θ ≤ 625 / 671 := by
  refine ⟨piK_pos (one_lt_of hk hθ), ?_⟩
  have := piK_le hk (by norm_num) hθ (by norm_num); norm_num at this ⊢; linarith

/-- **The level gap is at least half the square gap**: `|Λ_k − Λ_l| ≥ |k² − l²|/2`. -/
theorem abs_Lam_sub_ge {k l : ℕ} (hk : 3 ≤ k) (hl : 3 ≤ l) {θ : ℝ} (hθ : 12 / 25 ≤ θ) :
    |(k : ℝ) ^ 2 - (l : ℝ) ^ 2| / 2 ≤ |Lam k θ - Lam l θ| := by
  rw [Lam_sub (one_lt_of hk hθ) (one_lt_of hl hθ), abs_mul]
  have h1 := piK_mem hk hθ
  have h2 := piK_mem hl hθ
  have hp : piK k θ * piK l θ ≤ 1 := by nlinarith
  have hp0 : 0 ≤ piK k θ * piK l θ := by nlinarith
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - piK k θ * piK l θ / 2)]
  nlinarith [abs_nonneg ((k : ℝ) ^ 2 - (l : ℝ) ^ 2)]

/-- **The Hilbert frequencies** `λ_k = √Λ_k`. -/
def lamF (k : ℕ) (θ : ℝ) : ℝ := √(Lam k θ)

/-- `k² ≤ Λ_k ≤ (k + 1)²`. -/
theorem Lam_mem {k : ℕ} (hk : 3 ≤ k) {θ : ℝ} (hθ : 12 / 25 ≤ θ) :
    (k : ℝ) ^ 2 ≤ Lam k θ ∧ Lam k θ ≤ ((k : ℝ) + 1) ^ 2 := by
  have h := bet_mem hk hθ
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  unfold Lam
  constructor <;> nlinarith

/-- `k ≤ λ_k ≤ k + 1`. -/
theorem lamF_mem {k : ℕ} (hk : 3 ≤ k) {θ : ℝ} (hθ : 12 / 25 ≤ θ) :
    (k : ℝ) ≤ lamF k θ ∧ lamF k θ ≤ (k : ℝ) + 1 := by
  have h := Lam_mem hk hθ
  unfold lamF
  constructor
  · exact Real.le_sqrt_of_sq_le h.1
  · exact Real.sqrt_le_iff.mpr ⟨by positivity, h.2⟩

/-- `λ_k² = Λ_k`. -/
theorem lamF_sq {k : ℕ} (hk : 3 ≤ k) {θ : ℝ} (hθ : 12 / 25 ≤ θ) : lamF k θ ^ 2 = Lam k θ := by
  unfold lamF
  exact Real.sq_sqrt (le_trans (sq_nonneg _) (Lam_mem hk hθ).1)

/-- **The Hilbert frequencies are separated by `1/3`.** -/
theorem lamF_gap {k l : ℕ} (hk : 3 ≤ k) (hkl : k < l) {θ : ℝ} (hθ : 12 / 25 ≤ θ) :
    lamF k θ + 1 / 3 ≤ lamF l θ := by
  have hl : 3 ≤ l := by omega
  have hA := lamF_mem hk hθ
  have hB := lamF_mem hl hθ
  have hA2 := lamF_sq hk hθ
  have hB2 := lamF_sq hl hθ
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hkl' : (k : ℝ) + 1 ≤ l := by exact_mod_cast hkl
  have hg : ((l : ℝ) + k) / 2 ≤ Lam l θ - Lam k θ := by
    have := abs_Lam_sub_ge hl hk hθ
    rw [abs_of_nonneg (by nlinarith : (0 : ℝ) ≤ (l : ℝ) ^ 2 - (k : ℝ) ^ 2)] at this
    have hpos : 0 ≤ Lam l θ - Lam k θ := by
      rw [Lam_sub (one_lt_of hl hθ) (one_lt_of hk hθ)]
      have h1 := piK_mem hk hθ
      have h2 := piK_mem hl hθ
      have : piK l θ * piK k θ ≤ 1 := by nlinarith
      exact mul_nonneg (by nlinarith) (by linarith)
    rw [abs_of_nonneg hpos] at this
    nlinarith
  nlinarith

/-- The partial fractions of `k/(Λ_k − Λ_l)` in the frequencies `λ = √Λ`. -/
theorem div_Lam_sub_eq {k l : ℕ} (hk : 3 ≤ k) (hl : 3 ≤ l) (hkl : k ≠ l) {θ : ℝ} (hθ : 12 / 25 ≤ θ) :
    (k : ℝ) / (Lam k θ - Lam l θ)
      = (k : ℝ) / (2 * lamF k θ) * (1 / (lamF k θ - lamF l θ) + 1 / (lamF k θ + lamF l θ)) := by
  have hA := lamF_mem hk hθ
  have hB := lamF_mem hl hθ
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hne : lamF k θ - lamF l θ ≠ 0 := by
    rcases lt_or_gt_of_ne hkl with h | h
    · have := lamF_gap hk h hθ; intro h'; linarith
    · have := lamF_gap hl h hθ; intro h'; linarith
  have hpos : lamF k θ + lamF l θ ≠ 0 := by linarith
  have hA0 : lamF k θ ≠ 0 := by linarith
  rw [← lamF_sq hk hθ, ← lamF_sq hl hθ]
  have hsq : lamF k θ ^ 2 - lamF l θ ^ 2 ≠ 0 := by
    rw [sq_sub_sq]; exact mul_ne_zero hpos hne
  field_simp
  ring

/-- The derivative of `ρ` off its four corners. -/
def rhoD (θ : ℝ) : ℝ :=
  if θ < 12 / 25 then 0 else if θ < 1 / 2 then 50 else if θ < 1 then 0 else if θ < 11 / 10 then -10 else 0

/-- The derivative of `τ` off its two corners. -/
def tauD (θ : ℝ) : ℝ := if θ < 3 / 5 then 0 else if θ < 13 / 20 then 20 else 0

/-- The derivative of `ρτ` off its six corners. -/
def rhoTD (θ : ℝ) : ℝ := rhoD θ * tau θ + rho θ * tauD θ

/-- The corners of `ρ`. -/
def cornersRho : Set ℝ := {12 / 25, 1 / 2, 1, 11 / 10}

/-- The corners of `ρτ`. -/
def cornersRhoT : Set ℝ := {12 / 25, 1 / 2, 1, 11 / 10, 3 / 5, 13 / 20}

/-- `ρ′ = ρ_D` off the corners of `ρ`. -/
theorem hasDerivAt_rho {θ : ℝ} (hθ : θ ∉ cornersRho) : HasDerivAt rho (rhoD θ) θ := by
  simp only [cornersRho, mem_insert_iff, mem_singleton_iff, not_or] at hθ
  obtain ⟨h1, h2, h3, h4⟩ := hθ
  rcases lt_or_gt_of_ne h1 with h1 | h1
  · -- below 12/25
    have : rho =ᶠ[𝓝 θ] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds h1] with t ht using rho_eq_zero_of_le (le_of_lt ht)
    rw [show rhoD θ = 0 by simp [rhoD, h1]]
    exact (hasDerivAt_const θ (0 : ℝ)).congr_of_eventuallyEq this
  rcases lt_or_gt_of_ne h2 with h2 | h2
  · have : rho =ᶠ[𝓝 θ] fun t => (t - 12 / 25) * 50 := by
      filter_upwards [Ioo_mem_nhds h1 h2] with t ht
      unfold rho
      rw [min_eq_left (by linarith [ht.2] : (t - 12 / 25) * 50 ≤ (11 / 10 - t) * 10),
        min_eq_right (by linarith [ht.2] : (t - 12 / 25) * 50 ≤ 1), max_eq_right (by linarith [ht.1])]
    rw [show rhoD θ = 50 by rw [rhoD, if_neg (not_lt.mpr h1.le), if_pos h2]]
    exact ((hasDerivAt_id θ).sub_const _ |>.mul_const 50 |>.congr_deriv (by ring)).congr_of_eventuallyEq this
  rcases lt_or_gt_of_ne h3 with h3 | h3
  · have : rho =ᶠ[𝓝 θ] fun _ => 1 := by
      filter_upwards [Ioo_mem_nhds h2 h3] with t ht using rho_eq_one ht.1.le ht.2.le
    rw [show rhoD θ = 0 by rw [rhoD, if_neg (not_lt.mpr h1.le), if_neg (not_lt.mpr h2.le), if_pos h3]]
    exact (hasDerivAt_const θ (1 : ℝ)).congr_of_eventuallyEq this
  rcases lt_or_gt_of_ne h4 with h4 | h4
  · have : rho =ᶠ[𝓝 θ] fun t => (11 / 10 - t) * 10 := by
      filter_upwards [Ioo_mem_nhds h3 h4] with t ht
      unfold rho
      rw [min_eq_right (by linarith [ht.1] : (11 / 10 - t) * 10 ≤ (t - 12 / 25) * 50),
        min_eq_right (by linarith [ht.1] : (11 / 10 - t) * 10 ≤ 1), max_eq_right (by linarith [ht.2])]
    rw [show rhoD θ = -10 by
      rw [rhoD, if_neg (not_lt.mpr h1.le), if_neg (not_lt.mpr h2.le), if_neg (not_lt.mpr h3.le), if_pos h4]]
    exact ((hasDerivAt_const θ (11 / 10 : ℝ)).sub (hasDerivAt_id θ) |>.mul_const 10 |>.congr_deriv (by ring))
      |>.congr_of_eventuallyEq this
  · have : rho =ᶠ[𝓝 θ] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds h4] with t ht using rho_eq_zero_of_ge (le_of_lt ht)
    rw [show rhoD θ = 0 by
      rw [rhoD, if_neg (not_lt.mpr h1.le), if_neg (not_lt.mpr h2.le), if_neg (not_lt.mpr h3.le),
        if_neg (not_lt.mpr h4.le)]]
    exact (hasDerivAt_const θ (0 : ℝ)).congr_of_eventuallyEq this

/-- `τ′ = τ_D` off `3/5` and `13/20`. -/
theorem hasDerivAt_tau {θ : ℝ} (h1 : θ ≠ 3 / 5) (h2 : θ ≠ 13 / 20) : HasDerivAt tau (tauD θ) θ := by
  rcases lt_or_gt_of_ne h1 with h1 | h1
  · have : tau =ᶠ[𝓝 θ] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds h1] with t ht
      unfold tau
      exact max_eq_left ((min_le_right _ _).trans (by linarith [mem_Iio.mp ht]))
    rw [show tauD θ = 0 by simp [tauD, h1]]
    exact (hasDerivAt_const θ (0 : ℝ)).congr_of_eventuallyEq this
  rcases lt_or_gt_of_ne h2 with h2 | h2
  · have : tau =ᶠ[𝓝 θ] fun t => (t - 3 / 5) * 20 := by
      filter_upwards [Ioo_mem_nhds h1 h2] with t ht
      unfold tau
      rw [min_eq_right (by linarith [ht.2] : (t - 3 / 5) * 20 ≤ 1), max_eq_right (by linarith [ht.1])]
    rw [show tauD θ = 20 by simp [tauD, not_lt.mpr h1.le, h2]]
    exact ((hasDerivAt_id θ).sub_const _ |>.mul_const 20 |>.congr_deriv (by ring)).congr_of_eventuallyEq this
  · have : tau =ᶠ[𝓝 θ] fun _ => 1 := by
      filter_upwards [Ioi_mem_nhds h2] with t ht
      unfold tau
      rw [min_eq_left (by linarith [mem_Ioi.mp ht] : (1 : ℝ) ≤ (t - 3 / 5) * 20), max_eq_right zero_le_one]
    rw [show tauD θ = 0 by simp [tauD, not_lt.mpr h1.le, not_lt.mpr h2.le]]
    exact (hasDerivAt_const θ (1 : ℝ)).congr_of_eventuallyEq this

/-- `(ρτ)′ = ρ_Dτ + ρτ_D` off the corners of `ρτ`. -/
theorem hasDerivAt_rhoT {θ : ℝ} (hθ : θ ∉ cornersRhoT) : HasDerivAt rhoT (rhoTD θ) θ := by
  simp only [cornersRhoT, mem_insert_iff, mem_singleton_iff, not_or] at hθ
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hθ
  have hr : θ ∉ cornersRho := by
    simp only [cornersRho, mem_insert_iff, mem_singleton_iff, not_or]; exact ⟨h1, h2, h3, h4⟩
  exact (hasDerivAt_rho hr).mul (hasDerivAt_tau h5 h6)

/-- `|ρ_D| ≤ 50`. -/
theorem abs_rhoD_le (θ : ℝ) : |rhoD θ| ≤ 50 := by
  unfold rhoD; split_ifs <;> norm_num

/-- `0 ≤ τ ≤ 1`. -/
theorem tau_mem (θ : ℝ) : 0 ≤ tau θ ∧ tau θ ≤ 1 := by
  unfold tau; exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

/-- `|τ_D| ≤ 20`. -/
theorem abs_tauD_le (θ : ℝ) : |tauD θ| ≤ 20 := by
  unfold tauD; split_ifs <;> norm_num

/-- `|(ρτ)_D| ≤ 70`. -/
theorem abs_rhoTD_le (θ : ℝ) : |rhoTD θ| ≤ 70 := by
  unfold rhoTD
  have h1 := abs_rhoD_le θ
  have h2 := abs_tauD_le θ
  have h3 := tau_mem θ
  have h4 := rho_nonneg θ
  have h5 := rho_le_one θ
  calc |rhoD θ * tau θ + rho θ * tauD θ| ≤ |rhoD θ| * |tau θ| + |rho θ| * |tauD θ| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ 50 * 1 + 1 * 20 := by
        rw [abs_of_nonneg h3.1, abs_of_nonneg h4]
        exact add_le_add (mul_le_mul h1 h3.2 h3.1 (by norm_num)) (mul_le_mul h5 h2 (abs_nonneg _) zero_le_one)
    _ = 70 := by norm_num

/-- `ρ_D` is measurable. -/
theorem measurable_rhoD : Measurable rhoD := by
  unfold rhoD
  refine Measurable.ite measurableSet_Iio measurable_const ?_
  refine Measurable.ite measurableSet_Iio measurable_const ?_
  refine Measurable.ite measurableSet_Iio measurable_const ?_
  exact Measurable.ite measurableSet_Iio measurable_const measurable_const

/-- `τ_D` is measurable. -/
theorem measurable_tauD : Measurable tauD := by
  unfold tauD
  refine Measurable.ite measurableSet_Iio measurable_const ?_
  exact Measurable.ite measurableSet_Iio measurable_const measurable_const

/-- `(ρτ)_D` is measurable. -/
theorem measurable_rhoTD : Measurable rhoTD :=
  (measurable_rhoD.mul continuous_tau.measurable).add (continuous_rho.measurable.mul measurable_tauD)

/-- `ρτ = 0` on `θ ≤ 3/5`. -/
theorem rhoT_eq_zero {θ : ℝ} (h : θ ≤ 3 / 5) : rhoT θ = 0 := by
  unfold rhoT tau
  rw [max_eq_left ((min_le_right _ _).trans (by linarith)), mul_zero]

end Cvs.Route.Visibility.AliasPairThetaKernel
