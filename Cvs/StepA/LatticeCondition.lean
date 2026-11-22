import Mathlib
import Cvs.Finite.OddDivisionPolynomial
import Cvs.Finite.OddEigenvectorResolvent
import Cvs.Finite.SymmetricModeSet
import Cvs.StepA.OrderedOrdinates

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The product envelope and the explicit lattice condition `LAT`

For roots `r_i ≥ γ_i² > 0`: `∏(1 − s/r_i)² ≤ Φ(s) = ∏ max(1, s/γ_i²)²`, and `≥ Ψ(s) = ∏(1 − s/γ_i²)²`
for `s ≤ γ_i²`. `LAT L N` is `Λ_Y² < γ_1²` and `Λ_h² < 6.24²` for these envelopes with weights `e_K²`;
under it every polynomial with dominated roots has `Ω_Y < γ_1` and `Ω_h < 6.24`.
-/

noncomputable section

open Matrix Real Polynomial

namespace Cvs.Finite.OddDisplacementPencil
open Cvs.ZeroCounting
open Cvs.Finite.SymmetricModeSet (Idx mode negI)
open Cvs.Finite.OddEigenvectorResolvent (xdiv om)

variable {L : ℝ} {N : ℕ}

/-! ### The envelopes -/

/-- The upper envelope `Φ_M(s) = ∏_{i<M} max(1, s/γ_i²)²`. -/
def phiEnv (γ : ℕ → ℝ) (M : ℕ) (s : ℝ) : ℝ := ∏ i ∈ Finset.range M, max 1 (s / γ i ^ 2) ^ 2

/-- The lower envelope `Ψ_M(s) = ∏_{i<M} (1 − s/γ_i²)²`. -/
def psiEnv (γ : ℕ → ℝ) (M : ℕ) (s : ℝ) : ℝ := ∏ i ∈ Finset.range M, (1 - s / γ i ^ 2) ^ 2

-- H_fix Step 4 (`X_C² ≤ Φ e²`)
/-- **The upper product envelope**: for `n ≤ M`, `γ_i ≠ 0` and `γ_i² ≤ r_i` (`i < n`), and `s ≥ 0`,
`∏_{i<n}(1 − s/r_i)² ≤ ∏_{i<M} max(1, s/γ_i²)²`. -/
theorem prod_sq_le_phiEnv {γ r : ℕ → ℝ} {n M : ℕ} (hn : n ≤ M) (hγ : ∀ i < n, γ i ≠ 0)
    (hr : ∀ i < n, γ i ^ 2 ≤ r i) {s : ℝ} (hs : 0 ≤ s) :
    ∏ i ∈ Finset.range n, (1 - s / r i) ^ 2 ≤ phiEnv γ M s := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  unfold phiEnv
  rw [Finset.prod_range_add]
  have hrest : 1 ≤ ∏ i ∈ Finset.range m, max 1 (s / γ (n + i) ^ 2) ^ 2 :=
    Finset.one_le_prod₀ fun i _ => one_le_pow₀ (le_max_left _ _)
  have hhead : ∏ i ∈ Finset.range n, (1 - s / r i) ^ 2
      ≤ ∏ i ∈ Finset.range n, max 1 (s / γ i ^ 2) ^ 2 := by
    refine Finset.prod_le_prod₀ (fun i _ => sq_nonneg _) fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    have hγ2 : 0 < γ i ^ 2 := by have := hγ i hi'; positivity
    have hrp : 0 < r i := lt_of_lt_of_le hγ2 (hr i hi')
    have hsr : 0 ≤ s / r i := div_nonneg hs hrp.le
    have hle : s / r i ≤ s / γ i ^ 2 := div_le_div_of_nonneg_left hs hγ2 (hr i hi')
    have habs : |1 - s / r i| ≤ max 1 (s / γ i ^ 2) := by
      have h1 := le_max_left 1 (s / γ i ^ 2)
      have h2 := le_max_right 1 (s / γ i ^ 2)
      rw [abs_le]
      constructor <;> linarith
    calc (1 - s / r i) ^ 2 = |1 - s / r i| ^ 2 := (sq_abs _).symm
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) habs 2
  exact hhead.trans (le_mul_of_one_le_right (Finset.prod_nonneg fun i _ => sq_nonneg _) hrest)

-- H_fix Step 4 (`X_C² ≥ Ψ e²` below `γ_1`)
/-- **The lower product envelope**: for `n ≤ M`, `0 ≤ s ≤ γ_i²` (`i < M`) and `γ_i² ≤ r_i`
(`i < n`), `∏_{i<M}(1 − s/γ_i²)² ≤ ∏_{i<n}(1 − s/r_i)²`. -/
theorem psiEnv_le_prod_sq {γ r : ℕ → ℝ} {n M : ℕ} (hn : n ≤ M) (hr : ∀ i < n, γ i ^ 2 ≤ r i)
    {s : ℝ} (hs0 : 0 ≤ s) (hs : ∀ i < M, s ≤ γ i ^ 2) :
    psiEnv γ M s ≤ ∏ i ∈ Finset.range n, (1 - s / r i) ^ 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hfac : ∀ i < n + m, 0 ≤ 1 - s / γ i ^ 2 ∧ 1 - s / γ i ^ 2 ≤ 1 := fun i hi =>
    ⟨sub_nonneg.mpr (div_le_one_of_le₀ (hs i hi) (sq_nonneg _)),
      sub_le_self _ (div_nonneg hs0 (sq_nonneg _))⟩
  unfold psiEnv
  rw [Finset.prod_range_add]
  have hrest : ∏ i ∈ Finset.range m, (1 - s / γ (n + i) ^ 2) ^ 2 ≤ 1 := by
    refine Finset.prod_le_one₀ (fun i _ => sq_nonneg _) fun i hi => ?_
    have h := hfac (n + i) (by have := Finset.mem_range.mp hi; omega)
    exact pow_le_one₀ h.1 h.2
  have hhead : ∏ i ∈ Finset.range n, (1 - s / γ i ^ 2) ^ 2
      ≤ ∏ i ∈ Finset.range n, (1 - s / r i) ^ 2 := by
    refine Finset.prod_le_prod₀ (fun i _ => sq_nonneg _) fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    have h := hfac i (by omega)
    refine pow_le_pow_left₀ h.1 ?_ 2
    rcases (sq_nonneg (γ i)).eq_or_lt with h0 | h0
    · have hs00 : s = 0 := le_antisymm (h0 ▸ hs i (by omega)) hs0
      simp [hs00]
    · linarith [div_le_div_of_nonneg_left hs0 h0 (hr i hi')]
  calc _ ≤ ∏ i ∈ Finset.range n, (1 - s / γ i ^ 2) ^ 2 :=
        mul_le_of_le_one_right (Finset.prod_nonneg fun i _ => sq_nonneg _) hrest
    _ ≤ _ := hhead

/-! ### `LAT` -/

/-- The numerator of `Λ_Y²`: `∑_{K=1}^N ν_K⁴ Φ(ν_K²) e_K²`. -/
def lamYNum (L : ℝ) (N : ℕ) : ℝ :=
  ∑ k : Fin N, nu L ((k : ℕ) + 1) ^ 4 * phiEnv ordSeq (N - 1) (nu L ((k : ℕ) + 1) ^ 2)
    * eCoef N ((k : ℕ) + 1) ^ 2

/-- The denominator of `Λ_Y²`: `∑_{ν_K < γ_1} ν_K² Ψ(ν_K²) e_K²`. -/
def lamYDen (L : ℝ) (N : ℕ) : ℝ :=
  ∑ k : Fin N, if nu L ((k : ℕ) + 1) < ordSeq 0 then
    nu L ((k : ℕ) + 1) ^ 2 * psiEnv ordSeq (N - 1) (nu L ((k : ℕ) + 1) ^ 2) * eCoef N ((k : ℕ) + 1) ^ 2
    else 0

/-- The numerator of `Λ_h²`: `2∑_{K=1}^N ν_K² Φ(ν_K²) e_K²`. -/
def lamHNum (L : ℝ) (N : ℕ) : ℝ :=
  2 * ∑ k : Fin N, nu L ((k : ℕ) + 1) ^ 2 * phiEnv ordSeq (N - 1) (nu L ((k : ℕ) + 1) ^ 2)
    * eCoef N ((k : ℕ) + 1) ^ 2

/-- The denominator of `Λ_h²`: `1 + 2∑_{ν_K < γ_1} Ψ(ν_K²) e_K²`. -/
def lamHDen (L : ℝ) (N : ℕ) : ℝ :=
  1 + 2 * ∑ k : Fin N, if nu L ((k : ℕ) + 1) < ordSeq 0 then
    psiEnv ordSeq (N - 1) (nu L ((k : ℕ) + 1) ^ 2) * eCoef N ((k : ℕ) + 1) ^ 2 else 0

/-- **The lattice condition `LAT(L, N)`**: `Λ_Y² < γ_1²` and `Λ_h² < 6.24²`, cleared of
denominators. -/
def LAT (L : ℝ) (N : ℕ) : Prop :=
  lamYNum L N < ordSeq 0 ^ 2 * lamYDen L N ∧ lamHNum L N < (6.24 : ℝ) ^ 2 * lamHDen L N

/-- `p` is a nonzero multiple of `∏_{i<n}(X − r_i)` with `n ≤ N − 1` and `r_i ≥ γ_i²`. -/
def Dominated (N : ℕ) (p : ℝ[X]) : Prop :=
  ∃ (c : ℝ) (n : ℕ) (r : ℕ → ℝ), c ≠ 0 ∧ n ≤ N - 1 ∧ (∀ i < n, ordSeq i ^ 2 ≤ r i) ∧
    p = C c * ∏ i ∈ Finset.range n, (X - C (r i))

/-! ### `Ω_Y` and `Ω_h` of a dominated polynomial -/

/-- With nonzero roots, `p(s) = p(0)·∏(1 − s/r_i)`. -/
theorem eval_sq_eq_eval_zero_sq_mul (c : ℝ) {n : ℕ} {r : ℕ → ℝ} (hr : ∀ i < n, r i ≠ 0) (s : ℝ) :
    (C c * ∏ i ∈ Finset.range n, (X - C (r i))).eval s ^ 2
      = (C c * ∏ i ∈ Finset.range n, (X - C (r i))).eval 0 ^ 2
        * ∏ i ∈ Finset.range n, (1 - s / r i) ^ 2 := by
  simp only [eval_mul, eval_C, eval_prod, eval_sub, eval_X, mul_pow, ← Finset.prod_pow]
  rw [mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  have h := hr i (Finset.mem_range.mp hi)
  rw [← mul_pow]
  congr 1
  field_simp
  ring

theorem eval_zero_ne_zero_of_dominated {c : ℝ} {n : ℕ} {r : ℕ → ℝ} (hc : c ≠ 0)
    (hr : ∀ i < n, r i ≠ 0) : (C c * ∏ i ∈ Finset.range n, (X - C (r i))).eval 0 ≠ 0 := by
  simp only [eval_mul, eval_C, eval_prod, eval_sub, eval_X, zero_sub]
  refine mul_ne_zero hc (Finset.prod_ne_zero_iff.mpr fun i hi => neg_ne_zero.mpr ?_)
  exact hr i (Finset.mem_range.mp hi)

/-- The two pointwise envelope bounds on the lattice, for a dominated polynomial. -/
theorem lattice_envelope (hL : 0 < L) {c : ℝ} {n : ℕ} {r : ℕ → ℝ} (hn : n ≤ N - 1)
    (hr : ∀ i < n, ordSeq i ^ 2 ≤ r i) (k : Fin N) :
    (C c * ∏ i ∈ Finset.range n, (X - C (r i))).eval (nu L ((k : ℕ) + 1) ^ 2) ^ 2
        ≤ (C c * ∏ i ∈ Finset.range n, (X - C (r i))).eval 0 ^ 2
          * phiEnv ordSeq (N - 1) (nu L ((k : ℕ) + 1) ^ 2)
      ∧ (nu L ((k : ℕ) + 1) < ordSeq 0 →
        (C c * ∏ i ∈ Finset.range n, (X - C (r i))).eval 0 ^ 2
            * psiEnv ordSeq (N - 1) (nu L ((k : ℕ) + 1) ^ 2)
          ≤ (C c * ∏ i ∈ Finset.range n, (X - C (r i))).eval (nu L ((k : ℕ) + 1) ^ 2) ^ 2) := by
  have hγ : ∀ i, ordSeq i ≠ 0 := fun i => (ordSeq_pos i).ne'
  have hr0 : ∀ i < n, r i ≠ 0 := fun i hi =>
    (lt_of_lt_of_le (pow_pos (ordSeq_pos i) 2) (hr i hi)).ne'
  have hnu : 0 ≤ nu L ((k : ℕ) + 1) := by unfold nu; positivity
  rw [eval_sq_eq_eval_zero_sq_mul c hr0]
  refine ⟨mul_le_mul_of_nonneg_left (prod_sq_le_phiEnv hn (fun i _ => hγ i) hr (sq_nonneg _))
    (sq_nonneg _), fun hlt => mul_le_mul_of_nonneg_left
      (psiEnv_le_prod_sq hn hr (sq_nonneg _) fun i _ => ?_) (sq_nonneg _)⟩
  calc nu L ((k : ℕ) + 1) ^ 2 ≤ ordSeq 0 ^ 2 := pow_le_pow_left₀ hnu hlt.le 2
    _ ≤ ordSeq i ^ 2 := ordSeq_sq_mono (Nat.zero_le i)

/-- **`Ω_Y < γ_1` for a dominated polynomial under `LAT`**: `(W²v)·v < γ_1² |v|²`, `v = vecOf p`. -/
theorem W2_dot_lt_of_LAT (hL : 0 < L) (hLAT : LAT L N) {p : ℝ[X]} (hp : Dominated N p) :
    (fun i => om L N i ^ 2 * vecOf L N p i) ⬝ᵥ vecOf L N p
      < ordSeq 0 ^ 2 * (vecOf L N p ⬝ᵥ vecOf L N p) := by
  obtain ⟨c, n, r, hc, hn, hr, rfl⟩ := hp
  have hr0 : ∀ i < n, r i ≠ 0 := fun i hi =>
    (lt_of_lt_of_le (pow_pos (ordSeq_pos i) 2) (hr i hi)).ne'
  set p := C c * ∏ i ∈ Finset.range n, (X - C (r i)) with hpdef
  have hP0 : 0 < p.eval 0 ^ 2 := lt_of_le_of_ne (sq_nonneg _)
    (Ne.symm (pow_ne_zero 2 (eval_zero_ne_zero_of_dominated hc hr0)))
  rw [dot_W2_vecOf, dot_vecOf_self]
  have h1 : ∑ k : Fin N, nu L ((k : ℕ) + 1) ^ 4 * p.eval (nu L ((k : ℕ) + 1) ^ 2) ^ 2
      * eCoef N ((k : ℕ) + 1) ^ 2 ≤ p.eval 0 ^ 2 * lamYNum L N := by
    rw [lamYNum, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have h := (lattice_envelope (N := N) (c := c) hL hn hr k).1
    have h4 : 0 ≤ nu L ((k : ℕ) + 1) ^ 4 * eCoef N ((k : ℕ) + 1) ^ 2 := by positivity
    calc nu L ((k : ℕ) + 1) ^ 4 * p.eval (nu L ((k : ℕ) + 1) ^ 2) ^ 2 * eCoef N ((k : ℕ) + 1) ^ 2
        = (nu L ((k : ℕ) + 1) ^ 4 * eCoef N ((k : ℕ) + 1) ^ 2)
          * p.eval (nu L ((k : ℕ) + 1) ^ 2) ^ 2 := by ring
      _ ≤ (nu L ((k : ℕ) + 1) ^ 4 * eCoef N ((k : ℕ) + 1) ^ 2)
          * (p.eval 0 ^ 2 * phiEnv ordSeq (N - 1) (nu L ((k : ℕ) + 1) ^ 2)) :=
        mul_le_mul_of_nonneg_left h h4
      _ = _ := by ring
  have h2 : p.eval 0 ^ 2 * lamYDen L N ≤ ∑ k : Fin N, nu L ((k : ℕ) + 1) ^ 2
      * p.eval (nu L ((k : ℕ) + 1) ^ 2) ^ 2 * eCoef N ((k : ℕ) + 1) ^ 2 := by
    rw [lamYDen, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    split_ifs with hk
    · have h := (lattice_envelope (N := N) (c := c) hL hn hr k).2 hk
      have h4 : 0 ≤ nu L ((k : ℕ) + 1) ^ 2 * eCoef N ((k : ℕ) + 1) ^ 2 := by positivity
      calc p.eval 0 ^ 2 * (nu L ((k : ℕ) + 1) ^ 2 * psiEnv ordSeq (N - 1) (nu L ((k : ℕ) + 1) ^ 2)
            * eCoef N ((k : ℕ) + 1) ^ 2)
          = (nu L ((k : ℕ) + 1) ^ 2 * eCoef N ((k : ℕ) + 1) ^ 2)
            * (p.eval 0 ^ 2 * psiEnv ordSeq (N - 1) (nu L ((k : ℕ) + 1) ^ 2)) := by ring
        _ ≤ (nu L ((k : ℕ) + 1) ^ 2 * eCoef N ((k : ℕ) + 1) ^ 2)
            * p.eval (nu L ((k : ℕ) + 1) ^ 2) ^ 2 := mul_le_mul_of_nonneg_left h h4
        _ = _ := by ring
    · rw [mul_zero]; positivity
  have hg : 0 ≤ ordSeq 0 ^ 2 := sq_nonneg _
  calc 2 * ∑ k : Fin N, nu L ((k : ℕ) + 1) ^ 4 * p.eval (nu L ((k : ℕ) + 1) ^ 2) ^ 2
        * eCoef N ((k : ℕ) + 1) ^ 2 ≤ 2 * (p.eval 0 ^ 2 * lamYNum L N) := by linarith
    _ < 2 * (p.eval 0 ^ 2 * (ordSeq 0 ^ 2 * lamYDen L N)) := by
      have := mul_lt_mul_of_pos_left hLAT.1 hP0; linarith
    _ = ordSeq 0 ^ 2 * (2 * (p.eval 0 ^ 2 * lamYDen L N)) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hg
      linarith

/-- **`Ω_h < 6.24` for a dominated polynomial under `LAT`**: `|v|² < 6.24² |xOf p|²`,
`v = vecOf p`. -/
theorem dot_lt_of_LAT (hL : 0 < L) (hLAT : LAT L N) {p : ℝ[X]} (hp : Dominated N p) :
    vecOf L N p ⬝ᵥ vecOf L N p < (6.24 : ℝ) ^ 2 * (xOf L N p ⬝ᵥ xOf L N p) := by
  obtain ⟨c, n, r, hc, hn, hr, rfl⟩ := hp
  have hr0 : ∀ i < n, r i ≠ 0 := fun i hi =>
    (lt_of_lt_of_le (pow_pos (ordSeq_pos i) 2) (hr i hi)).ne'
  set p := C c * ∏ i ∈ Finset.range n, (X - C (r i)) with hpdef
  have hP0 : 0 < p.eval 0 ^ 2 := lt_of_le_of_ne (sq_nonneg _)
    (Ne.symm (pow_ne_zero 2 (eval_zero_ne_zero_of_dominated hc hr0)))
  rw [dot_vecOf_self, dot_xOf_self]
  have h1' : ∑ k : Fin N, nu L ((k : ℕ) + 1) ^ 2 * p.eval (nu L ((k : ℕ) + 1) ^ 2) ^ 2
      * eCoef N ((k : ℕ) + 1) ^ 2 ≤ p.eval 0 ^ 2 * ∑ k : Fin N, nu L ((k : ℕ) + 1) ^ 2
        * phiEnv ordSeq (N - 1) (nu L ((k : ℕ) + 1) ^ 2) * eCoef N ((k : ℕ) + 1) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have h := (lattice_envelope (N := N) (c := c) hL hn hr k).1
    have h4 : 0 ≤ nu L ((k : ℕ) + 1) ^ 2 * eCoef N ((k : ℕ) + 1) ^ 2 := by positivity
    calc nu L ((k : ℕ) + 1) ^ 2 * p.eval (nu L ((k : ℕ) + 1) ^ 2) ^ 2 * eCoef N ((k : ℕ) + 1) ^ 2
        = (nu L ((k : ℕ) + 1) ^ 2 * eCoef N ((k : ℕ) + 1) ^ 2)
          * p.eval (nu L ((k : ℕ) + 1) ^ 2) ^ 2 := by ring
      _ ≤ (nu L ((k : ℕ) + 1) ^ 2 * eCoef N ((k : ℕ) + 1) ^ 2)
          * (p.eval 0 ^ 2 * phiEnv ordSeq (N - 1) (nu L ((k : ℕ) + 1) ^ 2)) :=
        mul_le_mul_of_nonneg_left h h4
      _ = _ := by ring
  have h1 : 2 * ∑ k : Fin N, nu L ((k : ℕ) + 1) ^ 2 * p.eval (nu L ((k : ℕ) + 1) ^ 2) ^ 2
      * eCoef N ((k : ℕ) + 1) ^ 2 ≤ p.eval 0 ^ 2 * lamHNum L N := by
    rw [lamHNum]; linarith
  have h2' : p.eval 0 ^ 2 * ∑ k : Fin N, (if nu L ((k : ℕ) + 1) < ordSeq 0 then
      psiEnv ordSeq (N - 1) (nu L ((k : ℕ) + 1) ^ 2) * eCoef N ((k : ℕ) + 1) ^ 2 else 0)
      ≤ ∑ k : Fin N, p.eval (nu L ((k : ℕ) + 1) ^ 2) ^ 2 * eCoef N ((k : ℕ) + 1) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    split_ifs with hk
    · have h := (lattice_envelope (N := N) (c := c) hL hn hr k).2 hk
      have h4 : 0 ≤ eCoef N ((k : ℕ) + 1) ^ 2 := by positivity
      calc p.eval 0 ^ 2 * (psiEnv ordSeq (N - 1) (nu L ((k : ℕ) + 1) ^ 2)
            * eCoef N ((k : ℕ) + 1) ^ 2)
          = eCoef N ((k : ℕ) + 1) ^ 2
            * (p.eval 0 ^ 2 * psiEnv ordSeq (N - 1) (nu L ((k : ℕ) + 1) ^ 2)) := by ring
        _ ≤ eCoef N ((k : ℕ) + 1) ^ 2 * p.eval (nu L ((k : ℕ) + 1) ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_left h h4
        _ = _ := by ring
    · rw [mul_zero]; positivity
  have h2 : p.eval 0 ^ 2 * lamHDen L N ≤ p.eval 0 ^ 2 + 2 * ∑ k : Fin N,
      p.eval (nu L ((k : ℕ) + 1) ^ 2) ^ 2 * eCoef N ((k : ℕ) + 1) ^ 2 := by
    rw [lamHDen, mul_add, mul_one]; linarith
  calc 2 * ∑ k : Fin N, nu L ((k : ℕ) + 1) ^ 2 * p.eval (nu L ((k : ℕ) + 1) ^ 2) ^ 2
        * eCoef N ((k : ℕ) + 1) ^ 2 ≤ p.eval 0 ^ 2 * lamHNum L N := h1
    _ < p.eval 0 ^ 2 * ((6.24 : ℝ) ^ 2 * lamHDen L N) := mul_lt_mul_of_pos_left hLAT.2 hP0
    _ = (6.24 : ℝ) ^ 2 * (p.eval 0 ^ 2 * lamHDen L N) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by norm_num)

end Cvs.Finite.OddDisplacementPencil
