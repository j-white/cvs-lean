import Mathlib
import Cvs.Finite.OddDivisionPolynomial
import Cvs.StepA.LatticeCondition
import Cvs.StepA.OrderedOrdinates

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `LAT` holds eventually along a fixed bandwidth

The binomial weights are Gaussian of width `√N`, `Φ` is bounded on a fixed band, and
`Ψ(s) ≥ (1 − s∑1/γ_i²)²`; at `N = ⌈ΩL/2π⌉` this gives `Λ_h², Λ_Y² = O(Ω/L)`, so
`LAT(L, ⌈ΩL/2π⌉)` holds for all large `L`.
-/

noncomputable section

open Real Filter Topology

namespace Cvs.Finite.OddDisplacementPencil
open Cvs.ZeroCounting
/-- The fixed-bandwidth mode count `⌈ΩL/2π⌉₊`. -/
abbrev band (Ω : ℝ) : ℝ → ℕ := fun L => ⌈Ω * L / (2 * π)⌉₊

/-! ### The binomial weights -/

/-- `e_0 = 1`. -/
private lemma eCoef_zero (N : ℕ) : eCoef N 0 = 1 := by
  unfold eCoef
  rw [add_zero]
  exact div_self (by exact_mod_cast (Nat.choose_pos (by omega : N ≤ 2 * N)).ne')

/-- `0 ≤ e_K`. -/
private lemma eCoef_nonneg (N K : ℕ) : 0 ≤ eCoef N K := by unfold eCoef; positivity

/-- `e_K ≤ 1`: the middle binomial coefficient is the largest. -/
private lemma eCoef_le_one (N K : ℕ) : eCoef N K ≤ 1 := by
  unfold eCoef
  have hpos : (0 : ℝ) < Nat.choose (2 * N) N := by
    exact_mod_cast Nat.choose_pos (by omega : N ≤ 2 * N)
  rw [div_le_one hpos]
  have h := Nat.choose_le_middle (N + K) (2 * N)
  rw [show 2 * N / 2 = N by omega] at h
  exact_mod_cast h

/-- The ratio recurrence of the binomial weights: `e_{K+1}(N+K+1) = e_K(N−K)`. -/
private lemma eCoef_succ_mul (N K : ℕ) :
    eCoef N (K + 1) * ((N : ℝ) + K + 1) = eCoef N K * ((N - K : ℕ) : ℝ) := by
  unfold eCoef
  have h := Nat.choose_succ_right_eq (2 * N) (N + K)
  rw [show 2 * N - (N + K) = N - K by omega] at h
  have h' : (Nat.choose (2 * N) (N + K + 1) : ℝ) * ((N : ℝ) + K + 1)
      = (Nat.choose (2 * N) (N + K) : ℝ) * ((N - K : ℕ) : ℝ) := by
    exact_mod_cast h
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_assoc, h']

/-- For `K < N`: `e_{K+1} = e_K (1 − (2K+1)/(N+K+1))`. -/
private lemma eCoef_succ {N K : ℕ} (hK : K < N) :
    eCoef N (K + 1) = eCoef N K * (1 - (2 * (K : ℝ) + 1) / ((N : ℝ) + K + 1)) := by
  have h := eCoef_succ_mul N K
  rw [Nat.cast_sub hK.le] at h
  have hne : (N : ℝ) + K + 1 ≠ 0 := by positivity
  have e1 : 1 - (2 * (K : ℝ) + 1) / ((N : ℝ) + K + 1) = ((N : ℝ) - K) / ((N : ℝ) + K + 1) := by
    field_simp; ring
  rw [e1, mul_div_assoc', eq_div_iff hne, h]

/-- **Gaussian bound with denominator `N + K`**: `e_K ≤ exp(−K²/(N+K))` for `K ≤ N`. -/
private lemma eCoef_le_exp_aux (N : ℕ) : ∀ K : ℕ, K ≤ N →
    eCoef N K ≤ Real.exp (-((K : ℝ) ^ 2) / ((N : ℝ) + K)) := by
  intro K
  induction K with
  | zero => intro _; simp [eCoef_zero]
  | succ K ih =>
    intro hK
    have hKN : K < N := by omega
    have ih := ih hKN.le
    have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hNK : (0 : ℝ) < (N : ℝ) + K := by positivity
    have hNK1 : (0 : ℝ) < (N : ℝ) + K + 1 := by positivity
    have hr0 : 0 ≤ 1 - (2 * (K : ℝ) + 1) / ((N : ℝ) + K + 1) := by
      rw [sub_nonneg, div_le_one hNK1]
      have : (K : ℝ) + 1 ≤ N := by exact_mod_cast hK
      linarith
    have hr : 1 - (2 * (K : ℝ) + 1) / ((N : ℝ) + K + 1)
        ≤ Real.exp (-((2 * (K : ℝ) + 1) / ((N : ℝ) + K + 1))) := by
      have := Real.add_one_le_exp (-((2 * (K : ℝ) + 1) / ((N : ℝ) + K + 1)))
      linarith
    have h1 : (K : ℝ) ^ 2 / ((N : ℝ) + K + 1) ≤ (K : ℝ) ^ 2 / ((N : ℝ) + K) :=
      div_le_div_of_nonneg_left (sq_nonneg _) hNK (by linarith)
    have h2 : ((K : ℝ) + 1) ^ 2 / ((N : ℝ) + (K + 1))
        = (K : ℝ) ^ 2 / ((N : ℝ) + K + 1) + (2 * K + 1) / ((N : ℝ) + K + 1) := by
      rw [← add_assoc, ← add_div]; ring_nf
    rw [eCoef_succ hKN]
    calc eCoef N K * (1 - (2 * (K : ℝ) + 1) / ((N : ℝ) + K + 1))
        ≤ Real.exp (-((K : ℝ) ^ 2) / ((N : ℝ) + K))
          * Real.exp (-((2 * (K : ℝ) + 1) / ((N : ℝ) + K + 1))) :=
          mul_le_mul ih hr hr0 (Real.exp_pos _).le
      _ = Real.exp (-((K : ℝ) ^ 2 / ((N : ℝ) + K) + (2 * (K : ℝ) + 1) / ((N : ℝ) + K + 1))) := by
          rw [← Real.exp_add, neg_div, neg_add]
      _ ≤ Real.exp (-(((K + 1 : ℕ) : ℝ) ^ 2) / ((N : ℝ) + ((K + 1 : ℕ) : ℝ))) := by
          apply Real.exp_le_exp.mpr
          push_cast
          rw [neg_div, neg_le_neg_iff, h2]
          linarith

-- H_fix Step 6 (`e_k ≤ exp(−k²/2N)`)
/-- **Gaussian upper bound of the binomial weight**: `e_K ≤ exp(−K²/2N)`. -/
theorem eCoef_le_exp (N K : ℕ) : eCoef N K ≤ Real.exp (-((K : ℝ) ^ 2) / (2 * N)) := by
  rcases le_or_gt K N with hK | hK
  · refine (eCoef_le_exp_aux N K hK).trans (Real.exp_le_exp.mpr ?_)
    rcases Nat.eq_zero_or_pos K with rfl | hK0
    · simp
    · have hK0' : (0 : ℝ) < K := by exact_mod_cast hK0
      have hNK : (0 : ℝ) < (N : ℝ) + K := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
      have hle : (N : ℝ) + K ≤ 2 * N := by
        have : (K : ℝ) ≤ N := by exact_mod_cast hK
        linarith
      rw [neg_div, neg_div, neg_le_neg_iff]
      exact div_le_div_of_nonneg_left (sq_nonneg _) hNK hle
  · have h0 : eCoef N K = 0 := by
      unfold eCoef
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
    rw [h0]
    exact (Real.exp_pos _).le

-- H_fix Step 6 (`e_k` is bounded below on `K² ≪ N`)
/-- **Lower bound of the binomial weight**: `1 − K²/N ≤ e_K` for `K ≤ N`. -/
theorem one_sub_le_eCoef {N K : ℕ} (hK : K ≤ N) : 1 - (K : ℝ) ^ 2 / N ≤ eCoef N K := by
  induction K with
  | zero => simp [eCoef_zero]
  | succ K ih =>
    have hKN : K < N := by omega
    have ih := ih hKN.le
    have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hNK1 : (0 : ℝ) < (N : ℝ) + K + 1 := by positivity
    have hr0 : 0 ≤ 1 - (2 * (K : ℝ) + 1) / ((N : ℝ) + K + 1) := by
      rw [sub_nonneg, div_le_one hNK1]
      have : (K : ℝ) + 1 ≤ N := by exact_mod_cast hK
      linarith
    have hb0 : 0 ≤ (2 * (K : ℝ) + 1) / ((N : ℝ) + K + 1) := by positivity
    have hbN : (2 * (K : ℝ) + 1) / ((N : ℝ) + K + 1) ≤ (2 * (K : ℝ) + 1) / N :=
      div_le_div_of_nonneg_left (by positivity) hN (by linarith)
    have ha0 : 0 ≤ (K : ℝ) ^ 2 / N := by positivity
    have h1 := mul_le_mul_of_nonneg_right ih hr0
    have e1 : (((K + 1 : ℕ) : ℝ)) ^ 2 / N = (K : ℝ) ^ 2 / N + (2 * (K : ℝ) + 1) / N := by
      push_cast; rw [← add_div]; ring_nf
    rw [eCoef_succ hKN, e1]
    nlinarith [mul_nonneg ha0 hb0]

/-- The binomial moment `∑_{K=1}^N K^{2j} e_K²`. -/
def binomMoment (j N : ℕ) : ℝ :=
  ∑ k : Fin N, (((k : ℕ) + 1 : ℕ) : ℝ) ^ (2 * j) * eCoef N ((k : ℕ) + 1) ^ 2

/-- The low binomial moment `∑_{2K² ≤ N} K² e_K²`. -/
def lowMoment (N : ℕ) : ℝ :=
  ∑ k : Fin N, if 2 * ((k : ℕ) + 1) ^ 2 ≤ N then
    (((k : ℕ) + 1 : ℕ) : ℝ) ^ 2 * eCoef N ((k : ℕ) + 1) ^ 2 else 0

/-- `e_K² ≤ exp(−K²/N)`. -/
private lemma eCoef_sq_le_exp (N K : ℕ) : eCoef N K ^ 2 ≤ Real.exp (-((K : ℝ) ^ 2) / N) := by
  calc eCoef N K ^ 2 ≤ Real.exp (-((K : ℝ) ^ 2) / (2 * N)) ^ 2 :=
        pow_le_pow_left₀ (eCoef_nonneg N K) (eCoef_le_exp N K) 2
    _ = Real.exp (-((K : ℝ) ^ 2) / N) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring

/-- **Polynomial decay of the binomial weight**: `K^{2m} e_K² ≤ m! N^m` for `N > 0`. -/
private lemma pow_mul_eCoef_sq_le (m : ℕ) {N : ℕ} (hN : 0 < N) (K : ℕ) :
    (K : ℝ) ^ (2 * m) * eCoef N K ^ 2 ≤ m.factorial * (N : ℝ) ^ m := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set x : ℝ := (K : ℝ) ^ 2 / N with hx
  have hx0 : 0 ≤ x := by positivity
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have h1 : x ^ m ≤ m.factorial * Real.exp x := by
    have := Real.pow_div_factorial_le_exp x hx0 m
    rwa [div_le_iff₀ hf, mul_comm] at this
  have h2 : eCoef N K ^ 2 ≤ Real.exp (-x) := by
    rw [hx, ← neg_div]; exact eCoef_sq_le_exp N K
  have hK : (K : ℝ) ^ (2 * m) = x ^ m * (N : ℝ) ^ m := by
    rw [hx, div_pow, ← pow_mul, div_mul_cancel₀ _ (pow_ne_zero _ hNr.ne')]
  have hee : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc (K : ℝ) ^ (2 * m) * eCoef N K ^ 2 = (x ^ m * eCoef N K ^ 2) * (N : ℝ) ^ m := by
        rw [hK]; ring
    _ ≤ (m.factorial * Real.exp x * Real.exp (-x)) * (N : ℝ) ^ m := by
        gcongr
    _ = m.factorial * (Real.exp x * Real.exp (-x)) * (N : ℝ) ^ m := by ring
    _ = m.factorial * (N : ℝ) ^ m := by rw [hee, mul_one]

/-- The telescoping tail `∑_{T ≤ k < N} (1/k − 1/(k+1)) ≤ 1/T`. -/
private lemma sum_Ico_telescope_le {T N : ℕ} (hTN : T ≤ N) :
    ∑ k ∈ Finset.Ico T N, (1 / (k : ℝ) - 1 / ((k : ℝ) + 1)) ≤ 1 / (T : ℝ) := by
  have h := Finset.sum_range_sub' (fun k : ℕ => 1 / (k : ℝ)) N
  have h' := Finset.sum_range_sub' (fun k : ℕ => 1 / (k : ℝ)) T
  rw [Finset.sum_Ico_eq_sub _ hTN]
  push_cast at h h'
  rw [h, h']
  have : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
  linarith

-- H_fix Step 6 (the binomial weights are Gaussian of width `√N`: upper moments)
/-- **The binomial moments are `O(N^{j+1/2})`**: `(∑_{K≤N} K^{2j} e_K²)² ≤ C (N+1)^{2j+1}`. -/
theorem binomMoment_sq_le (j : ℕ) :
    ∃ C : ℝ, ∀ N : ℕ, binomMoment j N ^ 2 ≤ C * ((N : ℝ) + 1) ^ (2 * j + 1) := by
  refine ⟨(1 + 2 * ((j + 1).factorial : ℝ)) ^ 2 * 2 ^ (2 * j + 1), fun N => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h0 : binomMoment j 0 = 0 := by simp [binomMoment]
    rw [h0, zero_pow two_ne_zero]
    positivity
  set T := Nat.sqrt N with hTdef
  have hT1 : 1 ≤ T := Nat.le_sqrt.2 (by omega)
  have hTN : T ≤ N := Nat.sqrt_le_self N
  have hT2 : T ^ 2 ≤ N := Nat.sqrt_le' N
  have hT3 : N < (T + 1) ^ 2 := Nat.lt_succ_sqrt' N
  have ht1 : (1 : ℝ) ≤ T := by exact_mod_cast hT1
  have ht0 : (0 : ℝ) < T := by linarith
  have hnt : (N : ℝ) ≤ ((T : ℝ) + 1) ^ 2 := by exact_mod_cast hT3.le
  have htn : (T : ℝ) ^ 2 ≤ N := by exact_mod_cast hT2
  set F : ℝ := ((j + 1).factorial : ℝ) with hF
  have hF0 : 0 ≤ F := by positivity
  set g : ℕ → ℝ := fun k => (((k + 1 : ℕ) : ℝ)) ^ (2 * j) * eCoef N (k + 1) ^ 2 with hg
  have hS : binomMoment j N = ∑ k ∈ Finset.range T, g k + ∑ k ∈ Finset.Ico T N, g k := by
    rw [binomMoment, Finset.sum_range_add_sum_Ico _ hTN, ← Fin.sum_univ_eq_sum_range g N]
  -- the head `K ≤ T`
  have hhead : ∑ k ∈ Finset.range T, g k ≤ (T : ℝ) ^ (2 * j + 1) := by
    calc ∑ k ∈ Finset.range T, g k ≤ ∑ _k ∈ Finset.range T, (T : ℝ) ^ (2 * j) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hkT : k + 1 ≤ T := Finset.mem_range.1 hk
          have hkr : (((k + 1 : ℕ) : ℝ)) ≤ T := by exact_mod_cast hkT
          have he := eCoef_le_one N (k + 1)
          have he0 := eCoef_nonneg N (k + 1)
          have he2 : eCoef N (k + 1) ^ 2 ≤ 1 := pow_le_one₀ he0 he
          calc g k ≤ (((k + 1 : ℕ) : ℝ)) ^ (2 * j) * 1 :=
                mul_le_mul_of_nonneg_left he2 (by positivity)
            _ ≤ (T : ℝ) ^ (2 * j) := by rw [mul_one]; gcongr
      _ = (T : ℝ) ^ (2 * j + 1) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, pow_succ]; ring
  -- the tail `K > T`
  have htail : ∑ k ∈ Finset.Ico T N, g k ≤ F * (N : ℝ) ^ (j + 1) / T := by
    calc ∑ k ∈ Finset.Ico T N, g k
        ≤ ∑ k ∈ Finset.Ico T N, F * (N : ℝ) ^ (j + 1) * (1 / (k : ℝ) - 1 / ((k : ℝ) + 1)) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hkT : T ≤ k := (Finset.mem_Ico.1 hk).1
          have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hT1.trans hkT
          have hk0 : (0 : ℝ) < k := by linarith
          have hd := pow_mul_eCoef_sq_le (j + 1) hN (k + 1)
          have hsplit : (1 / (k : ℝ) - 1 / ((k : ℝ) + 1)) = 1 / ((k : ℝ) * ((k : ℝ) + 1)) := by
            field_simp; ring
          rw [hsplit]
          have hq : (0 : ℝ) < (k : ℝ) * ((k : ℝ) + 1) := by positivity
          rw [mul_one_div, le_div_iff₀ hq]
          simp only [hg]
          push_cast at hd ⊢
          have hkk : (k : ℝ) * ((k : ℝ) + 1) ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith
          calc ((k : ℝ) + 1) ^ (2 * j) * eCoef N (k + 1) ^ 2 * ((k : ℝ) * ((k : ℝ) + 1))
              ≤ ((k : ℝ) + 1) ^ (2 * j) * eCoef N (k + 1) ^ 2 * ((k : ℝ) + 1) ^ 2 := by
                gcongr
            _ = ((k : ℝ) + 1) ^ (2 * (j + 1)) * eCoef N (k + 1) ^ 2 := by ring
            _ ≤ F * (N : ℝ) ^ (j + 1) := hd
      _ = F * (N : ℝ) ^ (j + 1) * ∑ k ∈ Finset.Ico T N, (1 / (k : ℝ) - 1 / ((k : ℝ) + 1)) := by
          rw [Finset.mul_sum]
      _ ≤ F * (N : ℝ) ^ (j + 1) * (1 / (T : ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_Ico_telescope_le hTN) (by positivity)
      _ = F * (N : ℝ) ^ (j + 1) / T := by rw [mul_one_div]
  have htail' : F * (N : ℝ) ^ (j + 1) / T ≤ 2 * F * ((T : ℝ) + 1) ^ (2 * j + 1) := by
    rw [div_le_iff₀ ht0]
    have hN' : (N : ℝ) ^ (j + 1) ≤ (((T : ℝ) + 1) ^ 2) ^ (j + 1) := by gcongr
    have hT' : (T : ℝ) + 1 ≤ 2 * T := by linarith
    calc F * (N : ℝ) ^ (j + 1) ≤ F * (((T : ℝ) + 1) ^ 2) ^ (j + 1) := by gcongr
      _ = F * ((T : ℝ) + 1) ^ (2 * j + 1) * ((T : ℝ) + 1) := by
          rw [← pow_mul, show 2 * (j + 1) = (2 * j + 1) + 1 by ring, pow_succ, mul_assoc]
      _ ≤ F * ((T : ℝ) + 1) ^ (2 * j + 1) * (2 * T) := by gcongr
      _ = 2 * F * ((T : ℝ) + 1) ^ (2 * j + 1) * T := by ring
  have hbound : binomMoment j N ≤ (1 + 2 * F) * ((T : ℝ) + 1) ^ (2 * j + 1) := by
    have hTT : (T : ℝ) ^ (2 * j + 1) ≤ ((T : ℝ) + 1) ^ (2 * j + 1) := by gcongr; linarith
    rw [hS]
    linarith
  have hS0 : 0 ≤ binomMoment j N := Finset.sum_nonneg fun k _ => by positivity
  have hT2N : ((T : ℝ) + 1) ^ 2 ≤ 2 * ((N : ℝ) + 1) := by nlinarith [sq_nonneg ((T : ℝ) - 1)]
  calc binomMoment j N ^ 2 ≤ ((1 + 2 * F) * ((T : ℝ) + 1) ^ (2 * j + 1)) ^ 2 :=
        pow_le_pow_left₀ hS0 hbound 2
    _ = (1 + 2 * F) ^ 2 * (((T : ℝ) + 1) ^ 2) ^ (2 * j + 1) := by
        rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm (2 * j + 1) 2]
    _ ≤ (1 + 2 * F) ^ 2 * (2 * ((N : ℝ) + 1)) ^ (2 * j + 1) := by gcongr
    _ = (1 + 2 * F) ^ 2 * 2 ^ (2 * j + 1) * ((N : ℝ) + 1) ^ (2 * j + 1) := by
        rw [mul_pow]; ring

/-- `n³/3 ≤ ∑_{K=1}^n K²`. -/
private lemma cube_div_three_le_sum_sq (n : ℕ) :
    (n : ℝ) ^ 3 / 3 ≤ ∑ k ∈ Finset.range n, ((k : ℝ) + 1) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    push_cast
    nlinarith [ih, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

-- H_fix Step 6 (the binomial weights are Gaussian of width `√N`: the low window)
/-- **The low moment is at least a multiple of `N^{3/2}`**: `c N³ ≤ (∑_{2K²≤N} K² e_K²)²` for
`N ≥ 2`. -/
theorem lowMoment_sq_ge : ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 2 ≤ N → c * (N : ℝ) ^ 3 ≤ lowMoment N ^ 2 := by
  refine ⟨1 / (8 ^ 3 * 12 ^ 2), by norm_num, fun N hN => ?_⟩
  set T := Nat.sqrt (N / 2) with hTdef
  have hT1 : 1 ≤ T := Nat.le_sqrt.2 (by omega)
  have hT2 : 2 * T ^ 2 ≤ N := by
    have : T ^ 2 ≤ N / 2 := Nat.sqrt_le' (N / 2)
    omega
  have hT3 : N ≤ 2 * (T + 1) ^ 2 := by
    have : N / 2 < (T + 1) ^ 2 := Nat.lt_succ_sqrt' (N / 2)
    omega
  have hTN : T ≤ N := by nlinarith
  have hN8 : (N : ℝ) ≤ 8 * (T : ℝ) ^ 2 := by
    have h1 : (N : ℝ) ≤ 2 * ((T : ℝ) + 1) ^ 2 := by exact_mod_cast hT3
    have h2 : (1 : ℝ) ≤ T := by exact_mod_cast hT1
    nlinarith
  have hlow : (T : ℝ) ^ 3 / 12 ≤ lowMoment N := by
    have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hf0 : ∀ k : ℕ, 0 ≤ (if 2 * (k + 1) ^ 2 ≤ N then
        (((k + 1 : ℕ) : ℝ)) ^ 2 * eCoef N (k + 1) ^ 2 else 0) := fun k => by
      split_ifs <;> positivity
    rw [lowMoment, Fin.sum_univ_eq_sum_range (fun k => if 2 * (k + 1) ^ 2 ≤ N then
        (((k + 1 : ℕ) : ℝ)) ^ 2 * eCoef N (k + 1) ^ 2 else 0) N]
    calc (T : ℝ) ^ 3 / 12 ≤ (1 / 4) * ∑ k ∈ Finset.range T, ((k : ℝ) + 1) ^ 2 := by
          have := cube_div_three_le_sum_sq T
          linarith
      _ = ∑ k ∈ Finset.range T, ((k : ℝ) + 1) ^ 2 * (1 / 2) ^ 2 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
      _ ≤ ∑ k ∈ Finset.range T, (if 2 * (k + 1) ^ 2 ≤ N then
            (((k + 1 : ℕ) : ℝ)) ^ 2 * eCoef N (k + 1) ^ 2 else 0) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hkT : k + 1 ≤ T := Finset.mem_range.1 hk
          have hk2 : 2 * (k + 1) ^ 2 ≤ N := le_trans (by gcongr) hT2
          rw [ite_eq_left hk2]
          have he := one_sub_le_eCoef (show k + 1 ≤ N by nlinarith)
          have hk2r : 2 * ((k : ℝ) + 1) ^ 2 ≤ N := by exact_mod_cast hk2
          have hhalf : ((((k + 1 : ℕ) : ℝ)) ^ 2) / N ≤ 1 / 2 := by
            rw [div_le_iff₀ hNr]; push_cast; linarith
          have he2 : 1 / 2 ≤ eCoef N (k + 1) := by linarith
          push_cast
          gcongr
      _ ≤ ∑ k ∈ Finset.range N, (if 2 * (k + 1) ^ 2 ≤ N then
            (((k + 1 : ℕ) : ℝ)) ^ 2 * eCoef N (k + 1) ^ 2 else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hTN)
            fun k _ _ => hf0 k
  have hT0 : (0 : ℝ) ≤ (T : ℝ) ^ 3 / 12 := by positivity
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  calc 1 / (8 ^ 3 * 12 ^ 2) * (N : ℝ) ^ 3 ≤ 1 / (8 ^ 3 * 12 ^ 2) * (8 * (T : ℝ) ^ 2) ^ 3 := by
        gcongr
    _ = ((T : ℝ) ^ 3 / 12) ^ 2 := by ring
    _ ≤ lowMoment N ^ 2 := pow_le_pow_left₀ hT0 hlow 2

/-! ### The envelopes on a fixed band -/

-- H_fix Step 6 (`Φ` is bounded on the fixed band: finitely many zeros below a height)
/-- **`Φ_M` is bounded on `[0, A]` uniformly in `M`** when `γ_i² → ∞`. -/
theorem exists_phiEnv_le {γ : ℕ → ℝ} (hγ : Tendsto (fun i => γ i ^ 2) atTop atTop) (A : ℝ) :
    ∃ C : ℝ, ∀ (M : ℕ) (s : ℝ), 0 ≤ s → s ≤ A → phiEnv γ M s ≤ C := by
  obtain ⟨I, hI⟩ := Filter.eventually_atTop.1 (Filter.tendsto_atTop.1 hγ (max A 1))
  refine ⟨∏ i ∈ Finset.range I, max 1 (A / γ i ^ 2) ^ 2, fun M s hs hsA => ?_⟩
  unfold phiEnv
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.range M) (fun i => i < I)]
  have hhi : ∏ i ∈ (Finset.range M).filter (fun i => ¬ i < I), max 1 (s / γ i ^ 2) ^ 2 = 1 := by
    refine Finset.prod_eq_one fun i hi => ?_
    have hiI : I ≤ i := by
      simp only [Finset.mem_filter, not_lt] at hi
      exact hi.2
    have hγi := hI i hiI
    have hpos : 0 < γ i ^ 2 := by linarith [le_max_right A 1]
    have hle : s / γ i ^ 2 ≤ 1 := by
      rw [div_le_one hpos]
      linarith [le_max_left A 1]
    rw [max_eq_left hle, one_pow]
  rw [hhi, mul_one]
  calc ∏ i ∈ (Finset.range M).filter (fun i => i < I), max 1 (s / γ i ^ 2) ^ 2
      ≤ ∏ i ∈ (Finset.range M).filter (fun i => i < I), max 1 (A / γ i ^ 2) ^ 2 := by
        refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
        have h : s / γ i ^ 2 ≤ A / γ i ^ 2 := by gcongr
        have h1 : max 1 (s / γ i ^ 2) ≤ max 1 (A / γ i ^ 2) := max_le_max le_rfl h
        exact pow_le_pow_left₀ (le_max_left _ _ |>.trans' zero_le_one) h1 2
    _ ≤ ∏ i ∈ Finset.range I, max 1 (A / γ i ^ 2) ^ 2 := by
        refine Finset.prod_le_prod_of_subset_of_one_le₀ ?_ (fun i _ => by positivity)
          fun i _ _ => one_le_pow₀ (le_max_left _ _)
        intro i hi
        simp only [Finset.mem_filter] at hi
        exact Finset.mem_range.2 hi.2

/-- **Weierstrass product inequality**: `1 − ∑_{i<M} a_i ≤ ∏_{i<M} (1 − a_i)` for `a_i ∈ [0, 1]`. -/
private lemma one_sub_sum_le_prod {a : ℕ → ℝ} (h0 : ∀ i, 0 ≤ a i) (h1 : ∀ i, a i ≤ 1) (M : ℕ) :
    1 - ∑ i ∈ Finset.range M, a i ≤ ∏ i ∈ Finset.range M, (1 - a i) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, Finset.prod_range_succ]
    have hS : 0 ≤ ∑ i ∈ Finset.range M, a i := Finset.sum_nonneg fun i _ => h0 i
    have h1M : 0 ≤ 1 - a M := by linarith [h1 M]
    nlinarith [mul_le_mul_of_nonneg_right ih h1M, mul_nonneg hS (h0 M)]

-- H_fix Step 6 (`Ψ ≥ exp(−4Ss)`, in the exact form `(1 − sS)²`)
/-- **`Ψ_M(s) ≥ (1 − s∑1/γ_i²)²`** for `s ≥ 0` with `s∑1/γ_i² ≤ 1`. -/
theorem sq_one_sub_le_psiEnv {γ : ℕ → ℝ} (hsum : Summable fun i => 1 / γ i ^ 2) (M : ℕ) {s : ℝ}
    (hs : 0 ≤ s)
    (hsS : s * ∑' i, 1 / γ i ^ 2 ≤ 1) :
    (1 - s * ∑' i, 1 / γ i ^ 2) ^ 2 ≤ psiEnv γ M s := by
  have hnn : ∀ i, 0 ≤ 1 / γ i ^ 2 := fun i => by positivity
  have hle : ∀ i, 1 / γ i ^ 2 ≤ ∑' i, 1 / γ i ^ 2 := fun i => hsum.le_tsum i fun j _ => hnn j
  have ha0 : ∀ i, 0 ≤ s / γ i ^ 2 := fun i => by positivity
  have ha1 : ∀ i, s / γ i ^ 2 ≤ 1 := fun i => by
    rw [div_eq_mul_one_div]
    exact (mul_le_mul_of_nonneg_left (hle i) hs).trans hsS
  have hsumM : ∑ i ∈ Finset.range M, s / γ i ^ 2 ≤ s * ∑' i, 1 / γ i ^ 2 := by
    simp_rw [div_eq_mul_one_div s]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ fun j _ => hnn j) hs
  have hW := one_sub_sum_le_prod ha0 ha1 M
  have h0 : 0 ≤ 1 - s * ∑' i, 1 / γ i ^ 2 := by linarith
  unfold psiEnv
  rw [Finset.prod_pow]
  exact pow_le_pow_left₀ h0 (by linarith) 2

/-! ### Eventual `LAT` -/

theorem nu_eq_mul (L : ℝ) (K : ℕ) : nu L K = 2 * π / L * (K : ℝ) := by unfold nu; ring

/-- `Λ_h² < 6.24²` from a bound `C` on `Φ` along the lattice and a small second moment. -/
theorem lamH_lt {L a C : ℝ} {N : ℕ} (hnu : ∀ K : ℕ, nu L K = a * K)
    (hΦ : ∀ k : Fin N, phiEnv ordSeq (N - 1) (nu L ((k : ℕ) + 1) ^ 2) ≤ C)
    (hsmall : 2 * C * (a ^ 2 * binomMoment 1 N) < (6.24 : ℝ) ^ 2) :
    lamHNum L N < (6.24 : ℝ) ^ 2 * lamHDen L N := by
  have h : ∑ k : Fin N, nu L ((k : ℕ) + 1) ^ 2
      * phiEnv ordSeq (N - 1) (nu L ((k : ℕ) + 1) ^ 2) * eCoef N ((k : ℕ) + 1) ^ 2
      ≤ ∑ k : Fin N, C * (a ^ 2 * ((((k : ℕ) + 1 : ℕ) : ℝ) ^ (2 * 1)
        * eCoef N ((k : ℕ) + 1) ^ 2)) := by
    refine Finset.sum_le_sum fun k _ => ?_
    have hk := hΦ k
    have h0 : 0 ≤ nu L ((k : ℕ) + 1) ^ 2 * eCoef N ((k : ℕ) + 1) ^ 2 := by positivity
    have e1 : nu L ((k : ℕ) + 1) ^ 2 = a ^ 2 * (((k : ℕ) + 1 : ℕ) : ℝ) ^ (2 * 1) := by
      rw [hnu]; ring
    calc nu L ((k : ℕ) + 1) ^ 2 * phiEnv ordSeq (N - 1) (nu L ((k : ℕ) + 1) ^ 2)
          * eCoef N ((k : ℕ) + 1) ^ 2
        = (nu L ((k : ℕ) + 1) ^ 2 * eCoef N ((k : ℕ) + 1) ^ 2)
          * phiEnv ordSeq (N - 1) (nu L ((k : ℕ) + 1) ^ 2) := by ring
      _ ≤ (nu L ((k : ℕ) + 1) ^ 2 * eCoef N ((k : ℕ) + 1) ^ 2) * C :=
        mul_le_mul_of_nonneg_left hk h0
      _ = _ := by rw [e1]; ring
  have e : ∑ k : Fin N, C * (a ^ 2 * ((((k : ℕ) + 1 : ℕ) : ℝ) ^ (2 * 1)
      * eCoef N ((k : ℕ) + 1) ^ 2)) = C * (a ^ 2 * binomMoment 1 N) := by
    rw [binomMoment, Finset.mul_sum, Finset.mul_sum]
  have hD : 1 ≤ lamHDen L N := by
    rw [lamHDen]
    have : 0 ≤ ∑ k : Fin N, (if nu L ((k : ℕ) + 1) < ordSeq 0 then
        psiEnv ordSeq (N - 1) (nu L ((k : ℕ) + 1) ^ 2) * eCoef N ((k : ℕ) + 1) ^ 2 else 0) :=
      Finset.sum_nonneg fun k _ => by
        split_ifs
        · exact mul_nonneg (Finset.prod_nonneg fun i _ => sq_nonneg _) (sq_nonneg _)
        · exact le_rfl
    linarith
  have hN : lamHNum L N ≤ 2 * C * (a ^ 2 * binomMoment 1 N) := by
    rw [lamHNum]; linarith
  calc lamHNum L N < (6.24 : ℝ) ^ 2 := lt_of_le_of_lt hN hsmall
    _ ≤ (6.24 : ℝ) ^ 2 * lamHDen L N := le_mul_of_one_le_right (by norm_num) hD

/-- `Λ_Y² < γ_1²` from a bound `C` on `Φ` along the lattice, `Ψ ≥ 1/4` below `s₀ < γ_1²`, the low
window inside `ν² ≤ s₀`, and a fourth moment small against the low moment. -/
theorem lamY_lt {L a C s₀ : ℝ} {N : ℕ} (hnu : ∀ K : ℕ, nu L K = a * K)
    (hΦ : ∀ k : Fin N, phiEnv ordSeq (N - 1) (nu L ((k : ℕ) + 1) ^ 2) ≤ C)
    (hΨ : ∀ s : ℝ, 0 ≤ s → s ≤ s₀ → 1 / 4 ≤ psiEnv ordSeq (N - 1) s)
    (hs₀ : s₀ < ordSeq 0 ^ 2)
    (hlow : ∀ k : Fin N, 2 * ((k : ℕ) + 1) ^ 2 ≤ N → nu L ((k : ℕ) + 1) ^ 2 ≤ s₀)
    (hsmall : 4 * C * (a ^ 4 * binomMoment 2 N) < ordSeq 0 ^ 2 * (a ^ 2 * lowMoment N)) :
    lamYNum L N < ordSeq 0 ^ 2 * lamYDen L N := by
  have h1 : ∑ k : Fin N, nu L ((k : ℕ) + 1) ^ 4
      * phiEnv ordSeq (N - 1) (nu L ((k : ℕ) + 1) ^ 2) * eCoef N ((k : ℕ) + 1) ^ 2
      ≤ ∑ k : Fin N, C * (a ^ 4 * ((((k : ℕ) + 1 : ℕ) : ℝ) ^ (2 * 2)
        * eCoef N ((k : ℕ) + 1) ^ 2)) := by
    refine Finset.sum_le_sum fun k _ => ?_
    have hk := hΦ k
    have h0 : 0 ≤ nu L ((k : ℕ) + 1) ^ 4 * eCoef N ((k : ℕ) + 1) ^ 2 := by positivity
    have e1 : nu L ((k : ℕ) + 1) ^ 4 = a ^ 4 * (((k : ℕ) + 1 : ℕ) : ℝ) ^ (2 * 2) := by
      rw [hnu]; ring
    calc nu L ((k : ℕ) + 1) ^ 4 * phiEnv ordSeq (N - 1) (nu L ((k : ℕ) + 1) ^ 2)
          * eCoef N ((k : ℕ) + 1) ^ 2
        = (nu L ((k : ℕ) + 1) ^ 4 * eCoef N ((k : ℕ) + 1) ^ 2)
          * phiEnv ordSeq (N - 1) (nu L ((k : ℕ) + 1) ^ 2) := by ring
      _ ≤ (nu L ((k : ℕ) + 1) ^ 4 * eCoef N ((k : ℕ) + 1) ^ 2) * C :=
        mul_le_mul_of_nonneg_left hk h0
      _ = _ := by rw [e1]; ring
  have e : ∑ k : Fin N, C * (a ^ 4 * ((((k : ℕ) + 1 : ℕ) : ℝ) ^ (2 * 2)
      * eCoef N ((k : ℕ) + 1) ^ 2)) = C * (a ^ 4 * binomMoment 2 N) := by
    rw [binomMoment, Finset.mul_sum, Finset.mul_sum]
  have hγ : 0 < ordSeq 0 := ordSeq_pos 0
  have h2 : a ^ 2 * lowMoment N ≤ 4 * lamYDen L N := by
    rw [lowMoment, lamYDen, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have hψ0 : 0 ≤ psiEnv ordSeq (N - 1) (nu L ((k : ℕ) + 1) ^ 2) :=
      Finset.prod_nonneg fun i _ => sq_nonneg _
    by_cases hk : 2 * ((k : ℕ) + 1) ^ 2 ≤ N
    · have hs := hlow k hk
      have hlt : nu L ((k : ℕ) + 1) < ordSeq 0 :=
        abs_lt_of_sq_lt_sq (hs.trans_lt hs₀) hγ.le |>.trans_le' (le_abs_self _)
      rw [ite_eq_left hk, ite_eq_left hlt]
      have hψ := hΨ _ (sq_nonneg _) hs
      have h0 : 0 ≤ nu L ((k : ℕ) + 1) ^ 2 * eCoef N ((k : ℕ) + 1) ^ 2 := by positivity
      have e1 : nu L ((k : ℕ) + 1) ^ 2 = a ^ 2 * (((k : ℕ) + 1 : ℕ) : ℝ) ^ 2 := by
        rw [hnu]; ring
      calc a ^ 2 * ((((k : ℕ) + 1 : ℕ) : ℝ) ^ 2 * eCoef N ((k : ℕ) + 1) ^ 2)
          = (nu L ((k : ℕ) + 1) ^ 2 * eCoef N ((k : ℕ) + 1) ^ 2) * (4 * (1 / 4)) := by
            rw [e1]; ring
        _ ≤ (nu L ((k : ℕ) + 1) ^ 2 * eCoef N ((k : ℕ) + 1) ^ 2)
            * (4 * psiEnv ordSeq (N - 1) (nu L ((k : ℕ) + 1) ^ 2)) :=
          mul_le_mul_of_nonneg_left (by linarith) h0
        _ = _ := by ring
    · rw [ite_eq_right hk, mul_zero]
      split_ifs
      · exact mul_nonneg (by norm_num)
          (mul_nonneg (mul_nonneg (sq_nonneg _) hψ0) (sq_nonneg _))
      · norm_num
  have hY : lamYNum L N ≤ C * (a ^ 4 * binomMoment 2 N) := by rw [lamYNum]; linarith
  have hγ2 : 0 ≤ ordSeq 0 ^ 2 := sq_nonneg _
  have h3 : ordSeq 0 ^ 2 * (a ^ 2 * lowMoment N) ≤ ordSeq 0 ^ 2 * (4 * lamYDen L N) :=
    mul_le_mul_of_nonneg_left h2 hγ2
  linarith

theorem mul_lt_of_le_div_add_one {a X Y : ℝ} (hX : 0 ≤ X) (hY : 0 < Y) (h : a ≤ Y / (X + 1)) :
    a * X < Y := by
  have hX1 : 0 < X + 1 := by linarith
  calc a * X ≤ Y / (X + 1) * X := mul_le_mul_of_nonneg_right h hX
    _ < Y := by rw [div_mul_eq_mul_div, div_lt_iff₀ hX1]; nlinarith

/-- **`LAT` holds eventually along a fixed bandwidth**: for `Ω > 0`, `LAT(L, ⌈ΩL/2π⌉)` for all
large `L`. -/
theorem eventually_LAT {Ω : ℝ} (hΩ : 0 < Ω) : ∀ᶠ L in atTop, LAT L (band Ω L) := by
  obtain ⟨C, hC, hΦ⟩ : ∃ C : ℝ, 0 < C ∧
      ∀ (M : ℕ) (s : ℝ), 0 ≤ s → s ≤ (Ω + 1) ^ 2 → phiEnv ordSeq M s ≤ C := by
    obtain ⟨CΦ, hCΦ⟩ := exists_phiEnv_le tendsto_ordSeq_sq ((Ω + 1) ^ 2)
    refine ⟨max CΦ 0 + 1, by linarith [le_max_right CΦ 0], fun M s h0 h1 => ?_⟩
    exact (hCΦ M s h0 h1).trans (by linarith [le_max_left CΦ 0])
  have hγ0 : 0 < ordSeq 0 := ordSeq_pos 0
  obtain ⟨s₀, hs₀, hs₀γ, hΨ⟩ : ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ < ordSeq 0 ^ 2 ∧
      ∀ (M : ℕ) (s : ℝ), 0 ≤ s → s ≤ s₀ → 1 / 4 ≤ psiEnv ordSeq M s := by
    have hS : 0 ≤ ∑' i, 1 / ordSeq i ^ 2 := tsum_nonneg fun i => by positivity
    refine ⟨min (ordSeq 0 ^ 2 / 2) (1 / (2 * ((∑' i, 1 / ordSeq i ^ 2) + 1))),
      lt_min (by positivity) (by positivity),
      (min_le_left _ _).trans_lt (by linarith [pow_pos hγ0 2]), fun M s h0 h1 => ?_⟩
    have hsS : s * ∑' i, 1 / ordSeq i ^ 2 ≤ 1 / 2 := by
      calc s * ∑' i, 1 / ordSeq i ^ 2
          ≤ 1 / (2 * ((∑' i, 1 / ordSeq i ^ 2) + 1)) * ∑' i, 1 / ordSeq i ^ 2 :=
            mul_le_mul_of_nonneg_right (h1.trans (min_le_right _ _)) hS
        _ ≤ 1 / 2 := by rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]; linarith
    have h := sq_one_sub_le_psiEnv summable_inv_ordSeq_sq M h0
      (by linarith)
    nlinarith
  obtain ⟨C₁, hC₁⟩ := binomMoment_sq_le 1
  obtain ⟨C₂, hC₂⟩ := binomMoment_sq_le 2
  obtain ⟨c, hc, hlow⟩ := lowMoment_sq_ge
  have hC₁0 : 0 ≤ C₁ := by have := hC₁ 0; simpa [binomMoment] using this
  have hC₂0 : 0 ≤ C₂ := by have := hC₂ 0; simpa [binomMoment] using this
  have hX₁ : 0 ≤ 32 * C ^ 2 * Ω ^ 3 * C₁ := by positivity
  have hX₂ : 0 ≤ 2048 * C ^ 2 * C₂ * Ω ^ 2 := by positivity
  have hY₁ : (0 : ℝ) < 6.24 ^ 4 := by norm_num
  have hY₂ : 0 < ordSeq 0 ^ 4 * c := by positivity
  obtain ⟨a₀, ha₀, ha₀1, ha₀Ω, ha₀s, ha₀H, ha₀Y⟩ : ∃ a₀ : ℝ, 0 < a₀ ∧ a₀ ≤ 1 ∧ a₀ ≤ Ω / 2 ∧
      a₀ ≤ s₀ / Ω ∧ a₀ ≤ 6.24 ^ 4 / (32 * C ^ 2 * Ω ^ 3 * C₁ + 1) ∧
      a₀ ≤ ordSeq 0 ^ 4 * c / (2048 * C ^ 2 * C₂ * Ω ^ 2 + 1) :=
    ⟨min (min 1 (Ω / 2)) (min (s₀ / Ω) (min (6.24 ^ 4 / (32 * C ^ 2 * Ω ^ 3 * C₁ + 1))
      (ordSeq 0 ^ 4 * c / (2048 * C ^ 2 * C₂ * Ω ^ 2 + 1)))),
      lt_min (lt_min one_pos (by positivity)) (lt_min (by positivity)
        (lt_min (div_pos hY₁ (by linarith)) (div_pos hY₂ (by linarith)))),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  filter_upwards [eventually_ge_atTop (2 * π / a₀)] with L hL
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity) hL
  obtain ⟨a, had⟩ : ∃ a : ℝ, a = 2 * π / L := ⟨_, rfl⟩
  have ha : 0 < a := by rw [had]; positivity
  have haa₀ : a ≤ a₀ := by
    rw [had, div_le_iff₀ hLpos]
    rw [div_le_iff₀ ha₀] at hL
    linarith
  have hnu : ∀ K : ℕ, nu L K = a * K := fun K => by rw [had, nu_eq_mul]
  have hΩa : Ω * L / (2 * π) = Ω / a := by rw [had]; field_simp
  have hNlo : Ω / a ≤ (band Ω L : ℝ) := by rw [← hΩa]; exact Nat.le_ceil _
  have hNhi : (band Ω L : ℝ) < Ω / a + 1 := by rw [← hΩa]; exact Nat.ceil_lt_add_one (by positivity)
  have haΩa : a * (Ω / a) = Ω := by field_simp
  have h2a : 2 ≤ Ω / a := by rw [le_div_iff₀ ha]; linarith
  have hN2 : 2 ≤ band Ω L := by exact_mod_cast (show (2 : ℝ) ≤ band Ω L by linarith)
  have hNpos : (0 : ℝ) < band Ω L := by linarith
  have haN : a * (band Ω L : ℝ) ≤ 2 * Ω := by
    have := mul_le_mul_of_nonneg_left hNhi.le ha.le
    nlinarith
  have haN1 : a * ((band Ω L : ℝ) + 1) ≤ 2 * Ω := by
    have := mul_le_mul_of_nonneg_left hNhi.le ha.le
    nlinarith
  have hΦk : ∀ k : Fin (band Ω L),
      phiEnv ordSeq (band Ω L - 1) (nu L ((k : ℕ) + 1) ^ 2) ≤ C := fun k => by
    refine hΦ _ _ (sq_nonneg _) (pow_le_pow_left₀ (by rw [hnu]; positivity) ?_ 2)
    rw [hnu]
    have hK : (((k : ℕ) + 1 : ℕ) : ℝ) ≤ band Ω L := by exact_mod_cast k.isLt
    have h1 := mul_le_mul_of_nonneg_left hK ha.le
    have h2 := mul_lt_mul_of_pos_left hNhi ha
    rw [mul_add, haΩa, mul_one] at h2
    linarith [haa₀.trans ha₀1]
  have hm₁ : 0 ≤ binomMoment 1 (band Ω L) := Finset.sum_nonneg fun k _ => by positivity
  have hm₂ : 0 ≤ binomMoment 2 (band Ω L) := Finset.sum_nonneg fun k _ => by positivity
  have hl0 : 0 ≤ lowMoment (band Ω L) := Finset.sum_nonneg fun k _ => by
    split_ifs <;> positivity
  refine ⟨lamY_lt hnu hΦk (hΨ _) hs₀γ (fun k hk => ?_) ?_, lamH_lt hnu hΦk ?_⟩
  · -- the low window lies in `ν² ≤ s₀`
    rw [hnu]
    have hK2 : (((k : ℕ) + 1 : ℕ) : ℝ) ^ 2 * 2 ≤ band Ω L := by exact_mod_cast (by linarith)
    have h3 : a * Ω ≤ s₀ := by
      have := mul_le_mul_of_nonneg_right (haa₀.trans ha₀s) hΩ.le
      rwa [div_mul_cancel₀ _ hΩ.ne'] at this
    calc (a * (((k : ℕ) + 1 : ℕ) : ℝ)) ^ 2 = a * (a * ((((k : ℕ) + 1 : ℕ) : ℝ) ^ 2 * 2)) / 2 := by
          ring
      _ ≤ a * (a * band Ω L) / 2 := by
          gcongr
      _ ≤ a * (2 * Ω) / 2 := by gcongr
      _ = a * Ω := by ring
      _ ≤ s₀ := h3
  · -- the fourth moment is small against the low moment
    have hsq : (4 * C * (a ^ 2 * binomMoment 2 (band Ω L))) ^ 2
        < (ordSeq 0 ^ 2 * lowMoment (band Ω L)) ^ 2 := by
      have hN1 : (band Ω L : ℝ) + 1 ≤ 2 * band Ω L := by linarith
      have hlt := mul_lt_of_le_div_add_one hX₂ hY₂ (haa₀.trans ha₀Y)
      have ha2 : a ^ 2 ≤ a := by nlinarith [haa₀.trans ha₀1]
      have h4 : (a * band Ω L) ^ 2 ≤ (2 * Ω) ^ 2 := pow_le_pow_left₀ (by positivity) haN 2
      have hN3 : 0 ≤ (band Ω L : ℝ) ^ 3 := by positivity
      calc (4 * C * (a ^ 2 * binomMoment 2 (band Ω L))) ^ 2
          = 16 * C ^ 2 * a ^ 4 * binomMoment 2 (band Ω L) ^ 2 := by ring
        _ ≤ 16 * C ^ 2 * a ^ 4 * (C₂ * ((band Ω L : ℝ) + 1) ^ (2 * 2 + 1)) := by
          gcongr; exact hC₂ _
        _ ≤ 16 * C ^ 2 * a ^ 4 * (C₂ * (2 * (band Ω L : ℝ)) ^ (2 * 2 + 1)) := by
          gcongr
        _ = 512 * C ^ 2 * C₂ * a ^ 2 * (a * band Ω L) ^ 2 * (band Ω L : ℝ) ^ 3 := by ring
        _ ≤ 512 * C ^ 2 * C₂ * a * (2 * Ω) ^ 2 * (band Ω L : ℝ) ^ 3 := by gcongr
        _ = a * (2048 * C ^ 2 * C₂ * Ω ^ 2) * (band Ω L : ℝ) ^ 3 := by ring
        _ < ordSeq 0 ^ 4 * c * (band Ω L : ℝ) ^ 3 := by gcongr
        _ ≤ ordSeq 0 ^ 4 * lowMoment (band Ω L) ^ 2 := by
          rw [mul_assoc]; gcongr; exact hlow _ hN2
        _ = (ordSeq 0 ^ 2 * lowMoment (band Ω L)) ^ 2 := by ring
    have hlt := lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
    have ha2 : 0 < a ^ 2 := by positivity
    calc 4 * C * (a ^ 4 * binomMoment 2 (band Ω L))
        = a ^ 2 * (4 * C * (a ^ 2 * binomMoment 2 (band Ω L))) := by ring
      _ < a ^ 2 * (ordSeq 0 ^ 2 * lowMoment (band Ω L)) := mul_lt_mul_of_pos_left hlt ha2
      _ = ordSeq 0 ^ 2 * (a ^ 2 * lowMoment (band Ω L)) := by ring
  · -- the second moment is small
    have hsq : (2 * C * (a ^ 2 * binomMoment 1 (band Ω L))) ^ 2 < ((6.24 : ℝ) ^ 2) ^ 2 := by
      have hlt := mul_lt_of_le_div_add_one hX₁ hY₁ (haa₀.trans ha₀H)
      have h3 : (a * ((band Ω L : ℝ) + 1)) ^ 3 ≤ (2 * Ω) ^ 3 :=
        pow_le_pow_left₀ (by positivity) haN1 3
      calc (2 * C * (a ^ 2 * binomMoment 1 (band Ω L))) ^ 2
          = 4 * C ^ 2 * a ^ 4 * binomMoment 1 (band Ω L) ^ 2 := by ring
        _ ≤ 4 * C ^ 2 * a ^ 4 * (C₁ * ((band Ω L : ℝ) + 1) ^ (2 * 1 + 1)) := by
          gcongr; exact hC₁ _
        _ = 4 * C ^ 2 * C₁ * a * (a * ((band Ω L : ℝ) + 1)) ^ 3 := by ring
        _ ≤ 4 * C ^ 2 * C₁ * a * (2 * Ω) ^ 3 := by gcongr
        _ = a * (32 * C ^ 2 * Ω ^ 3 * C₁) := by ring
        _ < 6.24 ^ 4 := hlt
        _ = ((6.24 : ℝ) ^ 2) ^ 2 := by norm_num
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq

end Cvs.Finite.OddDisplacementPencil
