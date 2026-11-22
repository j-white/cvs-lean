import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The off-diagonal sum of `1/(a m |a - m|)` is bounded

For every `M`, `∑_{a ≠ m ≤ M} 1/(a m |a - m|) = 4 ∑_{n < M} H_n/(n+1)²` with `H_n` the
`n`-th harmonic number, and this is at most `8`, uniformly in `M`.
-/

namespace Cvs.Upstream.OffDiagonalHarmonicSum

open Finset

/-- The harmonic number `H_M = ∑_{i<M} 1/(i+1)` as a real number. -/
noncomputable def harm (M : ℕ) : ℝ := ∑ i ∈ range M, 1 / ((i : ℝ) + 1)

/-- The weight `1/(a m |a - m|)`. -/
noncomputable def w (a m : ℕ) : ℝ := 1 / ((a : ℝ) * m * |(a : ℝ) - m|)

/-- The off-diagonal double sum of `w` over `1 ≤ a, m ≤ M`. -/
noncomputable def S (M : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 M, ∑ m ∈ (Icc 1 M).filter (· ≠ a), w a m

/-- The weight is symmetric. -/
lemma w_comm (a m : ℕ) : w a m = w m a := by
  unfold w; rw [abs_sub_comm]; ring_nf

/-- Harmonic numbers are nonnegative. -/
lemma harm_nonneg (M : ℕ) : 0 ≤ harm M := sum_nonneg fun i _ => by positivity

/-- `H_M ≤ M`. -/
lemma harm_le (M : ℕ) : harm M ≤ M := by
  unfold harm
  calc ∑ i ∈ range M, 1 / ((i : ℝ) + 1) ≤ ∑ _i ∈ range M, (1 : ℝ) :=
        sum_le_sum fun i _ => by
          rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
    _ = M := by simp

/-- The recursion `H_{M+1} = H_M + 1/(M+1)`. -/
lemma harm_succ (M : ℕ) : harm (M + 1) = harm M + 1 / ((M : ℝ) + 1) := by
  unfold harm; rw [sum_range_succ]

/-- `∑_{a=1}^M 1/a = H_M`. -/
lemma sum_Icc_inv (M : ℕ) : ∑ a ∈ Icc 1 M, 1 / (a : ℝ) = harm M := by
  induction M with
  | zero => simp [harm]
  | succ M ih => rw [sum_Icc_succ_top (by omega), ih, harm_succ]; push_cast; ring

/-- `∑_{a=1}^M 1/(M+1-a) = H_M`. -/
lemma sum_Icc_inv_reflect (M : ℕ) :
    ∑ a ∈ Icc 1 M, 1 / ((M : ℝ) + 1 - a) = harm M := by
  rw [← sum_Icc_inv M]
  refine sum_nbij' (fun a => M + 1 - a) (fun a => M + 1 - a) ?_ ?_ ?_ ?_ ?_
  all_goals try (intro a ha; simp only [mem_Icc] at ha ⊢; omega)
  intro a ha
  simp only [mem_Icc] at ha
  rw [Nat.cast_sub (by omega)]; push_cast; ring

/-- The new column: `∑_{a=1}^M w(a, M+1) = 2 H_M/(M+1)²`. -/
lemma sum_w_top (M : ℕ) :
    ∑ a ∈ Icc 1 M, w a (M + 1) = 2 * harm M / ((M : ℝ) + 1) ^ 2 := by
  have key : ∀ a ∈ Icc 1 M, w a (M + 1) =
      (1 / ((M : ℝ) + 1) ^ 2) * (1 / (a : ℝ) + 1 / ((M : ℝ) + 1 - a)) := by
    intro a ha
    simp only [mem_Icc] at ha
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha.1
    have ha2 : (a : ℝ) ≤ M := by exact_mod_cast ha.2
    have h1 : (a : ℝ) ≠ 0 := by positivity
    have h2 : (M : ℝ) + 1 - a ≠ 0 := by linarith
    have h3 : (M : ℝ) + 1 ≠ 0 := by positivity
    unfold w
    push_cast
    rw [abs_of_neg (by linarith)]
    have h4 : -((a : ℝ) - (M + 1)) = (M : ℝ) + 1 - a := by ring
    rw [h4]
    field_simp
    ring
  rw [sum_congr rfl key, ← mul_sum, sum_add_distrib, sum_Icc_inv, sum_Icc_inv_reflect]
  ring

/-- Passing from `M` to `M+1` adds the new row and column, `2 ∑_{a=1}^M w(a, M+1)`. -/
lemma S_succ (M : ℕ) : S (M + 1) = S M + 2 * ∑ a ∈ Icc 1 M, w a (M + 1) := by
  unfold S
  simp only [sum_filter]
  have inner : ∀ a, (∑ m ∈ Icc 1 (M + 1), if m ≠ a then w a m else 0) =
      (∑ m ∈ Icc 1 M, if m ≠ a then w a m else 0) + if M + 1 ≠ a then w a (M + 1) else 0 :=
    fun a => sum_Icc_succ_top (by omega) _
  rw [sum_Icc_succ_top (by omega)]
  simp_rw [inner]
  rw [sum_add_distrib]
  have c1 : (∑ a ∈ Icc 1 M, if M + 1 ≠ a then w a (M + 1) else 0) =
      ∑ a ∈ Icc 1 M, w a (M + 1) :=
    sum_congr rfl fun a ha => by simp only [mem_Icc] at ha; rw [if_pos (by omega)]
  have c2 : (∑ m ∈ Icc 1 M, if m ≠ M + 1 then w (M + 1) m else 0) =
      ∑ a ∈ Icc 1 M, w a (M + 1) :=
    sum_congr rfl fun a ha => by
      simp only [mem_Icc] at ha; rw [if_pos (by omega), w_comm]
  rw [c1, c2]
  simp
  ring

/-- The exact identity `∑_{a ≠ m ≤ M} 1/(a m |a - m|) = 4 ∑_{n<M} H_n/(n+1)²`. -/
theorem S_eq (M : ℕ) : S M = ∑ n ∈ range M, 4 * harm n / ((n : ℝ) + 1) ^ 2 := by
  induction M with
  | zero => simp [S]
  | succ M ih =>
    rw [S_succ, ih, sum_w_top, sum_range_succ]
    ring

/-- Telescoping bound `∑_{n<M} H_n/(n+1)² ≤ 2 - (H_M + 2)/(M+1)`. -/
lemma tele (M : ℕ) :
    ∑ n ∈ range M, harm n / ((n : ℝ) + 1) ^ 2 ≤ 2 - (harm M + 2) / ((M : ℝ) + 1) := by
  induction M with
  | zero => simp [harm]
  | succ M ih =>
    rw [sum_range_succ, harm_succ]
    have h0 := harm_nonneg M
    have h1 := harm_le M
    have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    push_cast
    have key : (harm M + 2) / ((M : ℝ) + 1)
        - (harm M + 1 / ((M : ℝ) + 1) + 2) / ((M : ℝ) + 1 + 1)
        - harm M / ((M : ℝ) + 1) ^ 2
        = ((M : ℝ) + 1 - harm M) / (((M : ℝ) + 1) ^ 2 * ((M : ℝ) + 2)) := by
      field_simp
      ring
    have hnn : 0 ≤ ((M : ℝ) + 1 - harm M) / (((M : ℝ) + 1) ^ 2 * ((M : ℝ) + 2)) :=
      div_nonneg (by linarith) (by positivity)
    linarith

/-- For every `M`, `∑_{a ≠ m, 1 ≤ a, m ≤ M} 1/(a m |a - m|) ≤ 8`. -/
theorem offDiag_sum_le (M : ℕ) :
    ∑ a ∈ Finset.Icc 1 M, ∑ m ∈ (Finset.Icc 1 M).filter (· ≠ a),
      1 / ((a : ℝ) * m * |(a : ℝ) - m|) ≤ 8 := by
  show S M ≤ 8
  rw [S_eq]
  have h := tele M
  have hpos : 0 ≤ (harm M + 2) / ((M : ℝ) + 1) := by
    have := harm_nonneg M; positivity
  have : ∑ n ∈ range M, 4 * harm n / ((n : ℝ) + 1) ^ 2
      = 4 * ∑ n ∈ range M, harm n / ((n : ℝ) + 1) ^ 2 := by
    rw [mul_sum]; exact sum_congr rfl fun n _ => by ring
  rw [this]
  linarith

end Cvs.Upstream.OffDiagonalHarmonicSum
