import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The weight of the modes on a plateau supported in `(19/20, 3/2)`

A point `u` of the bulk is sampled by the mode `m ≥ 2` of a weight supported in `(19/20, 3/2)` exactly when
`19m/20 < u < 3m/2`, with weight `1/m`. For `u ≤ 6` the modes are listed case by case (at most `{2, 3}`, `{3, 4}`,
`{4, 5, 6}`, …) and for `u > 6` they number at most `22u/57 + 1`, each at least `2u/3`, so the weights sum to at
most `5/6` for every `u`: the edge weight of the cutoff route.
-/

namespace Cvs.L2a.PlateauModeWeight

open Finset

/-- The modes sampling `u` through a weight supported in `(19/20, 3/2)`. -/
noncomputable def plateauModes (M : ℕ) (u : ℝ) : Finset ℕ :=
  (Finset.Icc 2 M).filter fun m => 19 * (m : ℝ) / 20 < u ∧ u < 3 * m / 2

theorem mem_plateauModes {M : ℕ} {u : ℝ} {m : ℕ} :
    m ∈ plateauModes M u ↔ (2 ≤ m ∧ m ≤ M) ∧ 19 * (m : ℝ) / 20 < u ∧ u < 3 * m / 2 := by
  simp [plateauModes, Finset.mem_filter, Finset.mem_Icc]

/-- A natural strictly between `a₀ − 1` and `b₀ + 1` lies in `[a₀, b₀]`. -/
theorem mem_Icc_of_bounds {m a₀ b₀ : ℕ} (h1 : (a₀ : ℝ) - 1 < m) (h2 : (m : ℝ) < b₀ + 1) : m ∈ Finset.Icc a₀ b₀ := by
  rw [Finset.mem_Icc]
  constructor
  · have : (a₀ : ℝ) < m + 1 := by linarith
    have : a₀ < m + 1 := by exact_mod_cast this
    omega
  · have : m < b₀ + 1 := by exact_mod_cast h2
    omega

/-- The sum of the weights over a superset `[a₀, b₀]` bounds the sum over the modes. -/
theorem sum_le_of_subset {M : ℕ} {u : ℝ} {a₀ b₀ : ℕ} (h : plateauModes M u ⊆ Finset.Icc a₀ b₀) :
    ∑ m ∈ plateauModes M u, (1 : ℝ) / m ≤ ∑ m ∈ Finset.Icc a₀ b₀, (1 : ℝ) / m :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun m _ _ => by positivity

/-- **The plateau weight is at most `5/6`**: `Σ_{m ∈ plateauModes M u} 1/m ≤ 5/6` for every `u > 0`. -/
theorem plateau_weight_le (M : ℕ) {u : ℝ} (hu : 0 < u) : ∑ m ∈ plateauModes M u, (1 : ℝ) / m ≤ 5 / 6 := by
  -- the bounds every mode obeys: `2u/3 < m < 20u/19`, `m ≥ 2`
  have hb : ∀ m ∈ plateauModes M u, (2 : ℝ) ≤ m ∧ 2 * u / 3 < m ∧ (m : ℝ) < 20 * u / 19 := fun m hm => by
    rw [mem_plateauModes] at hm
    refine ⟨by exact_mod_cast hm.1.1, by linarith [hm.2.2], by linarith [hm.2.1]⟩
  -- a case with explicit endpoints
  have case : ∀ (a₀ b₀ : ℕ), ((a₀ : ℝ) - 1 ≤ 2 * u / 3 ∨ a₀ ≤ 2) → 20 * u / 19 ≤ b₀ + 1 →
      ∑ m ∈ plateauModes M u, (1 : ℝ) / m ≤ ∑ m ∈ Finset.Icc a₀ b₀, (1 : ℝ) / m := fun a₀ b₀ ha hb' => by
    apply sum_le_of_subset
    intro m hm
    obtain ⟨h2, hlo, hhi⟩ := hb m hm
    apply mem_Icc_of_bounds _ (by linarith)
    rcases ha with ha | ha
    · linarith
    · have : (a₀ : ℝ) ≤ 2 := by exact_mod_cast ha
      linarith
  rcases le_or_gt u (19 / 10) with h1 | h1
  · -- no mode: `m < 2`
    calc _ ≤ ∑ m ∈ Finset.Icc (2 : ℕ) 1, (1 : ℝ) / (m : ℝ) := case 2 1 (Or.inr le_rfl) (by norm_num; linarith)
      _ = 0 := by simp
      _ ≤ 5 / 6 := by norm_num
  rcases le_or_gt u (57 / 20) with h2 | h2
  · calc _ ≤ ∑ m ∈ Finset.Icc (2 : ℕ) 2, (1 : ℝ) / (m : ℝ) := case 2 2 (Or.inr le_rfl) (by norm_num; linarith)
      _ ≤ 5 / 6 := by norm_num
  rcases le_or_gt u 3 with h3 | h3
  · calc _ ≤ ∑ m ∈ Finset.Icc (2 : ℕ) 3, (1 : ℝ) / (m : ℝ) := case 2 3 (Or.inr le_rfl) (by norm_num; linarith)
      _ ≤ 5 / 6 := by rw [show Finset.Icc (2 : ℕ) 3 = {2, 3} by decide]; norm_num
  rcases le_or_gt u (19 / 5) with h4 | h4
  · calc _ ≤ ∑ m ∈ Finset.Icc (3 : ℕ) 3, (1 : ℝ) / (m : ℝ) := case 3 3 (Or.inl (by norm_num; linarith)) (by norm_num; linarith)
      _ ≤ 5 / 6 := by norm_num
  rcases le_or_gt u (9 / 2) with h5 | h5
  · calc _ ≤ ∑ m ∈ Finset.Icc (3 : ℕ) 4, (1 : ℝ) / (m : ℝ) := case 3 4 (Or.inl (by norm_num; linarith)) (by norm_num; linarith)
      _ ≤ 5 / 6 := by rw [show Finset.Icc (3 : ℕ) 4 = {3, 4} by decide]; norm_num
  rcases le_or_gt u (19 / 4) with h6 | h6
  · calc _ ≤ ∑ m ∈ Finset.Icc (4 : ℕ) 4, (1 : ℝ) / (m : ℝ) := case 4 4 (Or.inl (by norm_num; linarith)) (by norm_num; linarith)
      _ ≤ 5 / 6 := by norm_num
  rcases le_or_gt u (57 / 10) with h7 | h7
  · calc _ ≤ ∑ m ∈ Finset.Icc (4 : ℕ) 5, (1 : ℝ) / (m : ℝ) := case 4 5 (Or.inl (by norm_num; linarith)) (by norm_num; linarith)
      _ ≤ 5 / 6 := by rw [show Finset.Icc (4 : ℕ) 5 = {4, 5} by decide]; norm_num
  rcases le_or_gt u 6 with h8 | h8
  · calc _ ≤ ∑ m ∈ Finset.Icc (4 : ℕ) 6, (1 : ℝ) / (m : ℝ) := case 4 6 (Or.inl (by norm_num; linarith)) (by norm_num; linarith)
      _ ≤ 5 / 6 := by rw [show Finset.Icc (4 : ℕ) 6 = {4, 5, 6} by decide]; norm_num
  -- `u > 6`: at most `22u/57 + 1` modes, each at least `2u/3`
  have hsub : plateauModes M u ⊆ Finset.Ico (⌊2 * u / 3⌋₊ + 1) ⌈20 * u / 19⌉₊ := by
    intro m hm
    obtain ⟨_, hlo, hhi⟩ := hb m hm
    rw [Finset.mem_Ico]
    constructor
    · have : ⌊2 * u / 3⌋₊ < m := (Nat.floor_lt (by positivity)).mpr hlo
      omega
    · exact Nat.lt_ceil.mpr hhi
  have hcard : ((plateauModes M u).card : ℝ) ≤ 22 * u / 57 + 1 := by
    have h := Finset.card_le_card hsub
    rw [Nat.card_Ico] at h
    have hle : ⌊2 * u / 3⌋₊ + 1 ≤ ⌈20 * u / 19⌉₊ := by
      have : ⌊2 * u / 3⌋₊ < ⌈20 * u / 19⌉₊ :=
        Nat.lt_ceil.mpr (by linarith [Nat.floor_le (by positivity : (0 : ℝ) ≤ 2 * u / 3)])
      omega
    have h4 : ((plateauModes M u).card : ℝ) ≤ ((⌈20 * u / 19⌉₊ - (⌊2 * u / 3⌋₊ + 1) : ℕ) : ℝ) := by exact_mod_cast h
    rw [Nat.cast_sub hle] at h4
    push_cast at h4
    have hc : (⌈20 * u / 19⌉₊ : ℝ) < 20 * u / 19 + 1 := Nat.ceil_lt_add_one (by positivity)
    have hf : 2 * u / 3 - 1 < ⌊2 * u / 3⌋₊ := by linarith [Nat.lt_floor_add_one (2 * u / 3)]
    linarith
  calc ∑ m ∈ plateauModes M u, (1 : ℝ) / m ≤ ∑ _m ∈ plateauModes M u, 3 / (2 * u) := by
        apply Finset.sum_le_sum
        intro m hm
        obtain ⟨_, hlo, _⟩ := hb m hm
        rw [div_le_div_iff₀ (by linarith) (by positivity)]
        linarith
    _ = (plateauModes M u).card * (3 / (2 * u)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (22 * u / 57 + 1) * (3 / (2 * u)) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 11 / 19 + 3 / (2 * u) := by field_simp; ring
    _ ≤ 5 / 6 := by
        have : 3 / (2 * u) ≤ 1 / 4 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
        linarith

end Cvs.L2a.PlateauModeWeight
