import Mathlib
import Cvs.L2a.PrimePairingResonantSplit

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The resonant prime channel is at most the log-weighted mode masses

The resonant pairs at `k` are the modes `n ≤ M` with `k ∣ n` (Cvs.L2a.PrimePairingResonantSplit), each resonant tail energy is at most the
diagonal mass `∫_1^b Φ(nθ)² dθ` of its mode, and `Σ_{k ∣ n} Λ(k) = log n`: so for any set of prime powers `k ≤ b`,
`Σ_k 2Λ(k) resPart(k) ≤ Σ_{n ≤ M} 2 log n · ∫_1^b Φ(nθ)² dθ`, with no hypothesis on `Φ` but continuity.
-/

namespace Cvs.L2a.ResonantChannelModeMasses

open Real Set MeasureTheory ArithmeticFunction
open Cvs.L2a.TailOfModes Cvs.L2a.PrimePairingResonantSplit

/-- The diagonal mass of mode `n` of a tail: `∫_1^b Φ(nθ)² dθ`. -/
noncomputable def modeMass (Φ : ℝ → ℝ) (b : ℝ) (n : ℕ) : ℝ :=
  ∫ θ in (1 : ℝ)..b, Φ ((n : ℝ) * θ) ^ 2

/-- The resonant pairs at `k` are the modes `n ≤ M` with `k ∣ n`, paired with `n / k`. -/
theorem resPairs_eq_image (M : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    resPairs M k = ((Finset.Icc 1 M).filter (fun n => k ∣ n)).image (fun n => (n, n / k)) := by
  ext ⟨m, m'⟩
  simp only [resPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨⟨hm1, hmM⟩, ⟨hm'1, _⟩⟩, hres⟩
    refine ⟨m, ⟨⟨hm1, hmM⟩, ⟨m', by rw [hres]⟩⟩, rfl, ?_⟩
    rw [hres, Nat.mul_div_cancel_left m' (by omega)]
  · rintro ⟨n, ⟨⟨hn1, hnM⟩, hdvd⟩, rfl, rfl⟩
    have hnk : n = k * (n / k) := (Nat.mul_div_cancel' hdvd).symm
    have hpos : 1 ≤ n / k := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) (by omega)
    exact ⟨⟨⟨hn1, hnM⟩, ⟨hpos, (Nat.div_le_self n k).trans hnM⟩⟩, hnk⟩

/-- **The resonant part at `k` is at most the masses of the modes `k ∣ n`.** -/
theorem resPart_le_modeMasses (Φ : ℝ → ℝ) (M : ℕ) {b : ℝ} {k : ℕ} (hk : 1 ≤ k) (hkb : (k : ℝ) ≤ b)
    (hcont : ContinuousOn Φ (Icc 1 (M * b))) :
    resPart Φ M b k ≤ ∑ n ∈ (Finset.Icc 1 M).filter (fun n => k ∣ n), modeMass Φ b n := by
  have hb : (1 : ℝ) ≤ b := le_trans (by exact_mod_cast hk) hkb
  unfold resPart
  rw [resPairs_eq_image M hk, Finset.sum_image (fun n _ n' _ h => ((Prod.mk.injEq _ _ _ _).mp h).1)]
  apply Finset.sum_le_sum
  intro n hn
  rw [Finset.mem_filter, Finset.mem_Icc] at hn
  obtain ⟨⟨hn1, hnM⟩, hdvd⟩ := hn
  have hnk : n = k * (n / k) := (Nat.mul_div_cancel' hdvd).symm
  have hm'1 : 1 ≤ n / k := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) (by omega)
  have hcast : ((k : ℝ) * ((n / k : ℕ) : ℝ)) = (n : ℝ) := by
    rw [← Nat.cast_mul, ← hnk]
  have hint : IntervalIntegrable (fun ξ => Φ ξ ^ 2) volume ((k : ℝ) * ((n / k : ℕ) : ℝ))
      ((k : ℝ) * ((n / k : ℕ) : ℝ) * b) := by
    rw [hcast]
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hnM' : (n : ℝ) ≤ M := by exact_mod_cast hnM
    have hsub : Icc (n : ℝ) (n * b) ⊆ Icc 1 (M * b) := fun ξ hξ =>
      ⟨le_trans hn1' hξ.1, le_trans hξ.2 (mul_le_mul_of_nonneg_right hnM' (by linarith))⟩
    exact ((hcont.mono hsub).pow 2).intervalIntegrable_of_Icc (by nlinarith)
  have := resonant_le_mode_mass Φ hk hm'1 hkb hint
  unfold modeMass
  rw [← hcast]
  exact this

/-- **The resonant prime channel is at most the log-weighted mode masses**: for prime powers `1 ≤ k ≤ b` in `S`,
`Σ_{k ∈ S} 2Λ(k) resPart(k) ≤ Σ_{n ≤ M} 2 log n · ∫_1^b Φ(nθ)² dθ`. -/
theorem resonant_total_le (Φ : ℝ → ℝ) (M : ℕ) {b : ℝ} (S : Finset ℕ) (hS : ∀ k ∈ S, 1 ≤ k ∧ (k : ℝ) ≤ b)
    (hcont : ContinuousOn Φ (Icc 1 (M * b))) (hmass : ∀ n ∈ Finset.Icc 1 M, 0 ≤ modeMass Φ b n) :
    ∑ k ∈ S, 2 * Λ k * resPart Φ M b k ≤ ∑ n ∈ Finset.Icc 1 M, 2 * Real.log n * modeMass Φ b n := by
  calc ∑ k ∈ S, 2 * Λ k * resPart Φ M b k
      ≤ ∑ k ∈ S, 2 * Λ k * ∑ n ∈ (Finset.Icc 1 M).filter (fun n => k ∣ n), modeMass Φ b n := by
        apply Finset.sum_le_sum
        intro k hk
        exact mul_le_mul_of_nonneg_left (resPart_le_modeMasses Φ M (hS k hk).1 (hS k hk).2 hcont)
          (by have := vonMangoldt_nonneg (n := k); linarith)
    _ = ∑ n ∈ Finset.Icc 1 M, (∑ k ∈ S.filter (fun k => k ∣ n), 2 * Λ k) * modeMass Φ b n := by
        simp_rw [Finset.mul_sum, Finset.sum_filter, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro n _
        apply Finset.sum_congr rfl; intro k _
        split_ifs <;> simp
    _ ≤ ∑ n ∈ Finset.Icc 1 M, 2 * Real.log n * modeMass Φ b n := by
        apply Finset.sum_le_sum
        intro n hn
        apply mul_le_mul_of_nonneg_right _ (hmass n hn)
        rw [Finset.mem_Icc] at hn
        rw [← Finset.mul_sum, ← vonMangoldt_sum]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          rw [Finset.mem_filter] at hk
          rw [Nat.mem_divisors]
          exact ⟨hk.2, by omega⟩
        · intro k _ _
          exact vonMangoldt_nonneg

end Cvs.L2a.ResonantChannelModeMasses
