import Mathlib
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.TailModesPrimeSideBound
import Cvs.WeilForm.PrimePowerIndexed
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The prime side of the position-truncated tail as pair sums

When the truncation reaches every prime power up to `X`, the prime side of the position-truncated tail of Cvs.L2a.PositionTruncatedTail is
`Σ_{a, n ≤ ⌊X⌋} 2 log n · ∫_1^{X/max(a,n)} Φ(aθ) Φ(nθ)`: `TailModesPrimeSideBound`'s prime-power sum, regrouped by `n = k m`, with
`Σ_{k ∣ n} Λ(k) = log n`.
-/

namespace Cvs.L2a.PositionTailPrimePairs

open Real Set Finset ArithmeticFunction Cvs.L2a.PositionTruncatedTail

/-- Every element of the truncation index `primePowIndex P R` is a prime power. -/
theorem isPrimePow_of_mem_primePowIndex {P R k : ℕ} (hk : k ∈ Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R) :
    IsPrimePow k := by
  obtain ⟨⟨p, r⟩, hpr, rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨hp, hr⟩ := Finset.mem_product.mp hpr
  exact ⟨p, r, (Finset.mem_filter.mp hp).2.prime, (Finset.mem_Icc.mp hr).1, rfl⟩

/-- Summing `f(d m)` over `m ≤ N` with `d m ≤ N` is summing `f n` over the multiples `n ≤ N` of `d`. -/
theorem sum_filter_mul_eq {d N : ℕ} (hd : 0 < d) (f : ℕ → ℝ) :
    ∑ m ∈ (Finset.Icc 1 N).filter (fun m => d * m ≤ N), f (d * m)
      = ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n), f n := by
  refine Finset.sum_nbij' (fun m => d * m) (fun n => n / d) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
    refine ⟨⟨?_, hm.2⟩, dvd_mul_right d m⟩
    nlinarith [hm.1.1]
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    obtain ⟨⟨hn1, hnN⟩, c, rfl⟩ := hn
    rw [Nat.mul_div_cancel_left c hd]
    refine ⟨⟨?_, ?_⟩, hnN⟩
    · rcases Nat.eq_zero_or_pos c with h | h
      · subst h; simp at hn1
      · exact h
    · exact le_trans (Nat.le_mul_of_pos_left c hd) hnN
  · intro m _
    exact Nat.mul_div_cancel_left m hd
  · intro n hn
    simp only [Finset.mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2
  · intro m _
    rfl

/-- If the index contains every prime power up to `N`, then `Σ_{k ∈ I} Λ(k) Σ_{m ≤ N, km ≤ N} f(km)` equals
`Σ_{n ≤ N} log n · f n`. -/
theorem sum_vonMangoldt_regroup {I : Finset ℕ} (hI : ∀ k ∈ I, IsPrimePow k) {N : ℕ}
    (hN : ∀ k : ℕ, IsPrimePow k → k ≤ N → k ∈ I) (f : ℕ → ℝ) :
    ∑ k ∈ I, Λ k * ∑ m ∈ (Finset.Icc 1 N).filter (fun m => k * m ≤ N), f (k * m)
      = ∑ n ∈ Finset.Icc 1 N, Real.log n * f n := by
  have hI0 : ∀ k ∈ I, 0 < k := fun k hk => (hI k hk).pos
  have h1 : ∀ k ∈ I, Λ k * ∑ m ∈ (Finset.Icc 1 N).filter (fun m => k * m ≤ N), f (k * m)
      = ∑ n ∈ (Finset.Icc 1 N).filter (fun n => k ∣ n), Λ k * f n := by
    intro k hk
    rw [sum_filter_mul_eq (hI0 k hk) f, Finset.mul_sum]
  rw [Finset.sum_congr rfl h1]
  have h2 : ∀ n ∈ Finset.Icc 1 N, Real.log n * f n = ∑ k ∈ I.filter (fun k => k ∣ n), Λ k * f n := by
    intro n hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    have hn0 : n ≠ 0 := by omega
    rw [← vonMangoldt_sum, Finset.sum_mul]
    symm
    refine Finset.sum_subset (fun k hk => ?_) (fun k hk hkI => ?_)
    · obtain ⟨hkI, hkn⟩ := Finset.mem_filter.mp hk
      exact Nat.mem_divisors.mpr ⟨hkn, hn0⟩
    · have hkn : k ∣ n := (Nat.mem_divisors.mp hk).1
      have hk' : ¬ IsPrimePow k := by
        intro hpp
        exact hkI (Finset.mem_filter.mpr ⟨hN k hpp ((Nat.le_of_dvd (by omega) hkn).trans hnN), hkn⟩)
      rw [vonMangoldt_eq_zero_iff.mpr hk', zero_mul]
  rw [Finset.sum_congr rfl h2]
  refine Finset.sum_comm' fun k n => ?_
  simp only [Finset.mem_filter]
  tauto

/-- When the truncation reaches every prime power up to `X`, the prime side of the position-truncated tail is
`Σ_{a, n ≤ ⌊X⌋} 2 log n · pairI Φ X a n`. -/
theorem primeSide_posTail (Φ : ℝ → ℝ) {X : ℝ} (hX : 1 ≤ X) (hcont : ContinuousOn Φ (Set.Icc 1 X)) (P R : ℕ)
    (hPR : ∀ k : ℕ, IsPrimePow k → (k : ℝ) ≤ X → k ∈ Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R) :
    Cvs.Zeta.Explicit.Weil.primePowerSideTruncated P R
        (Cvs.Zeta.Explicit.Weil.selfConvolution (Cvs.L2a.TailLogScaleTest.logScale (posTail Φ X)))
      = ∑ a ∈ Finset.Icc 1 ⌊X⌋₊, ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, 2 * Real.log n * pairI Φ X a n := by
  set I := Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R
  have hI : ∀ k ∈ I, IsPrimePow k := fun k hk => isPrimePow_of_mem_primePowIndex hk
  have hN : ∀ k : ℕ, IsPrimePow k → k ≤ ⌊X⌋₊ → k ∈ I := fun k hk hkN =>
    hPR k hk ((Nat.cast_le.mpr hkN).trans (Nat.floor_le (by linarith)))
  rw [Cvs.L2a.TailModesPrimeSideBound.primeSide_eq_image (posTail Φ X) (fun θ hθ => posTail_zero Φ X hθ) P R]
  have h1 : ∀ k ∈ I, 2 * Λ k * ∫ θ in Ioi 1, posTail Φ X θ * posTail Φ X (k * θ)
      = ∑ a ∈ Finset.Icc 1 ⌊X⌋₊, 2 * (Λ k * ∑ m ∈ (Finset.Icc 1 ⌊X⌋₊).filter (fun m => k * m ≤ ⌊X⌋₊),
          pairI Φ X a (k * m)) := by
    intro k hk
    rw [integral_posTail_mul_dilate Φ hX hcont (hI k hk).one_lt.le, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.mul_sum, sum_vonMangoldt_regroup hI hN (fun n => pairI Φ X a n), Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

end Cvs.L2a.PositionTailPrimePairs
