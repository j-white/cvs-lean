import Mathlib
import Cvs.L2a.ModeTailPrimeSideExactRoot
import Cvs.L2a.NonstationaryPairsAllShifts
import Cvs.L2a.NonstationaryPairsOneShift
import Cvs.L2a.PrimeResonanceSum
import Cvs.L2a.SigmaFreeWeightedPairTotal
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.TailModesPrimeSideBound
import Cvs.L2a.TailOfModes
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
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
# The prime side of the tail of `M` modes, `σ`-free, for every `χ < c²`

`ModeTailPrimeSideExactRoot`'s columns (`σ`-free resonant and non-resonant pairs) with `SigmaFreeWeightedPairTotal`'s stationary sum: the prime side of the tail is at
most `2(S + (G/((3/4)c))(π²/6)Σ Λ(n)/n² + (8G(2/√3)/c²)·36(π²/6+6))`, `S` `SigmaFreeWeightedPairTotal`'s bound, with no `σ` anywhere.
-/

namespace Cvs.L2a.ModeTailPrimeSideSigmaFree

open Real Set ArithmeticFunction Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.TailOfModes
open Cvs.L2a.TailModesPrimeSideBound (primeSide_eq_image)
open Cvs.L2a.ModeTailPrimeSideExactRoot (column_le cross_term_le)

/-- **The prime side of the tail of `M` modes, `σ`-free, for every `χ < c²`.** -/
theorem primeSide_tail_le {c χ G K Ξ b s : ℝ} {ψ u : ℝ → ℝ} (P R N M : ℕ)
    (hc : 1 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hs1 : 1 ≤ s) (hsc : s ^ 2 * ((c ^ 2 - χ) / c ^ 2) ≤ c)
    (hidx : Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R ⊆ Finset.Icc 2 N)
    (hrb : (N : ℝ) + 2 ≤ b) (hΞ : (M : ℝ) * b ≤ Ξ)
    (hψ : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hG : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χ) ψ u ξ ≤ G) (hG0 : 0 ≤ G)
    (hcont : ContinuousOn ψ (Icc 1 Ξ)) (hedge : ∀ ξ ∈ Icc 1 Ξ, |ψ ξ| ≤ |ψ 1|) (hedge1 : ψ 1 ^ 2 ≤ K * G) :
    Cvs.Zeta.Explicit.Weil.primePowerSideTruncated P R
        (Cvs.Zeta.Explicit.Weil.selfConvolution (Cvs.L2a.TailLogScaleTest.logScale (tailF ψ M b)))
      ≤ 2 * (G * (Cvs.L2a.SigmaFreeWeightedPairTotal.C1 c χ K s * (π ^ 2 / 6) * ∑' n : ℕ, Λ n / (n : ℝ) ^ 2
            + 3 * Cvs.L2a.SigmaFreeWeightedPairTotal.C3 c s * ∑' n : ℕ, Λ n / ((n : ℝ) * √n)
            + Cvs.L2a.SigmaFreeWeightedPairTotal.Hc c χ K s * (log (Cvs.L2a.SigmaFreeWeightedPairTotal.sp c χ s)
              * (1 + log (Cvs.L2a.SigmaFreeWeightedPairTotal.sp c χ s)) ^ 2))
        + G / (3 / 4 * c) * (π ^ 2 / 6) * ∑' n : ℕ, Λ n / (n : ℝ) ^ 2
        + 8 * G * (2 / √3) / c ^ 2 * (36 * (π ^ 2 / 6 + 6))) := by
  have hc0 : 0 < c := by linarith
  set α := 3 / 4 * c with hα
  have hα0 : 0 < α := by positivity
  set κs := 2 / √3 with hκs
  have hκ0 : 0 ≤ κs := by positivity
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [primeSide_eq_image _ (tailF_zero ψ M b)]
  set I : ℕ → ℝ := fun k => ∫ θ in Ioi 1, tailF ψ M b θ * tailF ψ M b (k * θ) with hI
  set S : ℕ → ℝ := fun k => ∑ m' ∈ Finset.Icc 1 M, |∫ t in (k : ℝ)..b, ψ (m' * t) * ψ (1 / k * t)| with hS
  set Nr : ℕ → ℝ := fun k => ∑ m' ∈ Finset.Icc 1 M, ∑ m ∈ (Finset.Icc 1 M).erase (k * m'),
    1 / ((m' : ℝ) * m * |((k * m' : ℕ) : ℝ) - m|) with hNr
  -- one prime term
  have hterm : ∀ k ∈ Finset.Icc 2 N, 2 * Λ k * |I k|
      ≤ 2 * (Λ k / k * S k + G / α * (π ^ 2 / 6) * (Λ k / (k : ℝ) ^ 2) + 8 * G * κs / c ^ 2 * (Λ k / k * Nr k)) := by
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkN : (k : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hk).2
    have hk0 : (0 : ℝ) < k := by have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
                                 linarith
    have hΛ : 0 ≤ Λ k := vonMangoldt_nonneg
    have key := cross_term_le (k := k) (M := M) hc0 hχ0 hχ hχ0 hχ hk2 (by linarith) hΞ hψ hu hψ hu hG hG hG0 hcont hcont
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at key
    have hres : ∑ m' ∈ Finset.Icc 1 M, G / (α * ((k : ℝ) * m') ^ 2)
        ≤ G / α * (π ^ 2 / 6) * (1 / (k : ℝ) ^ 2) := by
      have e : ∀ m' ∈ Finset.Icc 1 M, G / (α * ((k : ℝ) * m') ^ 2) = G / α / (k : ℝ) ^ 2 * (1 / (m' : ℝ) ^ 2) := by
        intro m' hm'
        have : (0 : ℝ) < m' := by exact_mod_cast (Finset.mem_Icc.mp hm').1
        field_simp
      rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
      calc G / α / (k : ℝ) ^ 2 * ∑ m' ∈ Finset.Icc 1 M, 1 / (m' : ℝ) ^ 2
          ≤ G / α / (k : ℝ) ^ 2 * (π ^ 2 / 6) :=
            mul_le_mul_of_nonneg_left (Cvs.L2a.NonstationaryPairsOneShift.sum_inv_sq_le M) (by positivity)
        _ = _ := by field_simp
    have hnr : ∑ m' ∈ Finset.Icc 1 M, ∑ m ∈ (Finset.Icc 1 M).erase (k * m'),
        8 * G * κs / c ^ 2 * (1 / ((m' : ℝ) * m * |((k * m' : ℕ) : ℝ) - m|)) = 8 * G * κs / c ^ 2 * Nr k := by
      rw [hNr]; simp only; rw [Finset.mul_sum]; congr 1; funext m'; rw [Finset.mul_sum]
    rw [hnr] at key
    have hIk : |I k| ≤ 1 / k * S k + G / α * (π ^ 2 / 6) * (1 / (k : ℝ) ^ 2) + 1 / k * (8 * G * κs / c ^ 2 * Nr k) := by
      have := key; rw [hS]; linarith
    calc 2 * Λ k * |I k| ≤ 2 * Λ k * (1 / k * S k + G / α * (π ^ 2 / 6) * (1 / (k : ℝ) ^ 2)
          + 1 / k * (8 * G * κs / c ^ 2 * Nr k)) := mul_le_mul_of_nonneg_left hIk (by positivity)
      _ = _ := by field_simp
  -- the three sums
  have hstat := Cvs.L2a.SigmaFreeWeightedPairTotal.stationary_total_le (ψ := ψ) (u := u) (K := K) N M hc hχ0 hχ hs1 hsc hrb hΞ
    hψ hu hG hG0 hcont hedge hedge1
  have hL2 := Cvs.L2a.PrimeResonanceSum.summable_vonMangoldt_div_sq.sum_le_tsum (Finset.Icc 2 N)
    (fun n _ => div_nonneg vonMangoldt_nonneg (by positivity))
  have hnon : ∑ k ∈ Finset.Icc 2 N, Λ k / k * Nr k ≤ 36 * (π ^ 2 / 6 + 6) := by
    refine le_trans ?_ (Cvs.L2a.NonstationaryPairsAllShifts.prime_pairs_le N M M)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
    · intro k _ _
      apply mul_nonneg (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k))
      apply Finset.sum_nonneg; intro m' _; apply Finset.sum_nonneg; intro m _; positivity
  calc ∑ k ∈ Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R, 2 * Λ k * I k
      ≤ ∑ k ∈ Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R, 2 * Λ k * |I k| :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (le_abs_self _)
          (by have := (vonMangoldt_nonneg : 0 ≤ Λ k); positivity)
    _ ≤ ∑ k ∈ Finset.Icc 2 N, 2 * Λ k * |I k| :=
        Finset.sum_le_sum_of_subset_of_nonneg hidx fun k _ _ =>
          by have := (vonMangoldt_nonneg : 0 ≤ Λ k); positivity
    _ ≤ ∑ k ∈ Finset.Icc 2 N, 2 * (Λ k / k * S k + G / α * (π ^ 2 / 6) * (Λ k / (k : ℝ) ^ 2)
          + 8 * G * κs / c ^ 2 * (Λ k / k * Nr k)) := Finset.sum_le_sum hterm
    _ = 2 * (∑ k ∈ Finset.Icc 2 N, Λ k / k * S k + G / α * (π ^ 2 / 6) * ∑ k ∈ Finset.Icc 2 N, Λ k / (k : ℝ) ^ 2
          + 8 * G * κs / c ^ 2 * ∑ k ∈ Finset.Icc 2 N, Λ k / k * Nr k) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        have h1 : ∑ k ∈ Finset.Icc 2 N, Λ k / k * S k ≤ _ := hstat
        exact add_le_add (add_le_add h1 (mul_le_mul_of_nonneg_left hL2 (by positivity)))
          (mul_le_mul_of_nonneg_left hnon (by positivity))

end Cvs.L2a.ModeTailPrimeSideSigmaFree
