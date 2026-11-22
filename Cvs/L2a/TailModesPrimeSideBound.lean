import Mathlib
import Cvs.L2a.NonstationaryPairsAllShifts
import Cvs.L2a.NonstationaryPairsOneShift
import Cvs.L2a.PrimeResonanceSum
import Cvs.L2a.PrimeTermPairClassified
import Cvs.L2a.StationaryPairsWeightedTotal
import Cvs.L2a.TailLogScaleTest
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
# The prime side of the tail of `M` modes, bounded

Each prime term is at most the sum of its columns (Cvs.L2a.PrimeTermPairClassified). Weighted by `2Λ(k)` over every prime power the truncation
reaches, the prime side is at most `2(S_stat + (G/α)(π²/6)Σ Λ(n)/n² + (4G√κ/c²)·36(π²/6+6))`, `S_stat` the stationary
sum that Cvs.L2a.StationaryPairsWeightedTotal bounds.
-/

namespace Cvs.L2a.TailModesPrimeSideBound

open Real Set ArithmeticFunction Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.TailOfModes

/-- **One prime term**, by columns. -/
theorem prime_term_le {c χ G Ξ b : ℝ} {ψ u : ℝ → ℝ} {k M : ℕ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2)
    (hk : 2 ≤ k) (hkb : (k : ℝ) ≤ b) (hΞ : (M : ℝ) * b ≤ Ξ)
    (hψ : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hG : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χ) ψ u ξ ≤ G) (hG0 : 0 ≤ G)
    (hcont : ContinuousOn ψ (Icc 1 Ξ)) :
    |∫ θ in Ioi 1, tailF ψ M b θ * tailF ψ M b (k * θ)|
      ≤ ∑ m' ∈ Finset.Icc 1 M, (1 / k * |∫ t in (k : ℝ)..b, ψ (m' * t) * ψ (1 / k * t)|
        + G / (√3 / 2 * √(c ^ 2 - χ) * ((k : ℝ) * m') ^ 2)
        + 1 / k * ∑ m ∈ (Finset.Icc 1 M).erase (k * m'),
            4 * G * √(2 * c / (√3 * √(c ^ 2 - χ))) / c ^ 2
              * (1 / ((m' : ℝ) * m * |((k * m' : ℕ) : ℝ) - m|))) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hb1 : 1 ≤ b := hk'.trans hkb
  have hMb : (M : ℝ) * b ≤ Ξ := hΞ
  rw [integral_tailF_pair ψ ψ M hk' hkb (hcont.mono (Icc_subset_Icc le_rfl hMb)) (hcont.mono (Icc_subset_Icc le_rfl hMb))]
  calc |∑ m ∈ Finset.Icc 1 M, ∑ m' ∈ Finset.Icc 1 M, ∫ θ in (1 : ℝ)..b / k, ψ (m * θ) * ψ (m' * (k * θ))|
      ≤ ∑ m ∈ Finset.Icc 1 M, ∑ m' ∈ Finset.Icc 1 M, |∫ θ in (1 : ℝ)..b / k, ψ (m * θ) * ψ (m' * (k * θ))| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ m' ∈ Finset.Icc 1 M, ∑ m ∈ Finset.Icc 1 M, |∫ θ in (1 : ℝ)..b / k, ψ (m * θ) * ψ (m' * (k * θ))| :=
        Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum fun m' hm' =>
        Cvs.L2a.PrimeTermPairClassified.column_le hc hχ0 hχ hk hm' hkb hΞ hψ hu hG hG0 hcont

/-- The prime side of a tail is `Σ_k 2Λ(k) ∫F(θ)F(kθ)` over the prime powers reached. -/
theorem primeSide_eq_image (F : ℝ → ℝ) (hF : ∀ θ ≤ 1, F θ = 0) (P R : ℕ) :
    Cvs.Zeta.Explicit.Weil.primePowerSideTruncated P R (Cvs.Zeta.Explicit.Weil.selfConvolution (Cvs.L2a.TailLogScaleTest.logScale F))
      = ∑ k ∈ Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R, 2 * Λ k * ∫ θ in Ioi 1, F θ * F (k * θ) := by
  rw [Cvs.WeilForm.PrimePowerIndexed.primePowerSideTruncated_eq_image]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hk0 : k = 0
  · subst hk0; simp
  have hkp : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk0
  rw [Cvs.L2a.TailLogScaleTest.selfConvolution_neg_log, Cvs.L2a.TailLogScaleTest.selfConvolution_log F hF hkp]
  have hs : (k : ℝ) ^ (-(1 / 2) : ℝ) * √(k : ℝ) = 1 := by
    rw [sqrt_eq_rpow, ← rpow_add hkp]; norm_num
  calc Λ k * (k : ℝ) ^ (-(1 / 2) : ℝ) * (√(k : ℝ) * (∫ θ in Ioi 1, F θ * F (k * θ))
        + √(k : ℝ) * ∫ θ in Ioi 1, F θ * F (k * θ))
      = 2 * Λ k * ((k : ℝ) ^ (-(1 / 2) : ℝ) * √(k : ℝ)) * ∫ θ in Ioi 1, F θ * F (k * θ) := by ring
    _ = _ := by rw [hs, mul_one]

/-- **The prime side of the tail of `M` modes.** -/
theorem primeSide_tail_le {c χ G K Ξ b : ℝ} {ψ u : ℝ → ℝ} (P R N M : ℕ)
    (hc : 1 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hχs : χ ≤ c * √c)
    (hidx : Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R ⊆ Finset.Icc 2 N)
    (hrb : (N : ℝ) + 2 ≤ b) (hΞ : (M : ℝ) * b ≤ Ξ)
    (hψ : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hG : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χ) ψ u ξ ≤ G) (hG0 : 0 ≤ G) (hK : 0 ≤ K)
    (hcont : ContinuousOn ψ (Icc 1 Ξ)) (hedge : ∀ ξ ∈ Icc 1 Ξ, |ψ ξ| ≤ |ψ 1|) (hedge1 : ψ 1 ^ 2 ≤ K * G) :
    Cvs.Zeta.Explicit.Weil.primePowerSideTruncated P R
        (Cvs.Zeta.Explicit.Weil.selfConvolution (Cvs.L2a.TailLogScaleTest.logScale (tailF ψ M b)))
      ≤ 2 * (G * ((4 * Cvs.L2a.StationaryPairsWeightedTotal.Aw c χ K / √c + 16 * Cvs.L2a.StationaryPairsWeightedTotal.κw c χ * √c / c ^ 2
              + 16 * Cvs.L2a.StationaryPairsWeightedTotal.κw c χ / (3 * c)) * (π ^ 2 / 6) * ∑' n : ℕ, Λ n / (n : ℝ) ^ 2
            + 48 * Cvs.L2a.StationaryPairsWeightedTotal.κw c χ * √(√c) / c ^ 2 * ∑' n : ℕ, Λ n / ((n : ℝ) * √n)
            + (Cvs.L2a.StationaryPairsWeightedTotal.Aw c χ K / c + 2 * Cvs.L2a.StationaryPairsWeightedTotal.Qw c χ / √c)
              * (log √c * (1 + log √c) ^ 2))
        + G / (√3 / 2 * √(c ^ 2 - χ)) * (π ^ 2 / 6) * ∑' n : ℕ, Λ n / (n : ℝ) ^ 2
        + 4 * G * √(2 * c / (√3 * √(c ^ 2 - χ))) / c ^ 2 * (36 * (π ^ 2 / 6 + 6))) := by
  have hc0 : 0 < c := by linarith
  have hd : 0 < c ^ 2 - χ := by linarith
  set α := √3 / 2 * √(c ^ 2 - χ) with hα
  have hα0 : 0 < α := by positivity
  set κs := √(2 * c / (√3 * √(c ^ 2 - χ))) with hκs
  have hκ0 : 0 ≤ κs := sqrt_nonneg _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [primeSide_eq_image _ (tailF_zero ψ M b)]
  set I : ℕ → ℝ := fun k => ∫ θ in Ioi 1, tailF ψ M b θ * tailF ψ M b (k * θ) with hI
  set S : ℕ → ℝ := fun k => ∑ m' ∈ Finset.Icc 1 M, |∫ t in (k : ℝ)..b, ψ (m' * t) * ψ (1 / k * t)| with hS
  set Nr : ℕ → ℝ := fun k => ∑ m' ∈ Finset.Icc 1 M, ∑ m ∈ (Finset.Icc 1 M).erase (k * m'),
    1 / ((m' : ℝ) * m * |((k * m' : ℕ) : ℝ) - m|) with hNr
  -- one prime term
  have hterm : ∀ k ∈ Finset.Icc 2 N, 2 * Λ k * |I k|
      ≤ 2 * (Λ k / k * S k + G / α * (π ^ 2 / 6) * (Λ k / (k : ℝ) ^ 2) + 4 * G * κs / c ^ 2 * (Λ k / k * Nr k)) := by
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkN : (k : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hk).2
    have hk0 : (0 : ℝ) < k := by have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
                                 linarith
    have hΛ : 0 ≤ Λ k := vonMangoldt_nonneg
    have key := prime_term_le (k := k) (M := M) hc0 hχ0 hχ hk2 (by linarith) hΞ hψ hu hG hG0 hcont
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
        4 * G * κs / c ^ 2 * (1 / ((m' : ℝ) * m * |((k * m' : ℕ) : ℝ) - m|)) = 4 * G * κs / c ^ 2 * Nr k := by
      rw [hNr]; simp only; rw [Finset.mul_sum]; congr 1; funext m'; rw [Finset.mul_sum]
    rw [hnr] at key
    have hIk : |I k| ≤ 1 / k * S k + G / α * (π ^ 2 / 6) * (1 / (k : ℝ) ^ 2) + 1 / k * (4 * G * κs / c ^ 2 * Nr k) := by
      have := key; rw [hS]; linarith
    calc 2 * Λ k * |I k| ≤ 2 * Λ k * (1 / k * S k + G / α * (π ^ 2 / 6) * (1 / (k : ℝ) ^ 2)
          + 1 / k * (4 * G * κs / c ^ 2 * Nr k)) := mul_le_mul_of_nonneg_left hIk (by positivity)
      _ = _ := by field_simp
  -- the three sums
  have hstat := Cvs.L2a.StationaryPairsWeightedTotal.stationary_total_le (ψ := ψ) (u := u) N M hc hχ0 hχ hχs hrb hΞ
    hψ hu hG hG0 hK hcont hedge hedge1
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
          + 4 * G * κs / c ^ 2 * (Λ k / k * Nr k)) := Finset.sum_le_sum hterm
    _ = 2 * (∑ k ∈ Finset.Icc 2 N, Λ k / k * S k + G / α * (π ^ 2 / 6) * ∑ k ∈ Finset.Icc 2 N, Λ k / (k : ℝ) ^ 2
          + 4 * G * κs / c ^ 2 * ∑ k ∈ Finset.Icc 2 N, Λ k / k * Nr k) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        have h1 : ∑ k ∈ Finset.Icc 2 N, Λ k / k * S k ≤ _ := hstat
        exact add_le_add (add_le_add h1 (mul_le_mul_of_nonneg_left hL2 (by positivity)))
          (mul_le_mul_of_nonneg_left hnon (by positivity))

end Cvs.L2a.TailModesPrimeSideBound
