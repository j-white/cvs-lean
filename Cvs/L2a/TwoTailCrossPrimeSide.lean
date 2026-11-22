import Mathlib
import Cvs.L2a.NonstationaryPairsAllShifts
import Cvs.L2a.NonstationaryPairsOneShift
import Cvs.L2a.PrimeResonanceSum
import Cvs.L2a.StationaryPairsWeightedTotal
import Cvs.L2a.TailOfModes
import Cvs.L2a.TwoProlateCrossColumn
import Cvs.L2a.TwoProlateWeightedPairTotal
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.WeilForm.PrimePowerIndexed

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The cross prime side of two tails, bounded

For tails `F_a, F_b` of `M` modes of two prolates with `χ_a, χ_b ≤ χ_m`, each cross prime term
`|∫F_a(θ)F_b(kθ)|` is at most the sum of its cross columns (Cvs.L2a.TwoProlateCrossColumn). Weighted by `2Λ(k)` over every prime power the
truncation reaches, the total is at most `2(S + (G/α_m)(π²/6)Σ Λ(n)/n² + (8G√κ_m/c²)·36(π²/6+6))`, `S` the stationary
sum of Cvs.L2a.TwoProlateWeightedPairTotal with the roles of `ψ_a` and `ψ_b` exchanged.
-/

namespace Cvs.L2a.TwoTailCrossPrimeSide

open Real Set ArithmeticFunction Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.TailOfModes

/-- **One cross prime term**, by columns. -/
theorem cross_term_le {c χa χb χm G Ξ b : ℝ} {ψa ua ψb ub : ℝ → ℝ} {k M : ℕ} (hc : 0 < c)
    (hχa0 : 0 ≤ χa) (hχam : χa ≤ χm) (hχb0 : 0 ≤ χb) (hχbm : χb ≤ χm) (hχm : χm < c ^ 2)
    (hk : 2 ≤ k) (hkb : (k : ℝ) ≤ b) (hΞ : (M : ℝ) * b ≤ Ξ)
    (hψa : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψa (ua ξ / pP ξ) ξ)
    (hua : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ua (-(qP c χa ξ * ψa ξ)) ξ)
    (hψb : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψb (ub ξ / pP ξ) ξ)
    (hub : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ub (-(qP c χb ξ * ψb ξ)) ξ)
    (hGa : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χa) ψa ua ξ ≤ G) (hGb : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χb) ψb ub ξ ≤ G) (hG0 : 0 ≤ G)
    (hconta : ContinuousOn ψa (Icc 1 Ξ)) (hcontb : ContinuousOn ψb (Icc 1 Ξ)) :
    |∫ θ in Ioi 1, tailF ψa M b θ * tailF ψb M b (k * θ)|
      ≤ ∑ m' ∈ Finset.Icc 1 M, (1 / k * |∫ t in (k : ℝ)..b, ψb (m' * t) * ψa (1 / k * t)|
        + G / (√3 / 2 * √(c ^ 2 - χm) * ((k : ℝ) * m') ^ 2)
        + 1 / k * ∑ m ∈ (Finset.Icc 1 M).erase (k * m'),
            8 * G * √(2 * c / (√3 * √(c ^ 2 - χm))) / c ^ 2
              * (1 / ((m' : ℝ) * m * |((k * m' : ℕ) : ℝ) - m|))) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hb1 : 1 ≤ b := hk'.trans hkb
  have hMb : (M : ℝ) * b ≤ Ξ := hΞ
  rw [integral_tailF_pair ψa ψb M hk' hkb (hconta.mono (Icc_subset_Icc le_rfl hMb)) (hcontb.mono (Icc_subset_Icc le_rfl hMb))]
  calc |∑ m ∈ Finset.Icc 1 M, ∑ m' ∈ Finset.Icc 1 M, ∫ θ in (1 : ℝ)..b / k, ψa (m * θ) * ψb (m' * (k * θ))|
      ≤ ∑ m ∈ Finset.Icc 1 M, ∑ m' ∈ Finset.Icc 1 M, |∫ θ in (1 : ℝ)..b / k, ψa (m * θ) * ψb (m' * (k * θ))| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ m' ∈ Finset.Icc 1 M, ∑ m ∈ Finset.Icc 1 M, |∫ θ in (1 : ℝ)..b / k, ψa (m * θ) * ψb (m' * (k * θ))| :=
        Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum fun m' hm' =>
        Cvs.L2a.TwoProlateCrossColumn.column2_le hc hχa0 hχam hχb0 hχbm hχm hk hm' hkb hΞ hψa hua hψb hub hGa hGb hG0

/-- **The cross prime side of two tails of `M` modes**, `Σ_k 2Λ(k)|∫F_a(θ)F_b(kθ)|`. -/
theorem crossSide_le {c χa χb χm G K Ξ b : ℝ} {ψa ua ψb ub : ℝ → ℝ} (P R N M : ℕ)
    (hc : 1 ≤ c) (hχa0 : 0 ≤ χa) (hχam : χa ≤ χm) (hχb0 : 0 ≤ χb) (hχbm : χb ≤ χm) (hχm : χm < c ^ 2)
    (hχs : χb ≤ c * √c) (hΔ : |χa - χb| ≤ 3 / 4 * c * √c)
    (hidx : Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R ⊆ Finset.Icc 2 N)
    (hrb : (N : ℝ) + 2 ≤ b) (hΞ : (M : ℝ) * b ≤ Ξ)
    (hψa : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψa (ua ξ / pP ξ) ξ)
    (hua : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ua (-(qP c χa ξ * ψa ξ)) ξ)
    (hψb : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψb (ub ξ / pP ξ) ξ)
    (hub : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ub (-(qP c χb ξ * ψb ξ)) ξ)
    (hGa : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χa) ψa ua ξ ≤ G) (hGb : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χb) ψb ub ξ ≤ G) (hG0 : 0 ≤ G) (hK : 0 ≤ K)
    (hconta : ContinuousOn ψa (Icc 1 Ξ)) (hcontb : ContinuousOn ψb (Icc 1 Ξ))
    (hedge : ∀ ξ ∈ Icc 1 Ξ, |ψa ξ| ≤ |ψa 1|) (hedge1 : ψa 1 ^ 2 ≤ K * G) :
    ∑ k ∈ Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R, 2 * Λ k * |∫ θ in Ioi 1, tailF ψa M b θ * tailF ψb M b (k * θ)|
      ≤ 2 * (G * ((4 * Cvs.L2a.StationaryPairsWeightedTotal.Aw c χm K / √c + 32 * Cvs.L2a.StationaryPairsWeightedTotal.κw c χm * √c / c ^ 2
              + 32 * Cvs.L2a.StationaryPairsWeightedTotal.κw c χm / (3 * c)) * (π ^ 2 / 6) * ∑' n : ℕ, Λ n / (n : ℝ) ^ 2
            + 96 * Cvs.L2a.StationaryPairsWeightedTotal.κw c χm * √(√c) / c ^ 2 * ∑' n : ℕ, Λ n / ((n : ℝ) * √n)
            + (Cvs.L2a.StationaryPairsWeightedTotal.Aw c χm K / c + 2 * Cvs.L2a.StationaryPairsWeightedTotal.Qw c χm / √c)
              * (log √c * (1 + log √c) ^ 2))
        + G / (√3 / 2 * √(c ^ 2 - χm)) * (π ^ 2 / 6) * ∑' n : ℕ, Λ n / (n : ℝ) ^ 2
        + 8 * G * √(2 * c / (√3 * √(c ^ 2 - χm))) / c ^ 2 * (36 * (π ^ 2 / 6 + 6))) := by
  have hc0 : 0 < c := by linarith
  have hd : 0 < c ^ 2 - χm := by linarith
  set α := √3 / 2 * √(c ^ 2 - χm) with hα
  have hα0 : 0 < α := by positivity
  set κs := √(2 * c / (√3 * √(c ^ 2 - χm))) with hκs
  have hκ0 : 0 ≤ κs := sqrt_nonneg _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  set I : ℕ → ℝ := fun k => ∫ θ in Ioi 1, tailF ψa M b θ * tailF ψb M b (k * θ) with hI
  set S : ℕ → ℝ := fun k => ∑ m' ∈ Finset.Icc 1 M, |∫ t in (k : ℝ)..b, ψb (m' * t) * ψa (1 / k * t)| with hS
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
    have key := cross_term_le (k := k) (M := M) hc0 hχa0 hχam hχb0 hχbm hχm hk2 (by linarith) hΞ hψa hua hψb hub
      hGa hGb hG0 hconta hcontb
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
  have hstat := Cvs.L2a.TwoProlateWeightedPairTotal.stationary_total2_le (ψa := ψb) (ua := ub) (ψb := ψa) (ub := ua) N M hc
    hχb0 hχbm hχa0 hχam hχm hχs hΔ hrb hΞ hψb hub hψa hua hGb hGa hG0 hK hconta hedge hedge1
  have hL2 := Cvs.L2a.PrimeResonanceSum.summable_vonMangoldt_div_sq.sum_le_tsum (Finset.Icc 2 N)
    (fun n _ => div_nonneg vonMangoldt_nonneg (by positivity))
  have hnon : ∑ k ∈ Finset.Icc 2 N, Λ k / k * Nr k ≤ 36 * (π ^ 2 / 6 + 6) := by
    refine le_trans ?_ (Cvs.L2a.NonstationaryPairsAllShifts.prime_pairs_le N M M)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
    · intro k _ _
      apply mul_nonneg (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k))
      apply Finset.sum_nonneg; intro m' _; apply Finset.sum_nonneg; intro m _; positivity
  calc ∑ k ∈ Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R, 2 * Λ k * |I k|
      ≤ ∑ k ∈ Finset.Icc 2 N, 2 * Λ k * |I k| :=
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

end Cvs.L2a.TwoTailCrossPrimeSide
