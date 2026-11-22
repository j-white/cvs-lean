import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.ZetaValues
import Cvs.L2a.NonstationaryPairsOneShift
import Cvs.L2a.PrimeResonanceSum
import Cvs.L2a.StationaryPairsWeightedTotal
import Cvs.L2a.TwoProlatePairMonomials
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Upstream.VonMangoldtThreeHalvesSummable

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# All stationary pairs of two prolates, weighted by `Λ(k)/k`, in closed form

For the modes `m` of `ψ_a` and `1/k` of `ψ_b`, with `χ_m ≥ χ_a, χ_b`, `χ_a ≤ c√c`, `|χ_b − χ_a| ≤ (3/4)c√c`, and
`A, Q, κ` the window and envelope weights at `χ_m`:
`Σ_{k,m} (Λ(k)/k)|∫_k^b ψ_a(mt)ψ_b(t/k)| ≤ G((4A/√c + 32κ√c/c² + 32κ/(3c))(π²/6)Σ Λ(n)/n² + (96κ c^{1/4}/c²)Σ Λ(n)/n^{3/2}
+ (A/c + 2Q/√c) log √c (1 + log √c)²)`, for every truncation.
-/

namespace Cvs.L2a.TwoProlateWeightedPairTotal

open Real Set Finset ArithmeticFunction Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.NonresonantCrossIntegral
open Cvs.L2a.StationaryPairsWeightedTotal (Aw Qw κw strip_count)

/-- **One stationary pair of two prolates, either regime**, as monomials plus a strip indicator. -/
theorem pair2_le {c χa χb χm G K Ξ k m b : ℝ} {ψa ua ψb ub : ℝ → ℝ}
    (hc : 1 ≤ c) (hχa0 : 0 ≤ χa) (hχam : χa ≤ χm) (hχb0 : 0 ≤ χb) (hχbm : χb ≤ χm) (hχm : χm < c ^ 2)
    (hχs : χa ≤ c * √c) (hΔ : |χb - χa| ≤ 3 / 4 * c * √c) (hk1 : 1 ≤ k) (hkm2 : 2 ≤ k * m) (hm : 1 ≤ m)
    (hrb : k + 2 ≤ b) (hhi : m * b ≤ Ξ)
    (hψa : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψa (ua ξ / pP ξ) ξ)
    (hua : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ua (-(qP c χa ξ * ψa ξ)) ξ)
    (hψb : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψb (ub ξ / pP ξ) ξ)
    (hub : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ub (-(qP c χb ξ * ψb ξ)) ξ)
    (hGa : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χa) ψa ua ξ ≤ G) (hGb : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χb) ψb ub ξ ≤ G)
    (hG0 : 0 ≤ G) (hK : 0 ≤ K)
    (hcontb : ContinuousOn ψb (Icc 1 Ξ)) (hedgeb : ∀ ξ ∈ Icc 1 Ξ, |ψb ξ| ≤ |ψb 1|) (hedge1 : ψb 1 ^ 2 ≤ K * G) :
    |∫ t in k..b, ψa (m * t) * ψb (1 / k * t)|
      ≤ G * ((4 * Aw c χm K / √c + 32 * κw c χm * √c / c ^ 2 + 32 * κw c χm / (3 * c)) * (1 / m ^ 2) / k
        + 32 * κw c χm * √(√c) / c ^ 2 * (1 / (m * √m)) / √k
        + (Aw c χm K / c + 2 * Qw c χm / √c) * (if 6 * (k * m) ≤ √c then 1 / m else 0)) := by
  have hc0 : 0 < c := by linarith
  have hk0 : 0 < k := by linarith
  have hm0 : 0 < m := by linarith
  have hs0 : 0 < √c := sqrt_pos.mpr hc0
  have hA : 0 ≤ Aw c χm K := sqrt_nonneg _
  have hκ : 0 ≤ κw c χm := sqrt_nonneg _
  have hQ : 0 ≤ Qw c χm := by unfold Qw; positivity
  have hsk : 0 < √k := sqrt_pos.mpr hk0
  have hsm : 0 < √m := sqrt_pos.mpr hm0
  have hss : 0 < √(√c) := sqrt_pos.mpr hs0
  -- `1/(k²m³) ≤ 1/(k m²)`
  have hkm3 : 1 / (k ^ 2 * m ^ 3) ≤ 1 / (k * m ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, one_mul]
    have h1 : 1 ≤ k * m := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ k * m ^ 2)
    nlinarith
  have hs1c : 1 ≤ √c := Real.one_le_sqrt.mpr hc
  have hΔs : |χb - χa| ≤ 3 / 4 * c ^ 2 / √c := by
    have e : 3 / 4 * c ^ 2 / √c = 3 / 4 * c * √c := by
      rw [div_eq_iff hs0.ne']; linear_combination (-(3 / 4) * c) * mul_self_sqrt hc0.le
    rw [e]; exact hΔ
  have hsc : √c ^ 2 ≤ c := (sq_sqrt hc0.le).le
  have hcc : √c * √c = c := mul_self_sqrt hc0.le
  by_cases h : 6 * (k * m) ≤ √c
  · have key := Cvs.L2a.TwoProlatePairMonomials.strip2_mono (s := √c) hc hχa0 hχam hχb0 hχbm hχm hχs hΔs hk1 hkm2 hm hs1c hsc h hrb
      hhi hψa hua hψb hub hGa hGb hG0 hK hcontb hedgeb hedge1
    rw [if_pos h]
    refine key.trans (mul_le_mul_of_nonneg_left ?_ hG0)
    change Aw c χm K / (c * m) + 2 * Qw c χm / (√c * m)
        + κw c χm * (32 * √c * √c / (3 * c ^ 2 * k ^ 2 * m ^ 3) + 32 * √c / (c ^ 2 * k * m ^ 2)
          + 16 * √(√c) / (c ^ 2 * √k * (m * √m))) ≤ _
    have e1 : Aw c χm K / (c * m) + 2 * Qw c χm / (√c * m) = (Aw c χm K / c + 2 * Qw c χm / √c) * (1 / m) := by
      field_simp
    have e2 : κw c χm * (32 * √c * √c / (3 * c ^ 2 * k ^ 2 * m ^ 3)) = 32 * κw c χm / (3 * c) * (1 / (k ^ 2 * m ^ 3)) := by
      rw [mul_assoc 32 (√c) (√c), hcc]; field_simp
    have e3 : (4 * Aw c χm K / √c + 32 * κw c χm * √c / c ^ 2 + 32 * κw c χm / (3 * c)) * (1 / m ^ 2) / k
        = 4 * Aw c χm K / √c * (1 / (k * m ^ 2)) + κw c χm * (32 * √c / (c ^ 2 * k * m ^ 2))
          + 32 * κw c χm / (3 * c) * (1 / (k * m ^ 2)) := by
      field_simp
    have e4 : 32 * κw c χm * √(√c) / c ^ 2 * (1 / (m * √m)) / √k
        = 2 * (κw c χm * (16 * √(√c) / (c ^ 2 * √k * (m * √m)))) := by
      field_simp; ring
    have p1 : 0 ≤ 4 * Aw c χm K / √c * (1 / (k * m ^ 2)) := by positivity
    have p2 : 0 ≤ κw c χm * (16 * √(√c) / (c ^ 2 * √k * (m * √m))) := by positivity
    have p3 : 32 * κw c χm / (3 * c) * (1 / (k ^ 2 * m ^ 3)) ≤ 32 * κw c χm / (3 * c) * (1 / (k * m ^ 2)) :=
      mul_le_mul_of_nonneg_left hkm3 (by positivity)
    rw [e3, e4, mul_add (κw c χm), mul_add (κw c χm), e2, e1]
    linarith
  · have key := Cvs.L2a.TwoProlatePairMonomials.edge2_mono (s := √c) hc hχa0 hχam hχb0 hχbm hχm hΔs hk1 hkm2 hm hs1c (lt_of_not_ge h) hrb
      hhi hψa hua hψb hub hGa hGb hG0 hK hcontb hedgeb hedge1
    rw [if_neg h, mul_zero, add_zero]
    refine key.trans (mul_le_mul_of_nonneg_left ?_ hG0)
    change 4 * Aw c χm K / (√c * k * m ^ 2)
        + κw c χm * (32 * √c / (3 * c ^ 2 * k * m ^ 2) + 32 * √(√c) / (c ^ 2 * √k * (m * √m))) ≤ _
    have e3 : (4 * Aw c χm K / √c + 32 * κw c χm * √c / c ^ 2 + 32 * κw c χm / (3 * c)) * (1 / m ^ 2) / k
        = 4 * Aw c χm K / (√c * k * m ^ 2) + 3 * (κw c χm * (32 * √c / (3 * c ^ 2 * k * m ^ 2)))
          + 32 * κw c χm / (3 * c) * (1 / (k * m ^ 2)) := by
      field_simp
    have e4 : 32 * κw c χm * √(√c) / c ^ 2 * (1 / (m * √m)) / √k
        = κw c χm * (32 * √(√c) / (c ^ 2 * √k * (m * √m))) := by
      field_simp
    have p1 : 0 ≤ κw c χm * (32 * √c / (3 * c ^ 2 * k * m ^ 2)) := by positivity
    have p2 : 0 ≤ 32 * κw c χm / (3 * c) * (1 / (k * m ^ 2)) := by positivity
    rw [e3, e4, mul_add (κw c χm)]
    linarith

/-- **All stationary pairs of two prolates, weighted by `Λ(k)/k`**, for every truncation `k ≤ N`, `m ≤ M`. -/
theorem stationary_total2_le {c χa χb χm G K Ξ b : ℝ} {ψa ua ψb ub : ℝ → ℝ} (N M : ℕ)
    (hc : 1 ≤ c) (hχa0 : 0 ≤ χa) (hχam : χa ≤ χm) (hχb0 : 0 ≤ χb) (hχbm : χb ≤ χm) (hχm : χm < c ^ 2)
    (hχs : χa ≤ c * √c) (hΔ : |χb - χa| ≤ 3 / 4 * c * √c)
    (hrb : (N : ℝ) + 2 ≤ b) (hhi : M * b ≤ Ξ)
    (hψa : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψa (ua ξ / pP ξ) ξ)
    (hua : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ua (-(qP c χa ξ * ψa ξ)) ξ)
    (hψb : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψb (ub ξ / pP ξ) ξ)
    (hub : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ub (-(qP c χb ξ * ψb ξ)) ξ)
    (hGa : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χa) ψa ua ξ ≤ G) (hGb : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χb) ψb ub ξ ≤ G)
    (hG0 : 0 ≤ G) (hK : 0 ≤ K)
    (hcontb : ContinuousOn ψb (Icc 1 Ξ)) (hedgeb : ∀ ξ ∈ Icc 1 Ξ, |ψb ξ| ≤ |ψb 1|) (hedge1 : ψb 1 ^ 2 ≤ K * G) :
    ∑ k ∈ Finset.Icc 2 N, Λ k / k * ∑ m ∈ Finset.Icc 1 M, |∫ t in (k : ℝ)..b, ψa (m * t) * ψb (1 / k * t)|
      ≤ G * ((4 * Aw c χm K / √c + 32 * κw c χm * √c / c ^ 2 + 32 * κw c χm / (3 * c)) * (π ^ 2 / 6)
            * ∑' n : ℕ, Λ n / (n : ℝ) ^ 2
          + 96 * κw c χm * √(√c) / c ^ 2 * ∑' n : ℕ, Λ n / ((n : ℝ) * √n)
          + (Aw c χm K / c + 2 * Qw c χm / √c) * (log √c * (1 + log √c) ^ 2)) := by
  have hc0 : 0 < c := by linarith
  have hs1 : 1 ≤ √c := Real.one_le_sqrt.mpr hc
  set C1 := 4 * Aw c χm K / √c + 32 * κw c χm * √c / c ^ 2 + 32 * κw c χm / (3 * c) with hC1
  set C3 := 32 * κw c χm * √(√c) / c ^ 2 with hC3
  set Hc := Aw c χm K / c + 2 * Qw c χm / √c with hHc
  have hA : 0 ≤ Aw c χm K := sqrt_nonneg _
  have hκ : 0 ≤ κw c χm := sqrt_nonneg _
  have hQ : 0 ≤ Qw c χm := by unfold Qw; positivity
  have hC10 : 0 ≤ C1 := by positivity
  have hC30 : 0 ≤ C3 := by positivity
  have hHc0 : 0 ≤ Hc := by positivity
  set I : ℕ → ℝ := fun k => ∑ m ∈ Finset.Icc 1 M, (if 6 * ((k : ℝ) * m) ≤ √c then 1 / (m : ℝ) else 0) with hI
  have hterm : ∀ k ∈ Finset.Icc 2 N,
      Λ k / k * ∑ m ∈ Finset.Icc 1 M, |∫ t in (k : ℝ)..b, ψa (m * t) * ψb (1 / k * t)|
        ≤ G * (C1 * (π ^ 2 / 6) * (Λ k / (k : ℝ) ^ 2) + 3 * C3 * (Λ k / ((k : ℝ) * √k)))
          + G * Hc * (Λ k / k * I k) := by
    intro k hk
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    have hkN : (k : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hk).2
    have hk0 : (0 : ℝ) < k := by linarith
    have hsk : 0 < √(k : ℝ) := sqrt_pos.mpr hk0
    have hb0 : 0 ≤ b := by have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith
    have hpair : ∀ m ∈ Finset.Icc 1 M, |∫ t in (k : ℝ)..b, ψa (m * t) * ψb (1 / k * t)|
        ≤ G * (C1 / k * (1 / (m : ℝ) ^ 2) + C3 / √k * (1 / ((m : ℝ) * √m))
          + Hc * (if 6 * ((k : ℝ) * m) ≤ √c then 1 / (m : ℝ) else 0)) := by
      intro m hm
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
      have hmM : (m : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hm).2
      have := pair2_le (k := k) (m := m) hc hχa0 hχam hχb0 hχbm hχm hχs hΔ (by linarith) (by nlinarith) hm1
        (by linarith) ((mul_le_mul_of_nonneg_right hmM hb0).trans hhi) hψa hua hψb hub hGa hGb hG0 hK hcontb hedgeb hedge1
      refine this.trans (le_of_eq ?_)
      rw [hC1, hC3, hHc]; ring
    have hs := sum_le_sum hpair
    rw [← mul_sum, sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum] at hs
    have h1 := Cvs.L2a.NonstationaryPairsOneShift.sum_inv_sq_le M
    have h2 := Cvs.L2a.NonstationaryPairsOneShift.sum_inv_mul_sqrt_le M
    have hin : C1 / k * ∑ m ∈ Finset.Icc 1 M, 1 / (m : ℝ) ^ 2
          + C3 / √k * ∑ m ∈ Finset.Icc 1 M, 1 / ((m : ℝ) * √m) + Hc * I k
        ≤ C1 / k * (π ^ 2 / 6) + C3 / √k * 3 + Hc * I k := by
      have := add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ C1 / k))
        (mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ C3 / √k))
      linarith
    have hΛ : 0 ≤ Λ k / (k : ℝ) := div_nonneg vonMangoldt_nonneg hk0.le
    calc Λ k / k * ∑ m ∈ Finset.Icc 1 M, |∫ t in (k : ℝ)..b, ψa (m * t) * ψb (1 / k * t)|
        ≤ Λ k / k * (G * (C1 / k * (π ^ 2 / 6) + C3 / √k * 3 + Hc * I k)) :=
          mul_le_mul_of_nonneg_left (hs.trans (mul_le_mul_of_nonneg_left hin hG0)) hΛ
      _ = _ := by field_simp
  have hS2 := Cvs.L2a.PrimeResonanceSum.summable_vonMangoldt_div_sq
  have hS3 := Cvs.Upstream.VonMangoldtThreeHalvesSummable.summable_vonMangoldt_div_pow
  have t2 := hS2.sum_le_tsum (Finset.Icc 2 N) (fun n _ => div_nonneg vonMangoldt_nonneg (by positivity))
  have t3 := hS3.sum_le_tsum (Finset.Icc 2 N) (fun n _ => div_nonneg vonMangoldt_nonneg (by positivity))
  have tc := strip_count N M hs1
  calc _ ≤ ∑ k ∈ Finset.Icc 2 N, (G * (C1 * (π ^ 2 / 6) * (Λ k / (k : ℝ) ^ 2) + 3 * C3 * (Λ k / ((k : ℝ) * √k)))
          + G * Hc * (Λ k / k * I k)) := sum_le_sum hterm
    _ = G * (C1 * (π ^ 2 / 6) * ∑ k ∈ Finset.Icc 2 N, Λ k / (k : ℝ) ^ 2
          + 3 * C3 * ∑ k ∈ Finset.Icc 2 N, Λ k / ((k : ℝ) * √k))
          + G * Hc * ∑ k ∈ Finset.Icc 2 N, Λ k / k * I k := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_add_distrib, ← mul_sum, ← mul_sum]
    _ ≤ G * (C1 * (π ^ 2 / 6) * ∑' n : ℕ, Λ n / (n : ℝ) ^ 2 + 3 * C3 * ∑' n : ℕ, Λ n / ((n : ℝ) * √n))
          + G * Hc * (log √c * (1 + log √c) ^ 2) := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left _ hG0
          exact add_le_add (mul_le_mul_of_nonneg_left t2 (by positivity))
            (mul_le_mul_of_nonneg_left t3 (by positivity))
        · exact mul_le_mul_of_nonneg_left tc (by positivity)
    _ = _ := by rw [hC3]; ring

end Cvs.L2a.TwoProlateWeightedPairTotal
