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
import Cvs.L2a.ExactRootPairMonomials
import Cvs.L2a.NonstationaryPairsOneShift
import Cvs.L2a.PrimeResonanceSum
import Cvs.L2a.StationaryPairsWeightedTotal
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
# All stationary pairs at the exact root, weighted by `Λ(k)/k`, for every `χ < c²`

At `s = √c`, with `ℓ ≤ (c² − χ)/c²`, `L = 5/ℓ + 1`, `A`, `κ` the window and envelope weights:
`Σ_{k,m} (Λ(k)/k)|∫_k^b ψ(mt)ψ(t/k)| ≤ G(C₁(π²/6)Σ Λ(n)/n² + 3C₃ Σ Λ(n)/n^{3/2} + H log s'(1 + log s')²)`,
`C₁ = LA/√c + 20κ√c/c² + 32κ/(9c)`, `C₃ = 32√L κ c^{1/4}/(3c²)`, `H = A/c + 2√(10/(√3ℓ))/(σ√c)`, `s' = (3/5)√c ℓ ≥ 1`.
-/

namespace Cvs.L2a.ExactRootWeightedPairTotal

open Real Set Finset ArithmeticFunction Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.NonresonantCrossIntegral
open Cvs.L2a.StationaryPairsWeightedTotal (Aw Qw κw)

/-- `C₁ = (5/ℓ + 1)A/√c + 20κ√c/c² + 32κ/(9c)`. -/
noncomputable def C1 (c χ K ℓ : ℝ) : ℝ := (5 / ℓ + 1) * Aw c χ K / √c + 20 * κw c χ * √c / c ^ 2 + 32 * κw c χ / (9 * c)
/-- `C₃ = 32√(5/ℓ + 1) κ c^{1/4}/(3c²)`. -/
noncomputable def C3 (c χ ℓ : ℝ) : ℝ := 32 * √(5 / ℓ + 1) * κw c χ * √(√c) / (3 * c ^ 2)
/-- `H = A/c + 2√(10/(√3ℓ))/(σ√c)`. -/
noncomputable def Hc (c χ K ℓ : ℝ) : ℝ := Aw c χ K / c + 2 * √(10 / (√3 * ℓ)) / √(c ^ 2 - χ) / √c

set_option maxHeartbeats 2000000 in
/-- **One stationary pair at the exact root, either regime**, as monomials plus a strip indicator. -/
theorem pair_le {c χ G K Ξ k m b ℓ : ℝ} {ψ u : ℝ → ℝ}
    (hc : 1 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hℓ0 : 0 < ℓ) (hℓ : ℓ ≤ (c ^ 2 - χ) / c ^ 2)
    (hk1 : 1 ≤ k) (hkm2 : 2 ≤ k * m) (hm : 1 ≤ m) (hrb : k + 2 ≤ b) (hhi : m * b ≤ Ξ)
    (hψ : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hG : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χ) ψ u ξ ≤ G) (hG0 : 0 ≤ G) (hK : 0 ≤ K)
    (hcont : ContinuousOn ψ (Icc 1 Ξ)) (hedge : ∀ ξ ∈ Icc 1 Ξ, |ψ ξ| ≤ |ψ 1|) (hedge1 : ψ 1 ^ 2 ≤ K * G) :
    |∫ t in k..b, ψ (m * t) * ψ (1 / k * t)|
      ≤ G * (C1 c χ K ℓ / k * (1 / m ^ 2) + C3 c χ ℓ / √k * (1 / (m * √m))
        + Hc c χ K ℓ * (if 6 * (k * m) ≤ 3 / 5 * (√c * ℓ) then 1 / m else 0)) := by
  have hc0 : 0 < c := by linarith
  have hk0 : 0 < k := by linarith
  have hm0 : 0 < m := by linarith
  have hs0 : 0 < √c := sqrt_pos.mpr hc0
  have hd : 0 < c ^ 2 - χ := by linarith
  have hsd : 0 < √(c ^ 2 - χ) := sqrt_pos.mpr hd
  have hA : 0 ≤ Aw c χ K := sqrt_nonneg _
  have hκ : 0 ≤ κw c χ := sqrt_nonneg _
  have hsk : 0 < √k := sqrt_pos.mpr hk0
  have hsm : 0 < √m := sqrt_pos.mpr hm0
  have hss : 0 < √(√c) := sqrt_pos.mpr hs0
  have h5ℓ : 0 < 5 / ℓ := by positivity
  have hL1 : 1 ≤ √(5 / ℓ + 1) := Real.le_sqrt_of_sq_le (by linarith)
  have hkm3 : 1 / (k ^ 2 * m ^ 3) ≤ 1 / (k * m ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, one_mul]
    have h1 : 1 ≤ k * m := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ k * m ^ 2)
    nlinarith
  have hs1c : 1 ≤ √c := Real.one_le_sqrt.mpr hc
  have hsc : √c ^ 2 ≤ c := (sq_sqrt hc0.le).le
  have hcc : √c * √c = c := mul_self_sqrt hc0.le
  have hiff : (6 * (k * m) ≤ 3 / 5 * (√c * ℓ)) ↔ (10 * (k * m) ≤ √c * ℓ) := by
    constructor <;> intro h <;> linarith
  unfold C1 C3 Hc
  by_cases h : 10 * (k * m) ≤ √c * ℓ
  · have key := Cvs.L2a.ExactRootPairMonomials.strip_mono (s := √c) hc hχ0 hχ hℓ0 hℓ hk1 hkm2 hm hs1c hsc h hrb hhi
      hψ hu hG hG0 hK hcont hedge hedge1
    rw [if_pos (hiff.mpr h)]
    refine key.trans (mul_le_mul_of_nonneg_left ?_ hG0)
    change Aw c χ K / (c * m) + 2 * √(10 / (√3 * ℓ)) / √(c ^ 2 - χ) / (√c * m)
        + κw c χ * (32 * √c * √c / (9 * c ^ 2 * k ^ 2 * m ^ 3) + 20 * √c / (c ^ 2 * k * m ^ 2)
          + 32 * √(√c) / (3 * c ^ 2 * √k * (m * √m))) ≤ _
    have e1 : Aw c χ K / (c * m) + 2 * √(10 / (√3 * ℓ)) / √(c ^ 2 - χ) / (√c * m)
        = (Aw c χ K / c + 2 * √(10 / (√3 * ℓ)) / √(c ^ 2 - χ) / √c) * (1 / m) := by field_simp
    have e2 : κw c χ * (32 * √c * √c / (9 * c ^ 2 * k ^ 2 * m ^ 3))
        = 32 * κw c χ / (9 * c) * (1 / (k ^ 2 * m ^ 3)) := by
      rw [mul_assoc 32 (√c) (√c), hcc]; field_simp
    have e3 : ((5 / ℓ + 1) * Aw c χ K / √c + 20 * κw c χ * √c / c ^ 2 + 32 * κw c χ / (9 * c)) / k * (1 / m ^ 2)
        = (5 / ℓ + 1) * Aw c χ K / √c * (1 / (k * m ^ 2)) + κw c χ * (20 * √c / (c ^ 2 * k * m ^ 2))
          + 32 * κw c χ / (9 * c) * (1 / (k * m ^ 2)) := by
      field_simp
    have e4 : 32 * √(5 / ℓ + 1) * κw c χ * √(√c) / (3 * c ^ 2) / √k * (1 / (m * √m))
        = √(5 / ℓ + 1) * (κw c χ * (32 * √(√c) / (3 * c ^ 2 * √k * (m * √m)))) := by
      field_simp
    have p1 : 0 ≤ (5 / ℓ + 1) * Aw c χ K / √c * (1 / (k * m ^ 2)) := by positivity
    have p2 : 0 ≤ κw c χ * (32 * √(√c) / (3 * c ^ 2 * √k * (m * √m))) := by positivity
    have p2' : κw c χ * (32 * √(√c) / (3 * c ^ 2 * √k * (m * √m)))
        ≤ √(5 / ℓ + 1) * (κw c χ * (32 * √(√c) / (3 * c ^ 2 * √k * (m * √m)))) :=
      le_mul_of_one_le_left p2 hL1
    have p3 : 32 * κw c χ / (9 * c) * (1 / (k ^ 2 * m ^ 3)) ≤ 32 * κw c χ / (9 * c) * (1 / (k * m ^ 2)) :=
      mul_le_mul_of_nonneg_left hkm3 (by positivity)
    rw [e3, e4, mul_add (κw c χ), mul_add (κw c χ), e2, e1]
    linarith
  · have hlt : √c * ℓ < 10 * (k * m) := lt_of_not_ge h
    have key := Cvs.L2a.ExactRootPairMonomials.edge_mono (s := √c) hc hχ0 hχ hℓ0 hk1 hkm2 hm hs1c hlt hrb hhi
      hψ hu hG hG0 hK hcont hedge hedge1
    rw [if_neg (fun h' => h (hiff.mp h')), mul_zero, add_zero]
    refine key.trans (mul_le_mul_of_nonneg_left ?_ hG0)
    change (5 / ℓ + 1) * Aw c χ K / (√c * k * m ^ 2)
        + κw c χ * (64 * √c / (9 * c ^ 2 * k * m ^ 2)
          + 32 * √(5 / ℓ + 1) * √(√c) / (3 * c ^ 2 * √k * (m * √m))) ≤ _
    have e3 : ((5 / ℓ + 1) * Aw c χ K / √c + 20 * κw c χ * √c / c ^ 2 + 32 * κw c χ / (9 * c)) / k * (1 / m ^ 2)
        = (5 / ℓ + 1) * Aw c χ K / (√c * k * m ^ 2) + 45 / 16 * (κw c χ * (64 * √c / (9 * c ^ 2 * k * m ^ 2)))
          + 32 * κw c χ / (9 * c) * (1 / (k * m ^ 2)) := by
      field_simp; ring
    have e4 : 32 * √(5 / ℓ + 1) * κw c χ * √(√c) / (3 * c ^ 2) / √k * (1 / (m * √m))
        = κw c χ * (32 * √(5 / ℓ + 1) * √(√c) / (3 * c ^ 2 * √k * (m * √m))) := by
      field_simp
    have p1 : 0 ≤ κw c χ * (64 * √c / (9 * c ^ 2 * k * m ^ 2)) := by positivity
    have p2 : 0 ≤ 32 * κw c χ / (9 * c) * (1 / (k * m ^ 2)) := by positivity
    rw [e3, e4, mul_add (κw c χ)]
    linarith

/-- **All stationary pairs at the exact root, weighted by `Λ(k)/k`**, for every truncation, any `χ < c²`. -/
theorem stationary_total_le {c χ G K Ξ b ℓ : ℝ} {ψ u : ℝ → ℝ} (N M : ℕ)
    (hc : 1 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hℓ0 : 0 < ℓ) (hℓ : ℓ ≤ (c ^ 2 - χ) / c ^ 2)
    (hsℓ : 1 ≤ 3 / 5 * (√c * ℓ))
    (hrb : (N : ℝ) + 2 ≤ b) (hhi : M * b ≤ Ξ)
    (hψ : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hG : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χ) ψ u ξ ≤ G) (hG0 : 0 ≤ G) (hK : 0 ≤ K)
    (hcont : ContinuousOn ψ (Icc 1 Ξ)) (hedge : ∀ ξ ∈ Icc 1 Ξ, |ψ ξ| ≤ |ψ 1|) (hedge1 : ψ 1 ^ 2 ≤ K * G) :
    ∑ k ∈ Finset.Icc 2 N, Λ k / k * ∑ m ∈ Finset.Icc 1 M, |∫ t in (k : ℝ)..b, ψ (m * t) * ψ (1 / k * t)|
      ≤ G * (C1 c χ K ℓ * (π ^ 2 / 6) * ∑' n : ℕ, Λ n / (n : ℝ) ^ 2
          + 3 * C3 c χ ℓ * ∑' n : ℕ, Λ n / ((n : ℝ) * √n)
          + Hc c χ K ℓ * (log (3 / 5 * (√c * ℓ)) * (1 + log (3 / 5 * (√c * ℓ))) ^ 2)) := by
  have hc0 : 0 < c := by linarith
  have hs1 : 1 ≤ √c := Real.one_le_sqrt.mpr hc
  have hd : 0 < c ^ 2 - χ := by linarith
  set C1 := C1 c χ K ℓ with hC1
  set C3 := C3 c χ ℓ with hC3
  set Hc := Hc c χ K ℓ with hHc
  have hA : 0 ≤ Aw c χ K := sqrt_nonneg _
  have hκ : 0 ≤ κw c χ := sqrt_nonneg _
  have hC10 : 0 ≤ C1 := by rw [hC1]; unfold Cvs.L2a.ExactRootWeightedPairTotal.C1; positivity
  have hC30 : 0 ≤ C3 := by rw [hC3]; unfold Cvs.L2a.ExactRootWeightedPairTotal.C3; positivity
  have hHc0 : 0 ≤ Hc := by rw [hHc]; unfold Cvs.L2a.ExactRootWeightedPairTotal.Hc; positivity
  set I : ℕ → ℝ := fun k => ∑ m ∈ Finset.Icc 1 M, (if 6 * ((k : ℝ) * m) ≤ 3 / 5 * (√c * ℓ) then 1 / (m : ℝ) else 0)
    with hI
  have hterm : ∀ k ∈ Finset.Icc 2 N,
      Λ k / k * ∑ m ∈ Finset.Icc 1 M, |∫ t in (k : ℝ)..b, ψ (m * t) * ψ (1 / k * t)|
        ≤ G * (C1 * (π ^ 2 / 6) * (Λ k / (k : ℝ) ^ 2) + 3 * C3 * (Λ k / ((k : ℝ) * √k)))
          + G * Hc * (Λ k / k * I k) := by
    intro k hk
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    have hkN : (k : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hk).2
    have hk0 : (0 : ℝ) < k := by linarith
    have hsk : 0 < √(k : ℝ) := sqrt_pos.mpr hk0
    have hb0 : 0 ≤ b := by have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith
    have hpair : ∀ m ∈ Finset.Icc 1 M, |∫ t in (k : ℝ)..b, ψ (m * t) * ψ (1 / k * t)|
        ≤ G * (C1 / k * (1 / (m : ℝ) ^ 2) + C3 / √k * (1 / ((m : ℝ) * √m))
          + Hc * (if 6 * ((k : ℝ) * m) ≤ 3 / 5 * (√c * ℓ) then 1 / (m : ℝ) else 0)) := by
      intro m hm
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
      have hmM : (m : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hm).2
      have := pair_le (k := k) (m := m) hc hχ0 hχ hℓ0 hℓ (by linarith) (by nlinarith) hm1 (by linarith)
        ((mul_le_mul_of_nonneg_right hmM hb0).trans hhi) hψ hu hG hG0 hK hcont hedge hedge1
      exact this
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
    calc Λ k / k * ∑ m ∈ Finset.Icc 1 M, |∫ t in (k : ℝ)..b, ψ (m * t) * ψ (1 / k * t)|
        ≤ Λ k / k * (G * (C1 / k * (π ^ 2 / 6) + C3 / √k * 3 + Hc * I k)) :=
          mul_le_mul_of_nonneg_left (hs.trans (mul_le_mul_of_nonneg_left hin hG0)) hΛ
      _ = _ := by field_simp
  have hS2 := Cvs.L2a.PrimeResonanceSum.summable_vonMangoldt_div_sq
  have hS3 := Cvs.Upstream.VonMangoldtThreeHalvesSummable.summable_vonMangoldt_div_pow
  have t2 := hS2.sum_le_tsum (Finset.Icc 2 N) (fun n _ => div_nonneg vonMangoldt_nonneg (by positivity))
  have t3 := hS3.sum_le_tsum (Finset.Icc 2 N) (fun n _ => div_nonneg vonMangoldt_nonneg (by positivity))
  have tc := Cvs.L2a.StationaryPairsWeightedTotal.strip_count N M hsℓ
  calc _ ≤ ∑ k ∈ Finset.Icc 2 N, (G * (C1 * (π ^ 2 / 6) * (Λ k / (k : ℝ) ^ 2) + 3 * C3 * (Λ k / ((k : ℝ) * √k)))
          + G * Hc * (Λ k / k * I k)) := sum_le_sum hterm
    _ = G * (C1 * (π ^ 2 / 6) * ∑ k ∈ Finset.Icc 2 N, Λ k / (k : ℝ) ^ 2
          + 3 * C3 * ∑ k ∈ Finset.Icc 2 N, Λ k / ((k : ℝ) * √k))
          + G * Hc * ∑ k ∈ Finset.Icc 2 N, Λ k / k * I k := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_add_distrib, ← mul_sum, ← mul_sum]
    _ ≤ G * (C1 * (π ^ 2 / 6) * ∑' n : ℕ, Λ n / (n : ℝ) ^ 2 + 3 * C3 * ∑' n : ℕ, Λ n / ((n : ℝ) * √n))
          + G * Hc * (log (3 / 5 * (√c * ℓ)) * (1 + log (3 / 5 * (√c * ℓ))) ^ 2) := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left _ hG0
          exact add_le_add (mul_le_mul_of_nonneg_left t2 (by positivity))
            (mul_le_mul_of_nonneg_left t3 (by positivity))
        · exact mul_le_mul_of_nonneg_left tc (by positivity)
    _ = _ := by ring

end Cvs.L2a.ExactRootWeightedPairTotal
