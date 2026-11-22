import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.ZetaValues
import Cvs.L2a.NonstationaryPairsOneShift
import Cvs.L2a.PrimeResonanceSum
import Cvs.L2a.SigmaFreeEdgePairMonomials
import Cvs.L2a.SigmaFreeStripPairMonomials
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
# All stationary pairs with `σ`-free envelopes, weighted by `Λ(k)/k`, for every `χ < c²`

For `1 ≤ s`, `s²L ≤ c`, `L = (c² − χ)/c²`, `A_c = √(4K/(3c))`, `s' = max((3/5)sL, 1)`:
`Σ_{k,m} (Λ(k)/k)|∫_k^b ψ(mt)ψ(t/k)| ≤ G(C₁(π²/6)Σ Λ(n)/n² + 3C₃ Σ Λ(n)/n^{3/2} + H log s'(1 + log s')²)`, with
`C₁ = (23/3)A_c/s + κ₁s/c² + (64√2/27)Ls√c/c²`, `C₃ = (32√3/9)√(23/3)√s/c²`, `H = A_c/c + 2√(10/(3L))/(cs)`.
-/

namespace Cvs.L2a.SigmaFreeWeightedPairTotal

open Real Set Finset ArithmeticFunction Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.NonresonantCrossIntegral

/-- The strip threshold `s' = max((3/5)sL, 1)`. -/
noncomputable def sp (c χ s : ℝ) : ℝ := max (3 / 5 * (s * ((c ^ 2 - χ) / c ^ 2))) 1
/-- `κ₁ = 40/(9√3) + (16/9)(8/√3 + 2√3)`. -/
noncomputable def κ₁ : ℝ := 40 / (9 * √3) + 16 / 9 * (8 / √3 + 2 * √3)
/-- `C₁`. -/
noncomputable def C1 (c χ K s : ℝ) : ℝ :=
  23 / 3 * √(4 * K / (3 * c)) / s + κ₁ * s / c ^ 2 + 64 * √2 / 27 * ((c ^ 2 - χ) / c ^ 2) * s * √c / c ^ 2
/-- `C₃`. -/
noncomputable def C3 (c s : ℝ) : ℝ := 32 * √3 / 9 * √(23 / 3) * √s / c ^ 2
/-- `H`. -/
noncomputable def Hc (c χ K s : ℝ) : ℝ := √(4 * K / (3 * c)) / c + 2 * √(10 / (3 * ((c ^ 2 - χ) / c ^ 2))) / (c * s)

/-- **The strip pairs, counted**, at the threshold `s'`. -/
theorem strip_count (N M : ℕ) {c χ s : ℝ} :
    ∑ k ∈ Icc 2 N, Λ k / k * ∑ m ∈ Icc 1 M, (if 6 * ((k : ℝ) * m) ≤ sp c χ s then 1 / (m : ℝ) else 0)
      ≤ log (sp c χ s) * (1 + log (sp c χ s)) ^ 2 := by
  have h1 : (1 : ℝ) ≤ sp c χ s := le_max_right _ _
  exact Cvs.L2a.StationaryPairsWeightedTotal.strip_count N M h1

set_option maxHeartbeats 4000000 in
/-- **One stationary pair with `σ`-free envelopes, either regime**, as monomials plus a strip indicator. -/
theorem pair_le {c χ G K Ξ k m b s : ℝ} {ψ u : ℝ → ℝ}
    (hc : 1 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hs1 : 1 ≤ s) (hsc : s ^ 2 * ((c ^ 2 - χ) / c ^ 2) ≤ c)
    (hk1 : 1 ≤ k) (hkm2 : 2 ≤ k * m) (hm : 1 ≤ m) (hrb : k + 2 ≤ b) (hhi : m * b ≤ Ξ)
    (hψ : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hG : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χ) ψ u ξ ≤ G) (hG0 : 0 ≤ G)
    (hcont : ContinuousOn ψ (Icc 1 Ξ)) (hedge : ∀ ξ ∈ Icc 1 Ξ, |ψ ξ| ≤ |ψ 1|) (hedge1 : ψ 1 ^ 2 ≤ K * G) :
    |∫ t in k..b, ψ (m * t) * ψ (1 / k * t)|
      ≤ G * (C1 c χ K s / k * (1 / m ^ 2) + C3 c s / √k * (1 / (m * √m))
        + Hc c χ K s * (if 6 * (k * m) ≤ sp c χ s then 1 / m else 0)) := by
  have hc0 : 0 < c := by linarith
  have hk0 : 0 < k := by linarith
  have hm0 : 0 < m := by linarith
  have hs0 : 0 < s := by linarith
  have hd : 0 < c ^ 2 - χ := by linarith
  set L := (c ^ 2 - χ) / c ^ 2 with hLdef
  have hL0 : 0 < L := by positivity
  have hL1 : L ≤ 1 := by rw [hLdef, div_le_one (by positivity)]; linarith
  set Ac := √(4 * K / (3 * c)) with hAc
  have hAc0 : 0 ≤ Ac := sqrt_nonneg _
  have hsk : 0 < √k := sqrt_pos.mpr hk0
  have hsm : 0 < √m := sqrt_pos.mpr hm0
  have hkm3 : 1 / (k ^ 2 * m ^ 3) ≤ 1 / (k * m ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, one_mul]
    have h1 : 1 ≤ k * m := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ k * m ^ 2)
    nlinarith
  have hsL : √L ≤ 1 := (sqrt_le_sqrt hL1).trans_eq sqrt_one
  have hκ₁ : 0 ≤ κ₁ := by unfold κ₁; positivity
  unfold C1 C3 Hc
  rw [← hLdef, ← hAc]
  by_cases h : 10 * (k * m) ≤ s * L
  · have hsp : 6 * (k * m) ≤ sp c χ s := by
      unfold sp; rw [← hLdef]; exact le_max_of_le_left (by linarith)
    have key := Cvs.L2a.SigmaFreeStripPairMonomials.strip_mono (s := s) (K := K) hc hχ0 hχ hk1 hkm2 hm hs1 hsc h hrb hhi
      hψ hu hG hG0 hcont hedge hedge1
    rw [← hLdef, ← hAc] at key
    rw [if_pos hsp]
    refine key.trans (mul_le_mul_of_nonneg_left ?_ hG0)
    have e1 : Ac / (c * m) + 2 * √(10 / (3 * L)) / (c * s * m)
        = (Ac / c + 2 * √(10 / (3 * L)) / (c * s)) * (1 / m) := by field_simp
    have t1 : (40 / (9 * √3) + 16 / 9 * (8 / √3 + 2 * √3 * √L)) * s / (c ^ 2 * k * m ^ 2)
        ≤ κ₁ * s / c ^ 2 * (1 / (k * m ^ 2)) := by
      have : 40 / (9 * √3) + 16 / 9 * (8 / √3 + 2 * √3 * √L) ≤ κ₁ := by
        unfold κ₁; have : 2 * √3 * √L ≤ 2 * √3 := by nlinarith [sqrt_nonneg 3]
        linarith
      calc (40 / (9 * √3) + 16 / 9 * (8 / √3 + 2 * √3 * √L)) * s / (c ^ 2 * k * m ^ 2)
          ≤ κ₁ * s / (c ^ 2 * k * m ^ 2) := by gcongr
        _ = κ₁ * s / c ^ 2 * (1 / (k * m ^ 2)) := by field_simp
    have t2 : 64 * √2 / 27 * L * s * √c / (c ^ 2 * k ^ 2 * m ^ 3)
        ≤ 64 * √2 / 27 * L * s * √c / c ^ 2 * (1 / (k * m ^ 2)) := by
      calc 64 * √2 / 27 * L * s * √c / (c ^ 2 * k ^ 2 * m ^ 3)
            = 64 * √2 / 27 * L * s * √c / c ^ 2 * (1 / (k ^ 2 * m ^ 3)) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hkm3 (by positivity)
    have e3 : (23 / 3 * Ac / s + κ₁ * s / c ^ 2 + 64 * √2 / 27 * L * s * √c / c ^ 2) / k * (1 / m ^ 2)
        = 23 / 3 * Ac / s * (1 / (k * m ^ 2)) + κ₁ * s / c ^ 2 * (1 / (k * m ^ 2))
          + 64 * √2 / 27 * L * s * √c / c ^ 2 * (1 / (k * m ^ 2)) := by field_simp
    have p1 : 0 ≤ 23 / 3 * Ac / s * (1 / (k * m ^ 2)) := by positivity
    have p2 : 0 ≤ 32 * √3 / 9 * √(23 / 3) * √s / c ^ 2 / √k * (1 / (m * √m)) := by positivity
    rw [e3, e1]
    linarith
  · have hlt : s * L < 10 * (k * m) := lt_of_not_ge h
    have hsp : ¬ 6 * (k * m) ≤ sp c χ s := by
      unfold sp; rw [← hLdef]
      intro h'
      rcases le_max_iff.mp h' with h'' | h''
      · exact h (by linarith)
      · nlinarith
    have key := Cvs.L2a.SigmaFreeEdgePairMonomials.edge_mono (s := s) (K := K) hc hχ0 hχ hk1 hkm2 hm hs1 hlt hrb hhi
      hψ hu hG hG0 hcont hedge hedge1
    rw [← hAc] at key
    rw [if_neg hsp, mul_zero, add_zero]
    refine key.trans (mul_le_mul_of_nonneg_left ?_ hG0)
    have e3 : (23 / 3 * Ac / s + κ₁ * s / c ^ 2 + 64 * √2 / 27 * L * s * √c / c ^ 2) / k * (1 / m ^ 2)
        = 23 / 3 * Ac / (s * k * m ^ 2) + κ₁ * s / (c ^ 2 * k * m ^ 2)
          + 64 * √2 / 27 * L * s * √c / c ^ 2 * (1 / (k * m ^ 2)) := by field_simp
    have e4 : 32 * √3 / 9 * √(23 / 3) * √s / c ^ 2 / √k * (1 / (m * √m))
        = 32 * √3 / 9 * √(23 / 3) * √s / (c ^ 2 * √k * (m * √m)) := by field_simp
    have t1 : 128 / (9 * √3) * s / (c ^ 2 * k * m ^ 2) ≤ κ₁ * s / (c ^ 2 * k * m ^ 2) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ hs0.le
      unfold κ₁
      have : 128 / (9 * √3) = 16 / 9 * (8 / √3) := by ring
      have : 0 ≤ 40 / (9 * √3) := by positivity
      have : 0 ≤ 16 / 9 * (2 * √3) := by positivity
      nlinarith
    have p3 : 0 ≤ 64 * √2 / 27 * L * s * √c / c ^ 2 * (1 / (k * m ^ 2)) := by positivity
    rw [e3, e4]
    linarith

/-- **All stationary pairs with `σ`-free envelopes, weighted by `Λ(k)/k`**, for every truncation, any `χ < c²`. -/
theorem stationary_total_le {c χ G K Ξ b s : ℝ} {ψ u : ℝ → ℝ} (N M : ℕ)
    (hc : 1 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hs1 : 1 ≤ s) (hsc : s ^ 2 * ((c ^ 2 - χ) / c ^ 2) ≤ c)
    (hrb : (N : ℝ) + 2 ≤ b) (hhi : M * b ≤ Ξ)
    (hψ : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hG : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χ) ψ u ξ ≤ G) (hG0 : 0 ≤ G)
    (hcont : ContinuousOn ψ (Icc 1 Ξ)) (hedge : ∀ ξ ∈ Icc 1 Ξ, |ψ ξ| ≤ |ψ 1|) (hedge1 : ψ 1 ^ 2 ≤ K * G) :
    ∑ k ∈ Finset.Icc 2 N, Λ k / k * ∑ m ∈ Finset.Icc 1 M, |∫ t in (k : ℝ)..b, ψ (m * t) * ψ (1 / k * t)|
      ≤ G * (C1 c χ K s * (π ^ 2 / 6) * ∑' n : ℕ, Λ n / (n : ℝ) ^ 2
          + 3 * C3 c s * ∑' n : ℕ, Λ n / ((n : ℝ) * √n)
          + Hc c χ K s * (log (sp c χ s) * (1 + log (sp c χ s)) ^ 2)) := by
  have hc0 : 0 < c := by linarith
  have hs0 : 0 < s := by linarith
  have hd : 0 < c ^ 2 - χ := by linarith
  have hL0 : 0 < (c ^ 2 - χ) / c ^ 2 := by positivity
  set C1 := C1 c χ K s with hC1
  set C3 := C3 c s with hC3
  set Hc := Hc c χ K s with hHc
  have hC10 : 0 ≤ C1 := by
    rw [hC1]; unfold Cvs.L2a.SigmaFreeWeightedPairTotal.C1
    have hk : 0 ≤ κ₁ := by unfold κ₁; positivity
    have h1 : 0 ≤ 23 / 3 * √(4 * K / (3 * c)) / s := by positivity
    have h2 : 0 ≤ κ₁ * s / c ^ 2 := by positivity
    have h3 : 0 ≤ 64 * √2 / 27 * ((c ^ 2 - χ) / c ^ 2) * s * √c / c ^ 2 :=
      div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hL0.le) hs0.le) (sqrt_nonneg _)) (by positivity)
    linarith
  have hC30 : 0 ≤ C3 := by rw [hC3]; unfold Cvs.L2a.SigmaFreeWeightedPairTotal.C3; positivity
  have hHc0 : 0 ≤ Hc := by rw [hHc]; unfold Cvs.L2a.SigmaFreeWeightedPairTotal.Hc; positivity
  set I : ℕ → ℝ := fun k => ∑ m ∈ Finset.Icc 1 M, (if 6 * ((k : ℝ) * m) ≤ sp c χ s then 1 / (m : ℝ) else 0)
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
          + Hc * (if 6 * ((k : ℝ) * m) ≤ sp c χ s then 1 / (m : ℝ) else 0)) := by
      intro m hm
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
      have hmM : (m : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hm).2
      have := pair_le (k := k) (m := m) hc hχ0 hχ hs1 hsc (by linarith) (by nlinarith) hm1 (by linarith)
        ((mul_le_mul_of_nonneg_right hmM hb0).trans hhi) hψ hu hG hG0 hcont hedge hedge1
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
  have tc := strip_count N M (c := c) (χ := χ) (s := s)
  calc _ ≤ ∑ k ∈ Finset.Icc 2 N, (G * (C1 * (π ^ 2 / 6) * (Λ k / (k : ℝ) ^ 2) + 3 * C3 * (Λ k / ((k : ℝ) * √k)))
          + G * Hc * (Λ k / k * I k)) := sum_le_sum hterm
    _ = G * (C1 * (π ^ 2 / 6) * ∑ k ∈ Finset.Icc 2 N, Λ k / (k : ℝ) ^ 2
          + 3 * C3 * ∑ k ∈ Finset.Icc 2 N, Λ k / ((k : ℝ) * √k))
          + G * Hc * ∑ k ∈ Finset.Icc 2 N, Λ k / k * I k := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_add_distrib, ← mul_sum, ← mul_sum]
    _ ≤ G * (C1 * (π ^ 2 / 6) * ∑' n : ℕ, Λ n / (n : ℝ) ^ 2 + 3 * C3 * ∑' n : ℕ, Λ n / ((n : ℝ) * √n))
          + G * Hc * (log (sp c χ s) * (1 + log (sp c χ s)) ^ 2) := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left _ hG0
          exact add_le_add (mul_le_mul_of_nonneg_left t2 (by positivity))
            (mul_le_mul_of_nonneg_left t3 (by positivity))
        · exact mul_le_mul_of_nonneg_left tc (by positivity)
    _ = _ := by ring

end Cvs.L2a.SigmaFreeWeightedPairTotal
