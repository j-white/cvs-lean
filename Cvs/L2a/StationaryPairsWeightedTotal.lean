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
import Cvs.L2a.NearResonantPairHarmonic
import Cvs.L2a.NonstationaryPairsOneShift
import Cvs.L2a.PrimeResonanceSum
import Cvs.L2a.StationaryPairAtDelta
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
# All stationary pairs, weighted by `Λ(k)/k`, in closed form

With `s = √c`, `A = √(2K/(√3σ))`, `Q = √(4√3)/σ`, `κ = √(c/σ)`, `σ = √(c²−χ)`:
`Σ_{k,m} (Λ(k)/k)|∫_k^b ψ(mt)ψ(t/k)| ≤ G((4A/s + 16κs/c² + 16κ/(3c))(π²/6)Σ Λ(n)/n² + (48κ√s/c²)Σ Λ(n)/n^{3/2}
+ (A/c + 2Q/s) log s (1 + log s)²)`, for every truncation; the last term counts the strip pairs `6km ≤ s`.
-/

namespace Cvs.L2a.StationaryPairsWeightedTotal

open Real Set Finset ArithmeticFunction Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.NonresonantCrossIntegral
open Cvs.L2a.NearResonantPairHarmonic (H H_le)

/-- `Σ_{m=1}^n 1/m = H_n`. -/
theorem sum_Icc_inv (n : ℕ) : ∑ m ∈ Icc 1 n, 1 / (m : ℝ) = H n := by
  induction n with
  | zero => simp [H]
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega), ih]
    unfold H; rw [sum_range_succ]; push_cast; ring

/-- **The strip pairs, counted.** `Σ_{k ≥ 2} (Λ(k)/k) Σ_{6km ≤ s} 1/m ≤ log s (1 + log s)²`. -/
theorem strip_count (N M : ℕ) {s : ℝ} (hs : 1 ≤ s) :
    ∑ k ∈ Icc 2 N, Λ k / k * ∑ m ∈ Icc 1 M, (if 6 * ((k : ℝ) * m) ≤ s then 1 / (m : ℝ) else 0)
      ≤ log s * (1 + log s) ^ 2 := by
  set n := ⌊s⌋₊ with hn
  have hs0 : 0 ≤ s := by linarith
  have hlogs : 0 ≤ log s := log_nonneg hs
  have hlogn : log (n : ℝ) ≤ log s := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0]; simp [hlogs]
    · exact log_le_log (by exact_mod_cast hpos) (Nat.floor_le hs0)
  have hlogn0 : 0 ≤ log (n : ℝ) := Real.log_natCast_nonneg n
  have hH0 : 0 ≤ H n := by unfold H; positivity
  have hHn : H n ≤ 1 + log s := (H_le n).trans (by linarith)
  -- a strip pair has `k, m ≤ n`
  have hle : ∀ k m : ℕ, 1 ≤ k → 1 ≤ m → 6 * ((k : ℝ) * m) ≤ s → k ≤ n ∧ m ≤ n := by
    intro k m hk hm h
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    constructor
    · exact Nat.le_floor (by nlinarith)
    · exact Nat.le_floor (by nlinarith)
  have hinner : ∀ k ∈ Finset.Icc 2 N, Λ k / k * ∑ m ∈ Icc 1 M, (if 6 * ((k : ℝ) * m) ≤ s then 1 / (m : ℝ) else 0)
      ≤ if k ≤ n then Λ k / k * H n else 0 := by
    intro k hk
    have hk1 : 1 ≤ k := by have := (Finset.mem_Icc.mp hk).1; omega
    have hΛ : 0 ≤ Λ k / (k : ℝ) := div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k)
    split_ifs with hkn
    · apply mul_le_mul_of_nonneg_left _ hΛ
      rw [← sum_Icc_inv n, ← sum_filter]
      apply sum_le_sum_of_subset_of_nonneg
      · intro m hm
        rw [Finset.mem_filter, Finset.mem_Icc] at hm
        exact Finset.mem_Icc.mpr ⟨hm.1.1, (hle k m hk1 hm.1.1 hm.2).2⟩
      · intro _ _ _; positivity
    · have : ∑ m ∈ Icc 1 M, (if 6 * ((k : ℝ) * m) ≤ s then 1 / (m : ℝ) else 0) = 0 := by
        apply sum_eq_zero
        intro m hm
        rw [if_neg]
        intro h
        exact hkn (hle k m hk1 (Finset.mem_Icc.mp hm).1 h).1
      rw [this, mul_zero]
  calc _ ≤ ∑ k ∈ Finset.Icc 2 N, (if k ≤ n then Λ k / k * H n else 0) := sum_le_sum hinner
    _ = ∑ k ∈ (Finset.Icc 2 N).filter (· ≤ n), Λ k / k * H n := by rw [sum_filter]
    _ ≤ ∑ k ∈ Finset.Icc 1 n, Λ k / k * H n := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro k hk
          rw [Finset.mem_filter, Finset.mem_Icc] at hk
          exact Finset.mem_Icc.mpr ⟨by omega, hk.2⟩
        · intro k _ _
          exact mul_nonneg (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k)) hH0
    _ ≤ ∑ k ∈ Finset.Icc 1 n, log (n : ℝ) * (1 / (k : ℝ)) * H n := by
        apply sum_le_sum
        intro k hk
        have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
        have hkn : k ≤ n := (Finset.mem_Icc.mp hk).2
        have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
        apply mul_le_mul_of_nonneg_right _ hH0
        rw [mul_one_div]
        apply div_le_div_of_nonneg_right _ hk0.le
        exact vonMangoldt_le_log.trans (log_le_log hk0 (by exact_mod_cast hkn))
    _ = log (n : ℝ) * H n * H n := by rw [← sum_mul, ← mul_sum, sum_Icc_inv]
    _ ≤ log s * (1 + log s) * (1 + log s) := by
        apply mul_le_mul (mul_le_mul hlogn hHn hH0 hlogs) hHn hH0 (by positivity)
    _ = log s * (1 + log s) ^ 2 := by ring

/-- The window weight `A = √(2K/(√3σ))`. -/
noncomputable def Aw (c χ K : ℝ) : ℝ := √(2 * K / (√3 * √(c ^ 2 - χ)))
/-- The window weight `Q = √(4√3)/σ`. -/
noncomputable def Qw (c χ : ℝ) : ℝ := √(4 * √3) / √(c ^ 2 - χ)
/-- The envelope weight `κ = √(c/σ)`. -/
noncomputable def κw (c χ : ℝ) : ℝ := √(c / √(c ^ 2 - χ))

/-- **One stationary pair, either regime**, as monomials plus a strip indicator. -/
theorem pair_le {c χ G K Ξ k m b : ℝ} {ψ u : ℝ → ℝ}
    (hc : 1 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hχs : χ ≤ c * √c) (hk1 : 1 ≤ k) (hkm2 : 2 ≤ k * m) (hm : 1 ≤ m)
    (hrb : k + 2 ≤ b) (hhi : m * b ≤ Ξ)
    (hψ : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hG : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χ) ψ u ξ ≤ G) (hG0 : 0 ≤ G) (hK : 0 ≤ K)
    (hcont : ContinuousOn ψ (Icc 1 Ξ)) (hedge : ∀ ξ ∈ Icc 1 Ξ, |ψ ξ| ≤ |ψ 1|) (hedge1 : ψ 1 ^ 2 ≤ K * G) :
    |∫ t in k..b, ψ (m * t) * ψ (1 / k * t)|
      ≤ G * ((4 * Aw c χ K / √c + 16 * κw c χ * √c / c ^ 2 + 16 * κw c χ / (3 * c)) * (1 / m ^ 2) / k
        + 16 * κw c χ * √(√c) / c ^ 2 * (1 / (m * √m)) / √k
        + (Aw c χ K / c + 2 * Qw c χ / √c) * (if 6 * (k * m) ≤ √c then 1 / m else 0)) := by
  have hc0 : 0 < c := by linarith
  have hk0 : 0 < k := by linarith
  have hm0 : 0 < m := by linarith
  have hs0 : 0 < √c := sqrt_pos.mpr hc0
  have hA : 0 ≤ Aw c χ K := sqrt_nonneg _
  have hκ : 0 ≤ κw c χ := sqrt_nonneg _
  have hQ : 0 ≤ Qw c χ := by unfold Qw; positivity
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
  have hsc : √c ^ 2 ≤ c := (sq_sqrt hc0.le).le
  have hcc : √c * √c = c := mul_self_sqrt hc0.le
  by_cases h : 6 * (k * m) ≤ √c
  · have key := Cvs.L2a.StationaryPairAtDelta.strip_mono (s := √c) hc hχ0 hχ hχs hk1 hkm2 hm hs1c hsc h hrb hhi hψ hu hG
      hG0 hK hcont hedge hedge1
    rw [if_pos h]
    refine key.trans (mul_le_mul_of_nonneg_left ?_ hG0)
    change Aw c χ K / (c * m) + 2 * Qw c χ / (√c * m)
        + κw c χ * (16 * √c * √c / (3 * c ^ 2 * k ^ 2 * m ^ 3) + 16 * √c / (c ^ 2 * k * m ^ 2)
          + 8 * √(√c) / (c ^ 2 * √k * (m * √m))) ≤ _
    have e1 : Aw c χ K / (c * m) + 2 * Qw c χ / (√c * m) = (Aw c χ K / c + 2 * Qw c χ / √c) * (1 / m) := by
      field_simp
    have e2 : κw c χ * (16 * √c * √c / (3 * c ^ 2 * k ^ 2 * m ^ 3)) = 16 * κw c χ / (3 * c) * (1 / (k ^ 2 * m ^ 3)) := by
      rw [mul_assoc 16 (√c) (√c), hcc]; field_simp
    have e3 : (4 * Aw c χ K / √c + 16 * κw c χ * √c / c ^ 2 + 16 * κw c χ / (3 * c)) * (1 / m ^ 2) / k
        = 4 * Aw c χ K / √c * (1 / (k * m ^ 2)) + κw c χ * (16 * √c / (c ^ 2 * k * m ^ 2))
          + 16 * κw c χ / (3 * c) * (1 / (k * m ^ 2)) := by
      field_simp
    have e4 : 16 * κw c χ * √(√c) / c ^ 2 * (1 / (m * √m)) / √k
        = 2 * (κw c χ * (8 * √(√c) / (c ^ 2 * √k * (m * √m)))) := by
      field_simp; ring
    have p1 : 0 ≤ 4 * Aw c χ K / √c * (1 / (k * m ^ 2)) := by positivity
    have p2 : 0 ≤ κw c χ * (8 * √(√c) / (c ^ 2 * √k * (m * √m))) := by positivity
    have p3 : 16 * κw c χ / (3 * c) * (1 / (k ^ 2 * m ^ 3)) ≤ 16 * κw c χ / (3 * c) * (1 / (k * m ^ 2)) :=
      mul_le_mul_of_nonneg_left hkm3 (by positivity)
    rw [e3, e4, mul_add (κw c χ), mul_add (κw c χ), e2, e1]
    linarith
  · have key := Cvs.L2a.StationaryPairAtDelta.edge_mono (s := √c) hc hχ0 hχ hk1 hkm2 hm hs1c (lt_of_not_ge h) hrb hhi hψ hu hG hG0 hK
      hcont hedge hedge1
    rw [if_neg h, mul_zero, add_zero]
    refine key.trans (mul_le_mul_of_nonneg_left ?_ hG0)
    change 4 * Aw c χ K / (√c * k * m ^ 2)
        + κw c χ * (16 * √c / (3 * c ^ 2 * k * m ^ 2) + 16 * √(√c) / (c ^ 2 * √k * (m * √m))) ≤ _
    have e3 : (4 * Aw c χ K / √c + 16 * κw c χ * √c / c ^ 2 + 16 * κw c χ / (3 * c)) * (1 / m ^ 2) / k
        = 4 * Aw c χ K / (√c * k * m ^ 2) + 3 * (κw c χ * (16 * √c / (3 * c ^ 2 * k * m ^ 2)))
          + 16 * κw c χ / (3 * c) * (1 / (k * m ^ 2)) := by
      field_simp
    have e4 : 16 * κw c χ * √(√c) / c ^ 2 * (1 / (m * √m)) / √k
        = κw c χ * (16 * √(√c) / (c ^ 2 * √k * (m * √m))) := by
      field_simp
    have p1 : 0 ≤ κw c χ * (16 * √c / (3 * c ^ 2 * k * m ^ 2)) := by positivity
    have p2 : 0 ≤ 16 * κw c χ / (3 * c) * (1 / (k * m ^ 2)) := by positivity
    rw [e3, e4, mul_add (κw c χ)]
    linarith

/-- **All stationary pairs, weighted by `Λ(k)/k`**, for every truncation `k ≤ N`, `m ≤ M`. -/
theorem stationary_total_le {c χ G K Ξ b : ℝ} {ψ u : ℝ → ℝ} (N M : ℕ)
    (hc : 1 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hχs : χ ≤ c * √c)
    (hrb : (N : ℝ) + 2 ≤ b) (hhi : M * b ≤ Ξ)
    (hψ : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hG : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χ) ψ u ξ ≤ G) (hG0 : 0 ≤ G) (hK : 0 ≤ K)
    (hcont : ContinuousOn ψ (Icc 1 Ξ)) (hedge : ∀ ξ ∈ Icc 1 Ξ, |ψ ξ| ≤ |ψ 1|) (hedge1 : ψ 1 ^ 2 ≤ K * G) :
    ∑ k ∈ Finset.Icc 2 N, Λ k / k * ∑ m ∈ Finset.Icc 1 M, |∫ t in (k : ℝ)..b, ψ (m * t) * ψ (1 / k * t)|
      ≤ G * ((4 * Aw c χ K / √c + 16 * κw c χ * √c / c ^ 2 + 16 * κw c χ / (3 * c)) * (π ^ 2 / 6)
            * ∑' n : ℕ, Λ n / (n : ℝ) ^ 2
          + 48 * κw c χ * √(√c) / c ^ 2 * ∑' n : ℕ, Λ n / ((n : ℝ) * √n)
          + (Aw c χ K / c + 2 * Qw c χ / √c) * (log √c * (1 + log √c) ^ 2)) := by
  have hc0 : 0 < c := by linarith
  have hs1 : 1 ≤ √c := Real.one_le_sqrt.mpr hc
  set C1 := 4 * Aw c χ K / √c + 16 * κw c χ * √c / c ^ 2 + 16 * κw c χ / (3 * c) with hC1
  set C3 := 16 * κw c χ * √(√c) / c ^ 2 with hC3
  set Hc := Aw c χ K / c + 2 * Qw c χ / √c with hHc
  have hA : 0 ≤ Aw c χ K := sqrt_nonneg _
  have hκ : 0 ≤ κw c χ := sqrt_nonneg _
  have hQ : 0 ≤ Qw c χ := by unfold Qw; positivity
  have hC10 : 0 ≤ C1 := by positivity
  have hC30 : 0 ≤ C3 := by positivity
  have hHc0 : 0 ≤ Hc := by positivity
  set I : ℕ → ℝ := fun k => ∑ m ∈ Finset.Icc 1 M, (if 6 * ((k : ℝ) * m) ≤ √c then 1 / (m : ℝ) else 0) with hI
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
          + Hc * (if 6 * ((k : ℝ) * m) ≤ √c then 1 / (m : ℝ) else 0)) := by
      intro m hm
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
      have hmM : (m : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hm).2
      have := pair_le (k := k) (m := m) hc hχ0 hχ hχs (by linarith) (by nlinarith) hm1 (by linarith)
        ((mul_le_mul_of_nonneg_right hmM hb0).trans hhi) hψ hu hG hG0 hK hcont hedge hedge1
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
    calc Λ k / k * ∑ m ∈ Finset.Icc 1 M, |∫ t in (k : ℝ)..b, ψ (m * t) * ψ (1 / k * t)|
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

end Cvs.L2a.StationaryPairsWeightedTotal
