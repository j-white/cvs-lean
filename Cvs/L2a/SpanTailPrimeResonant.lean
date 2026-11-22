import Mathlib
import Cvs.L2a.PrimePairingResonantSplit
import Cvs.L2a.ResonantChannelModeMasses
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.TailModesPrimeSideBound
import Cvs.L2a.TailOfModes
import Cvs.L2a.TailPrimeSideByNorm
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
# The prime side of a span tail in resonant form

The prime side of the tail `F = tailF Φ M b` is `Σ_{k ∈ idx} 2Λ(k) ∫F(θ)F(kθ)` (Cvs.L2a.TailModesPrimeSideBound); the pairing vanishes for
`k > b` and splits into resonant and non-resonant parts for `k ≤ b` (Cvs.L2a.PrimePairingResonantSplit), and the resonant total is at most the
log-weighted mode masses (Cvs.L2a.ResonantChannelModeMasses). So the prime side is at most `Σ_{n ≤ M} 2 log n ∫_1^b Φ(nθ)² dθ` plus the
non-resonant pairs of the prime powers `k ≤ b`, for every `Φ` continuous on `[1, Mb]`.
-/

namespace Cvs.L2a.SpanTailPrimeResonant

open Real Set MeasureTheory ArithmeticFunction
open Cvs.L2a.TailOfModes Cvs.L2a.PrimePairingResonantSplit Cvs.L2a.ResonantChannelModeMasses

/-- The pairing vanishes for `k > b`: the dilated tail `F(kθ)` lives on `kθ ≤ b`. -/
theorem pairing_zero_of_lt (Φ : ℝ → ℝ) (M : ℕ) {b : ℝ} (hb : 0 ≤ b) {k : ℕ} (hbk : b < k) :
    ∫ θ in Ioi 1, tailF Φ M b θ * tailF Φ M b (k * θ) = 0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro θ hθ
  have hθ1 : (1 : ℝ) < θ := hθ
  have hk0 : (0 : ℝ) < k := by linarith
  have : tailF Φ M b (k * θ) = 0 := by
    unfold tailF
    rw [indicator_of_notMem]
    simp only [mem_Ioc, not_and, not_le]
    intro _
    nlinarith
  rw [this, mul_zero]

/-- **The prime side of a span tail is the resonant and non-resonant parts of the prime powers `k ≤ b`.** -/
theorem primeSide_eq (Φ : ℝ → ℝ) (M : ℕ) {b : ℝ} (hb : 0 ≤ b) (hcont : ContinuousOn Φ (Icc 1 (M * b)))
    (P R : ℕ) :
    Cvs.Zeta.Explicit.Weil.primePowerSideTruncated P R
        (Cvs.Zeta.Explicit.Weil.selfConvolution (Cvs.L2a.TailLogScaleTest.logScale (tailF Φ M b)))
      = ∑ k ∈ (Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R).filter (fun k : ℕ => (k : ℝ) ≤ b),
          2 * Λ k * (resPart Φ M b k + nonresPart Φ M b k) := by
  rw [Cvs.L2a.TailModesPrimeSideBound.primeSide_eq_image _ (tailF_zero Φ M b),
    ← Finset.sum_filter_add_sum_filter_not (Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R) (fun k : ℕ => (k : ℝ) ≤ b)]
  have hzero : ∑ k ∈ (Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R).filter (fun k : ℕ => ¬ (k : ℝ) ≤ b),
      2 * Λ k * ∫ θ in Ioi 1, tailF Φ M b θ * tailF Φ M b (k * θ) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_filter, not_le] at hk
    rw [pairing_zero_of_lt Φ M hb hk.2, mul_zero]
  rw [hzero, add_zero]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_filter] at hk
  have hk1 : 1 ≤ k := Cvs.L2a.TailPrimeSideByNorm.one_le_of_mem_primePowIndex hk.1
  rw [pairing_eq_res_add_nonres Φ M hk1 hk.2 hcont]

/-- **The prime side of a span tail is at most the log-weighted mode masses plus the non-resonant pairs.** -/
theorem primeSide_le (Φ : ℝ → ℝ) (M : ℕ) {b : ℝ} (hb : 1 ≤ b) (hcont : ContinuousOn Φ (Icc 1 (M * b)))
    (P R : ℕ) :
    Cvs.Zeta.Explicit.Weil.primePowerSideTruncated P R
        (Cvs.Zeta.Explicit.Weil.selfConvolution (Cvs.L2a.TailLogScaleTest.logScale (tailF Φ M b)))
      ≤ (∑ n ∈ Finset.Icc 1 M, 2 * Real.log n * modeMass Φ b n)
        + ∑ k ∈ (Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R).filter (fun k : ℕ => (k : ℝ) ≤ b),
            2 * Λ k * nonresPart Φ M b k := by
  rw [primeSide_eq Φ M (by linarith) hcont P R]
  have hS : ∀ k ∈ (Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R).filter (fun k : ℕ => (k : ℝ) ≤ b),
      1 ≤ k ∧ (k : ℝ) ≤ b := fun k hk => by
    rw [Finset.mem_filter] at hk
    exact ⟨Cvs.L2a.TailPrimeSideByNorm.one_le_of_mem_primePowIndex hk.1, hk.2⟩
  have hmass : ∀ n ∈ Finset.Icc 1 M, 0 ≤ modeMass Φ b n := fun n _ =>
    intervalIntegral.integral_nonneg hb (fun θ _ => sq_nonneg _)
  have h := resonant_total_le Φ M _ hS hcont hmass
  have hsplit : ∑ k ∈ (Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R).filter (fun k : ℕ => (k : ℝ) ≤ b),
        2 * Λ k * (resPart Φ M b k + nonresPart Φ M b k)
      = (∑ k ∈ (Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R).filter (fun k : ℕ => (k : ℝ) ≤ b),
            2 * Λ k * resPart Φ M b k)
        + ∑ k ∈ (Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R).filter (fun k : ℕ => (k : ℝ) ≤ b),
            2 * Λ k * nonresPart Φ M b k := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [hsplit]
  exact add_le_add h (le_refl _)

end Cvs.L2a.SpanTailPrimeResonant
