import Mathlib
import Cvs.L2a.IndexOneGainFree
import Cvs.L2a.TailOfModes
import Cvs.L2a.TrivialGainAdditiveCross

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The trivial gains of Cvs.L2a.PlateauAssemblyTrivialGain from cross constants

Given cross constants `C_j ≥ 0` charging the mode cross terms on `[j, b]` to the tail mass there for `2 ≤ j < k₀`,
and a positive tail mass on `[1, b]`, the sequence `δ₁ = 1 − T/(Σ + T)`, `δ_j = C_j/(1 + C_j)` satisfies `δ_j < 1`
and the trivial-gain inequality of Cvs.L2a.PlateauAssemblyTrivialGain for every `1 ≤ j < k₀`; `δ₁` does not enter the resonant constant (Cvs.L2a.IndexOneGainFree).
-/

namespace Cvs.L2a.TrivialGainsCrossConstants

open Real Set Finset MeasureTheory Cvs.L2a.TailOfModes Cvs.L2a.TrivialGainAdditiveCross Cvs.L2a.IndexOneGainFree

/-- The trivial-gain sequence: the free choice at `1`, `C_j/(1 + C_j)` from 2 on. -/
noncomputable def deltaSeq (S₁ T₁ : ℝ) (C : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j = 1 then 1 - T₁ / (S₁ + T₁) else C j / (1 + C j)

/-- **The trivial gains of Cvs.L2a.PlateauAssemblyTrivialGain from cross constants.** -/
theorem trivial_gains (Φ : ℝ → ℝ) {M k₀ : ℕ} {b : ℝ} (C : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j) (hb1 : 1 ≤ b) (hMb : (M : ℝ) ≤ b)
    (hcont : ContinuousOn Φ (Icc 1 (M * b)))
    (hT : 0 < ∫ θ in (1 : ℝ)..b, tailF Φ M b θ ^ 2)
    (hcross : ∀ j ∈ Finset.Icc 1 M, 2 ≤ j → j < k₀ →
      |∑ m ∈ Finset.Icc 1 M, ∑ m' ∈ (Finset.Icc 1 M).erase m, ∫ θ in (j : ℝ)..b, Φ (m * θ) * Φ (m' * θ)|
        ≤ C j * ∫ θ in (j : ℝ)..b, tailF Φ M b θ ^ 2) :
    (∀ j, deltaSeq (∑ m ∈ Finset.Icc 1 M, ∫ θ in (1 : ℝ)..b, Φ (m * θ) ^ 2)
        (∫ θ in (1 : ℝ)..b, tailF Φ M b θ ^ 2) C j < 1)
    ∧ ∀ j ∈ Finset.Icc 1 M, j < k₀ →
      (1 - deltaSeq (∑ m ∈ Finset.Icc 1 M, ∫ θ in (1 : ℝ)..b, Φ (m * θ) ^ 2)
          (∫ θ in (1 : ℝ)..b, tailF Φ M b θ ^ 2) C j)
        * ∑ m ∈ Finset.Icc 1 M, ∫ θ in (j : ℝ)..b, Φ (m * θ) ^ 2 ≤ ∫ θ in (j : ℝ)..b, tailF Φ M b θ ^ 2 := by
  set S₁ := ∑ m ∈ Finset.Icc 1 M, ∫ θ in (1 : ℝ)..b, Φ (m * θ) ^ 2 with hS₁
  set T₁ := ∫ θ in (1 : ℝ)..b, tailF Φ M b θ ^ 2 with hT₁
  have hS0 : 0 ≤ S₁ := Finset.sum_nonneg fun m _ => intervalIntegral.integral_nonneg hb1 fun θ _ => sq_nonneg _
  refine ⟨fun j => ?_, fun j hj hjk => ?_⟩
  · unfold deltaSeq
    split_ifs
    · exact (free_gain hS0 hT).1
    · rw [div_lt_one (by linarith [hC j])]; linarith
  · unfold deltaSeq
    split_ifs with h1
    · subst h1
      simpa using (free_gain hS0 hT).2
    · have hj2 : 2 ≤ j := by
        have := (Finset.mem_Icc.mp hj).1; omega
      have hjM : (j : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hj).2
      have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
      exact trivial_gain_of_cross Φ hj1 (hjM.trans hMb) hcont (hC j) (hcross j hj hj2 hjk)

end Cvs.L2a.TrivialGainsCrossConstants
