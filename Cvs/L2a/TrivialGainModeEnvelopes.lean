import Mathlib
import Cvs.L2a.TailOfModes

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The trivial-gain constant from mode-pair envelopes

On `[j, b]` with `j ≥ 1` the tail is the plain Poisson sum `Σ_m Φ(mθ)`, so its mass is the mode-pair Gram
`Σ_{m,m′} ∫_j^b Φ(mθ)Φ(m′θ)` with diagonal the mode masses; relative envelopes `E_{mm′}` of the off-diagonal pairs,
symmetric with row sums at most `δ`, give `(1 − δ)Σ_m ∫_j^b Φ(mθ)² ≤ ∫_j^b tailF²`, the hypothesis on `δ_j` in Cvs.L2a.PlateauAssemblyTrivialGain.
-/

namespace Cvs.L2a.TrivialGainModeEnvelopes

open Real Set Finset MeasureTheory Cvs.L2a.TailOfModes

/-- **The tail mass on `[j, b]` is the mode-pair Gram**, for `j ≥ 1`. -/
theorem integral_tailF_sq_eq_gram (Φ : ℝ → ℝ) {M : ℕ} {b j : ℝ} (hj : 1 ≤ j) (hjb : j ≤ b)
    (hcont : ContinuousOn Φ (Icc 1 (M * b))) :
    ∫ θ in j..b, tailF Φ M b θ ^ 2
      = ∑ m ∈ Finset.Icc 1 M, ∑ m' ∈ Finset.Icc 1 M, ∫ θ in j..b, Φ (m * θ) * Φ (m' * θ) := by
  -- each dilate is continuous on `[j, b]`
  have hcm : ∀ m ∈ Finset.Icc 1 M, ContinuousOn (fun θ => Φ (m * θ)) (Icc j b) := fun m hm => by
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hmM : (m : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hm).2
    refine hcont.comp (continuous_const.mul continuous_id).continuousOn fun θ hθ => ?_
    have hθ0 : 0 ≤ θ := by linarith [hθ.1]
    constructor
    · nlinarith [hθ.1]
    · have := mul_le_mul hmM hθ.2 hθ0 (by positivity : (0 : ℝ) ≤ M)
      simpa using this
  have hII : ∀ m ∈ Finset.Icc 1 M, ∀ m' ∈ Finset.Icc 1 M,
      IntervalIntegrable (fun θ => Φ (m * θ) * Φ (m' * θ)) volume j b := fun m hm m' hm' =>
    ((hcm m hm).mul (hcm m' hm')).intervalIntegrable_of_Icc hjb
  -- the tail on `[j, b]` is the plain sum
  have htail : ∫ θ in j..b, tailF Φ M b θ ^ 2
      = ∑ m ∈ Finset.Icc 1 M, ∑ m' ∈ Finset.Icc 1 M, ∫ θ in j..b, Φ (m * θ) * Φ (m' * θ) := by
    have hcongr : ∫ θ in j..b, tailF Φ M b θ ^ 2
        = ∫ θ in j..b, ∑ m ∈ Finset.Icc 1 M, ∑ m' ∈ Finset.Icc 1 M, Φ (m * θ) * Φ (m' * θ) := by
      refine intervalIntegral.integral_congr_ae ?_
      refine Filter.Eventually.of_forall fun θ hθ => ?_
      rw [uIoc_of_le hjb] at hθ
      have hθ1 : θ ∈ Ioc 1 b := ⟨lt_of_le_of_lt hj hθ.1, hθ.2⟩
      unfold tailF
      rw [Set.indicator_of_mem hθ1, sq, Finset.sum_mul_sum]
    have hsumII : ∀ m ∈ Finset.Icc 1 M,
        IntervalIntegrable (fun θ => ∑ m' ∈ Finset.Icc 1 M, Φ (m * θ) * Φ (m' * θ)) volume j b :=
      fun m hm => (continuousOn_finsetSum _ fun m' hm' => (hcm m hm).mul (hcm m' hm')).intervalIntegrable_of_Icc hjb
    rw [hcongr, intervalIntegral.integral_finsetSum hsumII]
    apply Finset.sum_congr rfl; intro m hm
    exact intervalIntegral.integral_finsetSum fun m' hm' => hII m hm m' hm'
  exact htail

end Cvs.L2a.TrivialGainModeEnvelopes
