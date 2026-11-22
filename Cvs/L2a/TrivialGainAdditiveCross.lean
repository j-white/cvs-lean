import Mathlib
import Cvs.L2a.TailOfModes
import Cvs.L2a.TrivialGainModeEnvelopes

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The trivial gain from an additive cross bound

On `[j, b]` the tail mass `N_j` is the mode masses plus their cross terms (Cvs.L2a.TrivialGainModeEnvelopes), so a cross bound charged to the
tail mass itself, `|Σ_{m≠m′} X_{mm′}| ≤ C·N_j`, gives `(1/(1 + C))Σ_m ∫_j^b Φ(mθ)² ≤ N_j` for every `C ≥ 0`: the
hypothesis of Cvs.L2a.PlateauAssemblyTrivialGain on `δ_j` with `δ_j = C/(1 + C) < 1` whatever the size of `C`.
-/

namespace Cvs.L2a.TrivialGainAdditiveCross

open Real Set Finset MeasureTheory Cvs.L2a.TailOfModes Cvs.L2a.TrivialGainModeEnvelopes

/-- **Gram form**: `N = Σ_m X_mm + Σ_{m≠m′} X_{mm′}` with `|Σ_{m≠m′}X| ≤ C·N` gives `(1/(1 + C))Σ_m X_mm ≤ N`. -/
theorem gain_of_cross (s : Finset ℕ) (X : ℕ → ℕ → ℝ) {N C : ℝ} (hC : 0 ≤ C)
    (hN : N = ∑ m ∈ s, ∑ m' ∈ s, X m m')
    (hcross : |∑ m ∈ s, ∑ m' ∈ s.erase m, X m m'| ≤ C * N) :
    (1 / (1 + C)) * ∑ m ∈ s, X m m ≤ N := by
  have hsplit : ∑ m ∈ s, ∑ m' ∈ s, X m m' = ∑ m ∈ s, X m m + ∑ m ∈ s, ∑ m' ∈ s.erase m, X m m' := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m hm => (Finset.add_sum_erase s _ hm).symm
  have h1 := neg_abs_le (∑ m ∈ s, ∑ m' ∈ s.erase m, X m m')
  have hle : ∑ m ∈ s, X m m ≤ (1 + C) * N := by rw [hN] at hcross ⊢; linarith [hsplit]
  rw [one_div, ← div_eq_inv_mul, div_le_iff₀ (by linarith)]
  linarith

/-- **The trivial gain on `[j, b]` from an additive cross bound.** -/
theorem trivial_gain_of_cross (Φ : ℝ → ℝ) {M : ℕ} {b j C : ℝ} (hj : 1 ≤ j) (hjb : j ≤ b)
    (hcont : ContinuousOn Φ (Icc 1 (M * b))) (hC : 0 ≤ C)
    (hcross : |∑ m ∈ Finset.Icc 1 M, ∑ m' ∈ (Finset.Icc 1 M).erase m, ∫ θ in j..b, Φ (m * θ) * Φ (m' * θ)|
      ≤ C * ∫ θ in j..b, tailF Φ M b θ ^ 2) :
    (1 - C / (1 + C)) * ∑ m ∈ Finset.Icc 1 M, ∫ θ in j..b, Φ (m * θ) ^ 2 ≤ ∫ θ in j..b, tailF Φ M b θ ^ 2 := by
  have h := gain_of_cross (Finset.Icc 1 M) (fun m m' => ∫ θ in j..b, Φ (m * θ) * Φ (m' * θ)) hC
    (integral_tailF_sq_eq_gram Φ hj hjb hcont) hcross
  have e : 1 - C / (1 + C) = 1 / (1 + C) := by field_simp; ring
  rw [e]
  simpa only [sq] using h

end Cvs.L2a.TrivialGainAdditiveCross
