import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The norm of a tail with modes: the first mode plus the cross-mode form

For `F(θ) = Σ_{m ≤ M} G(mθ)` on `(1, b]`, `∫₁ᵇ F² = Σ_m ∫₁ᵇ G(mθ)² + Σ_{m ≠ m'} ∫₁ᵇ G(mθ)G(m'θ)`, and every same-mode
term is a square, so `∫₁ᵇ F² ≥ ∫₁ᵇ G² + Σ_{m ≠ m'} ∫₁ᵇ G(mθ)G(m'θ)`: the tail norm exceeds the first-mode norm by
the cross-mode form, whatever `G` is.
-/

namespace Cvs.L2a.ModeTailNormCrossForm

open Real Set Finset intervalIntegral

/-- The square of a finite sum of functions integrates to the double sum of the pair integrals. -/
theorem integral_sq_finset_sum {lo hi : ℝ} {s : Finset ℕ} (f : ℕ → ℝ → ℝ)
    (hI : ∀ m ∈ s, ∀ m' ∈ s, IntervalIntegrable (fun θ => f m θ * f m' θ) MeasureTheory.volume lo hi) :
    ∫ θ in lo..hi, (∑ m ∈ s, f m θ) ^ 2 = ∑ m ∈ s, ∑ m' ∈ s, ∫ θ in lo..hi, f m θ * f m' θ := by
  have e : ∀ θ, (∑ m ∈ s, f m θ) ^ 2 = ∑ m ∈ s, ∑ m' ∈ s, f m θ * f m' θ := by
    intro θ; rw [sq, Finset.sum_mul_sum]
  simp_rw [e]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl; intro m hm
    rw [integral_finsetSum]; intro m' hm'; exact hI m hm m' hm'
  · intro m hm
    have h := IntervalIntegrable.sum s fun m' hm' => hI m hm m' hm'
    simpa only [Finset.sum_fn] using h

end Cvs.L2a.ModeTailNormCrossForm
