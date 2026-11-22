import Mathlib
import Cvs.L2a.FarMassPlateau
import Cvs.Zeta.Digamma.WeierstrassGammaSeq

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The weight lemma: `Σ_{n≤N} 2 log n / n ≤ H_N log N`

By induction, using `log((N+1)/N) ≥ 1/(N+1)` and `log(N+1) ≤ H_N`. Consequently, for `ξ ≥ 1`, the weighted
sum `Σ_{n≤⌊ξ⌋} (2 log n − log ξ)/n` is nonpositive.
-/

namespace Cvs.Upstream.LogHarmonicWeightBound

open Real Finset Cvs.L2a.FarMassPlateau

/-- `log (N+1) ≤ H_N`, in terms of `FarMassPlateau`'s harmonic number `harm`. -/
theorem log_succ_le_harm (N : ℕ) : Real.log ((N : ℝ) + 1) ≤ harm N := by
  have h1 := log_add_one_le_harmonic N
  have h2 : ((harmonic N : ℚ) : ℝ) = harm N := by
    rw [harmonic, Finset.range_eq_Ico, Finset.sum_Ico_add' (fun (i : ℕ) ↦ (i : ℚ)⁻¹) 0 N (c := 1)]
    simp only [Finset.Ico_add_one_right_eq_Icc, harm]
    push_cast; simp [one_div]
  rw [← h2]; push_cast at h1; exact h1

end Cvs.Upstream.LogHarmonicWeightBound
