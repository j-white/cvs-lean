import Mathlib
import Cvs.Zeta.Digamma
import Cvs.Zeta.DigammaEulerLimitInstance
import Cvs.Zeta.ExplicitFormula.ArchimedeanBoundTestFree

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The halo at any depth
-/

namespace Cvs.Detection

open MeasureTheory

/-- **The halo at depth `K`.** Keeping any initial segment of the bank bounds `W` below; is `K =
1`. -/
theorem W_ge_partial (K : ℕ) (u : ℝ) :
    (∑ k ∈ Finset.range K, Cvs.Zeta.digammaDeficit u k) / 2 ≤ Cvs.Detection.W u := by
  have hsum := Cvs.Transform.tsum_digammaDeficit u
  have hle : ∑ k ∈ Finset.range K, Cvs.Zeta.digammaDeficit u k
      ≤ ∑' k : ℕ, Cvs.Zeta.digammaDeficit u k :=
    Summable.sum_le_tsum _ (fun i _ => Cvs.Zeta.digammaDeficit_nonneg u i)
      (Cvs.Transform.summable_digammaDeficit u)
  rw [Cvs.Detection.W, ← hsum]
  linarith [hle]

end Cvs.Detection
