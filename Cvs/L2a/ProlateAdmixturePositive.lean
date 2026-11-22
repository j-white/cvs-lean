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
# L2a for an admixture `ψ_a − κψ_b`: positive for every large `c`, uniformly in `M`, `J`, `P`, `R`, `N`

With `TailModesPositiveLargeC`'s scales, the norm is at least `N_a/2 − κ²N_b` (Cvs.L2a.ModeTailNormUpperDifferenceLower), `N_b ≤ C_b G/c`, `TwoTailCrossPrimeSide`'s cross bound is at most twice
`TailModesTerminalInequality`'s prime bound, and Cvs.L2a.ProlateTailCombinationTerminal on the pair gives the rest; so `16ΓC_bκ² ≤ r₀ = arccos(1/2) − arccos(1/√2)` is enough,
`C_b = K + π + 1 + 4π²/6 + 2C_x + 24(π²/6 + 6)`, with `K`, `Γ = G/G_m` fixed and `|χ_a − χ_b| ≤ (3/4)c√c`.
-/

namespace Cvs.L2a.ProlateAdmixturePositive

open Real Set MeasureTheory Filter Cvs.L2a.TailOfModes

/-- A tail of a function continuous on `[1, Mb]` is square-integrable on `(1, ∞)`. -/
theorem tailF_sq_integrableOn {ψ : ℝ → ℝ} {M : ℕ} {b : ℝ}
    (hcont : ContinuousOn ψ (Icc 1 (M * b))) : IntegrableOn (fun θ => tailF ψ M b θ ^ 2) (Ioi 1) := by
  have hint : IntegrableOn (fun θ => (∑ m ∈ Finset.Icc 1 M, ψ (m * θ)) ^ 2) (Ioc 1 b) := by
    apply ContinuousOn.integrableOn_Icc (a := 1) (b := b) _ |>.mono_set Ioc_subset_Icc_self
    apply ContinuousOn.pow
    apply continuousOn_finsetSum; intro m hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hmM : (m : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hm).2
    exact hcont.comp (continuousOn_const.mul continuousOn_id) (fun θ hθ =>
      ⟨one_le_mul_of_one_le_of_one_le hm1 hθ.1,
        mul_le_mul hmM hθ.2 (show (0 : ℝ) ≤ θ by linarith [hθ.1]) (Nat.cast_nonneg M)⟩)
  have e : (fun θ => tailF ψ M b θ ^ 2) = (Ioc 1 b).indicator (fun θ => (∑ m ∈ Finset.Icc 1 M, ψ (m * θ)) ^ 2) := by
    funext θ; unfold tailF
    by_cases h : θ ∈ Ioc 1 b
    · simp [indicator_of_mem h]
    · simp [indicator_of_notMem h]
  rw [e]
  exact ((integrable_indicator_iff measurableSet_Ioc).mpr hint).integrableOn

end Cvs.L2a.ProlateAdmixturePositive
