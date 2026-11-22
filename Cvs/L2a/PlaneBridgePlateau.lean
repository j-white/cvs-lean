import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The plateau from the plane bridge

The edge and far Poisson sums of a continuous span function are in `L²(1, ∞)`; if the far sum is
`Σ αᵢ vᵢ + F^⊥` with `v` orthonormal profiles and `F^⊥` orthogonal to them, the pairings of the edge sum with the
profiles at most `ρ ‖F_e‖` in square sum and `‖F^⊥‖ ≤ η ‖F_e‖`, then the plateau of Cvs.L2a.FarMassPlateau holds with `w = 1` and
`r = ρ + 2η`: `(1 − (ρ + 2η))(1 − ε) H_k ∫_k^b Φ² ≤ ∫F²`, with no reference to the coefficients of the span.
-/

namespace Cvs.L2a.PlaneBridgePlateau

open Real Set MeasureTheory
open scoped InnerProductSpace

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The function of a combination of `L²` elements is the combination of their functions, almost everywhere. -/
theorem coeFn_sum_smul_toLp {α : Type*} [MeasurableSpace α] {μ : Measure α} (v : ι → α → ℝ)
    (hv : ∀ i, MemLp (v i) 2 μ) (a : ι → ℝ) :
    ⇑(∑ i, a i • (hv i).toLp (v i)) =ᵐ[μ] fun x => ∑ i, a i * v i x := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact Lp.coeFn_zero _ _ _
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    filter_upwards [Lp.coeFn_add (a j • (hv j).toLp (v j)) (∑ i ∈ s, a i • (hv i).toLp (v i)),
      Lp.coeFn_smul (a j) ((hv j).toLp (v j)), (hv j).coeFn_toLp, ih] with x h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, Finset.sum_insert hj, smul_eq_mul]

end Cvs.L2a.PlaneBridgePlateau
