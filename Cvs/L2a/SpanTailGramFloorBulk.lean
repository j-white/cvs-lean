import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The tail Gram floor of the rung span, given the bulk's near-orthogonality

For the rung span with `G = Σ a_iψ_i` and the bulk tail `B = Σ_m G_b(m·)` (`G_b = G·1_{(θ₀, ∞)}`, `1 < θ₀ ≤ 2`): if
`∫₁^{θ₀} B² ≤ s² ∫_{θ₀}^b G²` and `∫₁ᵇ B² ≥ (1 − ε) ∫_{θ₀}^b G²` with `s + ε ≤ 1`, then
`∫₁ᵇ (Σ_m G(mθ))² ≥ (1 − s − ε) Σ_i a_i² (∫₁ᵇ ψ_i² − Σ_j T_j)`: the tail Gram of the span is bounded below by the
first-mode floor of Cvs.Prolate.Gram.RungGramFloorAtInfinity through the split of an earlier result, and only the two bulk inputs remain.
-/

namespace Cvs.L2a.SpanTailGramFloorBulk

open Real Set Finset intervalIntegral

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A function that is a continuous function on a measurable set and `0` elsewhere is interval integrable. -/
theorem intervalIntegrable_ite {f : ℝ → ℝ} {P : ℝ → Prop} [DecidablePred P] {a b : ℝ} (hab : a ≤ b)
    (hP : MeasurableSet {θ | P θ}) (hf : ContinuousOn f (Icc a b)) :
    IntervalIntegrable (fun θ => if P θ then f θ else 0) MeasureTheory.volume a b := by
  have e : (fun θ => if P θ then f θ else 0) = Set.indicator {θ | P θ} f := by
    funext θ; simp [Set.indicator]
  rw [e, intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  exact (hf.integrableOn_Icc).indicator hP

end Cvs.L2a.SpanTailGramFloorBulk
