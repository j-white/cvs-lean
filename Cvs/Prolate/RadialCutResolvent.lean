import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The resolvent of a radial cut, exactly

For `((w²−1)ψ')' + (c²w² − χ)ψ = 0` and `f = logScale(1_{(M,∞)}ψ)`, `u = (w²−1)ψ'`, `D_b = b²(w²−1) + c²w⁴`:
`G̃ = √w((b+½)(w²−1)ψ + wu)/D_b` solves `G̃' − bG̃ = −f + E_b` in `s = log w`, with `E_b` explicit, so
`2(S(0)/b − L_b) = ∫_M^∞ ψ²(2c²w⁴/(bD_b) + 2c²w⁴(2−w²)/D_b²) + Mψ(M)²(M²−1)/D_b(M) − 2∫ f K_b E_b`.
-/

noncomputable section

open MeasureTheory Real Set Filter Topology

namespace Cvs.Prolate.RadialCutResolvent

/-- The flux `u = (w² − 1)ψ'`. -/
def uu (v : ℝ → ℝ) (w : ℝ) : ℝ := (w ^ 2 - 1) * v w

section Radial

variable {ψ v v' : ℝ → ℝ} {c χ : ℝ}
    (hψ : ∀ r ∈ Ici (1 : ℝ), HasDerivAt ψ (v r) r)
    (hv : ∀ r ∈ Ici (1 : ℝ), HasDerivAt v (v' r) r)
    (hode : ∀ r ∈ Ici (1 : ℝ), (r ^ 2 - 1) * v' r + 2 * r * v r + (c ^ 2 * r ^ 2 - χ) * ψ r = 0)

end Radial

section Radial

variable {ψ v v' : ℝ → ℝ} {c χ : ℝ}
    (hψ : ∀ r ∈ Ici (1 : ℝ), HasDerivAt ψ (v r) r)
    (hv : ∀ r ∈ Ici (1 : ℝ), HasDerivAt v (v' r) r)
    (hode : ∀ r ∈ Ici (1 : ℝ), (r ^ 2 - 1) * v' r + 2 * r * v r + (c ^ 2 * r ^ 2 - χ) * ψ r = 0)

include hψ in
theorem continuousOn_comp_exp {a : ℝ} (ha : 0 ≤ a) : ContinuousOn (fun y => ψ (exp y)) (Ici a) := fun y hy =>
  ((hψ (exp y) (one_le_exp (le_trans ha hy))).continuousAt.comp (continuous_exp.continuousAt)).continuousWithinAt

end Radial

end Cvs.Prolate.RadialCutResolvent
