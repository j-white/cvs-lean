import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.MeasureTheory.Function.L2Space

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The correlation through a plane, in `L²`

For square-integrable `F_e`, `F_f` on a measure space, with `F_f = Σ αⱼ vⱼ + F^⊥` in `L²`, `v` orthonormal and
`F^⊥` orthogonal to the plane, the plane bridge of an earlier result reads in integrals:
`−((ρ + 2η)(∫F_e² + ∫F_f²)) ≤ 2 ∫ F_e F_f` whenever `Σⱼ (∫ F_e vⱼ)² ≤ ρ² ∫F_e²` and `∫(F^⊥)² ≤ η² ∫F_e²`,
which is the correlation hypothesis of Cvs.L2a.FarMassPlateau with `w = 1` once the edge and far sums are the `L²` elements.
-/

namespace Cvs.L2a.PlaneCorrelationL2

open MeasureTheory Finset
open scoped InnerProductSpace

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The squared norm of an `L²` element is the integral of its square. -/
theorem norm_sq_eq_integral (f : α →₂[μ] ℝ) : ‖f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [sq]

/-- The inner product of two `L²` elements is the integral of their product. -/
theorem inner_eq_integral (f g : α →₂[μ] ℝ) : ⟪f, g⟫_ℝ = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [mul_comm]

end Cvs.L2a.PlaneCorrelationL2
