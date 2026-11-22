import Mathlib
import Cvs.L2a.PlaneCorrelationL2

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The separated arch kernel `η/(η² − θ²)` on physical L²

On `0 < θ < 1 < η` the arch cross kernel `η/(η² − θ²) = max(θ, η)/|η² − θ²|` is the rank-one kernel `1/η`
plus `CubicTailSeparatedKernel`'s cubic kernel `θ²/(η(η² − θ²))`, so the separated pairing splits exactly as
`∫∫ G(θ)F(η)η/(η² − θ²) = ∫∫ G(θ)F(η)θ²/(η(η² − θ²)) + (∫₀¹ G)(∫₁^∞ F(η)/η dη)`. Carleman's inequality for the
first term and Cauchy–Schwarz for the second give `|∫∫ G(θ)F(η)η/(η² − θ²)| ≤ (π/2 + 1)‖F‖₂‖G‖₂`.
-/

noncomputable section

open Real Set MeasureTheory Filter

namespace Cvs.WeilForm.SeparatedArchKernelL2


/-! ### The kernel -/

/-! ### Cauchy–Schwarz in physical L² -/

/-- The `L²` norm of a representative is the square root of its energy. -/
theorem norm_toLp_eq_sqrt {α : Type*} [MeasurableSpace α] {μ : Measure α} {g : α → ℝ}
    (hg : MemLp g 2 μ) : ‖hg.toLp g‖ = √(∫ x, g x ^ 2 ∂μ) := by
  have h := Cvs.L2a.PlaneCorrelationL2.norm_sq_eq_integral (hg.toLp g)
  have he : (∫ x, (hg.toLp g) x ^ 2 ∂μ) = ∫ x, g x ^ 2 ∂μ :=
    integral_congr_ae (by filter_upwards [hg.coeFn_toLp] with x hx; rw [hx])
  rw [← Real.sqrt_sq (norm_nonneg _), h, he]

/-! ### The reciprocal pole factor -/

/-! ### The split and the bound -/

end Cvs.WeilForm.SeparatedArchKernelL2
