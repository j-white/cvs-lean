import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The edge layer variable

With `ξ(s) = 1 + s²/(2c²)`, a pairing over `[ξ(s₀), ξ(s₁)]` is the pairing of `F(ξ(s))·s/c²` over `[s₀, s₁]`, and the
rung's frequency in `s` is exactly `(a/p)(ξ(s))·ξ'(s) = √(2q(ξ(s))/(ξ(s) + 1))/c`: smooth up to `s = 0`, where it
equals `σ = √(c² − χ)/c`, instead of the `1/√(ξ − 1)` singularity of the frequency in `ξ`.
-/

namespace Cvs.Prolate.LiouvilleGreen.EdgeLayerVariable

open Real Set MeasureTheory intervalIntegral

/-- The edge layer variable: `ξ(s) = 1 + s²/(2c²)`. -/
noncomputable def xiOf (c s : ℝ) : ℝ := 1 + s ^ 2 / (2 * c ^ 2)

theorem hasDerivAt_xiOf (c s : ℝ) (hc : c ≠ 0) : HasDerivAt (xiOf c) (s / c ^ 2) s := by
  unfold xiOf
  have := ((hasDerivAt_pow 2 s).div_const (2 * c ^ 2)).const_add 1
  refine this.congr_deriv ?_
  field_simp
  ring

end Cvs.Prolate.LiouvilleGreen.EdgeLayerVariable
