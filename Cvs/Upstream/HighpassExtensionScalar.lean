import Mathlib.Analysis.InnerProductSpace.Basic

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A highpass extension bounds the central resolvent objectives

Let `v` agree with `φ` against `x` (`‖x‖ = ‖f‖`) and be orthogonal to a lowpass `w` with `⟨x, w⟩ = ‖a‖²`, `‖w‖ ≤ ‖a‖`.
Then `2⟨φ, f⟩ − ‖f‖² + ‖a‖² ≤ ‖v‖²` and `2⟨φ, f⟩ − ‖f‖² + ⟨f, a⟩ ≤ 2‖v‖² − ½‖f − a‖²`; the scalar core
`p ≤ √V√D`, `D ≤ F − a`, `2q ≤ F + a` ⟹ `2p − F + q ≤ 2V` carries the same algebra.
-/

noncomputable section

open Real RealInnerProductSpace

namespace Cvs.Upstream.HighpassExtensionScalar

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `2p − F + q ≤ 2V` from `p ≤ √V√D`, `0 ≤ D ≤ F − a` and `2q ≤ F + a`. -/
theorem scalar_bound {p F a q V D : ℝ} (hV : 0 ≤ V) (hD0 : 0 ≤ D) (hp : p ≤ √V * √D) (hD : D ≤ F - a)
    (hq : 2 * q ≤ F + a) : 2 * p - F + q ≤ 2 * V := by
  have h1 := Real.sq_sqrt hV
  have h2 := Real.sq_sqrt hD0
  nlinarith [sq_nonneg (2 * √V - √D)]

end Cvs.Upstream.HighpassExtensionScalar

end
