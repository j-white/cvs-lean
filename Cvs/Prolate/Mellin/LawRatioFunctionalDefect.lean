import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The functional-equation defect of the law ratio

The cosine factor of the Mellin transform maps the reflected Gaussian reference to the Gaussian reference:
`2Γ(s) cos(πs/2) c^{−s} mg c (1 − s) = √(2π/c) · mg c s` (self-duality of `e^{−cw²/2}`). Hence for
`0 < Re s < 1` and any `μ`, the combination `2Γ(s) cos(πs/2) c^{−s} M(1 − s) − μ M(s)`, `M = mel h`, equals
`mg c s · D(s)` with `D(s) = √(2π/c) P(1 − s) − μ P(s)`, `P = lawRatio c h`. On `Re s = ½`, `P(1 − s) = conj P(s)`.
-/

noncomputable section

open Real Complex ComplexConjugate

namespace Cvs.Prolate.Mellin.LawRatioFunctionalDefect


/-- A positive real base: `(r : ℂ)^w = exp(w log r)`. -/
theorem ofReal_cpow_eq_exp {r : ℝ} (hr : 0 < r) (w : ℂ) : (r : ℂ) ^ w = exp (w * (Real.log r : ℂ)) := by
  rw [cpow_def_of_ne_zero (by exact_mod_cast hr.ne'), ← ofReal_log hr.le, mul_comm]

end Cvs.Prolate.Mellin.LawRatioFunctionalDefect
