import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A cross-rung pair as an amplitude against two phases

With two rungs in Prüfer form, `ψ_i = √(E_i/a_i) cos Θ_i` and `ψ_j = √(E_j/a_j) cos Θ_j` (Cvs.Upstream.SturmLiouvillePrufer), the pair
`ψ_i(t) ψ_j(mt)` is the amplitude `√(E_i(t)/a_i(t)) √(E_j(mt)/a_j(mt))` against `(cos(Θ_i(t) − Θ_j(mt)) +
cos(Θ_i(t) + Θ_j(mt)))/2`, and the phase difference has derivative `Θ_i'(t) − m Θ_j'(mt)` in the two rates.
-/

namespace Cvs.Prolate.CrossRungPhasePair

open Real Set

/-- `cos x cos y = (cos(x − y) + cos(x + y))/2`. -/
theorem cos_mul_cos (x y : ℝ) : Real.cos x * Real.cos y = (Real.cos (x - y) + Real.cos (x + y)) / 2 := by
  rw [Real.cos_sub, Real.cos_add]; ring

end Cvs.Prolate.CrossRungPhasePair
