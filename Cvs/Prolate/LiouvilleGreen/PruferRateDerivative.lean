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
# The derivative of the Prüfer rate

The rate `Θ' = a/p + w q uψ/(aE)` of Cvs.Upstream.SturmLiouvillePrufer is differentiable wherever `p`, `q`, `w` are and `a > 0`, `E > 0`, with
the explicit derivative `(wq·p − a·p')/p²` for the frequency and the quotient rule for the correction, whose
numerator `w q uψ` has derivative `(w' q + w q') uψ + w q (u'ψ + uψ')` with `u' = −qψ`, `ψ' = u/p`, and whose
denominator `aE` has derivative `w q E + a E'`: the data behind `∫|φ''|` in the tests of Cvs.Upstream.FirstDerivativeTestVariation and Cvs.Upstream.SecondDerivativeWindowTest.
-/

namespace Cvs.Prolate.LiouvilleGreen.PruferRateDerivative

open Real Set

variable {p p' a w w' q q' ψ u : ℝ → ℝ}

/-- The derivative of the frequency `a/p`. -/
noncomputable def freq' (p p' a w q : ℝ → ℝ) (t : ℝ) : ℝ := (w t * q t * p t - a t * p' t) / p t ^ 2

end Cvs.Prolate.LiouvilleGreen.PruferRateDerivative
