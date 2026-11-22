import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues

/-!
# `O(log T)` zeros of `ζ` in a fixed-radius disc at height `T`

Rung 6 of the Guinand–Weil ladder needs `ξ'/ξ` bounded on horizontal lines, which reduces to
counting zeros in a unit window at height `T`.
-/

open Complex Real Set Metric

namespace Cvs.Zeta

theorem analyticAt_riemannZeta {z : ℂ} (hz : z ≠ 1) : AnalyticAt ℂ riemannZeta z :=
  DifferentiableOn.analyticAt
    (fun _ hw => (differentiableAt_riemannZeta hw).differentiableWithinAt)
    ((isOpen_compl_singleton).mem_nhds hz)

end Cvs.Zeta
