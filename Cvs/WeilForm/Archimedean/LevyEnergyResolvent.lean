import Mathlib
import Cvs.WeilForm.SelfConvolutionMaximum
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Lévy energy as a resolvent series

With `b_n = 2n + ½`, `S = f ⋆ f` and `L_b = ∫_0^∞ e^{−bv} S(v) dv = ∫ f(x) ∫_{y>x} f(y) e^{−b(y−x)} dy dx`:
`archFull f = Σ_n 2(S(0)/b_n − L_{b_n})` whenever the series converges (and then the Lévy integrand is integrable),
and `a(t) − a(0) = Σ_n 2t²/(b_n(b_n² + t²))`.
-/

noncomputable section

open MeasureTheory Real Set Filter Topology
open Cvs.Zeta.Explicit.Weil (selfConvolution)

namespace Cvs.WeilForm.Archimedean.LevyEnergyResolvent

theorem integrable_mul_shift {f : ℝ → ℝ} (hf : MemLp f 2 volume) (u : ℝ) :
    Integrable (fun s => f s * f (s + u)) volume :=
  hf.integrable_mul (hf.comp_measurePreserving (measurePreserving_add_right volume u))

theorem abs_selfConvolution_le {f : ℝ → ℝ} (hf : MemLp f 2 volume) (u : ℝ) :
    |selfConvolution f u| ≤ selfConvolution f 0 :=
  Cvs.WeilForm.SelfConvolutionMaximum.abs_selfConvolution_le u hf.integrable_sq (integrable_mul_shift hf u)

/-! ### The symbol as a resolvent series -/

end Cvs.WeilForm.Archimedean.LevyEnergyResolvent
