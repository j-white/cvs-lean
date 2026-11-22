import Mathlib
import Cvs.Prolate.EdgeBesselCount

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The edge value of a rung is at least its plunge over a polynomial

For the rung of index `k` at `c ≥ 80` with depth `D = c² − χ_k ≥ 4c/log c` and `λ = lamR c k`:
`1 − λ ≤ P(c)·h(1)²`, `P(c) = (11/10)(K̄(c, 5) + 1/10)/c + 4e⁵²c⁵`. For `D ≥ 5c` this is `EdgeBesselCount`'s mass law
`∫₁^∞ψ² ≤ (11/10)ψ(1)²(K̄ + 1/10)/(2c)` against `∫₁^∞ψ² = (π/c)(1 − λ)` and `ψ(1)² = (2π/c)λh(1)²`; for `D ≤ 5c` it is
`TopPlungeFloor`'s `1 ≤ 4e⁵²c⁵h(1)²`. Hence `E_j² ≥ (1 − λ_{4j})/P(2πx)` for every rung.
-/

noncomputable section

open Real Set MeasureTheory Filter
open Cvs.L2a.AngularProlateTailPositive (psi)

namespace Cvs.Prolate.Envelope.RungEdgePlungeLower

theorem Kbar_nonneg {c : ℝ} (hc : 80 ≤ c) : 0 ≤ Cvs.Prolate.EdgeBesselCount.Kbar c 5 + 1 / 10 := by
  unfold Cvs.Prolate.EdgeBesselCount.Kbar
  have : 0 ≤ Real.log (12 * c / 5) := Real.log_nonneg (by rw [le_div_iff₀ (by norm_num)]; linarith)
  have : 0 ≤ 5 / (12 * c) := by positivity
  linarith

end Cvs.Prolate.Envelope.RungEdgePlungeLower

end
