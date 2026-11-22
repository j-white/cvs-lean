import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The orbit gap at integer `M` and its failure in the windows

For integers `2 ≤ m ≤ M − 1` the orbit product `(m² − 1)((M/m)² − 1)` is at least `15/4`, with equality at
`(M, m) = (3, 2)`; for real `X` in the window `m < X < m²/√(m² − 1)` it is below `1`. Both are restated through
`Ymax x = x/√(x² − 1)`: the gap is `Ymax (M/m) < m`, the window is `m < Ymax (X/m)`, and the window top is below `m + 1`.
-/

namespace Cvs.L2a.OrbitGapIntegerM

open Real

/-- `Ymax x = x/√(x² − 1)`, the top of the orbit through `(x, ·)`. -/
noncomputable def Ymax (x : ℝ) : ℝ := x / √(x ^ 2 - 1)

end Cvs.L2a.OrbitGapIntegerM
