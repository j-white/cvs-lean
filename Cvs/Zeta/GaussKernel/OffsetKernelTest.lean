import Mathlib
import Cvs.Zeta.GaussKernel.AdmissibleKernel

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The offset kernel as a Guinand–Weil test

`research/pathlaw/lean/Cvs.Zeta/GuinandWeilClassical.lean` proves the classical explicit
formula for **any** `h : ℂ → ℂ` that is differentiable, even, and satisfies two decay
conditions; `GaussClassical.lean` instantiates it at `e^{-w²}`.
-/

namespace Cvs.GaussKernel

open Cvs.Zeta.GaussKernel.AdmissibleKernel

/-! ### The two hypotheses that are immediate

`guinand_weil_classical` also asks that `h` be entire and even.  Both hold for
`gaussAmp` by inspection, and both are statable here — unlike `StripDecayRe`,
which is phrased in `Cvs.Zeta`'s vocabulary. -/

/-- **The offset kernel is even.**  Negating `w` exchanges the two bumps. -/
theorem gaussAmp_even (lam a : ℝ) (w : ℂ) :
    gaussAmp lam a (-w) = gaussAmp lam a w := by
  simp only [gaussAmp]
  rw [show (-w - (a : ℂ)) ^ 2 = (w + (a : ℂ)) ^ 2 by ring,
    show (-w + (a : ℂ)) ^ 2 = (w - (a : ℂ)) ^ 2 by ring]
  ring

end Cvs.GaussKernel
