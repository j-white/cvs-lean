import Mathlib
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZetaRealSegment

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The low-eigenvalue count is bounded by the number of distinct low zeros

`Z_≤T = {ρ : |Im ρ| ≤ T}` is a finite set of points, closed under `ρ ↦ ρ̄` and `ρ ↦ 1 − ρ`, with no real point;
`N_dist(T) = #{ρ : 0 < Im ρ ≤ T}` counts distinct zeros. If `aᵀAa = Σ_ρ m_ρ Re(u_{1−ρ}(a)u_ρ(a))`, summable, and
`Σ_{|Im ρ| > T} |m_ρ Re(u_{1−ρ}u_ρ)| ≤ ε aᵀMa`, then `n₋(εM − A)` and `n₋(A + εM)` are at most `2 N_dist(T)`, and
at most `N_dist(T)` when `u_{1−s} = ω_s u_s`.
-/

noncomputable section

open Matrix Module ComplexConjugate

namespace Cvs.StepA.LowEigenvalueCountZeros


/-- The nontrivial zeros. -/
abbrev Z := Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet

/-- **No nontrivial zero is real.** -/
theorem im_ne_zero (ρ : Z) : (ρ : ℂ).im ≠ 0 := by
  intro him
  obtain ⟨hz, h0, h1⟩ := ρ.2
  have hreal : (ρ : ℂ) = (((ρ : ℂ).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  rw [hreal] at hz
  exact Cvs.Zeta.riemannZeta_ne_zero_of_mem_Ioo h0 h1 hz

/-! ### The low zeros as a finite set of points -/

/-! ### The count -/

section Count

variable {ι : Type*} [Fintype ι]

end Count

end Cvs.StepA.LowEigenvalueCountZeros
