import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The zero-side pairing: every `ρ(1 − ρ)` is an eigenvalue, and RH is non-neutrality

On finitely supported `f : ℂ →₀ ℂ`, `B f g = ∑_ρ f(ρ) · conj g(1 − ρ̄)` pairs `ρ` with its reflection `1 − ρ̄`, and
`(T f)(ρ) = ρ(1 − ρ) f(ρ)` is `B`-self-adjoint because `λ(1 − ρ̄) = conj λ(ρ)`. Every `δ_ρ` is an eigenvector of
`ρ(1 − ρ)`, and `B δ_ρ δ_ρ ≠ 0` exactly when `Re ρ = ½`: this is a spectral object over `B` precisely under RH.
-/

noncomputable section

open Finsupp

namespace Cvs.Zeta.ZeroSidePairingEigenvalues


/-- Multiplication by the spectral parameter, `(T f)(ρ) = ρ(1 − ρ) f(ρ)`. -/
def zeroSideT : (ℂ →₀ ℂ) →ₗ[ℂ] ℂ →₀ ℂ :=
  Finsupp.lsum ℂ fun ρ => (ρ * (1 - ρ)) • Finsupp.lsingle ρ

theorem zeroSideT_single (ρ a : ℂ) : zeroSideT (single ρ a) = (ρ * (1 - ρ)) • single ρ a := by
  simp [zeroSideT]

end Cvs.Zeta.ZeroSidePairingEigenvalues
