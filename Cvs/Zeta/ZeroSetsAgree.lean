import Mathlib
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.XiStrip

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The two zero sets are one

The explicit formula indexes its zero side by the zeros of `Cvs.Zeta.riemannXi`.
-/

namespace Cvs.Zeta.ZeroIndex

open Cvs.Zeta.GaussKernel.AdmissibleKernel

/-- **The explicit formula's zero set is the criterion's zero set.**  `ξ`
vanishes exactly on the non-trivial zeros of `ζ`. -/
theorem riemannXi_eq_zero_iff_mem_nonTrivialZeroSet (s : ℂ) :
    Cvs.Zeta.riemannXi s = 0 ↔ s ∈ nonTrivialZeroSet := by
  constructor
  · intro h
    obtain ⟨h0, h1⟩ := Cvs.Zeta.riemannXi_zero_mem_strip h
    have hne : s ≠ 1 := fun hs => by simp [hs] at h1
    exact ⟨(Cvs.Zeta.riemannXi_eq_zero_iff_riemannZeta h0 hne).mp h, h0, h1⟩
  · rintro ⟨hz, h0, h1⟩
    have hne : s ≠ 1 := fun hs => by simp [hs] at h1
    exact (Cvs.Zeta.riemannXi_eq_zero_iff_riemannZeta h0 hne).mpr hz

/-- A zero of `ξ` is a member of the criterion's index type. -/
noncomputable def toNonTrivialZero {s : ℂ} (h : Cvs.Zeta.riemannXi s = 0) :
    nonTrivialZeroSet :=
  ⟨s, (riemannXi_eq_zero_iff_mem_nonTrivialZeroSet s).mp h⟩

@[simp] theorem coe_toNonTrivialZero {s : ℂ} (h : Cvs.Zeta.riemannXi s = 0) :
    ((toNonTrivialZero h : nonTrivialZeroSet) : ℂ) = s := rfl

/-- Conversely, every member of the criterion's index type is a zero of `ξ`. -/
theorem riemannXi_apply_eq_zero (ρ : nonTrivialZeroSet) :
    Cvs.Zeta.riemannXi (ρ : ℂ) = 0 :=
  (riemannXi_eq_zero_iff_mem_nonTrivialZeroSet _).mpr ρ.2

end Cvs.Zeta.ZeroIndex
