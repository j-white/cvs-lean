import Mathlib
import Cvs.Upstream.CourantFischerAscending

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Generalised eigenvalues do not depend on the whitening

For `P` with `PᵀGP = 1`, `λ_k(PᵀAP)` (ascending) is the greatest `d` admitting a subspace `V` of codimension
`≤ k` with `d·vᵀGv ≤ vᵀAv` on `V` (Courant–Fischer for the pencil `(A, G)`). The right side mentions only `A`
and `G`, so any two `P, P'` with `PᵀGP = 1 = P'ᵀGP'` give the same ascending eigenvalues of `PᵀAP` and
`P'ᵀAP'`.
-/

noncomputable section

open Matrix Module

namespace Cvs.Upstream.WhiteningInvariantEigenvalues

open Cvs.Upstream.CourantFischerAscending (eigAsc quad_congr)

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `PᵀGP = 1` makes `P` injective: `(PᵀG)P = 1`. -/
theorem injective_of_gram {G P : Matrix n n ℝ} (hGP : Pᵀ * G * P = 1) :
    Function.Injective (toLin' P) := fun u v h => by
  have hu : (Pᵀ * G) *ᵥ (P *ᵥ u) = u := by rw [mulVec_mulVec, hGP, one_mulVec]
  have hv : (Pᵀ * G) *ᵥ (P *ᵥ v) = v := by rw [mulVec_mulVec, hGP, one_mulVec]
  rw [toLin'_apply, toLin'_apply] at h
  rw [← hu, ← hv, h]

/-- **Courant–Fischer for a pencil, max-min.** For `P` with `PᵀGP = 1`, `λ_k(PᵀAP)` is the greatest `d`
admitting a subspace `V` of codimension `≤ k` with `d·vᵀGv ≤ vᵀAv` on `V`. -/
theorem isGreatest_eigAsc_gram {A G P : Matrix n n ℝ} (hGP : Pᵀ * G * P = 1)
    (hAP : (Pᵀ * A * P).IsHermitian) (k : Fin (Fintype.card n)) :
    IsGreatest {d | ∃ V : Submodule ℝ (n → ℝ), Fintype.card n ≤ finrank ℝ V + k ∧
      ∀ v ∈ V, d * (v ⬝ᵥ (G *ᵥ v)) ≤ v ⬝ᵥ (A *ᵥ v)} (eigAsc hAP k) := by
  refine ⟨?_, fun d ⟨V, hcodim, hV⟩ => Cvs.Upstream.CourantFischerAscending.le_eigAsc_of_floor_gram hGP hAP hcodim hV k.2⟩
  obtain ⟨V', hcodim', hV'⟩ := (Cvs.Upstream.CourantFischerAscending.isGreatest_eigAsc hAP k).1
  refine ⟨V'.map (toLin' P), ?_, ?_⟩
  · rw [← (Submodule.equivMapOfInjective (toLin' P) (injective_of_gram hGP) V').finrank_eq]
    exact hcodim'
  · rintro _ ⟨y, hy, rfl⟩
    have h := hV' y hy
    rw [quad_congr] at h
    have e : y ⬝ᵥ y = (P *ᵥ y) ⬝ᵥ (G *ᵥ (P *ᵥ y)) := by
      rw [← quad_congr, hGP, one_mulVec]
    rw [toLin'_apply, ← e]
    exact h

end Cvs.Upstream.WhiteningInvariantEigenvalues
