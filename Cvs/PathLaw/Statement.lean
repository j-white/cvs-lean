/-
The Single-Atom Path Law — the Loewner matrix and the model predicate.

This file defines `atomEntry` (the unfolded Loewner divided-difference
matrix, mirroring `atom_matrix(..., parity="unfolded")` in
`paper/numerics/pathlaw_core.py`) and the real-scalar `MaskedRotationModel`, and proves the
conditional `single_atom_path_law_of_model`.

The Path Law itself is proved downstream, in both scalar settings:
`single_atom_path_lawC` (`PathLaw/Model.lean`) and `single_atom_path_lawR`
(`PathLaw/RealAtom.lean`).
-/
import Cvs.PathLaw.Transfer

open Real MeasureTheory

namespace Cvs.PathLaw

/-- The circle `𝕋 = ℝ/ℤ` carries a positive period. -/
instance : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩

/-- Entry `(k, l)` of the unfolded single-atom Loewner matrix for the prime
power `q` at cutoff `c` (mirrors `atom_matrix(..., parity="unfolded")` in
`paper/numerics/pathlaw_core.py`), with mask angle `α = 2π(1 − y/L)`. -/
noncomputable def atomEntry (q c : ℕ) (k l : ℤ) : ℝ :=
  let L : ℝ := Real.log c
  let y : ℝ := Real.log q
  let α : ℝ := 2 * π * (1 - y / L)
  weight q *
    (if k = l then (α / π) * Real.cos (α * k)
     else (Real.sin (α * l) - Real.sin (α * k)) / (π * (l - k)))

/-- A **masked-rotation model** for an operator `T` on `ℓ²(ℤ)`: a linear
isometry equivalence onto `L²(𝕋)` intertwining `T` with the arithmetically
weighted masked rotation, whose operator norm is the Chebyshev factor of the
capacity.

This bundles the two analytic steps:
* the *intertwining* clause is the DTFT (paper Section 6);
* the *norm* clause is the chain decomposition (paper Section 3). -/
def MaskedRotationModel (q c : ℕ) (T : AtomSpace →L[ℝ] AtomSpace) : Prop :=
  ∃ (e : AtomSpace ≃ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure (AddCircle (1 : ℝ))))
    (a : AddCircle (1 : ℝ)) (s₁ s₂ : Set (AddCircle (1 : ℝ)))
    (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂),
    (∀ x, (weight q • maskedRotation a s₁ s₂ h₁ h₂) (e x) = e (T x)) ∧
      ‖maskedRotation a s₁ s₂ h₁ h₂‖
        = chebFactor (capacity (Real.log c) (Real.log q))

/-- **The Path Law from a masked-rotation model** — proved. Any atom
admitting a masked-rotation model has operator norm exactly
`2 cos(π/(⌈L/log q⌉+1)) · Λ(q)/√q`. -/
theorem single_atom_path_law_of_model (q c : ℕ) (T : AtomSpace →L[ℝ] AtomSpace)
    (hmodel : MaskedRotationModel q c T) : ‖T‖ = pathLawNorm q c := by
  obtain ⟨e, a, s₁, s₂, h₁, h₂, htransfer, hchain⟩ := hmodel
  exact single_atom_path_law_of q c T e a s₁ s₂ h₁ h₂ htransfer hchain

/-!
The Path Law itself is PROVED, in both scalar settings:

* `Cvs.PathLaw.single_atom_path_lawC` (`PathLaw/Model.lean`) — over `ℂ`, the
  scalars of the paper's DTFT;
* `Cvs.PathLaw.single_atom_path_lawR` (`PathLaw/RealAtom.lean`) — over `ℝ`, by
  complexification.

The real-scalar `MaskedRotationModel` above remains available for the
conditional statement `single_atom_path_law_of_model`; no `proof_wanted`
remains in this development.
-/

end Cvs.PathLaw
