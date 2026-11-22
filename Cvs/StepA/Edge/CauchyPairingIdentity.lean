import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Cauchy pairing identity and the reflection of a repeated eigenvalue

For a Cauchy matrix `C` of nodes `a` and `N = diag(d) C`, eigenvectors `Nx = λx`, `Ny = νy` satisfy
`(λ + ν) ∑ xₖ aₖ (Cy)ₖ = ν (∑ x)(∑ y)`, and `diag(a)` carries an eigenvector with `∑ y = 0` to one at
`−λ`. On the edge pencil `M(L) = B(L)G` this is `(λ + ν)⟨DF, G⟩ = ν F(0) G(0)` with `D = −d/du`, and a
bottom eigenvalue with two independent eigenvectors makes the edge discriminant nonnegative.
-/

noncomputable section

open Matrix

namespace Cvs.StepA.Edge.CauchyPairingIdentity


/-! ### Cauchy matrices -/

section Cauchy

variable {n : Type*} [Fintype n] {K : Type*} [Field K]

end Cauchy

/-! ### The edge pencil -/

section Edge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The frame coordinates of a pairing vector: `(y₀ + iy₁)/2` and `(y₀ − iy₁)/2` in each block. -/
def lift (y : Fin 2 × ι → ℝ) (k : Fin 2 × ι) : ℂ :=
  ![((y (0, k.2) : ℂ) + y (1, k.2) * Complex.I) / 2,
    ((y (0, k.2) : ℂ) - y (1, k.2) * Complex.I) / 2] k.1

/-- `D = −d/du` in the pairing coordinates: `(δy₀ − gᵢy₁, gᵢy₀ + δy₁)` in each block. -/
def edgeDer (δ : ℝ) (g : ι → ℝ) (y : Fin 2 × ι → ℝ) (k : Fin 2 × ι) : ℝ :=
  ![δ * y (0, k.2) - g k.2 * y (1, k.2), g k.2 * y (0, k.2) + δ * y (1, k.2)] k.1

/-- `κ(y) = ∑ᵢ y(0,i)`, the value at `0` of the edge combination with pairing vector `y`. -/
def edgeVal (y : Fin 2 × ι → ℝ) : ℝ := ∑ i, y (0, i)

/-! ### Consequences for the edge discriminant -/

end Edge

end Cvs.StepA.Edge.CauchyPairingIdentity
