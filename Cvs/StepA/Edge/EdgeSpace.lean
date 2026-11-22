import Mathlib
import Cvs.StepA.Edge.CauchyPairingIdentity
import Cvs.StepA.Edge.DampedEdgeGram
import Cvs.StepA.Edge.ExtremeEigenvalueSum

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The edge space: coefficient vectors with the `L²(0, ∞)` inner product

`EdgeV P` is `Fin 2 × ι → ℝ` with `⟪x, y⟫ = xᵀ G y`, `G` the Gram matrix of the edge combinations
`∑ x_{(e,i)} e^{−δu}(cos, sin)(gᵢu)` for distinct positive ordinates; `D = −d/du` acts on it as
`edgeDer` with explicit inverse `opDinv`, and evaluation at `0` is represented by `κ`.
-/

noncomputable section

open Matrix
open scoped RealInnerProductSpace

namespace Cvs.StepA.Edge.PlanarBoxLemma
open Cvs.ZeroCounting
open Cvs.StepA.Edge.DampedEdgeGram (gram gram_comm gram_posDef)
open Cvs.StepA.Edge.CauchyPairingIdentity (edgeDer edgeVal)

/-- A family of distinct positive ordinates `g` at a positive depth `δ`. -/
structure EdgeData (ι : Type*) where
  /-- The common depth. -/
  δ : ℝ
  /-- The ordinates. -/
  g : ι → ℝ
  hδ : 0 < δ
  hg0 : ∀ i, 0 < g i
  hg : Function.Injective g

variable {ι : Type*} [Fintype ι]

/-- The coefficient space of the edge combinations of a family `P`. -/
def EdgeV (_P : EdgeData ι) : Type _ := Fin 2 × ι → ℝ

variable (P : EdgeData ι)

/-- The additive structure of the edge space: that of the coefficient vectors. -/
@[reducible] def EdgeV.addCommGroup : AddCommGroup (EdgeV P) :=
  inferInstanceAs (AddCommGroup (Fin 2 × ι → ℝ))

/-- The real structure of the edge space: that of the coefficient vectors. -/
@[reducible] def EdgeV.module : letI := EdgeV.addCommGroup P; Module ℝ (EdgeV P) :=
  inferInstanceAs (Module ℝ (Fin 2 × ι → ℝ))

/-- The coefficient vector of an element of the edge space. -/
def EdgeV.vec {P : EdgeData ι} (x : EdgeV P) : Fin 2 × ι → ℝ := x

/-- The `L²(0, ∞)` inner product of edge combinations, `⟪x, y⟫ = xᵀ G y`. -/
@[instance_reducible] def edgeCore : letI := EdgeV.addCommGroup P; letI := EdgeV.module P
    InnerProductSpace.Core ℝ (EdgeV P) :=
  letI := EdgeV.addCommGroup P
  letI := EdgeV.module P
  { inner x y := EdgeV.vec x ⬝ᵥ (gram P.δ P.g *ᵥ EdgeV.vec y)
    conj_inner_symm x y := by
      simp only [conj_trivial]
      rw [dotProduct_mulVec, ← mulVec_transpose, Cvs.StepA.Edge.ExtremeEigenvalueSum.gram_transpose,
        dotProduct_comm]
    re_inner_nonneg x := by
      simp only [RCLike.re_to_real]
      have h := (gram_posDef P.hδ P.hg0 P.hg).posSemidef
      simpa [star_trivial] using h.dotProduct_mulVec_nonneg (EdgeV.vec x)
    add_left x y z := add_dotProduct (EdgeV.vec x) (EdgeV.vec y) _
    smul_left x y r := by
      simp only [conj_trivial]
      exact smul_dotProduct r (EdgeV.vec x) _
    definite x hx := by
      by_contra h0
      have h := (gram_posDef P.hδ P.hg0 P.hg).dotProduct_mulVec_pos (x := EdgeV.vec x) h0
      simp only [star_trivial] at h
      exact h.ne' hx }

instance : NormedAddCommGroup (EdgeV P) :=
  letI := EdgeV.addCommGroup P
  letI := EdgeV.module P
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ _ _ _ _ (edgeCore P)

instance : InnerProductSpace ℝ (EdgeV P) :=
  letI := EdgeV.addCommGroup P
  letI := EdgeV.module P
  InnerProductSpace.ofCore (edgeCore P).toCore

instance : FiniteDimensional ℝ (EdgeV P) :=
  inferInstanceAs (FiniteDimensional ℝ (Fin 2 × ι → ℝ))

instance [Nonempty ι] : Nontrivial (EdgeV P) := inferInstanceAs (Nontrivial (Fin 2 × ι → ℝ))

/-- The inner product of the edge space is `xᵀ G y`. -/
theorem inner_def (x y : EdgeV P) : ⟪x, y⟫ = x.vec ⬝ᵥ (gram P.δ P.g *ᵥ y.vec) := rfl

/-! ### Operators from coefficient maps -/

/-- A linear map of coefficient vectors, as an operator on the edge space. -/
def ofLin (f : (Fin 2 × ι → ℝ) →ₗ[ℝ] (Fin 2 × ι → ℝ)) : EdgeV P →L[ℝ] EdgeV P :=
  LinearMap.toContinuousLinearMap (f : EdgeV P →ₗ[ℝ] EdgeV P)

@[simp] theorem ofLin_apply (f : (Fin 2 × ι → ℝ) →ₗ[ℝ] (Fin 2 × ι → ℝ)) (x : EdgeV P) :
    ofLin P f x = f x.vec := rfl

/-! ### Evaluation at `0` and `D = −d/du` -/

/-- Evaluation at `0` of the edge combination, `x ↦ ∑ᵢ x_{(0,i)}`, on coefficient vectors. -/
def edgeValLin : (Fin 2 × ι → ℝ) →ₗ[ℝ] ℝ where
  toFun x := edgeVal x
  map_add' x y := by simp [edgeVal, Finset.sum_add_distrib]
  map_smul' r x := by simp [edgeVal, Finset.mul_sum]

/-- `κ`, the representer of evaluation at `0`: `⟪κ, x⟫ = x(0)`. -/
def kap : EdgeV P := (InnerProductSpace.toDual ℝ (EdgeV P)).symm (LinearMap.toContinuousLinearMap
  (edgeValLin : EdgeV P →ₗ[ℝ] ℝ))

/-- `⟪κ, x⟫` is the value at `0` of the edge combination of `x`. -/
theorem inner_kap (x : EdgeV P) : ⟪kap P, x⟫ = edgeVal x.vec := by
  rw [kap, InnerProductSpace.toDual_symm_apply]
  rfl

/-- `D = −d/du` on coefficient vectors: `(δx₀ − gᵢx₁, gᵢx₀ + δx₁)` in each block. -/
def edgeDerLin (δ : ℝ) (g : ι → ℝ) : (Fin 2 × ι → ℝ) →ₗ[ℝ] (Fin 2 × ι → ℝ) where
  toFun x := edgeDer δ g x
  map_add' x y := by
    funext ⟨e, i⟩
    fin_cases e <;> simp [edgeDer] <;> ring
  map_smul' r x := by
    funext ⟨e, i⟩
    fin_cases e <;> simp [edgeDer] <;> ring

/-- `D⁻¹` on coefficient vectors: `(δx₀ + gᵢx₁, −gᵢx₀ + δx₁)/(δ² + gᵢ²)` in each block. -/
def edgeDerInvLin (δ : ℝ) (g : ι → ℝ) : (Fin 2 × ι → ℝ) →ₗ[ℝ] (Fin 2 × ι → ℝ) where
  toFun x := fun k => ![(δ * x (0, k.2) + g k.2 * x (1, k.2)) / (δ ^ 2 + g k.2 ^ 2),
    (-(g k.2 * x (0, k.2)) + δ * x (1, k.2)) / (δ ^ 2 + g k.2 ^ 2)] k.1
  map_add' x y := by
    funext ⟨e, i⟩
    fin_cases e <;> simp <;> ring
  map_smul' r x := by
    funext ⟨e, i⟩
    fin_cases e <;> simp <;> ring

/-- `D = −d/du` on the edge space. -/
def opD : EdgeV P →L[ℝ] EdgeV P := ofLin P (edgeDerLin P.δ P.g)

/-- `D⁻¹` on the edge space. -/
def opDinv : EdgeV P →L[ℝ] EdgeV P := ofLin P (edgeDerInvLin P.δ P.g)

/-- `D D⁻¹ = 1`. -/
theorem opD_opDinv (x : EdgeV P) : opD P (opDinv P x) = x := by
  show edgeDer P.δ P.g (edgeDerInvLin P.δ P.g x.vec) = x.vec
  funext ⟨e, i⟩
  have hd : P.δ ^ 2 + P.g i ^ 2 ≠ 0 := by have := P.hδ; positivity
  fin_cases e <;>
    simp [edgeDerInvLin, edgeDer] <;> field_simp <;> ring

/-- `D⁻¹ D = 1`. -/
theorem opDinv_opD (x : EdgeV P) : opDinv P (opD P x) = x := by
  show edgeDerInvLin P.δ P.g (edgeDer P.δ P.g x.vec) = x.vec
  funext ⟨e, i⟩
  have hd : P.δ ^ 2 + P.g i ^ 2 ≠ 0 := by have := P.hδ; positivity
  fin_cases e <;>
    simp [edgeDerInvLin, edgeDer] <;> field_simp <;> ring

/-- `D` is injective. -/
theorem opD_injective : Function.Injective (opD P) := fun x y h => by
  rw [← opDinv_opD P x, h, opDinv_opD]

end Cvs.StepA.Edge.PlanarBoxLemma
