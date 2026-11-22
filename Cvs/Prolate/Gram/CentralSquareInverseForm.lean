import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.Gram.BulkFloorFromFullTwist
import Cvs.Prolate.Gram.FullTwistOuterCell
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Route.Visibility.LayerFloorDeepRemainderB
import Cvs.Route.Visibility.VisibilityCentralSquareCut

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Central-square exclusion from the inverse of the outer-mass form

`invForm x v z` is the variational form of the inverse of `‖(1 − P)f‖² + ‖(1 − Q)f‖²` on `L²(ℝ)` at
`f = f_v`. `Dominance x` says its supremum over `z` dominates the inverse of `M_V = C + DCD + (1 − D²)`, and
`InverseBound x k ε` says it is at most `yᵀWy` at `v = Wy`, `W = (1 − ε)1_{j ≥ k} + (1 − λ_j)`. Together they give
`W ≤ M_V`, which is central-square exclusion `1 − ε` on the layer `{j ≥ k}`.
-/

noncomputable section

open Real Filter Matrix Finset Set
open Cvs.ZeroCounting
open Cvs.Prolate.Gram.ProlateCellGramHalfUnit (cellGram lam levT)
open Cvs.Prolate.Gram.FullTwistOuterCell (rungSum)
open Cvs.L2a.AngularProlateTailPositive (psi)

namespace Cvs.Prolate.Gram.CentralSquareInverseForm
open Cvs.ZeroCounting

/-- The central cut `1_{[−½, ½]} g`. -/
def cut (g : ℝ → ℝ) : ℝ → ℝ := (Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator g

/-- The central transform `Sz = √x·ψ_c(1_{[−½, ½]} z)` at `c = 2πx`. -/
def centralT (x : ℕ) (z : ℝ → ℝ) (t : ℝ) : ℝ := √x * psi (2 * π * x) (cut z) t

/-- The variational form of the inverse outer-mass form on the rung span:
`(|v|² + ‖f_v‖²_{[−½,½]} + 2⟨√x·ψ_c(f_v + 1_{[−½,½]}f_v), z⟩ − ‖z‖² + ‖Sz‖²)/2`, all norms on `[−½, ½]`. -/
def invForm (x : ℕ) (v : Fin x → ℝ) (z : ℝ → ℝ) : ℝ :=
  (v ⬝ᵥ v + (∫ t in (-(1 / 2 : ℝ))..(1 / 2), rungSum x v t ^ 2)
    + 2 * (∫ t in (-(1 / 2 : ℝ))..(1 / 2),
        √x * psi (2 * π * x) (fun s => rungSum x v s + cut (rungSum x v) s) t * z t)
    - (∫ t in (-(1 / 2 : ℝ))..(1 / 2), z t ^ 2) + ∫ t in (-(1 / 2 : ℝ))..(1 / 2), centralT x z t ^ 2) / 2

/-- The outer-mass form on the rung span, `M_V(u) = uᵀCu + (Du)ᵀC(Du) + Σ_j (1 − λ_j) u_j²`. -/
def outerForm (x : ℕ) (u : Fin x → ℝ) : ℝ :=
  u ⬝ᵥ (cellGram x *ᵥ u) + Cvs.Prolate.Gram.BulkFloorFromFullTwist.cellTwistAll x u ⬝ᵥ (cellGram x *ᵥ Cvs.Prolate.Gram.BulkFloorFromFullTwist.cellTwistAll x u)
    + ∑ j : Fin x, (1 - lam x j) * u j ^ 2

/-- **Dominance**: for all `u`, `v` and `η > 0` some continuous `z` has `2u·v ≤ M_V(u) + invForm x v z + η`. -/
def Dominance (x : ℕ) : Prop :=
  ∀ u v : Fin x → ℝ, ∀ η > 0, ∃ z : ℝ → ℝ, Continuous z ∧ 2 * (u ⬝ᵥ v) ≤ outerForm x u + invForm x v z + η

/-- Dominance at every scale `80 ≤ 2πx`. -/
def DominanceFrom : Prop := ∀ x : ℕ, 80 ≤ 2 * π * x → Dominance x

/-- The weight `W_j = (1 − ε)1_{j ≥ k} + (1 − λ_j)`. -/
def weight (x : ℕ) (k : Fin x) (ε : ℝ) (j : Fin x) : ℝ := (if k ≤ j then 1 - ε else 0) + (1 - lam x j)

/-- **The inverse bound** on the layer `{j ≥ k}`: `invForm x (Wy) z ≤ Σ_j W_j y_j²` for every `y` and continuous
`z`. -/
def InverseBound (x : ℕ) (k : Fin x) (ε : ℝ) : Prop :=
  ∀ (y : Fin x → ℝ) (z : ℝ → ℝ), Continuous z →
    invForm x (fun j => weight x k ε j * y j) z ≤ ∑ j, weight x k ε j * y j ^ 2

/-- The weighted square sum splits as `(1 − ε)Σ_{j ≥ k} v_j² + Σ_j (1 − λ_j) v_j²`. -/
theorem sum_weight_sq (x : ℕ) (k : Fin x) (ε : ℝ) (v : Fin x → ℝ) :
    ∑ j, weight x k ε j * v j ^ 2
      = (1 - ε) * ∑ j ∈ univ.filter (k ≤ ·), v j ^ 2 + ∑ j : Fin x, (1 - lam x j) * v j ^ 2 := by
  simp only [weight, add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-- **`W ≤ M_V`**: Dominance and the inverse bound give `Σ_j W_j v_j² ≤ M_V(v)`. -/
theorem weight_le_outerForm {x : ℕ} {k : Fin x} {ε : ℝ} (hD : Dominance x) (hI : InverseBound x k ε)
    (v : Fin x → ℝ) : ∑ j, weight x k ε j * v j ^ 2 ≤ outerForm x v := by
  have hvw : v ⬝ᵥ (fun j => weight x k ε j * v j) = ∑ j, weight x k ε j * v j ^ 2 := by
    simp only [dotProduct]
    exact Finset.sum_congr rfl fun j _ => by ring
  refine le_of_forall_pos_le_add fun η hη => ?_
  obtain ⟨z, hz, h⟩ := hD v (fun j => weight x k ε j * v j) η hη
  have h2 := hI v z hz
  rw [hvw] at h
  linarith

/-- **The full-twist floor from the inverse bound**: Dominance and `InverseBound x k ε` give `FullTwistPair x k ε`. -/
theorem fullTwistPair_of_inverseBound {x : ℕ} {k : Fin x} {ε : ℝ} (hD : Dominance x) (hI : InverseBound x k ε) :
    Cvs.Prolate.Gram.BulkFloorFromFullTwist.FullTwistPair x k ε := fun v => by
  have h := weight_le_outerForm hD hI v
  rw [sum_weight_sq, outerForm] at h
  linarith

/-- **Central-square exclusion from the inverse bound** at `80 ≤ 2πx`. -/
theorem centralSquarePair_of_inverseBound {x : ℕ} (hx : 80 ≤ 2 * π * x) {k : Fin x} {ε : ℝ}
    (hD : Dominance x) (hI : InverseBound x k ε) : Cvs.Prolate.Gram.FullTwistOuterCell.CentralSquarePair x k ε :=
  (Cvs.Prolate.Gram.FullTwistOuterCell.centralSquarePair_iff hx k ε).2 (fullTwistPair_of_inverseBound hD hI)

/-- **The inverse bound at the cut `T₀`**: eventually the first rung `k₀` of `{T ≥ T₀}` exists and
`InverseBound x k₀ ε` holds. -/
def InverseBoundCut (T₀ ε : ℝ) : Prop :=
  ∀ᶠ x : ℕ in atTop, ∃ k₀ : Fin x, T₀ ≤ levT x k₀ ∧ (∀ j < k₀, levT x j < T₀) ∧ InverseBound x k₀ ε

/-- **`CentralSquareCut` from the inverse bound at the cut** and Dominance. -/
theorem centralSquareCut_of_inverseBoundCut {T₀ ε : ℝ} (hD : DominanceFrom) (h : InverseBoundCut T₀ ε) :
    Cvs.Route.Visibility.VisibilityCentralSquareCut.CentralSquareCut T₀ ε := by
  filter_upwards [h, Cvs.Route.Visibility.LayerFloorDeepRemainderB.eventually_scale] with x ⟨k₀, h1, h2, h3⟩ hx
  exact ⟨k₀, h1, h2, centralSquarePair_of_inverseBound hx (hD x hx) h3⟩

end Cvs.Prolate.Gram.CentralSquareInverseForm

end
