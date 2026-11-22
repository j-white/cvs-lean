import Mathlib
import Cvs.Approximant.SingletonRegularisationColumn
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullTailConvergence
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.BulkFloorFromFullTwist
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Route.Visibility.LayerFloorDeepRemainderB

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The full twist is the outer cell of the cosine transform

Each rung is an eigenfunction of the finite cosine transform, `ψ_c h_{4n} = μ_n h_{4n}` on `[−1, 1]`, with
`√λ_n = √x·μ_n` at `c = 2πx` and `μ_n > 0`. So for `f = Σ v_n h_{4n}` the twisted form `(Dv)ᵀC(Dv)` is the outer-cell
mass `2∫_{(1/2,1]} (√x·ψ_c f)²` of the cosine transform, and the full-twist floor is the central-square exclusion: the
outer time mass of `f` plus the outer frequency mass of `f` is at least `(1 − ε)` times its layer mass.
-/

noncomputable section

open Real Filter Matrix Finset MeasureTheory Set

namespace Cvs.Prolate.Gram.FullTwistOuterCell
open Cvs.ZeroCounting

open Cvs.Prolate.Gram.ProlateCellGramHalfUnit (cellGram lam levT)
open Cvs.Prolate.EvenRungsByIndex (rung muR)

/-- The rung combination `f_v = Σ_n v_n h_{4n}` at `c = 2πx`. -/
def rungSum (x : ℕ) (v : Fin x → ℝ) (u : ℝ) : ℝ := ∑ n, v n * rung (2 * π * x) (2 * (n : ℕ)) u

/-- `√λ_n = √x·μ_n` for the rungs `n < x`. -/
theorem sqrt_lam_eq {x : ℕ} (hx : 80 ≤ 2 * π * x) (n : Fin x) :
    √(lam x n) = √x * muR (2 * π * x) (2 * (n : ℕ)) := by
  have hc : 0 < 2 * π * x := by linarith
  have hμ := Cvs.Prolate.EvenRungsByIndex.muR_pos_of_even hc (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.exists_level hx n) (even_two_mul _)
  have e : 2 * π * x / (2 * π) = x := by field_simp
  rw [Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lam, Cvs.Prolate.EvenRungsByIndex.lamR, e, Real.sqrt_sq (by positivity)]
  ring

/-- On `[−1, 1]` the twisted combination is the scaled cosine transform: `Σ √λ_n v_n h_{4n} = √x·ψ_c f_v`. -/
theorem twist_sum_eq {x : ℕ} (hx : 80 ≤ 2 * π * x) (v : Fin x → ℝ) {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) :
    ∑ n, Cvs.Prolate.Gram.BulkFloorFromFullTwist.cellTwistAll x v n * rung (2 * π * x) (2 * (n : ℕ)) u
      = √x * Cvs.L2a.AngularProlateTailPositive.psi (2 * π * x) (rungSum x v) u := by
  have hint : ∀ n ∈ (univ : Finset (Fin x)), IntervalIntegrable (rung (2 * π * x) (2 * (n : ℕ))) volume (-1) 1 :=
    fun n _ => (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.continuousOn_rung _ _).intervalIntegrable_of_Icc (by norm_num)
  have e : rungSum x v = fun t => ∑ n ∈ univ, v n * rung (2 * π * x) (2 * (n : ℕ)) t := rfl
  rw [e, Cvs.L2a.FullTailConvergence.psi_sum univ v _ hint, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Cvs.Prolate.EvenRungsByIndex.psi_rung (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.exists_level hx n) u hu]
  simp only [Cvs.Prolate.Gram.BulkFloorFromFullTwist.cellTwistAll, Cvs.Upstream.FullTwistLayerFloor.twistAll]
  rw [sqrt_lam_eq hx n]
  ring

/-- **The twisted form is the outer cell of the cosine transform**:
`(Dv)ᵀC(Dv) = 2∫_{(1/2,1]} (√x·ψ_c f_v)²`. -/
theorem quad_cellTwistAll {x : ℕ} (hx : 80 ≤ 2 * π * x) (v : Fin x → ℝ) :
    Cvs.Prolate.Gram.BulkFloorFromFullTwist.cellTwistAll x v ⬝ᵥ (cellGram x *ᵥ Cvs.Prolate.Gram.BulkFloorFromFullTwist.cellTwistAll x v)
      = 2 * ∫ u in Ioc (1 / 2 : ℝ) 1, (√x * Cvs.L2a.AngularProlateTailPositive.psi (2 * π * x) (rungSum x v) u) ^ 2 := by
  rw [Cvs.Prolate.Gram.ProlateCellGramHalfUnit.quad_cellGram]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
  rw [twist_sum_eq hx v ⟨by linarith [hu.1], hu.2⟩]

/-- The untwisted form is the outer cell of `f_v`: `vᵀCv = 2∫_{(1/2,1]} f_v²`. -/
theorem quad_cellGram_rungSum (x : ℕ) (v : Fin x → ℝ) :
    v ⬝ᵥ (cellGram x *ᵥ v) = 2 * ∫ u in Ioc (1 / 2 : ℝ) 1, rungSum x v u ^ 2 :=
  Cvs.Prolate.Gram.ProlateCellGramHalfUnit.quad_cellGram x v

/-- **Central-square exclusion** `1 − ε` on the layer `{j ≥ k}`: for every `f_v`, the outer time mass
`2∫_{(1/2,1]} f_v²` plus the outer frequency mass `2∫_{(1/2,1]} (√x·ψ_c f_v)²` is at least `(1 − ε)Σ_{j ≥ k} v_j²`. -/
def CentralSquarePair (x : ℕ) (k : Fin x) (ε : ℝ) : Prop :=
  ∀ v : Fin x → ℝ, (1 - ε) * ∑ j ∈ univ.filter (k ≤ ·), v j ^ 2
    ≤ (2 * ∫ u in Ioc (1 / 2 : ℝ) 1, rungSum x v u ^ 2)
      + 2 * ∫ u in Ioc (1 / 2 : ℝ) 1, (√x * Cvs.L2a.AngularProlateTailPositive.psi (2 * π * x) (rungSum x v) u) ^ 2

/-- **Lemma Q**: the central-square exclusion is the full-twist floor. -/
theorem centralSquarePair_iff {x : ℕ} (hx : 80 ≤ 2 * π * x) (k : Fin x) (ε : ℝ) :
    CentralSquarePair x k ε ↔ Cvs.Prolate.Gram.BulkFloorFromFullTwist.FullTwistPair x k ε := by
  refine forall_congr' fun v => ?_
  rw [quad_cellTwistAll hx, quad_cellGram_rungSum]

/-- **Central-square exclusion at the cut `T₀`**: eventually the first rung `k₀` of `{T ≥ T₀}` exists, the
central-square exclusion `1 − ε` holds on its layer, and the far-twist residue below it is at most `ρ`. -/
def CentralSquareFloor (T₀ ε ρ : ℝ) : Prop :=
  ∀ᶠ x : ℕ in atTop, ∃ k₀ : Fin x, T₀ ≤ levT x k₀ ∧ (∀ j < k₀, levT x j < T₀) ∧
    CentralSquarePair x k₀ ε ∧ Cvs.Prolate.Gram.BulkFloorFromFullTwist.FarTwistRes x k₀ ρ

/-- The central-square floor is the full-twist floor. -/
theorem centralSquareFloor_iff (T₀ ε ρ : ℝ) : CentralSquareFloor T₀ ε ρ ↔ Cvs.Prolate.Gram.BulkFloorFromFullTwist.FullTwistFloor T₀ ε ρ := by
  constructor
  · intro h
    filter_upwards [h, Cvs.Route.Visibility.LayerFloorDeepRemainderB.eventually_scale] with x ⟨k₀, h1, h2, h3, h4⟩ hx
    exact ⟨k₀, h1, h2, (centralSquarePair_iff hx k₀ ε).1 h3, h4⟩
  · intro h
    filter_upwards [h, Cvs.Route.Visibility.LayerFloorDeepRemainderB.eventually_scale] with x ⟨k₀, h1, h2, h3, h4⟩ hx
    exact ⟨k₀, h1, h2, (centralSquarePair_iff hx k₀ ε).2 h3, h4⟩

end Cvs.Prolate.Gram.FullTwistOuterCell
