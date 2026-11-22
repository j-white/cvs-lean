import Mathlib
import Cvs.Prolate.Gram.CentralSquareExclusionConstant
import Cvs.Prolate.Gram.CentralSquareInverseForm
import Cvs.Prolate.Gram.CentralTransformInverseBound
import Cvs.Prolate.Gram.InverseFormConvexSplit
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Prolate.Gram.RobinQZeroFarExponent
import Cvs.Prolate.Gram.TunnellingFloorSumPlunge
import Cvs.Prolate.Mellin.RungWindowLawRightEdge
import Cvs.Prolate.TunnellingExponentSharpPlunge
import Cvs.Prolate.TunnellingTraceBelowLevel
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Route.Visibility.LayerFloorDeepRemainderB
import Cvs.Route.Visibility.VisibilityCentralSquareCut
import Cvs.Route.Visibility.VisibilityRobinFarExponent
import Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The inverse bound at the cut from the layer block alone

Below the cut `k₀` the weight is `1 − λ_j`. Rungs with `T_j ≤ T₁` take the per-rung bound `1 + 2e^{πx}` of the
central gap, rungs with `T₁ < T_j < T₀` a per-rung rate `e^{κc}`, and `TunnellingTraceBelowLevel`'s tunnelling traces vanish whenever
`W(T₁) > ¼` and `κ < 2W(T₀)`. So the inverse bound at the cut follows from the bound `θ < 1` on the layer block
`{j ≥ k₀}` alone, and with Dominance it gives `CentralSquareCut T₀ ε`; `T₁ = ½` qualifies.
-/

noncomputable section

open Real Filter Finset
open Cvs.ZeroCounting
open Cvs.Prolate.Gram.ProlateCellGramHalfUnit (lam levT)
open Cvs.Route.Visibility.LayerFloorDeepRemainderB (C0inf muStar)

namespace Cvs.Prolate.Gram.LayerBlockInverseCut
open Cvs.ZeroCounting

/-- **The inverse bound on the layer block at the cut `T₀`** with constant `θ`: eventually the first rung `k₀` of
`{T ≥ T₀}` exists and `invForm x (W·y on {j ≥ k₀}) z ≤ θ Σ_{j ≥ k₀} W_j y_j²`. -/
def LayerInverseBoundCut (T₀ ε θ : ℝ) : Prop :=
  ∀ᶠ x : ℕ in atTop, ∃ k₀ : Fin x, T₀ ≤ levT x k₀ ∧ (∀ j < k₀, levT x j < T₀) ∧
    Cvs.Prolate.Gram.InverseFormConvexSplit.UpperInverseBound x k₀ k₀ ε θ

/-- **The middle-band rate** `κ` on `T₁ < T < T₀`: eventually every rung there has
`invForm x (α e_j) z ≤ α² e^{κc}`, `c = 2πx`. -/
def MiddleRate (T₁ T₀ κ : ℝ) : Prop :=
  ∀ᶠ x : ℕ in atTop, ∀ j : Fin x, T₁ < levT x j → levT x j < T₀ →
    Cvs.Prolate.Gram.InverseFormConvexSplit.RungInverseBound x j (Real.exp (κ * (2 * π * x)))

/-- `1 + 2e^{πx} ≤ 3e^{c/2}` at `c = 2πx`. -/
theorem one_add_two_exp_le (x : ℕ) : 1 + 2 * Real.exp (π * x) ≤ 3 * Real.exp (1 / 2 * (2 * π * x)) := by
  have e : 1 / 2 * (2 * π * (x : ℝ)) = π * x := by ring
  rw [e]
  have : 1 ≤ Real.exp (π * x) := Real.one_le_exp (by have := Real.pi_pos; positivity)
  linarith

/-- **The inverse bound at one scale from the layer block**: with the central gap at `1 − e^{−πx}`, the middle
rate on `T₁ < T_j < T₀`, the layer bound `θ ∈ (0, 1)`, and both tunnelling traces at most `(1 − θ)/2`,
`InverseBound x k₀ ε` holds at the first rung `k₀` of `{T ≥ T₀}`. -/
theorem inverseBound_of_layer {x : ℕ} (hx : 80 ≤ 2 * π * x) {k₀ : Fin x} {T₀ T₁ κ ε θ : ℝ} (hε : ε ≤ 1)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hk : ∀ j < k₀, levT x j < T₀)
    (hG : Cvs.Prolate.Gram.CentralTransformInverseBound.CentralGap x (1 - Real.exp (-(π * x))))
    (hM : ∀ j : Fin x, T₁ < levT x j → levT x j < T₀ → Cvs.Prolate.Gram.InverseFormConvexSplit.RungInverseBound x j (Real.exp (κ * (2 * π * x))))
    (hU : Cvs.Prolate.Gram.InverseFormConvexSplit.UpperInverseBound x k₀ k₀ ε θ)
    (hdeep : ∑ j ∈ univ.filter (fun j : Fin x => levT x j ≤ T₁),
      (1 - lam x j) * Real.exp (1 / 2 * (2 * π * x)) ≤ (1 - θ) / 6)
    (hmid : ∑ j ∈ univ.filter (fun j : Fin x => levT x j ≤ T₀),
      (1 - lam x j) * Real.exp (κ * (2 * π * x)) ≤ (1 - θ) / 2) :
    Cvs.Prolate.Gram.CentralSquareInverseForm.InverseBound x k₀ ε := by
  set c := 2 * π * (x : ℝ)
  set g : Fin x → ℝ := fun j => if levT x j ≤ T₁ then 1 + 2 * Real.exp (π * x) else Real.exp (κ * c)
  have hg : ∀ j < k₀, 0 < g j := fun j _ => by
    simp only [g]; split_ifs
    · positivity
    · exact Real.exp_pos _
  have hR : ∀ j < k₀, Cvs.Prolate.Gram.InverseFormConvexSplit.RungInverseBound x j (g j) := fun j hj => by
    simp only [g]; split_ifs with h
    · exact Cvs.Prolate.Gram.CentralTransformInverseBound.rungInverseBound_exp hx hG j
    · exact hM j (not_le.1 h) (hk j hj)
  have hσ : 1 - Real.exp (-(π * x)) ≤ 1 := by linarith [Real.exp_pos (-(π * x))]
  have h0 : ∀ z : ℝ → ℝ, Continuous z → Cvs.Prolate.Gram.CentralSquareInverseForm.invForm x 0 z ≤ 0 := fun z hz =>
    Cvs.Prolate.Gram.CentralTransformInverseBound.invForm_zero_le hσ hG hz
  have hl : ∀ j : Fin x, 0 ≤ 1 - lam x j := fun j => by linarith [Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lam_le_one hx j.2]
  have hsum : ∑ j ∈ univ.filter (· < k₀), Cvs.Prolate.Gram.CentralSquareInverseForm.weight x k₀ ε j * g j ≤ 1 - θ := by
    have hterm : ∀ j ∈ univ.filter (· < k₀), Cvs.Prolate.Gram.CentralSquareInverseForm.weight x k₀ ε j * g j
        ≤ (if levT x j ≤ T₁ then 3 * ((1 - lam x j) * Real.exp (1 / 2 * c)) else 0)
          + (if levT x j ≤ T₀ then (1 - lam x j) * Real.exp (κ * c) else 0) := fun j hj => by
      have hjk : j < k₀ := (Finset.mem_filter.1 hj).2
      have hw : Cvs.Prolate.Gram.CentralSquareInverseForm.weight x k₀ ε j = 1 - lam x j := by
        simp [Cvs.Prolate.Gram.CentralSquareInverseForm.weight, not_le.2 hjk]
      rw [hw]
      simp only [g]
      by_cases h1 : levT x j ≤ T₁
      · have h2 : levT x j ≤ T₀ := (hk j hjk).le
        simp only [h1, h2, if_true]
        have := mul_le_mul_of_nonneg_left (one_add_two_exp_le x) (hl j)
        have : 0 ≤ (1 - lam x j) * Real.exp (κ * c) := mul_nonneg (hl j) (Real.exp_pos _).le
        nlinarith
      · have h2 : levT x j ≤ T₀ := (hk j hjk).le
        simp only [h1, h2, if_true, if_false, zero_add]
        exact le_rfl
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_add_distrib]
    have hA : ∑ j ∈ univ.filter (· < k₀), (if levT x j ≤ T₁ then 3 * ((1 - lam x j) * Real.exp (1 / 2 * c)) else 0)
        ≤ 3 * ∑ j ∈ univ.filter (fun j : Fin x => levT x j ≤ T₁), (1 - lam x j) * Real.exp (1 / 2 * c) := by
      refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun j _ _ => ?_).trans_eq ?_
      · split_ifs
        · exact mul_nonneg (by norm_num) (mul_nonneg (hl j) (Real.exp_pos _).le)
        · exact le_rfl
      · rw [Finset.mul_sum, ← Finset.sum_filter]
    have hB : ∑ j ∈ univ.filter (· < k₀), (if levT x j ≤ T₀ then (1 - lam x j) * Real.exp (κ * c) else 0)
        ≤ ∑ j ∈ univ.filter (fun j : Fin x => levT x j ≤ T₀), (1 - lam x j) * Real.exp (κ * c) := by
      refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun j _ _ => ?_).trans_eq ?_
      · split_ifs
        · exact mul_nonneg (hl j) (Real.exp_pos _).le
        · exact le_rfl
      · rw [← Finset.sum_filter]
    linarith
  exact Cvs.Prolate.Gram.InverseFormConvexSplit.inverseBound_of_split hx hε hθ0 (by linarith : 0 < 1 - θ) (by linarith) hU g hg hR h0 hsum

/-- **The inverse bound at the cut from the layer block**: for `T₁ ≤ T₀ < 1`, `W(T₁) > ¼`, `κ < 2W(T₀)`,
`θ ∈ (0, 1)` and `ε ≤ 1`, the central gap, the middle rate and the layer bound give `InverseBoundCut T₀ ε`. -/
theorem inverseBoundCut_of_layer {T₀ T₁ κ ε θ : ℝ} (hε : ε ≤ 1) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hT : T₁ ≤ T₀)
    (hT₀ : T₀ < 1) (hW : 1 / 4 < Cvs.Prolate.TunnellingExponentSharpPlunge.tunW T₁) (hκ : κ < 2 * Cvs.Prolate.TunnellingExponentSharpPlunge.tunW T₀) (hG : Cvs.Prolate.Gram.CentralTransformInverseBound.CentralGapFrom)
    (hM : MiddleRate T₁ T₀ κ) (hL : LayerInverseBoundCut T₀ ε θ) : Cvs.Prolate.Gram.CentralSquareInverseForm.InverseBoundCut T₀ ε := by
  have hdeep := Cvs.Prolate.TunnellingTraceBelowLevel.trace_eventually_le (lt_of_le_of_lt hT hT₀) (by linarith : (1 / 2 : ℝ) < 2 * Cvs.Prolate.TunnellingExponentSharpPlunge.tunW T₁)
    (by linarith : 0 < (1 - θ) / 6)
  have hmid := Cvs.Prolate.TunnellingTraceBelowLevel.trace_eventually_le hT₀ hκ (by linarith : 0 < (1 - θ) / 2)
  filter_upwards [hL, hG, hM, hdeep, hmid, Cvs.Route.Visibility.LayerFloorDeepRemainderB.eventually_scale] with x ⟨k₀, h1, h2, h3⟩ hGx hMx hd hm hx
  exact ⟨k₀, h1, h2, inverseBound_of_layer hx hε hθ0 hθ1 h2 hGx hMx h3 hd hm⟩

/-- **`CentralSquareCut` from the layer block**: with Dominance, the same hypotheses give
`CentralSquareCut T₀ ε`. -/
theorem centralSquareCut_of_layer {T₀ T₁ κ ε θ : ℝ} (hε : ε ≤ 1) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hT : T₁ ≤ T₀)
    (hT₀ : T₀ < 1) (hW : 1 / 4 < Cvs.Prolate.TunnellingExponentSharpPlunge.tunW T₁) (hκ : κ < 2 * Cvs.Prolate.TunnellingExponentSharpPlunge.tunW T₀) (hD : Cvs.Prolate.Gram.CentralSquareInverseForm.DominanceFrom)
    (hG : Cvs.Prolate.Gram.CentralTransformInverseBound.CentralGapFrom) (hM : MiddleRate T₁ T₀ κ) (hL : LayerInverseBoundCut T₀ ε θ) :
    Cvs.Route.Visibility.VisibilityCentralSquareCut.CentralSquareCut T₀ ε :=
  Cvs.Prolate.Gram.CentralSquareInverseForm.centralSquareCut_of_inverseBoundCut hD (inverseBoundCut_of_layer hε hθ0 hθ1 hT hT₀ hW hκ hG hM hL)

/-- **`CentralSquareCut` from the layer block with the deep band cut at `½`**. -/
theorem centralSquareCut_of_layer_half {T₀ κ ε θ : ℝ} (hε : ε ≤ 1) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hT : 1 / 2 ≤ T₀) (hT₀ : T₀ < 1) (hκ : κ < 2 * Cvs.Prolate.TunnellingExponentSharpPlunge.tunW T₀) (hD : Cvs.Prolate.Gram.CentralSquareInverseForm.DominanceFrom)
    (hG : Cvs.Prolate.Gram.CentralTransformInverseBound.CentralGapFrom) (hM : MiddleRate (1 / 2) T₀ κ) (hL : LayerInverseBoundCut T₀ ε θ) :
    Cvs.Route.Visibility.VisibilityCentralSquareCut.CentralSquareCut T₀ ε :=
  centralSquareCut_of_layer hε hθ0 hθ1 hT hT₀ Cvs.Prolate.TunnellingTraceBelowLevel.quarter_lt_tunW_half hκ hD hG hM hL

/-- **hV from the layer block**: `Cvs.Route.Visibility.VisibilityRobinFarExponent.hV_wave16` with `CentralSquareCut` replaced by the layer bound, the middle
rate on `(½, T₀)`, the Slepian–Fuchs gap and Dominance. -/
theorem hV_layer {T₀ κ ε θ : ℝ} (hT : 1 / 2 ≤ T₀) (hT₀ : T₀ < 1)
    (hlt : ε < √2 * (1 / 2 - muStar * C0inf (57 / 60) / 2)) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hκ : κ < 2 * Cvs.Prolate.TunnellingExponentSharpPlunge.tunW T₀) (hL : LayerInverseBoundCut T₀ ε θ) (hM : MiddleRate (1 / 2) T₀ κ)
    (hG : Cvs.Prolate.Gram.CentralTransformInverseBound.CentralGapFrom) (hD : Cvs.Prolate.Gram.CentralSquareInverseForm.DominanceFrom) (hP : Cvs.Prolate.Gram.RobinQZeroFarExponent.PosQ0At 1) (hK : Cvs.Prolate.Gram.TunnellingFloorSumPlunge.KRDCount)
    (hB : Cvs.Prolate.Mellin.RungWindowLawRightEdge.EdgeLawSum) (hCarl : Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint.CarlsonBound) :
    ¬ RiemannHypothesis → ∀ᶠ x : ℕ in atTop, ¬ Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0 :=
  Cvs.Route.Visibility.VisibilityRobinFarExponent.hV_wave16 hT₀ hlt
    (centralSquareCut_of_layer_half (hlt.trans Cvs.Prolate.Gram.CentralSquareExclusionConstant.threshold_lt_one).le hθ0 hθ1 hT hT₀ hκ hD hG hM hL)
    hP hK hB hCarl

end Cvs.Prolate.Gram.LayerBlockInverseCut

end
