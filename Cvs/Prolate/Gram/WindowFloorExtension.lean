import Mathlib
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.EvenFirstCellEnergyGram
import Cvs.Prolate.Gram.RungCellGramDisplacement
import Cvs.Prolate.Gram.WindowFloorMinNormInterp

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# (WF′) is an extension statement on the rungs

With `v_j = √2 h_{4j}` in `L²(0, 1/2]` and `u_j = √2 h_{4j}` in `L²(1/2, 1]`, the pairs `(v_j, u_j)` are orthonormal.
(WF′) at `T₀` holds iff for some `ε > 0`, at all large `x`, the inner parts of the layer `{T_j ≥ T₀}` have cell
extensions `k_j` orthogonal to every rung whose Gram `Gram(v_j, k_j)` is at most `κ` with `μ*C₀∞/2 + ε ≤ 1/(1 + κ)`.
-/

noncomputable section

open Real Filter Matrix MeasureTheory

namespace Cvs.Prolate.Gram.WindowFloorExtension
open Cvs.ZeroCounting

open Cvs.Prolate.EvenRungsByIndex (rung rung_spec)
open Cvs.Prolate.Gram.EvenFirstCellEnergyGram (L2c)
open Cvs.Prolate.Gram.RungCellGramDisplacement (rungCellGram rungIdx rungIdx_level rungCellGram_posDef continuousOn_rung_cell)
open Cvs.Prolate.Gram.WindowFloorMinNormInterp (cellVec gram_cellVec)

/-- The inner half-cell `L²(0, 1/2]`. -/
abbrev L2i : Type := Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (1 / 2)))

/-- A function continuous on `[0, 1/2]` is square integrable on `(0, 1/2]`. -/
theorem memLp_inner {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (0 : ℝ) (1 / 2))) :
    MemLp f 2 (volume.restrict (Set.Ioc (0 : ℝ) (1 / 2))) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  refine MemLp.of_bound ((hf.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc) M ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  exact Filter.Eventually.of_forall fun s hs => hM s (Set.Ioc_subset_Icc_self hs)

/-- `√2 h_{4j}` is continuous on `[0, 1/2]`. -/
theorem continuousOn_innerFun {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Fin x) :
    ContinuousOn (fun s => √2 * rung (2 * π * x) (rungIdx x j) s) (Set.Icc (0 : ℝ) (1 / 2)) := by
  have := continuousOn_rung_cell (rungIdx_level hx j) (α := 0) (β := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num)
  rw [Set.uIcc_of_le (by norm_num)] at this
  exact continuousOn_const.mul this

/-- The inner vector `v_j = √2 h_{4j}` in `L²(0, 1/2]`. -/
def innerVec {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Fin x) : L2i :=
  (memLp_inner (continuousOn_innerFun hx j)).toLp fun s => √2 * rung (2 * π * x) (rungIdx x j) s

/-- The inner Gram is `1 − C`: `⟨v_a, v_b⟩ = 2∫_0^{1/2} h_{4a}h_{4b} = (1 − rungCellGram x)_ab`. -/
theorem inner_innerVec {x : ℕ} (hx : 80 ≤ 2 * π * x) (a b : Fin x) :
    inner ℝ (innerVec hx a) (innerVec hx b) = (1 - rungCellGram x) a b := by
  set F : ℝ → ℝ := fun s => rung (2 * π * x) (rungIdx x a) s * rung (2 * π * x) (rungIdx x b) s with hF
  have hae : (fun s => inner ℝ (innerVec hx a s) (innerVec hx b s)) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) (1 / 2))]
      fun s => 2 * F s := by
    filter_upwards [MemLp.coeFn_toLp (memLp_inner (continuousOn_innerFun hx a)),
      MemLp.coeFn_toLp (memLp_inner (continuousOn_innerFun hx b))] with s h1 h2
    simp only [innerVec] at *
    rw [h1, h2, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, RCLike.re_to_real]
    have h2' : √2 * √2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)
    simp only [hF]
    linear_combination (rung (2 * π * x) (rungIdx x a) s * rung (2 * π * x) (rungIdx x b) s) * h2'
  have ha := rungIdx_level hx a
  have hb := rungIdx_level hx b
  have hFc : ContinuousOn F (Set.Icc (-1 : ℝ) 1) :=
    (Cvs.Prolate.EvenRungsByIndex.continuousOn_rung ha).mul (Cvs.Prolate.EvenRungsByIndex.continuousOn_rung hb)
  have hint : ∀ α β : ℝ, -1 ≤ α → β ≤ 1 → α ≤ β → IntervalIntegrable F volume α β := fun α β hα hβ hαβ =>
    (hFc.mono (by rw [Set.uIcc_of_le hαβ]; exact Set.Icc_subset_Icc hα hβ)).intervalIntegrable
  have hsplit : ∫ s in (-(1 / 2) : ℝ)..(1 / 2), F s = (∫ s in (-(1 / 2) : ℝ)..0, F s) + ∫ s in (0 : ℝ)..(1 / 2), F s :=
    (intervalIntegral.integral_add_adjacent_intervals (hint _ _ (by norm_num) (by norm_num) (by norm_num))
      (hint _ _ (by norm_num) (by norm_num) (by norm_num))).symm
  have hrefl : ∫ s in (-(1 / 2) : ℝ)..0, F s = ∫ s in (0 : ℝ)..(1 / 2), F s := by
    have e := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1 / 2) F
    rw [neg_zero] at e
    rw [← e]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hs
    have hs' : s ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    simp only [hF]
    rw [(rung_spec ha).2.2.2.2.1 s hs', (rung_spec hb).2.2.2.2.1 s hs']
  rw [show inner ℝ (innerVec hx a) (innerVec hx b) = ∫ s, inner ℝ (innerVec hx a s) (innerVec hx b s)
      ∂(volume.restrict (Set.Ioc (0 : ℝ) (1 / 2))) from L2.inner_def _ _,
    integral_congr_ae hae, integral_const_mul, Cvs.Prolate.Gram.WindowFloorMinNormInterp.one_sub_rungCellGram_apply hx, hsplit, hrefl,
    intervalIntegral.integral_of_le (by norm_num)]
  ring

/-- The rungs are orthonormal as pairs: `⟨v_a, v_b⟩ + ⟨u_a, u_b⟩ = δ_ab`. -/
theorem orthonormal_pairs {x : ℕ} (hx : 80 ≤ 2 * π * x) (a b : Fin x) :
    inner ℝ (innerVec hx a) (innerVec hx b) + inner ℝ (cellVec hx a) (cellVec hx b) = if a = b then 1 else 0 := by
  rw [inner_innerVec, show inner ℝ (cellVec hx a) (cellVec hx b) = gram ℝ (cellVec hx) a b from rfl, gram_cellVec,
    Matrix.sub_apply, Matrix.one_apply]
  ring

end Cvs.Prolate.Gram.WindowFloorExtension

end
