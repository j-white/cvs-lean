import Mathlib
import Cvs.Prolate.EvenRungParseval
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.EvenFirstCellEnergyGram
import Cvs.Prolate.Gram.RungCellGramDisplacement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The window floor as a min-norm interpolation, its Cauchy dual, and the rung cell Gram in `L²(1/2, 1]`

On `M = gram u ≻ 0`, `aᵀ(M⁻¹)_{TT}a` is the least `‖w‖²` with `⟨w, u_b⟩ = (ι_T a)_b`, so rows with `⟨w_j, u_b⟩ = δ_jb`
and Gram `≤ c` give `F ≥ 1/c`. If `⟨u_b, ψ_k⟩ = n_b g_k/(χ_b − σ_k)` then `M` is a Cauchy Gram, and partial fractions
of `∏_{b ≠ j}(z − χ_b)/∏_{k ∈ S}(z − σ_k)` give such rows. The rung cell Gram is `gram(√2 h_{4j})` in `L²(1/2, 1]`;
on it are stated the sieve form, `‖C_NT‖² ≤ λ_max(E)`, fragility and the Cauchy dual under `CellCauchyBasis`.
-/

noncomputable section

open Matrix
open scoped MatrixOrder

namespace Cvs.Prolate.Gram.WindowFloorMinNormInterp
open Cvs.ZeroCounting


variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ι → Prop} [DecidablePred p]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The min-norm interpolation problem -/

/-! ### The Cauchy Gram and partial-fraction rows -/

/-! ### Product rows by partial fractions -/

section PartialFractions

open Polynomial

/-- **Partial fractions**: for `deg P < |S|`, distinct nodes `σ` and `z` off them,
`P(z)/∏_{k ∈ S}(z − σ_k) = Σ_{k ∈ S} P(σ_k) w_k/(z − σ_k)`, `w_k = ∏_{l ≠ k}(σ_k − σ_l)⁻¹`. -/
theorem eval_div_prod_eq_sum {κ : Type*} [DecidableEq κ] {S : Finset κ} {σ : κ → ℝ} (hσ : Set.InjOn σ S)
    {P : ℝ[X]} (hP : P.degree < S.card) {z : ℝ} (hz : ∀ k ∈ S, z ≠ σ k) :
    P.eval z / ∏ k ∈ S, (z - σ k) = ∑ k ∈ S, P.eval (σ k) * Lagrange.nodalWeight S σ k / (z - σ k) := by
  have hQ : ∏ k ∈ S, (z - σ k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k hk => sub_ne_zero.mpr (hz k hk)
  conv_lhs => rw [Lagrange.eq_interpolate hσ hP, Lagrange.eval_interpolate_not_at_node _ hz, Lagrange.eval_nodal]
  rw [mul_div_cancel_left₀ _ hQ]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [div_eq_mul_inv]; ring

end PartialFractions

/-! ### The rung cell Gram as a Gram matrix in `L²(1/2, 1]` -/

section Rung

open Real MeasureTheory
open Cvs.Prolate.EvenRungsByIndex (rung lev rung_spec)
open Cvs.Prolate.Gram.EvenFirstCellEnergyGram (L2c)
open Cvs.Prolate.Gram.RungCellGramDisplacement (cellGram rungCellGram rungIdx rungIdx_level rungCellGram_posDef quad_rungCellGram_le continuousOn_rung_cell)

/-- A function continuous on `[1/2, 1]` is square integrable on `(1/2, 1]`. -/
theorem memLp_cell {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (1 / 2 : ℝ) 1)) :
    MemLp f 2 (volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  refine MemLp.of_bound ((hf.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc) M ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  exact Filter.Eventually.of_forall fun s hs => hM s (Set.Ioc_subset_Icc_self hs)

theorem continuousOn_cellFun {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Fin x) :
    ContinuousOn (fun s => √2 * rung (2 * π * x) (rungIdx x j) s) (Set.Icc (1 / 2 : ℝ) 1) := by
  have := continuousOn_rung_cell (rungIdx_level hx j) (α := 1 / 2) (β := 1) (by norm_num) le_rfl (by norm_num)
  rw [Set.uIcc_of_le (by norm_num)] at this
  exact continuousOn_const.mul this

/-- The cell vector `u_j = √2 h_{4j}` in `L²(1/2, 1]`. -/
def cellVec {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Fin x) : L2c :=
  (memLp_cell (continuousOn_cellFun hx j)).toLp fun s => √2 * rung (2 * π * x) (rungIdx x j) s

/-- **The cell Gram is a Gram matrix**: `rungCellGram x = gram(u)` with `u_j = √2 h_{4j}` in `L²(1/2, 1]`. -/
theorem gram_cellVec {x : ℕ} (hx : 80 ≤ 2 * π * x) : gram ℝ (cellVec hx) = rungCellGram x := by
  ext a b
  have hae : (fun s => inner ℝ (cellVec hx a s) (cellVec hx b s)) =ᵐ[volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)]
      fun s => 2 * (rung (2 * π * x) (rungIdx x a) s * rung (2 * π * x) (rungIdx x b) s) := by
    filter_upwards [MemLp.coeFn_toLp (memLp_cell (continuousOn_cellFun hx a)),
      MemLp.coeFn_toLp (memLp_cell (continuousOn_cellFun hx b))] with s h1 h2
    simp only [cellVec] at *
    rw [h1, h2, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, RCLike.re_to_real]
    have h2' : √2 * √2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)
    linear_combination (rung (2 * π * x) (rungIdx x a) s * rung (2 * π * x) (rungIdx x b) s) * h2'
  rw [show gram ℝ (cellVec hx) a b = inner ℝ (cellVec hx a) (cellVec hx b) from rfl, L2.inner_def,
    integral_congr_ae hae, integral_const_mul, rungCellGram, cellGram, of_apply,
    intervalIntegral.integral_of_le (by norm_num)]

/-- The inner cell Gram: `(1 − C)_jk = ∫_{−1/2}^{1/2} h_{4j}h_{4k}`. -/
theorem one_sub_rungCellGram_apply {x : ℕ} (hx : 80 ≤ 2 * π * x) (j k : Fin x) :
    (1 - rungCellGram x) j k =
      ∫ s in (-(1 / 2) : ℝ)..(1 / 2), rung (2 * π * x) (rungIdx x j) s * rung (2 * π * x) (rungIdx x k) s := by
  set F : ℝ → ℝ := fun s => rung (2 * π * x) (rungIdx x j) s * rung (2 * π * x) (rungIdx x k) s
  have hj := rungIdx_level hx j
  have hk := rungIdx_level hx k
  have hFc : ContinuousOn F (Set.Icc (-1 : ℝ) 1) :=
    (Cvs.Prolate.EvenRungsByIndex.continuousOn_rung hj).mul (Cvs.Prolate.EvenRungsByIndex.continuousOn_rung hk)
  have hint : ∀ α β : ℝ, -1 ≤ α → β ≤ 1 → α ≤ β → IntervalIntegrable F volume α β := fun α β hα hβ hαβ =>
    (hFc.mono (by rw [Set.uIcc_of_le hαβ]; exact Set.Icc_subset_Icc hα hβ)).intervalIntegrable
  have hfull : ∫ s in (-1 : ℝ)..1, F s = (1 : Matrix (Fin x) (Fin x) ℝ) j k := by
    by_cases hjk : j = k
    · subst hjk
      rw [one_apply_eq]
      refine (intervalIntegral.integral_congr fun s _ => ?_).trans (rung_spec hj).2.2.2.2.2
      simp only [F]; ring
    · rw [one_apply_ne hjk]
      exact Cvs.Prolate.EvenRungParseval.integral_rung_mul_rung (c := 2 * π * x) (k := ⟨rungIdx x j, hj⟩)
        (j := ⟨rungIdx x k, hk⟩) fun he => hjk (Fin.ext (by
          have := congrArg Subtype.val he; simp only [rungIdx] at this; omega))
  have h1 : ∫ s in (-1 : ℝ)..1, F s = (∫ s in (-1 : ℝ)..(-(1 / 2)), F s) +
      (∫ s in (-(1 / 2) : ℝ)..(1 / 2), F s) + ∫ s in (1 / 2 : ℝ)..1, F s := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hint _ _ (by norm_num) (by norm_num) (by norm_num))
      (hint _ _ (by norm_num) (by norm_num) (by norm_num)),
      intervalIntegral.integral_add_adjacent_intervals (hint _ _ (by norm_num) (by norm_num) (by norm_num))
      (hint _ _ (by norm_num) (by norm_num) (by norm_num))]
  have hrefl : ∫ s in (-1 : ℝ)..(-(1 / 2)), F s = ∫ s in (1 / 2 : ℝ)..1, F s := by
    rw [← intervalIntegral.integral_comp_neg (a := 1 / 2) (b := 1) F]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hs
    have hs' : s ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [hs.1], hs.2⟩
    simp only [F]
    rw [(rung_spec hj).2.2.2.2.1 s hs', (rung_spec hk).2.2.2.2.1 s hs']
  rw [Matrix.sub_apply, ← hfull, h1, hrefl, rungCellGram, cellGram, of_apply]
  ring

end Rung

end Cvs.Prolate.Gram.WindowFloorMinNormInterp
