import Mathlib
import Cvs.Prolate.EvenRungParseval
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.EvenRungsComplete
import Cvs.Prolate.Gram.CellGramTraceComparison
import Cvs.Prolate.Gram.CentralResolventTrace
import Cvs.Prolate.Gram.EvenFirstCellEnergyGram
import Cvs.Prolate.Gram.FiniteFourierSplitCells
import Cvs.Prolate.Gram.WindowFloorExtension
import Cvs.Prolate.Gram.WindowFloorTransferSolutions
import Cvs.Prolate.GroundConcentrationStrict
import Cvs.Prolate.SincTopIsRung
import Cvs.Upstream.FourierTransferDualOperator
import Cvs.WeilForm.ChannelKernelBoundedOperator
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowCutBoundedBridge

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Parseval over the even prolates in `E2`, the norm `‖𝓕‖ ≤ √λ₀`, and the inner resolvent

`z ↦ zf z` embeds `E2` isometrically in `L²(0, 1]`, carrying `h_{2k}` to the rung Hilbert basis, so
`‖z‖² = Σ_k ⟨h_{2k}, z⟩²`. With `𝓕h_{2k} = σ_kh_{2k}` and `σ_k² ≤ λ₀` this gives `‖𝓕z‖² ≤ λ₀‖z‖²`; since `λ₀ < 1`,
`t ↦ Qy + Q𝓕Qt` is a contraction, and the inner resolvent equation `t = Qt = Qy + Q𝓕t` has a unique solution.
-/

noncomputable section

open Real MeasureTheory Set Filter
open scoped NNReal

namespace Cvs.Prolate.Gram.EvenProlateParsevalSplit
open Cvs.ZeroCounting

open Cvs.WeilForm.WeilFormOnWindowL2 (window)
open Cvs.Prolate.EvenRungsByIndex (rung lamR rung_spec)
open Cvs.Prolate.EvenRungParseval (LevelIdx rungBasis)
open Cvs.Prolate.Gram.WindowFloorTransferSolutions (E2 innerProj)
open Cvs.Prolate.Gram.FiniteFourierSplitCells (zf fourierE2)
open Cvs.Prolate.Gram.CellGramTraceComparison (prolE IsInnerSol)
open Cvs.Prolate.Gram.CentralResolventTrace (sigma)

/-! ### The embedding of `E2` in `L²(0, 1]` -/

/-- The class of `zf z` in the window `L²(0, 1]`. -/
def toWindow (z : E2) : window 1 :=
  ⟨(Cvs.Prolate.Gram.FiniteFourierSplitCells.memLp_zf z).toLp (zf z), by
    filter_upwards [(Cvs.Prolate.Gram.FiniteFourierSplitCells.memLp_zf z).coeFn_toLp] with u hu hne
    rw [hu]; exact Cvs.Prolate.Gram.FiniteFourierSplitCells.zf_eq_zero hne⟩

/-- The embedding preserves inner products. -/
theorem inner_toWindow (z w : E2) : inner ℝ (toWindow z) (toWindow w) = inner ℝ z w := by
  rw [Submodule.coe_inner, Cvs.Prolate.Gram.FiniteFourierSplitCells.inner_eq_integral, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(Cvs.Prolate.Gram.FiniteFourierSplitCells.memLp_zf z).coeFn_toLp, (Cvs.Prolate.Gram.FiniteFourierSplitCells.memLp_zf w).coeFn_toLp] with u h1 h2
  simp only [toWindow]
  rw [h1, h2, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, RCLike.re_to_real, mul_comm]

/-- The embedding carries `h_{2k}` to the rung Hilbert basis vector. -/
theorem toWindow_prolE {c : ℝ} (hc : c ≠ 0) (k : LevelIdx c) : toWindow (prolE k) = rungBasis hc k := by
  have hwc : ∀ k : LevelIdx c, ContinuousOn (rung c k) (Icc (-1) 1) := fun k => Cvs.Prolate.EvenRungsByIndex.continuousOn_rung k.2
  have hb : (rungBasis hc : LevelIdx c → window 1) = Cvs.Prolate.EvenRungParseval.basisVec hwc := Cvs.Prolate.EvenRungParseval.coe_hilbertBasis _ _ _ _ _
  rw [congrFun hb k]
  apply Subtype.ext
  simp only [Cvs.Prolate.EvenRungParseval.basisVec, Submodule.coe_smul, toWindow]
  apply Lp.ext
  have hcut := (Cvs.WeilForm.ChannelKernelBoundedOperator.memLp_cut_of_continuous
    (Cvs.Prolate.SincTopIsRung.continuous_clampExt (hwc k)) 1).coeFn_toLp
  filter_upwards [(Cvs.Prolate.Gram.FiniteFourierSplitCells.memLp_zf (prolE k)).coeFn_toLp, Cvs.Prolate.Gram.CellGramTraceComparison.zf_prolE k,
    Lp.coeFn_smul (√2) (Cvs.Prolate.SincTopIsRung.wCls hwc k : Lp ℝ 2 volume), hcut] with u h1 h2 h3 h4
  rw [h1, h2, h3, Pi.smul_apply, smul_eq_mul]
  have e : ((Cvs.Prolate.SincTopIsRung.wCls hwc k : window 1) : ℝ → ℝ) u
      = Cvs.WeilForm.WindowCutBoundedBridge.cut 1 (Cvs.Prolate.SincTopIsRung.clampExt (rung c k)) u := h4
  rw [e, Cvs.WeilForm.WindowCutBoundedBridge.cut]
  by_cases hu : u ∈ Ioc (0 : ℝ) 1
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu,
      Cvs.Prolate.SincTopIsRung.clampExt_of_mem ⟨by linarith [hu.1], hu.2⟩]
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, mul_zero]

/-- **Parseval over the even prolates in `E2`**: `Σ_k ⟨h_{2k}, z⟩⟨h_{2k}, w⟩ = ⟨z, w⟩` for `c ≠ 0`. -/
theorem hasSum_inner_prolE {c : ℝ} (hc : c ≠ 0) (z w : E2) :
    HasSum (fun k : LevelIdx c => inner ℝ (prolE k) z * inner ℝ (prolE k) w) (inner ℝ z w) := by
  have h := (rungBasis hc).hasSum_inner_mul_inner (toWindow z) (toWindow w)
  rw [inner_toWindow] at h
  refine h.congr_fun fun k => ?_
  rw [← toWindow_prolE hc k, inner_toWindow, inner_toWindow, real_inner_comm]

/-! ### The norm of the finite Fourier transform -/

/-- `σ_k² ≤ λ₀`. -/
theorem sigma_sq_le {c : ℝ} (hc : 0 < c) (k : LevelIdx c) : sigma c k ^ 2 ≤ lamR c 0 := by
  rw [Cvs.Prolate.Gram.CentralResolventTrace.sigma_sq]; exact Cvs.Prolate.EvenRungsByIndex.lamR_anti hc k.2 (Nat.zero_le k)

/-- **`‖𝓕z‖² ≤ λ₀‖z‖²`** for `c > 0`. -/
theorem norm_sq_fourierE2_le {c : ℝ} (hc : 0 < c) (z : E2) :
    ‖fourierE2 c z‖ ^ 2 ≤ lamR c 0 * ‖z‖ ^ 2 := by
  have h1 := hasSum_inner_prolE hc.ne' (fourierE2 c z) (fourierE2 c z)
  have h2 := (hasSum_inner_prolE hc.ne' z z).mul_left (lamR c 0)
  rw [real_inner_self_eq_norm_sq] at h1 h2
  refine hasSum_le (fun k => ?_) h1 h2
  have e : inner ℝ (prolE k) (fourierE2 c z) = sigma c k * inner ℝ (prolE k) z := by
    rw [← Cvs.Prolate.Gram.FiniteFourierSplitCells.fourierE2_symm, Cvs.Prolate.Gram.CellGramTraceComparison.fourierE2_prolE hc, inner_smul_left, conj_trivial]
  rw [e]
  nlinarith [sigma_sq_le hc k, sq_nonneg (inner ℝ (prolE k) z)]

/-- **`‖𝓕z‖ ≤ √λ₀‖z‖`** for `c > 0`. -/
theorem norm_fourierE2_le_sqrt {c : ℝ} (hc : 0 < c) (z : E2) : ‖fourierE2 c z‖ ≤ √(lamR c 0) * ‖z‖ := by
  rw [← Real.sqrt_sq (norm_nonneg (fourierE2 c z)), ← Real.sqrt_sq (norm_nonneg z), ← Real.sqrt_mul
    (Cvs.Prolate.EvenRungsByIndex.lamR_zero_pos hc).le]
  exact Real.sqrt_le_sqrt (norm_sq_fourierE2_le hc z)

/-! ### The inner resolvent -/

/-- `‖Qz‖ ≤ ‖z‖`. -/
theorem norm_innerProj_le (z : E2) : ‖innerProj z‖ ≤ ‖z‖ := by
  have h := Cvs.Prolate.Gram.WindowFloorTransferSolutions.isSymmProj_innerProj.norm_sq_add z
  nlinarith [norm_nonneg (innerProj z), norm_nonneg z, norm_nonneg (z - innerProj z)]

/-- `‖Q𝓕Qz‖ ≤ √λ₀‖z‖`. -/
theorem norm_inner_fourier_le {c : ℝ} (hc : 0 < c) (z : E2) :
    ‖innerProj (fourierE2 c (innerProj z))‖ ≤ √(lamR c 0) * ‖z‖ :=
  (norm_innerProj_le _).trans ((norm_fourierE2_le_sqrt hc _).trans
    (mul_le_mul_of_nonneg_left (norm_innerProj_le z) (Real.sqrt_nonneg _)))

/-- **The inner resolvent equation is solvable** for `c > 0`: some `t` has `Qt = t` and `t = Qy + Q𝓕t`. -/
theorem exists_innerSol {c : ℝ} (hc : 0 < c) (y : E2) : ∃ t, IsInnerSol c y t := by
  set K : ℝ≥0 := ⟨√(lamR c 0), Real.sqrt_nonneg _⟩
  set f : E2 → E2 := fun t => innerProj y + innerProj (fourierE2 c (innerProj t))
  have hK : K < 1 := by
    rw [← NNReal.coe_lt_coe, NNReal.coe_one]
    exact (Real.sqrt_lt' one_pos).mpr (by rw [one_pow]; exact Cvs.Prolate.GroundConcentrationStrict.lamR_zero_lt_one hc)
  have hL : LipschitzWith K f := by
    refine LipschitzWith.of_dist_le_mul fun t t' => ?_
    rw [dist_eq_norm, dist_eq_norm]
    have e : f t - f t' = innerProj (fourierE2 c (innerProj (t - t'))) := by
      simp only [f, map_sub]; abel
    rw [e]
    exact norm_inner_fourier_le hc _
  have hf : ContractingWith K f := ⟨hK, hL⟩
  set t := ContractingWith.fixedPoint f hf
  have ht : f t = t := ContractingWith.fixedPoint_isFixedPt hf
  have hQ : innerProj t = t := by
    rw [← ht]; simp only [f, map_add, Cvs.Prolate.Gram.WindowFloorTransferSolutions.isSymmProj_innerProj.idem]
  refine ⟨t, hQ, ?_⟩
  conv_lhs => rw [← ht]
  simp only [f, hQ]

/-- **The inner resolvent solution is unique** for `c > 0`. -/
theorem innerSol_unique {c : ℝ} (hc : 0 < c) {y t t' : E2} (ht : IsInnerSol c y t) (ht' : IsInnerSol c y t') :
    t = t' := by
  have e : t - t' = innerProj (fourierE2 c (innerProj (t - t'))) := by
    have h1 := ht.2
    have h2 := ht'.2
    rw [map_sub, ht.1, ht'.1, map_sub, map_sub]
    rw [← sub_eq_zero]
    have : t - t' - (innerProj (fourierE2 c t) - innerProj (fourierE2 c t'))
        = (t - (innerProj y + innerProj (fourierE2 c t))) - (t' - (innerProj y + innerProj (fourierE2 c t'))) := by
      abel
    rw [this, ← h1, ← h2, sub_self, sub_self, sub_zero]
  have hle := norm_inner_fourier_le hc (t - t')
  rw [← e] at hle
  have hlt : √(lamR c 0) < 1 := (Real.sqrt_lt' one_pos).mpr (by rw [one_pow]; exact Cvs.Prolate.GroundConcentrationStrict.lamR_zero_lt_one hc)
  have h0 : ‖t - t'‖ = 0 := by nlinarith [norm_nonneg (t - t')]
  exact sub_eq_zero.mp (norm_eq_zero.mp h0)

end Cvs.Prolate.Gram.EvenProlateParsevalSplit

end
