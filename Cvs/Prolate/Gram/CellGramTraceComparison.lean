import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.EvenRungParseval
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.CentralResolventTrace
import Cvs.Prolate.Gram.EvenFirstCellEnergyGram
import Cvs.Prolate.Gram.FiniteFourierSplitCells
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Prolate.Gram.RungCellGramDisplacement
import Cvs.Prolate.Gram.RungFixedFourierTransfer
import Cvs.Prolate.Gram.WindowFloorExtension
import Cvs.Prolate.Gram.WindowFloorIsSchurFloor
import Cvs.Prolate.Gram.WindowFloorMinNormInterp
import Cvs.Prolate.Gram.WindowFloorTransferSolutions
import Cvs.Prolate.Mellin.CosineTransformMellin
import Cvs.Route.Visibility.LayerFloorDeepRemainderB
import Cvs.Upstream.ContractionTraceComparison
import Cvs.Upstream.InverseExcessPencilTop

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The trace comparison for the cell Gram of the prolate rungs

Every even prolate `h_{2k}` is an eigenvector of the finite Fourier transform on `E2`, `𝓕h_{2k} = σ_k h_{2k}` with `σ_k
= √(c/2π)μ_k`. For inner solutions `t_k = Qh_{2k} + Q𝓕t_k` and any value `T` of the trace `Σ_k g(σ_k)⟨t_k, Qh_{2k}⟩`
with `μ*T < 1`: `Σ_j μ_j((C⁻¹)_jj − 1) ≤ 2a_tT/(1 − μ*T)` and `c_E ≤ μ_t + 2a_tT/(1 − μ*T)`.
-/

noncomputable section

open Real MeasureTheory Set Filter Matrix

namespace Cvs.Prolate.Gram.CellGramTraceComparison
open Cvs.ZeroCounting

open Cvs.Prolate.EvenRungsByIndex (rung muR lamR rung_spec)
open Cvs.Prolate.EvenRungParseval (LevelIdx)
open Cvs.Prolate.Gram.EvenFirstCellEnergyGram (L2c)
open Cvs.Prolate.Gram.WindowFloorExtension (L2i memLp_inner)
open Cvs.Prolate.Gram.WindowFloorTransferSolutions (E2 rungE innerProj)
open Cvs.Prolate.Gram.FiniteFourierSplitCells (fourierE2 zf fimg cosInt)
open Cvs.Prolate.Gram.ProlateCellGramHalfUnit (lam lamTop mu cellGram)
open Cvs.Route.Visibility.LayerFloorDeepRemainderB (muStar cE)
open Cvs.Prolate.Gram.CentralResolventTrace (gpoly aTop sigma)
open Cvs.Upstream.InverseExcessPencilTop (excessTrace)

/-! ### The even prolates in `E2` and their Fourier eigenvalues -/

section Prolates

variable {c : ℝ}

/-- `√2 h_{2k}` is continuous on `[−1, 1]`. -/
theorem continuousOn_prolFun (k : LevelIdx c) : ContinuousOn (fun s => √2 * rung c k s) (Icc (-1) 1) :=
  continuousOn_const.mul (Cvs.Prolate.EvenRungsByIndex.continuousOn_rung k.2)

/-- The inner part `√2 h_{2k}` in `L²(0, 1/2]`. -/
def prolInner (k : LevelIdx c) : L2i :=
  (memLp_inner ((continuousOn_prolFun k).mono (Icc_subset_Icc (by norm_num) (by norm_num)))).toLp
    fun s => √2 * rung c k s

/-- The cell part `√2 h_{2k}` in `L²(1/2, 1]`. -/
def prolCell (k : LevelIdx c) : L2c :=
  (Cvs.Prolate.Gram.WindowFloorMinNormInterp.memLp_cell ((continuousOn_prolFun k).mono (Icc_subset_Icc (by norm_num) le_rfl))).toLp
    fun s => √2 * rung c k s

/-- The even prolate `h_{2k}` in `E2 = L²(0, 1/2] ⊕ L²(1/2, 1]`. -/
def prolE (k : LevelIdx c) : E2 := WithLp.toLp 2 (prolInner k, prolCell k)

/-- `zf h_{2k} = 1_{(0,1]}·√2 h_{2k}` almost everywhere. -/
theorem zf_prolE (k : LevelIdx c) :
    zf (prolE k) =ᵐ[volume] (Ioc (0 : ℝ) 1).indicator fun s => √2 * rung c k s := by
  have h1 := (ae_eq_restrict_iff_indicator_ae_eq (μ := volume) (s := Ioc (0 : ℝ) (1 / 2)) measurableSet_Ioc).1
    (MemLp.coeFn_toLp (memLp_inner ((continuousOn_prolFun k).mono
      (Icc_subset_Icc (by norm_num) (by norm_num)))))
  have h2 := (ae_eq_restrict_iff_indicator_ae_eq (μ := volume) (s := Ioc (1 / 2 : ℝ) 1) measurableSet_Ioc).1
    (MemLp.coeFn_toLp (Cvs.Prolate.Gram.WindowFloorMinNormInterp.memLp_cell ((continuousOn_prolFun k).mono (Icc_subset_Icc (by norm_num) le_rfl))))
  filter_upwards [h1, h2] with u hu1 hu2
  simp only [zf, prolE, prolInner, prolCell, WithLp.ofLp_toLp] at hu1 hu2 ⊢
  rw [hu1, hu2]
  by_cases ha : u ∈ Ioc (0 : ℝ) (1 / 2)
  · have hb : u ∉ Ioc (1 / 2 : ℝ) 1 := fun h => by linarith [h.1, ha.2]
    have hc : u ∈ Ioc (0 : ℝ) 1 := ⟨ha.1, by linarith [ha.2]⟩
    rw [Set.indicator_of_mem ha, Set.indicator_of_notMem hb, Set.indicator_of_mem hc, add_zero]
  · by_cases hb : u ∈ Ioc (1 / 2 : ℝ) 1
    · have hc : u ∈ Ioc (0 : ℝ) 1 := ⟨by linarith [hb.1], hb.2⟩
      rw [Set.indicator_of_notMem ha, Set.indicator_of_mem hb, Set.indicator_of_mem hc, zero_add]
    · have hc : u ∉ Ioc (0 : ℝ) 1 := fun h => by
        by_cases h' : u ≤ 1 / 2
        · exact ha ⟨h.1, h'⟩
        · exact hb ⟨lt_of_not_ge h', h.2⟩
      rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem hb, Set.indicator_of_notMem hc, add_zero]

/-- The cosine integral of `h_{2k}` is half its finite cosine transform: `J h_{2k}(s) = (√2/2)ψ_c h_{2k}(s)`. -/
theorem cosInt_prolE (k : LevelIdx c) (s : ℝ) :
    cosInt c (prolE k) s = √2 / 2 * Cvs.L2a.AngularProlateTailPositive.psi c (rung c k) s := by
  rw [Cvs.Prolate.Mellin.CosineTransformMellin.psi_eq_two_integral (Cvs.Prolate.EvenRungsByIndex.continuousOn_rung k.2) (rung_spec k.2).2.2.2.2.1, cosInt]
  have e : (fun u => Real.cos (c * s * u) * zf (prolE k) u) =ᵐ[volume]
      (Ioc (0 : ℝ) 1).indicator fun u => √2 * (rung c k u * Real.cos (c * u * s)) := by
    filter_upwards [zf_prolE k] with u hu
    rw [hu]
    by_cases h : u ∈ Ioc (0 : ℝ) 1
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, show c * s * u = c * u * s by ring]; ring
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]
  rw [integral_congr_ae e, integral_indicator measurableSet_Ioc, integral_const_mul]
  ring

/-- **Every even prolate is a Fourier eigenvector in `E2`**: `𝓕h_{2k} = σ_k h_{2k}` for `c > 0`. -/
theorem fourierE2_prolE (hc : 0 < c) (k : LevelIdx c) : fourierE2 c (prolE k) = sigma c k • prolE k := by
  have hr : √(2 * c / π) = 2 * √(c / (2 * π)) := by
    rw [show 2 * c / π = 2 ^ 2 * (c / (2 * π)) by field_simp, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  have hpt : ∀ s ∈ Icc (-1 : ℝ) 1, fimg c (prolE k) s = sigma c k * (√2 * rung c k s) := by
    intro s hs
    rw [Cvs.Prolate.Gram.FiniteFourierSplitCells.fimg, cosInt_prolE, Cvs.Prolate.EvenRungsByIndex.psi_rung k.2 s hs, Cvs.Prolate.Gram.CentralResolventTrace.sigma, hr]
    ring
  have hae : ∀ {a b : ℝ}, -1 ≤ a → b ≤ 1 →
      fimg c (prolE k) =ᵐ[volume.restrict (Ioc a b)] fun s => sigma c k • (√2 * rung c k s) := by
    intro a b ha hb
    rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall fun s hs => by
      rw [smul_eq_mul]; exact hpt s ⟨by linarith [hs.1], by linarith [hs.2]⟩
  change WithLp.toLp 2 (_, _) = sigma c k • WithLp.toLp 2 (prolInner k, prolCell k)
  rw [← WithLp.toLp_smul]
  congr 1
  refine Prod.ext ?_ ?_
  · simp only [Prod.smul_fst, prolInner]
    rw [← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (hae (by norm_num) (by norm_num))
  · simp only [Prod.smul_snd, prolCell]
    rw [← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (hae (by norm_num) le_rfl)

end Prolates

/-! ### The selected rungs among the even prolates -/

/-- The selected rung `h_{4j}` as an even prolate index. -/
def selIdx {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Fin x) : LevelIdx (2 * π * x) :=
  ⟨2 * (j : ℕ), Cvs.Prolate.Gram.RungCellGramDisplacement.rungIdx_level hx j⟩

/-- The selected index map is injective. -/
theorem selIdx_injective {x : ℕ} (hx : 80 ≤ 2 * π * x) : Function.Injective (selIdx hx) := by
  intro i j h
  have : 2 * (i : ℕ) = 2 * j := congrArg Subtype.val h
  exact Fin.ext (by omega)

/-- The selected prolate is the rung `e_j` of `E2`. -/
theorem prolE_selIdx {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Fin x) : prolE (selIdx hx j) = rungE hx j := rfl

/-- `𝓕e_j = √λ_j e_j`. -/
theorem fourierE2_rungE {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Fin x) :
    fourierE2 (2 * π * x) (rungE hx j) = √(lam x j) • rungE hx j := by
  rw [← prolE_selIdx, fourierE2_prolE (by linarith) (selIdx hx j)]
  congr 1
  exact Cvs.Prolate.Gram.CentralResolventTrace.sigma_two_mul hx j

/-- `𝓕̃ = 𝓕 + Σ_b (1 − √λ_b)e_b e_bᵀ` on `E2`. -/
theorem fourierFixed_eq {x : ℕ} (hx : 80 ≤ 2 * π * x) (z : E2) :
    Cvs.Prolate.Gram.RungFixedFourierTransfer.fourierFixed hx z
      = fourierE2 (2 * π * x) z + ∑ b : Fin x, ((1 - √(lam x b)) * inner ℝ (rungE hx b) z) • rungE hx b :=
  Cvs.Upstream.ContractionTraceComparison.fixT_eq (Cvs.Prolate.Gram.WindowFloorTransferSolutions.inner_rungE hx) (Cvs.Prolate.Gram.FiniteFourierSplitCells.fourierE2_symm _) (fourierE2_rungE hx)
    (Cvs.Prolate.Gram.RungFixedFourierTransfer.rungProj_apply hx) z

/-- The cell Gram is the Gram of the cell parts `e_b − Qe_b` in `E2`. -/
theorem cellGram_eq_gram {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    cellGram x = gram ℝ fun b => rungE hx b - innerProj (rungE hx b) := by
  rw [Cvs.Prolate.Gram.WindowFloorIsSchurFloor.cellGram_eq_rungCellGram, Cvs.Prolate.Gram.WindowFloorTransferSolutions.gram_cellPart]

/-! ### The trace and the comparison -/

/-- `t` solves the inner resolvent equation at `y`: `Qt = t` and `t = Qy + Q𝓕t`. -/
def IsInnerSol (c : ℝ) (y t : E2) : Prop := innerProj t = t ∧ t = innerProj y + innerProj (fourierE2 c t)

/-- The trace term `g(σ_k)⟨t_k, Qh_{2k}⟩` of `Tr[(I − Q𝓕Q)⁻¹Qg(𝓕)Q]` in the prolate eigenbasis. -/
def traceTerm (c : ℝ) (t : LevelIdx c → E2) (k : LevelIdx c) : ℝ :=
  gpoly (sigma c k) * inner ℝ (t k) (innerProj (prolE k))

/-- `⟨t, Qy⟩ ≥ 0` for an inner solution `t` at `y`, `c > 0`. -/
theorem inner_innerSol_nonneg {c : ℝ} (hc : 0 < c) {y t : E2} (ht : IsInnerSol c y t) :
    0 ≤ inner ℝ t (innerProj y) := by
  rw [Cvs.Upstream.ContractionTraceComparison.inner_eq_form Cvs.Prolate.Gram.WindowFloorTransferSolutions.isSymmProj_innerProj ht.1 ht.2]
  exact Cvs.Upstream.ContractionTraceComparison.form_self_nonneg (Cvs.Prolate.Gram.FiniteFourierSplitCells.norm_fourierE2_le hc) t

/-- Every trace term is nonnegative. -/
theorem traceTerm_nonneg {c : ℝ} (hc : 0 < c) {t : LevelIdx c → E2} (ht : ∀ k, IsInnerSol c (prolE k) (t k))
    (k : LevelIdx c) : 0 ≤ traceTerm c t k :=
  mul_nonneg (Cvs.Prolate.Gram.CentralResolventTrace.gpoly_nonneg (Cvs.Prolate.Gram.CentralResolventTrace.abs_sigma_le_one hc k.2)) (inner_innerSol_nonneg hc (ht k))

/-- A value of the trace is nonnegative. -/
theorem trace_nonneg {c : ℝ} (hc : 0 < c) {t : LevelIdx c → E2} (ht : ∀ k, IsInnerSol c (prolE k) (t k))
    {T : ℝ} (hT : HasSum (traceTerm c t) T) : 0 ≤ T :=
  hT.nonneg (traceTerm_nonneg hc ht)

/-- **(B), the excess form**: for inner solutions `t_k` and a value `T` of the trace with `μ*T < 1`,
`Σ_j μ_j((C⁻¹)_jj − 1) ≤ 2a_tT/(1 − μ*T)`. -/
theorem excessTrace_le_trace {x : ℕ} (hx : 80 ≤ 2 * π * x) {t : LevelIdx (2 * π * x) → E2}
    (ht : ∀ k, IsInnerSol (2 * π * x) (prolE k) (t k)) {T : ℝ} (hT : HasSum (traceTerm (2 * π * x) t) T)
    (hmT : muStar * T < 1) :
    excessTrace (fun j : Fin x => mu x j) (cellGram x) ≤ 2 * aTop x * T / (1 - muStar * T) := by
  have hc : 0 < 2 * π * x := by linarith
  have hsel : ∀ j, IsInnerSol (2 * π * x) (rungE hx j) (t (selIdx hx j)) := fun j => by
    rw [← prolE_selIdx]; exact ht _
  have hTs : ∑ b : Fin x, gpoly √(lam x b) * inner ℝ (t (selIdx hx b)) (innerProj (rungE hx b)) ≤ T := by
    have h := sum_le_hasSum (Finset.univ.map ⟨selIdx hx, selIdx_injective hx⟩)
      (fun k _ => traceTerm_nonneg hc ht k) hT
    rw [Finset.sum_map] at h
    refine le_of_eq_of_le (Finset.sum_congr rfl fun b _ => ?_) h
    simp only [Function.Embedding.coeFn_mk, traceTerm, prolE_selIdx]
    rw [show sigma (2 * π * x) (selIdx hx b) = √(lam x b) from Cvs.Prolate.Gram.CentralResolventTrace.sigma_two_mul hx b]
  rw [cellGram_eq_gram hx]
  refine Cvs.Upstream.ContractionTraceComparison.excessTrace_le Cvs.Prolate.Gram.WindowFloorTransferSolutions.isSymmProj_innerProj (Cvs.Prolate.Gram.FiniteFourierSplitCells.fourierE2_symm _) (Cvs.Prolate.Gram.FiniteFourierSplitCells.norm_fourierE2_le hc)
    (Cvs.Prolate.Gram.RungFixedFourierTransfer.fourierFixed_symm hx) (Cvs.Prolate.Gram.RungFixedFourierTransfer.fourierFixed_norm_le hx) (Cvs.Prolate.Gram.WindowFloorTransferSolutions.inner_rungE hx) (fourierE2_rungE hx)
    (fourierFixed_eq hx) (fun b => (hsel b).1) (fun b => (hsel b).2) ?_ (fun b => ?_) (fun b => Cvs.Prolate.Gram.ProlateCellGramHalfUnit.mu_nonneg hx b.2)
    (Cvs.Prolate.Gram.CentralResolventTrace.mu_le_aTop_mul hx) (Cvs.Prolate.Gram.CentralResolventTrace.delta_le_muStar_mul hx) (Cvs.Prolate.Gram.CentralResolventTrace.aTop_nonneg hx)
    Cvs.Route.Visibility.LayerFloorDeepRemainderB.muStar_pos.le hTs hmT
  · rw [Cvs.Prolate.Gram.WindowFloorTransferSolutions.gram_cellPart]; exact Cvs.Prolate.Gram.RungCellGramDisplacement.rungCellGram_posDef hx
  · exact Real.sqrt_le_one.mpr (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lam_le_one hx b.2)

/-- **(B), the pencil form**: `c_E ≤ μ_t + 2a_tT/(1 − μ*T)` for inner solutions and a trace value `μ*T < 1`. -/
theorem cE_le_trace {x : ℕ} (hx : 80 ≤ 2 * π * x) {t : LevelIdx (2 * π * x) → E2}
    (ht : ∀ k, IsInnerSol (2 * π * x) (prolE k) (t k)) {T : ℝ} (hT : HasSum (traceTerm (2 * π * x) t) T)
    (hmT : muStar * T < 1) : cE x ≤ mu x (x - 1) + 2 * aTop x * T / (1 - muStar * T) := by
  have h1 := Cvs.Upstream.InverseExcessPencilTop.cE_le_muTop_add_excess hx
  have h2 := excessTrace_le_trace hx ht hT hmT
  unfold Cvs.Upstream.InverseExcessPencilTop.prolateExcess at h1
  linarith

end Cvs.Prolate.Gram.CellGramTraceComparison

end
