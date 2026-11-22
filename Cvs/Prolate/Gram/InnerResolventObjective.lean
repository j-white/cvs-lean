import Mathlib
import Cvs.Prolate.EvenRungParseval
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.CellGramTraceComparison
import Cvs.Prolate.Gram.CentralResolventTrace
import Cvs.Prolate.Gram.EvenFirstCellEnergyGram
import Cvs.Prolate.Gram.FiniteFourierSplitCells
import Cvs.Prolate.Gram.WindowFloorExtension
import Cvs.Prolate.Gram.WindowFloorTransferSolutions
import Cvs.Upstream.ContractionTraceComparison

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The inner resolvent solution attains the resolvent objective on `L²(I)`

For an inner solution `t = Qt = Qh_{2k} + Q𝓕t` in `E2`, the even function `f = t₁(|s|)/√2` on `I = [−1/2, 1/2]` has
`∫_I h_{2k}f = ⟨t, Qh_{2k}⟩`, `∫_I f² = ‖t‖²` and `⟨f, Af⟩ = ⟨t, 𝓕t⟩`, so the objective
`2⟨Qh, f⟩ − ‖f‖² + ⟨f, Af⟩` equals `⟨t, Qh_{2k}⟩`, which is therefore at most `⟨Qh_{2k}, (I − A)⁻¹Qh_{2k}⟩`.
-/

noncomputable section

open Real MeasureTheory Set Filter

namespace Cvs.Prolate.Gram.InnerResolventObjective
open Cvs.ZeroCounting

open Cvs.Prolate.EvenRungsByIndex (rung rung_spec)
open Cvs.Prolate.EvenRungParseval (LevelIdx)
open Cvs.Prolate.Gram.EvenFirstCellEnergyGram (L2c)
open Cvs.Prolate.Gram.WindowFloorExtension (L2i)
open Cvs.Prolate.Gram.WindowFloorTransferSolutions (E2 innerProj)
open Cvs.Prolate.Gram.FiniteFourierSplitCells (zf fourierE2 cosInt fimg)
open Cvs.Prolate.Gram.CentralResolventTrace (cI L2I resObj resQuad centralForm)
open Cvs.Prolate.Gram.CellGramTraceComparison (prolE IsInnerSol)

/-! ### Reflection on `I` -/

/-- The right half `(0, 1/2]` of `I`. -/
abbrev Ipos : Set ℝ := Ioc 0 (1 / 2)

/-- The left half `[−1/2, 0)` of `I`. -/
abbrev Ineg : Set ℝ := Ico (-1 / 2) 0

/-- `−[−1/2, 0) = (0, 1/2]`. -/
theorem preimage_neg_Ineg : (fun s : ℝ => -s) ⁻¹' Ineg = Ipos := by
  ext s; simp only [mem_preimage, mem_Ico, mem_Ioc]; constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- `−(0, 1/2] = [−1/2, 0)`. -/
theorem preimage_neg_Ipos : (fun s : ℝ => -s) ⁻¹' Ipos = Ineg := by
  ext s; simp only [mem_preimage, mem_Ico, mem_Ioc]; constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- `s ↦ −s` carries `(0, 1/2]` to `[−1/2, 0)` preserving Lebesgue measure. -/
theorem mp_pos : MeasurePreserving (fun s : ℝ => -s) (volume.restrict Ipos) (volume.restrict Ineg) := by
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage (s := Ineg) measurableSet_Ico
  rwa [show (Neg.neg : ℝ → ℝ) = fun s => -s from rfl, preimage_neg_Ineg] at h

/-- `s ↦ −s` carries `[−1/2, 0)` to `(0, 1/2]` preserving Lebesgue measure. -/
theorem mp_neg : MeasurePreserving (fun s : ℝ => -s) (volume.restrict Ineg) (volume.restrict Ipos) := by
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage (s := Ipos) measurableSet_Ioc
  rwa [show (Neg.neg : ℝ → ℝ) = fun s => -s from rfl, preimage_neg_Ipos] at h

/-- `s ↦ −s` is a measurable embedding. -/
theorem measurableEmbedding_neg : MeasurableEmbedding (fun s : ℝ => -s) := (Homeomorph.neg ℝ).measurableEmbedding

/-- `∫_{[−1/2,0)} F = ∫_{(0,1/2]} F(−s)`. -/
theorem integral_Ineg (F : ℝ → ℝ) : ∫ s in Ineg, F s = ∫ s in Ipos, F (-s) :=
  (mp_pos.integral_comp measurableEmbedding_neg F).symm

/-- The even extension `A(|s|)` of `A` from `(0, 1/2]`, as two indicators. -/
def sym (A : ℝ → ℝ) (s : ℝ) : ℝ := Ipos.indicator A s + Ineg.indicator (fun s => A (-s)) s

/-- Integrability on a subset `S ⊆ I` passes to the measure restricted to `I`. -/
theorem integrableOn_cI {S : Set ℝ} (hS : MeasurableSet S) (hsub : S ⊆ cI) {F : ℝ → ℝ} (h : IntegrableOn F S) :
    IntegrableOn F S (volume.restrict cI) := by
  unfold IntegrableOn; rw [Measure.restrict_restrict hS, inter_eq_left.mpr hsub]; exact h

/-- `(0, 1/2] ⊆ I`. -/
theorem Ipos_sub : Ipos ⊆ cI := fun s hs => ⟨by linarith [hs.1], hs.2⟩

/-- `[−1/2, 0) ⊆ I`. -/
theorem Ineg_sub : Ineg ⊆ cI := fun s hs => ⟨hs.1, by linarith [hs.2]⟩

/-- `∫_I w·sym A = ∫_{(0,1/2]} w A + ∫_{(0,1/2]} w(−s)A(s)`. -/
theorem integral_mul_sym {w A : ℝ → ℝ} (h1 : IntegrableOn (fun s => w s * A s) Ipos)
    (h2 : IntegrableOn (fun s => w s * A (-s)) Ineg) :
    ∫ s in cI, w s * sym A s = (∫ s in Ipos, w s * A s) + ∫ s in Ipos, w (-s) * A s := by
  have e : ∀ s, w s * sym A s
      = Ipos.indicator (fun s => w s * A s) s + Ineg.indicator (fun s => w s * A (-s)) s := by
    intro s
    rw [sym, mul_add, Set.indicator_mul_right, Set.indicator_mul_right]
  simp_rw [e]
  rw [integral_add ((integrableOn_cI measurableSet_Ioc Ipos_sub h1).integrable_indicator measurableSet_Ioc)
      ((integrableOn_cI measurableSet_Ico Ineg_sub h2).integrable_indicator measurableSet_Ico),
    setIntegral_indicator measurableSet_Ioc, setIntegral_indicator measurableSet_Ico,
    inter_eq_right.mpr Ipos_sub, inter_eq_right.mpr Ineg_sub, integral_Ineg]
  simp only [neg_neg]

/-- A bounded measurable weight times an integrable function on a subset of `[−1, 1]` is integrable. -/
theorem integrableOn_mul_of_continuousOn {w A : ℝ → ℝ} {S : Set ℝ} (hS : MeasurableSet S) (hsub : S ⊆ Icc (-1) 1)
    (hw : ContinuousOn w (Icc (-1) 1)) (hA : IntegrableOn A S) : IntegrableOn (fun s => w s * A s) S := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hw
  refine hA.bdd_mul (c := C) ((hw.mono hsub).aestronglyMeasurable hS) ?_
  rw [ae_restrict_iff' hS]
  exact Eventually.of_forall fun s hs => hC s (hsub hs)

/-! ### The even function of an inner vector -/

/-- `F/√2` is square integrable with `F`. -/
theorem memLp_div_sqrt {F : ℝ → ℝ} {μ : Measure ℝ} (h : MemLp F 2 μ) : MemLp (fun s => F s / √2) 2 μ := by
  have := h.const_smul (√2)⁻¹
  convert this using 1
  ext s; simp only [Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]

section Inner

variable (t : E2)

/-- The inner component `t₁ ∈ L²(0, 1/2]`. -/
def t1 : ℝ → ℝ := ((WithLp.ofLp t).1 : ℝ → ℝ)

/-- `t₁` is square integrable on `(0, 1/2]`. -/
theorem memLp_t1 : MemLp (t1 t) 2 (volume.restrict Ipos) := Lp.memLp _

/-- `t₁` is integrable on `(0, 1/2]`. -/
theorem integrableOn_t1 : IntegrableOn (t1 t) Ipos := (memLp_t1 t).integrable one_le_two

/-- `t₁(−s)` is integrable on `[−1/2, 0)`. -/
theorem integrableOn_t1_neg : IntegrableOn (fun s => t1 t (-s)) Ineg :=
  (mp_neg.integrable_comp_emb measurableEmbedding_neg).mpr (integrableOn_t1 t)

/-- `t₁(−s)` is square integrable on `[−1/2, 0)`. -/
theorem memLp_t1_neg : MemLp (fun s => t1 t (-s)) 2 (volume.restrict Ineg) :=
  (memLp_t1 t).comp_measurePreserving mp_neg

/-- The even function `f = t₁(|s|)/√2` on `I`. -/
def evenFun (s : ℝ) : ℝ := sym (fun s => t1 t s / √2) s

/-- `f` is square integrable on `I`. -/
theorem memLp_evenFun : MemLp (evenFun t) 2 (volume.restrict cI) := by
  have h1 : MemLp (Ipos.indicator fun s => t1 t s / √2) 2 (volume.restrict cI) := by
    rw [memLp_indicator_iff_restrict measurableSet_Ioc.nullMeasurableSet, Measure.restrict_restrict measurableSet_Ioc,
      inter_eq_left.mpr Ipos_sub]
    exact memLp_div_sqrt (memLp_t1 t)
  have h2 : MemLp (Ineg.indicator fun s => t1 t (-s) / √2) 2 (volume.restrict cI) := by
    rw [memLp_indicator_iff_restrict measurableSet_Ico.nullMeasurableSet, Measure.restrict_restrict measurableSet_Ico,
      inter_eq_left.mpr Ineg_sub]
    exact memLp_div_sqrt (memLp_t1_neg t)
  exact h1.add h2

/-- The class of `f` in `L²(I)`. -/
def evenVec : L2I := (memLp_evenFun t).toLp (evenFun t)

/-- The class of `f` is represented by `f`. -/
theorem coe_evenVec : (evenVec t : ℝ → ℝ) =ᵐ[volume.restrict cI] evenFun t := (memLp_evenFun t).coeFn_toLp

end Inner

/-! ### The three integrals -/

/-- `∫_I w f = √2∫_{(0,1/2]} w t₁` for `w` continuous on `[−1, 1]` and even on `(0, 1/2]`. -/
theorem integral_mul_evenVec {w : ℝ → ℝ} (hw : ContinuousOn w (Icc (-1) 1)) (hwe : ∀ s ∈ Ipos, w (-s) = w s)
    (t : E2) : ∫ s in cI, w s * evenVec t s = √2 * ∫ s in Ipos, w s * t1 t s := by
  have hpos : Ipos ⊆ Icc (-1) 1 := fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hneg : Ineg ⊆ Icc (-1) 1 := fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have e1 : ∫ s in cI, w s * evenVec t s = ∫ s in cI, w s * evenFun t s := by
    refine integral_congr_ae ?_
    filter_upwards [coe_evenVec t] with s hs; rw [hs]
  have i1 : IntegrableOn (fun s => w s * (t1 t s / √2)) Ipos :=
    integrableOn_mul_of_continuousOn measurableSet_Ioc hpos hw ((integrableOn_t1 t).div_const _)
  have i2 : IntegrableOn (fun s => w s * (t1 t (-s) / √2)) Ineg :=
    integrableOn_mul_of_continuousOn measurableSet_Ico hneg hw ((integrableOn_t1_neg t).div_const _)
  simp only [evenFun] at e1
  rw [e1, integral_mul_sym (A := fun s => t1 t s / √2) i1 i2]
  have e2 : ∫ s in Ipos, w (-s) * (t1 t s / √2) = ∫ s in Ipos, w s * (t1 t s / √2) :=
    setIntegral_congr_fun measurableSet_Ioc fun s hs => by rw [hwe s hs]
  rw [e2, ← two_mul]
  simp_rw [mul_div_assoc']
  rw [integral_div, mul_div_assoc', div_eq_iff (by positivity)]
  linear_combination (∫ s in Ipos, w s * t1 t s) * (Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)).symm

/-- `∫_I f² = ∫_{(0,1/2]} t₁²`. -/
theorem integral_evenVec_sq (t : E2) : ∫ s in cI, evenVec t s ^ 2 = ∫ s in Ipos, t1 t s ^ 2 := by
  set A : ℝ → ℝ := fun s => t1 t s / √2
  have e1 : ∫ s in cI, evenVec t s ^ 2 = ∫ s in cI, evenFun t s * sym A s := by
    refine integral_congr_ae ?_
    filter_upwards [coe_evenVec t] with s hs; rw [hs, sq]; rfl
  have hsq := (memLp_div_sqrt (memLp_t1 t)).integrable_sq
  have hsq' := (memLp_div_sqrt (memLp_t1_neg t)).integrable_sq
  have hv : ∀ s ∈ Ipos, evenFun t s = A s := fun s hs => by
    have hn : s ∉ Ineg := fun h => by linarith [h.2, hs.1]
    simp only [evenFun, sym, Set.indicator_of_mem hs, Set.indicator_of_notMem hn, add_zero, A]
  have hvn : ∀ s ∈ Ineg, evenFun t s = A (-s) := fun s hs => by
    have hn : s ∉ Ipos := fun h => by linarith [h.1, hs.2]
    simp only [evenFun, sym, Set.indicator_of_mem hs, Set.indicator_of_notMem hn, zero_add, A]
  have hv' : ∀ s ∈ Ipos, evenFun t (-s) = A s := fun s hs => by
    rw [hvn (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩, neg_neg]
  have i1 : IntegrableOn (fun s => evenFun t s * A s) Ipos := by
    refine hsq.congr ?_
    rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall fun s hs => by rw [hv s hs, sq]
  have i2 : IntegrableOn (fun s => evenFun t s * A (-s)) Ineg := by
    refine hsq'.congr ?_
    rw [EventuallyEq, ae_restrict_iff' measurableSet_Ico]
    exact Eventually.of_forall fun s hs => by rw [hvn s hs, sq]
  rw [e1, integral_mul_sym i1 i2]
  have e2 : ∀ F : ℝ → ℝ, (∀ s ∈ Ipos, F s = A s) →
      ∫ s in Ipos, F s * A s = ∫ s in Ipos, t1 t s ^ 2 / 2 := fun F hF =>
    setIntegral_congr_fun measurableSet_Ioc fun s hs => by
      simp only [A]; rw [hF s hs, div_mul_div_comm, Real.mul_self_sqrt (by norm_num), sq]
  rw [e2 _ hv, e2 (fun s => evenFun t (-s)) hv', integral_div]
  ring

/-- `cosInt c t s = ∫_{(0,1/2]} cos(csu) t₁(u)` for `Qt = t`. -/
theorem cosInt_eq_of_inner {c : ℝ} {t : E2} (ht : innerProj t = t) (s : ℝ) :
    cosInt c t s = ∫ u in Ipos, Real.cos (c * s * u) * t1 t u := by
  have h2 : (WithLp.ofLp t).2 = 0 := by rw [← ht]; rfl
  have hz : zf t =ᵐ[volume] Ipos.indicator (t1 t) := by
    have h := (ae_eq_restrict_iff_indicator_ae_eq (μ := volume) (s := Ioc (1 / 2 : ℝ) 1) measurableSet_Ioc).1
      (Lp.coeFn_zero ℝ 2 (volume.restrict (Ioc (1 / 2 : ℝ) 1)))
    filter_upwards [h] with u hu
    simp only [zf, h2]
    rw [hu]
    simp only [Pi.zero_def, Set.indicator_zero, add_zero]
    rfl
  rw [cosInt, ← integral_indicator measurableSet_Ioc]
  refine integral_congr_ae ?_
  filter_upwards [hz] with u hu
  rw [hu]
  by_cases h : u ∈ Ipos
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]

/-! ### The objective at `f` -/

section Objective

variable {c : ℝ} {t : E2}

/-- `Qt = t` forces the cell component of `t` to vanish. -/
theorem snd_eq_zero (ht : innerProj t = t) : (WithLp.ofLp t).2 = 0 := by rw [← ht]; rfl

/-- `⟨t, Qh_{2k}⟩ = √2∫_{(0,1/2]} h_{2k}t₁` for `Qt = t`. -/
theorem inner_innerProj_prolE (ht : innerProj t = t) (k : LevelIdx c) :
    inner ℝ t (innerProj (prolE k)) = √2 * ∫ s in Ipos, rung c k s * t1 t s := by
  rw [Cvs.Prolate.Gram.WindowFloorTransferSolutions.innerProj_apply, WithLp.prod_inner_apply, snd_eq_zero ht, inner_zero_left, add_zero]
  change inner ℝ (WithLp.ofLp t).1 (Cvs.Prolate.Gram.CellGramTraceComparison.prolInner k) = _
  rw [L2.inner_def, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (Cvs.Prolate.Gram.WindowFloorExtension.memLp_inner ((Cvs.Prolate.Gram.CellGramTraceComparison.continuousOn_prolFun k).mono
    (Icc_subset_Icc (by norm_num) (by norm_num))))] with s hs
  simp only [Cvs.Prolate.Gram.CellGramTraceComparison.prolInner] at hs ⊢
  rw [hs, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, RCLike.re_to_real, t1]
  ring

/-- `‖t‖² = ∫_{(0,1/2]} t₁²` for `Qt = t`. -/
theorem norm_sq_of_inner (ht : innerProj t = t) : ‖t‖ ^ 2 = ∫ s in Ipos, t1 t s ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, WithLp.prod_inner_apply, snd_eq_zero ht, inner_zero_left, add_zero,
    L2.inner_def]
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  simp only [t1]
  rw [real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, RCLike.re_to_real, sq]

/-- `⟨t, 𝓕t⟫ = √(2c/π)∫_{(0,1/2]} t₁ J(t)` for `Qt = t`. -/
theorem inner_fourierE2_of_inner (ht : innerProj t = t) :
    inner ℝ t (fourierE2 c t) = √(2 * c / π) * ∫ s in Ipos, t1 t s * cosInt c t s := by
  rw [WithLp.prod_inner_apply, snd_eq_zero ht, inner_zero_left, add_zero]
  change inner ℝ (WithLp.ofLp t).1 ((Cvs.Prolate.Gram.FiniteFourierSplitCells.memLp_fimg_of c t).toLp (fimg c t)) = _
  rw [L2.inner_def, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (Cvs.Prolate.Gram.FiniteFourierSplitCells.memLp_fimg_of (a := 0) (b := 1 / 2) c t)] with s hs
  rw [hs, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, RCLike.re_to_real, t1, Cvs.Prolate.Gram.FiniteFourierSplitCells.fimg]
  ring

/-- `⟨f, Af⟩ = 2√(c/2π)∫_{(0,1/2]} J(t)t₁` for `Qt = t`. -/
theorem centralForm_evenVec (ht : innerProj t = t) :
    centralForm c (evenVec t) = 2 * √(c / (2 * π)) * ∫ s in Ipos, cosInt c t s * t1 t s := by
  have hin : ∀ s, ∫ τ in cI, evenVec t s * Real.cos (c * s * τ) * evenVec t τ
      = evenVec t s * (√2 * cosInt c t s) := by
    intro s
    have e : (fun τ => evenVec t s * Real.cos (c * s * τ) * evenVec t τ)
        = fun τ => evenVec t s * (Real.cos (c * s * τ) * evenVec t τ) := funext fun τ => by ring
    rw [e, integral_const_mul,
      integral_mul_evenVec (by fun_prop : Continuous fun τ => Real.cos (c * s * τ)).continuousOn
        (fun τ _ => by rw [mul_neg, Real.cos_neg]) t, cosInt_eq_of_inner ht]
  have hJc : Continuous (cosInt c t) := Cvs.Prolate.Gram.FiniteFourierSplitCells.continuous_cosInt c t
  have hout : ∫ s in cI, evenVec t s * (√2 * cosInt c t s) = 2 * ∫ s in Ipos, cosInt c t s * t1 t s := by
    simp_rw [mul_comm (evenVec t _)]
    rw [integral_mul_evenVec (w := fun s => √2 * cosInt c t s) (continuous_const.mul hJc).continuousOn
      (fun s _ => by rw [Cvs.Prolate.Gram.FiniteFourierSplitCells.cosInt_neg]) t]
    simp_rw [mul_assoc]
    rw [integral_const_mul, ← mul_assoc, Real.mul_self_sqrt (by norm_num)]
  rw [centralForm]
  simp_rw [hin]
  rw [hout]
  ring

/-- **The objective attains `⟨t, Qh_{2k}⟩`** at `f = t₁(|s|)/√2` for an inner solution `t` at `h_{2k}`. -/
theorem resObj_evenVec (k : LevelIdx c) (ht : IsInnerSol c (prolE k) t) :
    resObj c (rung c k) (evenVec t) = inner ℝ t (innerProj (prolE k)) := by
  have h1 : ∫ s in cI, rung c k s * evenVec t s = √2 * ∫ s in Ipos, rung c k s * t1 t s :=
    integral_mul_evenVec (Cvs.Prolate.EvenRungsByIndex.continuousOn_rung k.2)
      (fun s hs => (rung_spec k.2).2.2.2.2.1 s ⟨by linarith [hs.1], by linarith [hs.2]⟩) t
  have hX := inner_innerProj_prolE ht.1 k
  have hN := norm_sq_of_inner ht.1
  have hF := inner_fourierE2_of_inner (c := c) ht.1
  have hC := centralForm_evenVec (c := c) ht.1
  have hform := Cvs.Upstream.ContractionTraceComparison.inner_eq_form Cvs.Prolate.Gram.WindowFloorTransferSolutions.isSymmProj_innerProj ht.1 ht.2
  have hform' : Cvs.Upstream.ContractionTraceComparison.form (fourierE2 c) t t = ‖t‖ ^ 2 - inner ℝ t (fourierE2 c t) := by
    rw [Cvs.Upstream.ContractionTraceComparison.form, inner_sub_right, real_inner_self_eq_norm_sq]
  have hr : √(2 * c / π) = 2 * √(c / (2 * π)) := by
    rw [show 2 * c / π = 2 ^ 2 * (c / (2 * π)) by field_simp, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  have hC' : centralForm c (evenVec t) = inner ℝ t (fourierE2 c t) := by
    rw [hC, hF, hr]
    simp_rw [mul_comm (cosInt c t _)]
  rw [resObj, h1, integral_evenVec_sq, ← hN, hC', ← hX]
  linarith

/-- **`⟨t, Qh_{2k}⟩ ≤ ⟨Qh_{2k}, (I − A)⁻¹Qh_{2k}⟩`** when the objective is bounded above. -/
theorem inner_le_resQuad (k : LevelIdx c) (ht : IsInnerSol c (prolE k) t)
    (hb : BddAbove (range (resObj c (rung c k)))) : inner ℝ t (innerProj (prolE k)) ≤ resQuad c (rung c k) :=
  (resObj_evenVec k ht).symm.le.trans (le_ciSup hb _)

end Objective

end Cvs.Prolate.Gram.InnerResolventObjective

end
