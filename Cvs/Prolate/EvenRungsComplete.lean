import Mathlib
import Cvs.Finite.DisplacementIdentity
import Cvs.Finite.RecentredTransform
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.AngularEdgeValueNonzero
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.SincTopIsRung
import Cvs.Upstream.FourierLaplace
import Cvs.WeilForm.OddCapTransfer
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.TransformNowhereLocallyZero
import Cvs.WeilForm.TruncatedFormPolarised
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowRepresentative

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The even rungs are complete in the window `L²(0, 1]`

For `c ≠ 0` the folded cosine transform `F` has trivial kernel on `L²(0, 1]`, through the entire
transform of the even extension; so `F²` has trivial kernel, and the classes of all the even
angular rungs `rung c k` have trivial orthogonal complement.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology
open FourierLaplace (fourierLaplace)
open scoped Interval

namespace Cvs.Prolate.EvenRungsComplete
open Cvs.ZeroCounting

open Cvs.WeilForm.WeilFormOnWindowL2 (window)
open Cvs.WeilForm.WindowRepresentative (rep rep_supp)
open Cvs.WeilForm.SelfConvolutionTransform (cf)
open Cvs.Prolate.SincTopIsRung
open Cvs.Prolate.EvenRungsByIndex (IsLevelIdx rung rung_spec)

/-! ### The even extension of a window class -/

/-- The even extension `s ↦ φ(s) + φ(−s)` of a class of `L²(0, 1]`. -/
def evenExt (φ : window 1) (s : ℝ) : ℝ := rep φ s + rep φ (-s)

theorem memLp_evenExt (φ : window 1) :
    MemLp (evenExt φ) 2 (volume : Measure ℝ) :=
  (Cvs.WeilForm.WindowRepresentative.memLp_rep φ).add
    ((Cvs.WeilForm.WindowRepresentative.memLp_rep φ).comp_measurePreserving
      (Measure.measurePreserving_neg (volume : Measure ℝ)))

theorem integrable_evenExt (φ : window 1) :
    Integrable (evenExt φ) (volume : Measure ℝ) :=
  (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep φ).add (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep φ).comp_neg

theorem evenExt_eq_zero (φ : window 1) {s : ℝ} (hs : 1 < |s|) :
    evenExt φ s = 0 := by
  have h1 : s ∉ Ioc (0 : ℝ) 1 := fun h => by
    rw [abs_of_pos h.1] at hs; linarith [h.2]
  have h2 : -s ∉ Ioc (0 : ℝ) 1 := fun h => by
    rw [abs_of_neg (by linarith [h.1])] at hs; linarith [h.2]
  rw [evenExt, rep_supp φ s h1, rep_supp φ (-s) h2, add_zero]

/-- The even extension carries at least the mass of the class: `φ(s)² ≤ (φ(s) + φ(−s))²`. -/
theorem sq_rep_le_sq_evenExt (φ : window 1) (s : ℝ) :
    rep φ s ^ 2 ≤ evenExt φ s ^ 2 := by
  by_cases hs : s ∈ Ioc (0 : ℝ) 1
  · have h2 : -s ∉ Ioc (0 : ℝ) 1 := fun h => by linarith [h.1, hs.1]
    rw [evenExt, rep_supp φ (-s) h2, add_zero]
  · rw [rep_supp φ s hs]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity

theorem sq_norm_le_integral_evenExt (φ : window 1) :
    ‖φ‖ ^ 2 ≤ ∫ s, evenExt φ s ^ 2 := by
  rw [Cvs.WeilForm.OddCapTransfer.sq_norm_eq_integral_rep]
  exact integral_mono (Cvs.WeilForm.WindowRepresentative.integrable_sq_rep φ) (memLp_evenExt φ).integrable_sq
    (sq_rep_le_sq_evenExt φ)

/-- **The transform of the even extension at a real point is the folded cosine transform.** -/
theorem fourierLaplace_evenExt (c : ℝ) (φ : window 1) (ξ : ℝ) :
    fourierLaplace (cf (evenExt φ)) ((c * ξ : ℝ) : ℂ)
      = (cosFn c φ ξ : ℂ) := by
  set w : ℝ := c * ξ with hw
  have hb : ∀ t : ℝ, ‖Complex.exp (Complex.I * (w : ℂ) * (t : ℂ))‖ ≤ 1 := fun t => by
    rw [FourierLaplace.norm_exp_I_mul]; simp
  have hm : AEStronglyMeasurable (fun t : ℝ => Complex.exp (Complex.I * (w : ℂ) * (t : ℂ)))
      (volume : Measure ℝ) := (by fun_prop : Continuous _).aestronglyMeasurable
  have hi1 : Integrable
      (fun t : ℝ => ((rep φ t : ℝ) : ℂ) * Complex.exp (Complex.I * (w : ℂ) * (t : ℂ)))
      (volume : Measure ℝ) :=
    (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep φ).ofReal.mul_bdd hm (Eventually.of_forall hb)
  have hi2 : Integrable
      (fun t : ℝ => ((rep φ (-t) : ℝ) : ℂ) * Complex.exp (Complex.I * (w : ℂ) * (t : ℂ)))
      (volume : Measure ℝ) :=
    (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep φ).comp_neg.ofReal.mul_bdd hm (Eventually.of_forall hb)
  have hsplit : fourierLaplace (cf (evenExt φ)) (w : ℂ)
      = (∫ t : ℝ, ((rep φ t : ℝ) : ℂ) * Complex.exp (Complex.I * (w : ℂ) * (t : ℂ)))
        + ∫ t : ℝ, ((rep φ (-t) : ℝ) : ℂ) * Complex.exp (Complex.I * (w : ℂ) * (t : ℂ)) := by
    rw [fourierLaplace, ← integral_add hi1 hi2]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [cf, evenExt, Complex.ofReal_add]
    ring
  have hneg : (∫ t : ℝ, ((rep φ (-t) : ℝ) : ℂ) * Complex.exp (Complex.I * (w : ℂ) * (t : ℂ)))
      = ∫ t : ℝ, ((rep φ t : ℝ) : ℂ) * Complex.exp (Complex.I * (w : ℂ) * ((-t : ℝ) : ℂ)) := by
    rw [← integral_neg_eq_self (fun t : ℝ =>
      ((rep φ t : ℝ) : ℂ) * Complex.exp (Complex.I * (w : ℂ) * ((-t : ℝ) : ℂ)))]
    simp only [neg_neg]
  have hi3 : Integrable
      (fun t : ℝ => ((rep φ t : ℝ) : ℂ) * Complex.exp (Complex.I * (w : ℂ) * ((-t : ℝ) : ℂ)))
      (volume : Measure ℝ) := by
    simpa only [neg_neg] using hi2.comp_neg
  rw [hsplit, hneg, ← integral_add hi1 hi3]
  have hpt : ∀ t : ℝ, ((rep φ t : ℝ) : ℂ) * Complex.exp (Complex.I * (w : ℂ) * (t : ℂ))
      + ((rep φ t : ℝ) : ℂ) * Complex.exp (Complex.I * (w : ℂ) * ((-t : ℝ) : ℂ))
      = ((2 * (rep φ t * Real.cos (c * ξ * t)) : ℝ) : ℂ) := by
    intro t
    have e : Complex.exp (Complex.I * (w : ℂ) * (t : ℂ))
        + Complex.exp (Complex.I * (w : ℂ) * ((-t : ℝ) : ℂ))
        = 2 * Complex.cos ((c * ξ * t : ℝ) : ℂ) := by
      rw [Complex.two_cos, hw]
      push_cast
      ring_nf
    have e2 : ((2 * (rep φ t * Real.cos (c * ξ * t)) : ℝ) : ℂ)
        = 2 * (((rep φ t : ℝ) : ℂ) * Complex.cos ((c * ξ * t : ℝ) : ℂ)) := by
      push_cast; ring
    rw [e2]
    linear_combination ((rep φ t : ℝ) : ℂ) * e
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_complex_ofReal, integral_const_mul]
  rfl

/-- The even extension has compact support. -/
theorem hasCompactSupport_evenExt (φ : window 1) :
    HasCompactSupport (cf (evenExt φ)) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) ?_
  intro s hs
  rw [Function.mem_support] at hs
  by_contra hmem
  refine hs ?_
  have h1 : 1 < |s| := by
    by_contra hle
    exact hmem (abs_le.1 (not_lt.1 hle))
  simp only [cf, evenExt_eq_zero φ h1, Complex.ofReal_zero]

/-- The zero function's cut class is `0`. -/
theorem cutCls_zero : cutCls (continuous_const (y := (0 : ℝ))) = 0 := by
  have hz : Continuous fun s : ℝ => (0 : ℝ) * s := continuous_const.mul continuous_id
  rw [cutCls_eq continuous_const hz (fun s _ => by simp), cutCls_smul continuous_id 0 hz, zero_smul]

/-- **`F φ = 0` forces `φ = 0`** on `L²(0, 1]` when `c ≠ 0`. -/
theorem eq_zero_of_cosMap_eq_zero {c : ℝ} (hc : c ≠ 0) {φ : window 1}
    (h : cosMap c φ = 0) : φ = 0 := by
  have hz : ∀ ξ ∈ Icc (0 : ℝ) 1, cosFn c φ ξ = 0 := fun ξ hξ =>
    eqOn_of_cutCls_eq (continuous_cosFn c φ) continuous_const (h.trans cutCls_zero.symm) hξ
  -- the entire transform of the even extension vanishes near `0`
  have hent : Differentiable ℂ (fourierLaplace (cf (evenExt φ))) :=
    FourierLaplace.differentiable_fourierLaplace_of_integrable (integrable_evenExt φ).ofReal
      (hasCompactSupport_evenExt φ)
  have ht : Tendsto (fun n : ℕ => ((c * (1 / ((n : ℝ) + 1)) : ℝ) : ℂ)) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have h1 := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul c
      rw [mul_zero] at h1
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
      rwa [Complex.ofReal_zero] at h2
    · simp only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_eq_zero]
      exact mul_ne_zero hc (by positivity)
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ),
      fourierLaplace (cf (evenExt φ)) z = 0 := by
    refine ht.frequently (Frequently.of_forall fun n => ?_)
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    rw [fourierLaplace_evenExt, hz _ ⟨by positivity, ?_⟩, Complex.ofReal_zero]
    rw [div_le_one (by positivity)]
    linarith
  have hev := ((hent.analyticAt 0).frequently_zero_iff_eventually_zero).1 hfreq
  -- the normalised shift `t ↦ a · φₑ(t − 2)` then contradicts `Cvs.WeilForm.TransformNowhereLocallyZero`
  by_contra hφ
  have hN : 0 < ∫ s, evenExt φ s ^ 2 :=
    lt_of_lt_of_le (by have := norm_pos_iff.2 hφ; positivity) (sq_norm_le_integral_evenExt φ)
  set a : ℝ := (√(∫ s, evenExt φ s ^ 2))⁻¹ with ha
  have hψ : MemLp (fun t => a * evenExt φ (t - 2)) 2 (volume : Measure ℝ) :=
    ((memLp_evenExt φ).comp_measurePreserving
      (measurePreserving_sub_right (volume : Measure ℝ) 2)).const_mul a
  have hsupp : ∀ s ∉ Ioc (0 : ℝ) 3, a * evenExt φ (s - 2) = 0 := by
    intro s hs
    rw [evenExt_eq_zero φ, mul_zero]
    rw [mem_Ioc, not_and_or, not_lt, not_le] at hs
    rcases hs with hs | hs
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hnorm : ∫ t, (a * evenExt φ (t - 2)) ^ 2 = 1 := by
    simp only [mul_pow]
    rw [integral_const_mul, integral_sub_right_eq_self (fun t => evenExt φ t ^ 2) 2, ha, inv_pow,
      sq_sqrt hN.le, inv_mul_cancel₀ hN.ne']
  apply Cvs.WeilForm.TransformNowhereLocallyZero.not_eventually_zero (by norm_num : (0 : ℝ) ≤ 3) hψ hsupp hnorm 0
  filter_upwards [hev] with z hz
  rw [Cvs.Finite.DisplacementIdentity.fourierLaplace_cf_const_mul a (fun t => evenExt φ (t - 2)),
    Cvs.Finite.RecentredTransform.fourierLaplace_shift _ 2]
  have he : (∫ s : ℝ, cf (fun t => evenExt φ (t - 2)) (2 + s)
      * Complex.exp (Complex.I * z * (s : ℂ)))
      = fourierLaplace (cf (evenExt φ)) z := by
    rw [fourierLaplace]
    simp only [cf, add_sub_cancel_left]
  rw [he, hz, mul_zero, mul_zero]

/-- `F² φ = 0` forces `φ = 0` when `c ≠ 0`. -/
theorem eq_zero_of_sqCLM_eq_zero {c : ℝ} (hc : c ≠ 0) {φ : window 1}
    (h : sqCLM c φ = 0) : φ = 0 := by
  refine eq_zero_of_cosMap_eq_zero hc ?_
  have h1 := inner_sqCLM_self c φ
  rw [h, inner_zero_left] at h1
  exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h1.symm)

/-! ### An angular eigenfunction from each eigenvector of `F²` in the complement -/

section Angular

variable {ι : Type*} {c ν : ℝ} {w w₁ w₂ : ι → ℝ → ℝ} {χw : ι → ℝ}

/-- **A nonzero eigenvector of `F²` orthogonal to the rungs yields an even angular eigenfunction
orthogonal to them.** -/
theorem exists_angular_of_mem_eigE (hw : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (w i) (w₁ i s) s)
    (hw₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (w₁ i) (w₂ i s) s)
    (hw₂c : ∀ i, ContinuousOn (w₂ i) (uIcc (-1) 1))
    (hwang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * w₂ i s - 2 * s * w₁ i s - c ^ 2 * s ^ 2 * w i s + χw i * w i s = 0)
    (hwc : ∀ i, ContinuousOn (w i) (Icc (-1) 1))
    (hweven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, w i (-s) = w i s)
    (hν : ν ≠ 0) {h : window 1} (hhE : h ∈ eigE c ν hwc) (hh0 : h ≠ 0) :
    ∃ (χ : ℝ) (g g₁ g₂ : ℝ → ℝ), (∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) ∧
      (∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) ∧
      (∀ s ∈ uIcc (-1 : ℝ) 1,
        (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0) ∧
      (∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) ∧ (∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0) ∧
      ∀ i, ∫ s in (-1 : ℝ)..1, g s * w i s = 0 := by
  have := finiteDimensional_eigE (c := c) hwc hν
  have : Nontrivial ↥(eigE c ν hwc) := ⟨⟨⟨h, hhE⟩, 0, fun he => hh0 (congrArg Subtype.val he)⟩⟩
  set A := angE hw hw₁ hw₂c hwang hwc hweven hν with hAdef
  have hsym : LinearMap.IsSymmetric (𝕜 := ℝ) (E := ↥(eigE c ν hwc)) A := fun u v =>
    inner_angCls_comm hν ((mem_eigE hwc).1 u.2).2 ((mem_eigE hwc).1 v.2).2
  have hEV := LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional (𝕜 := ℝ)
    (E := ↥(eigE c ν hwc)) hsym
  obtain ⟨g, hg⟩ := hEV.exists_hasEigenvector
  have hg0 : g ≠ 0 := hg.2
  obtain ⟨χ', hgA⟩ : ∃ χ' : ℝ, A g = χ' • g := ⟨_, Module.End.mem_eigenspace_iff.1 hg.1⟩
  set gv : window 1 := (g : window 1) with hgvdef
  have hgv := (mem_eigE hwc).1 g.2
  -- `A ĝ = χ' ĝ` on `[−1, 1]`
  have hsc : Continuous fun s => χ' * smRep c ν gv s := continuous_const.mul continuous_smRep
  have hcls : cutCls (continuous_angRep (c := c) (ν := ν) (v := gv)) = cutCls hsc := by
    have e1 : ((A g : ↥(eigE c ν hwc)) : window 1)
        = cutCls (continuous_angRep (c := c) (ν := ν) (v := gv)) := rfl
    rw [← e1, hgA, cutCls_smul continuous_smRep χ' hsc]
    show χ' • gv = _
    rw [← eq_cutCls_smRep hν hgv.2]
  have heq := eqOn_of_cutCls_eq continuous_angRep hsc hcls
  have heq' : ∀ s ∈ Icc (-1 : ℝ) 1, angRep c ν gv s = χ' * smRep c ν gv s := by
    intro s hs
    rcases le_total 0 s with h0 | h0
    · exact heq ⟨h0, hs.2⟩
    · have := heq (show -s ∈ Icc (0 : ℝ) 1 from ⟨by linarith, by linarith [hs.1]⟩)
      simp only at this
      rwa [angRep_neg, smRep_neg] at this
  have hI : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * smRep₂ c ν gv s - 2 * s * smRep₁ c ν gv s
      - c ^ 2 * s ^ 2 * smRep c ν gv s + (-χ') * smRep c ν gv s = 0 := by
    intro s hs
    rw [hI] at hs
    have := heq' s hs
    unfold angRep angOp at this
    linarith
  -- `ĝ` is not identically zero on `[−1, 1]`
  have hne : ∃ s ∈ Icc (-1 : ℝ) 1, smRep c ν gv s ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hg0
    apply Subtype.ext
    show gv = 0
    have e0 : gv = cutCls (continuous_smRep (c := c) (ν := ν) (v := gv)) := eq_cutCls_smRep hν hgv.2
    have hz : cutCls (continuous_smRep (c := c) (ν := ν) (v := gv))
        = cutCls (continuous_const (y := (0 : ℝ))) :=
      cutCls_eq _ _ (fun s hs => hcon s ⟨by linarith [hs.1], hs.2⟩)
    rw [e0, hz, cutCls_zero]
  -- orthogonality to the rungs
  have horth : ∀ i, ∫ s in (-1 : ℝ)..1, smRep c ν gv s * w i s = 0 := by
    intro i
    have hvi := (mem_compl hwc).1 hgv.1 i
    rw [inner_cut_classes (rep_wCls hwc i) (rep_eq_smRep hν hgv.2)] at hvi
    have h1 := integral_even_eq_two_mul (v := fun s => clampExt (w i) s * smRep c ν gv s)
      ((continuous_clampExt (hwc i)).mul continuous_smRep)
      (fun s => by rw [clampExt_neg (hweven i), smRep_neg])
    have h2 : ∫ s in (-1 : ℝ)..1, clampExt (w i) s * smRep c ν gv s
        = ∫ s in (-1 : ℝ)..1, smRep c ν gv s * w i s := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le (by norm_num)] at hs
      simp only [clampExt_of_mem hs]; ring
    have h3 : ∫ s in (0 : ℝ)..1, clampExt (w i) s * smRep c ν gv s
        = ∫ s in (0 : ℝ)..1, w i s * smRep c ν gv s := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le zero_le_one] at hs
      simp only [clampExt_of_mem ⟨by linarith [hs.1], hs.2⟩]
    rw [← h2, h1, h3, hvi, mul_zero]
  exact ⟨-χ', smRep c ν gv, smRep₁ c ν gv, smRep₂ c ν gv, fun s _ => hasDerivAt_smRep s,
    fun s _ => hasDerivAt_smRep₁ s, hang, fun s _ => smRep_neg s, hne, horth⟩

end Angular

/-! ### Completeness -/

section Complete

variable {ι : Type*} {c : ℝ} {w w₁ w₂ : ι → ℝ → ℝ} {χw μw : ι → ℝ}

/-- **Completeness from catching every level**: if each even angular eigenfunction pairs
nontrivially with some `w i`, the classes of the `w i` have trivial orthogonal complement. -/
theorem compl_eq_bot (hc : c ≠ 0) (hw : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (w i) (w₁ i s) s)
    (hw₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (w₁ i) (w₂ i s) s)
    (hw₂c : ∀ i, ContinuousOn (w₂ i) (uIcc (-1) 1))
    (hwang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * w₂ i s - 2 * s * w₁ i s - c ^ 2 * s ^ 2 * w i s + χw i * w i s = 0)
    (hwc : ∀ i, ContinuousOn (w i) (Icc (-1) 1))
    (hweven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, w i (-s) = w i s)
    (hwμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, Cvs.L2a.AngularProlateTailPositive.psi c (w i) s = μw i * w i s)
    (hcatch : ∀ (χ : ℝ) (g g₁ g₂ : ℝ → ℝ), (∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) →
      (∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) →
      (∀ s ∈ uIcc (-1 : ℝ) 1,
        (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0) →
      (∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) → (∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0) →
      ∃ i, ∫ s in (-1 : ℝ)..1, g s * w i s ≠ 0) :
    compl hwc = ⊥ := by
  have hinv : ∀ v : window 1, v ∈ compl hwc → sqCLM c v ∈ compl hwc :=
    fun v hv => sqCLM_mem_compl hwc hweven hwμ hv
  have hE : ∀ (μ : ℝ) (u : ↥(compl hwc)), sqPerp c hwc hinv u = μ • u → u = 0 := by
    intro μ u hu
    have hu' : sqCLM c (u : window 1) = μ • (u : window 1) :=
      congrArg Subtype.val hu
    by_cases hμ0 : μ = 0
    · rw [hμ0, zero_smul] at hu'
      exact Subtype.ext (eq_zero_of_sqCLM_eq_zero hc hu')
    by_contra hu0
    have huE : (u : window 1) ∈ eigE c μ hwc := (mem_eigE hwc).2 ⟨u.2, hu'⟩
    have hu0' : (u : window 1) ≠ 0 := fun h => hu0 (Subtype.ext h)
    obtain ⟨χ, g, g₁, g₂, hg, hg₁, hang, heven, hg0, horth⟩ :=
      exists_angular_of_mem_eigE hw hw₁ hw₂c hwang hwc hweven hμ0 huE hu0'
    obtain ⟨i, hi⟩ := hcatch χ g g₁ g₂ hg hg₁ hang heven hg0
    exact hi (horth i)
  have hT : sqPerp c hwc hinv = 0 := by
    by_contra hne
    rcases eigenvector_sqPerp hwc hinv hne with ⟨u, hu0, hu⟩ | ⟨u, hu0, hu⟩
    · exact hu0 (hE _ u hu)
    · exact hu0 (hE _ u hu)
  rw [Submodule.eq_bot_iff]
  intro v hv
  refine eq_zero_of_sqCLM_eq_zero hc ?_
  have h := congrArg (fun S : ↥(compl hwc) →L[ℝ] ↥(compl hwc) =>
    ((S ⟨v, hv⟩ : ↥(compl hwc)) : window 1)) hT
  simpa only [sqPerp_coe, zero_apply, ZeroMemClass.coe_zero] using h

end Complete

/-! ### The even rungs -/

/-- **Every even angular eigenfunction pairs nontrivially with the rung of its level.** -/
theorem exists_integral_mul_rung_ne {c χ : ℝ} {g g₁ g₂ : ℝ → ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0) :
    ∃ k : {k : ℕ // ∃ χ, IsLevelIdx c k χ},
      ∫ s in (-1 : ℝ)..1, g s * rung c k s ≠ 0 := by
  have hmem := Cvs.Prolate.EdgeCentreSign.mem_evenSpec_of_angular hg hg₁ hang heven hg0
  set k := (Cvs.Prolate.EdgeCentreSign.evenSpec (Cvs.Prolate.RegularSolutionEdge.sqC c) ∩ Iio χ).ncard with hk
  have hidx : IsLevelIdx c k χ := ⟨hmem, rfl⟩
  have hex : ∃ χ, IsLevelIdx c k χ := ⟨χ, hidx⟩
  refine ⟨⟨k, hex⟩, ?_⟩
  obtain ⟨hr, hr₁, -, hrang, -, hnorm⟩ := rung_spec hex
  rw [Cvs.Prolate.EvenRungsByIndex.lev_eq hidx] at hrang
  obtain ⟨s₀, hs₀, hgs₀⟩ := hg0
  have hg1 : g 1 ≠ 0 := Cvs.Prolate.AngularEdgeValueNonzero.edge_ne_zero hg hg₁ hang hs₀ hgs₀
  have hr1 : rung c k 1 ≠ 0 := Cvs.Prolate.EvenRungsByIndex.rung_one_ne_zero hex
  have hgR := Cvs.Prolate.RegularSolutionEdge.angular_eq_mul_regSol hg hg₁ hang
  have hrR := Cvs.Prolate.RegularSolutionEdge.angular_eq_mul_regSol hr hr₁ hrang
  have hpt : ∀ s ∈ Ι (-1 : ℝ) 1, g s * rung c k s
      = g 1 / rung c k 1 * rung c k s ^ 2 := by
    intro s hs
    rw [uIoc_of_le (by norm_num)] at hs
    rw [hgR s hs, hrR s hs]
    field_simp
  rw [intervalIntegral.integral_congr_ae (Eventually.of_forall hpt),
    intervalIntegral.integral_const_mul, hnorm, mul_one]
  exact div_ne_zero hg1 hr1

/-- **The even rungs are complete**: for `c ≠ 0` the classes of all the rungs `rung c k` have
trivial orthogonal complement in `L²(0, 1]`. -/
theorem compl_rungs_eq_bot {c : ℝ} (hc : c ≠ 0) :
    compl (w := fun k : {k : ℕ // ∃ χ, IsLevelIdx c k χ} =>
      rung c k) (fun k => Cvs.Prolate.EvenRungsByIndex.continuousOn_rung k.2) = ⊥ :=
  compl_eq_bot hc (fun k => (rung_spec k.2).1)
    (fun k => (rung_spec k.2).2.1)
    (fun k => (rung_spec k.2).2.2.1)
    (fun k => (rung_spec k.2).2.2.2.1) _
    (fun k => (rung_spec k.2).2.2.2.2.1)
    (fun k => Cvs.Prolate.EvenRungsByIndex.psi_rung k.2)
    (fun _ _ _ _ hg hg₁ hang heven hg0 => exists_integral_mul_rung_ne hg hg₁ hang heven hg0)

end Cvs.Prolate.EvenRungsComplete
