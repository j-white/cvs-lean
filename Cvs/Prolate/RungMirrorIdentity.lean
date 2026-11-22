import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Upstream.CosineTransformHalfLine

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The mirror identity: `K ψ = −τ ψ` on `(1, ∞)`

For `g` continuous and even on `[−1, 1]` with `psi c g = μ g` there (Cvs.Prolate.CosineTransformEigenRelation), `ψ = psi c g` and `τ = μ √(c/2π)`, the
cosine transform `calK c` of Cvs.Upstream.CosineTransformHalfLine applied to `1_(1,∞) ψ` equals `−τ ψ` almost everywhere on `(1, ∞)`. Unitarity gives
`τ² ∫₀^∞ ψ² = ∫₀¹ ψ²` and `(c/2π) ∫₀^∞ ψ² = ∫₀¹ g²`, hence `τ² = ∫₀¹ ψ² / ∫₀^∞ ψ²` and `|τ| ≤ 1` when `g ≢ 0`.
-/

noncomputable section

open MeasureTheory Set Real Cvs.Prolate.SlepianCommutingRelation Cvs.L2a.AngularProlateTailPositive Cvs.Upstream.CosineTransformHalfLine

namespace Cvs.Prolate.RungMirrorIdentity

variable {c μ : ℝ} {g : ℝ → ℝ}

/-- `(0, ∞) ∩ [0, 1] = (0, 1]`. -/
theorem Ioi_inter_Icc_eq : Ioi (0 : ℝ) ∩ Icc 0 1 = Ioc 0 1 := by
  ext x
  simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]
  constructor
  · rintro ⟨h0, -, h1⟩; exact ⟨h0, h1⟩
  · rintro ⟨h0, h1⟩; exact ⟨h0, h0.le, h1⟩

/-- The cut `1_[0,1] g` of a function continuous on `[−1, 1]` is in `L² ∩ L¹(0, ∞)`. -/
theorem memLp_cut (hgc : ContinuousOn g (Icc (-1 : ℝ) 1)) :
    MemLp ((Icc (0 : ℝ) 1).indicator g) 2 (volume.restrict (Ioi 0)) ∧
      IntegrableOn ((Icc (0 : ℝ) 1).indicator g) (Ioi 0) := by
  have hc01 : ContinuousOn g (Icc (0 : ℝ) 1) := hgc.mono (Icc_subset_Icc (by norm_num) le_rfl)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc01
  have hL : MemLp g 2 (volume.restrict (Icc (0 : ℝ) 1)) :=
    MemLp.of_bound (hc01.aestronglyMeasurable measurableSet_Icc) C
      ((ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ hC))
  exact ⟨((memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet).2 hL).restrict _,
    (hc01.integrableOn_Icc.integrable_indicator measurableSet_Icc).integrableOn⟩

/-- The complex cut `1_[0,1] g` is in `L²(0, ∞)`. -/
theorem memLp_cut_ofReal (hgc : ContinuousOn g (Icc (-1 : ℝ) 1)) :
    MemLp (fun x => (((Icc (0 : ℝ) 1).indicator g x : ℝ) : ℂ)) 2 (volume.restrict (Ioi 0)) :=
  (memLp_cut hgc).1.ofReal

/-- For even `g`, `psi c g y = 2 ∫₀^∞ 1_[0,1] g (x) cos (c x y) dx`. -/
theorem psi_eq_integral (hgc : ContinuousOn g (Icc (-1 : ℝ) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (y : ℝ) :
    psi c g y = 2 * ∫ x in Ioi 0, (Icc (0 : ℝ) 1).indicator g x * Real.cos (c * x * y) := by
  set f : ℝ → ℝ := fun s => g s * Real.cos (c * y * s) with hf
  have hfc : ContinuousOn f (Icc (-1 : ℝ) 1) := hgc.mul (by fun_prop)
  have hi1 : IntervalIntegrable f volume (-1) 0 :=
    (hfc.mono (by rw [uIcc_of_le (by norm_num)]; exact Icc_subset_Icc le_rfl (by norm_num))).intervalIntegrable
  have hi2 : IntervalIntegrable f volume 0 1 :=
    (hfc.mono (by rw [uIcc_of_le (by norm_num)]; exact Icc_subset_Icc (by norm_num) le_rfl)).intervalIntegrable
  have hpsi : psi c g y = ∫ s in (-1 : ℝ)..1, f s := rfl
  have hneg : ∫ s in (-1 : ℝ)..0, f s = ∫ s in (0 : ℝ)..1, f s := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1) f
    rw [neg_zero] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le (by norm_num)] at hs
    simp only [hf, heven s ⟨by linarith [hs.1], hs.2⟩, mul_neg, Real.cos_neg]
  have hset : ∫ x in Ioi 0, (Icc (0 : ℝ) 1).indicator g x * Real.cos (c * x * y)
      = ∫ s in (0 : ℝ)..1, f s := by
    have e : ∀ x, (Icc (0 : ℝ) 1).indicator g x * Real.cos (c * x * y)
        = (Icc (0 : ℝ) 1).indicator f x := by
      intro x
      by_cases hx : x ∈ Icc (0 : ℝ) 1
      · rw [indicator_of_mem hx, indicator_of_mem hx, hf, mul_right_comm c x y]
      · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_mul]
    simp only [e]
    rw [setIntegral_indicator measurableSet_Icc, Ioi_inter_Icc_eq,
      intervalIntegral.integral_of_le zero_le_one]
  rw [hpsi, ← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, hneg, hset]
  ring

/-- **The cut is the transform of `ψ`, up to scale**: `calK c (1_[0,1] g) = √(c/2π) ψ` almost everywhere. -/
theorem calK_cut (hc : 0 < c) (hgc : ContinuousOn g (Icc (-1 : ℝ) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) :
    calK c (fun x => (((Icc (0 : ℝ) 1).indicator g x : ℝ) : ℂ)) =ᵐ[volume]
      fun y => ((√(c / (2 * π)) * psi c g y : ℝ) : ℂ) := by
  obtain ⟨hL, hI⟩ := memLp_cut hgc
  filter_upwards [calK_ofReal_eq_integral hc hL hI] with y hy
  rw [hy, psi_eq_integral hgc heven y]
  have hs : √(2 * c / π) = √(c / (2 * π)) * 2 := by
    rw [show 2 * c / π = 2 ^ 2 * (c / (2 * π)) by field_simp,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num), mul_comm]
  rw [hs, mul_assoc]

/-- `ψ = psi c g` is in `L²(0, ∞)`. -/
theorem memLp_psi (hc : 0 < c) (hgc : ContinuousOn g (Icc (-1 : ℝ) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) :
    MemLp (fun x => (psi c g x : ℂ)) 2 (volume.restrict (Ioi 0)) := by
  have ha : 0 < √(c / (2 * π)) := Real.sqrt_pos.2 (by positivity)
  have hK := (memLp_calK hc (memLp_cut_ofReal hgc)).const_smul (((√(c / (2 * π)))⁻¹ : ℝ) : ℂ)
  refine hK.ae_eq ?_
  filter_upwards [ae_restrict_of_ae (calK_cut hc hgc heven)] with y hy
  rw [Pi.smul_apply, hy, smul_eq_mul, ← Complex.ofReal_mul, ← mul_assoc, inv_mul_cancel₀ ha.ne',
    one_mul]

/-- **The low part**: `calK c (1_(−∞,1] ψ) = τ ψ` almost everywhere, with `τ = μ √(c/2π)`. -/
theorem calK_low (hc : 0 < c) (hgc : ContinuousOn g (Icc (-1 : ℝ) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) :
    calK c ((Iic 1).indicator fun x => (psi c g x : ℂ)) =ᵐ[volume]
      fun y => ((μ * √(c / (2 * π)) * psi c g y : ℝ) : ℂ) := by
  have hcongr : ((Iic 1).indicator fun x => (psi c g x : ℂ)) =ᵐ[volume.restrict (Ioi 0)]
      (μ : ℂ) • fun x => (((Icc (0 : ℝ) 1).indicator g x : ℝ) : ℂ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hx
    by_cases h1 : x ≤ 1
    · have hm : x ∈ Icc (0 : ℝ) 1 := ⟨hx0.le, h1⟩
      have hm' : x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, h1⟩
      rw [indicator_of_mem (show x ∈ Iic (1 : ℝ) from h1), Pi.smul_apply, indicator_of_mem hm,
        hμ x hm', smul_eq_mul, Complex.ofReal_mul]
    · have hm : x ∉ Icc (0 : ℝ) 1 := fun h => h1 h.2
      rw [indicator_of_notMem (show x ∉ Iic (1 : ℝ) from h1), Pi.smul_apply, indicator_of_notMem hm,
        Complex.ofReal_zero, smul_zero]
  rw [calK_congr hcongr]
  filter_upwards [calK_smul hc (μ : ℂ) (memLp_ev (memLp_cut_ofReal hgc)), calK_cut hc hgc heven] with y h1 h2
  rw [h1, Pi.smul_apply, h2, smul_eq_mul]
  push_cast
  ring

/-- **The transform of `ψ` vanishes beyond `1`**: `calK c ψ = √(2π/c) 1_[0,1] g`, which is `0` on `(1, ∞)`. -/
theorem calK_psi_eq_zero (hc : 0 < c) (hgc : ContinuousOn g (Icc (-1 : ℝ) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) :
    calK c (fun x => (psi c g x : ℂ)) =ᵐ[volume.restrict (Ioi 1)] 0 := by
  have ha : 0 < √(c / (2 * π)) := Real.sqrt_pos.2 (by positivity)
  set r : ℂ := (((√(c / (2 * π)))⁻¹ : ℝ) : ℂ)
  have hψ : (fun x => (psi c g x : ℂ)) =ᵐ[volume.restrict (Ioi 0)]
      r • calK c (fun x => (((Icc (0 : ℝ) 1).indicator g x : ℝ) : ℂ)) := by
    filter_upwards [ae_restrict_of_ae (calK_cut hc hgc heven)] with y hy
    rw [Pi.smul_apply, hy, smul_eq_mul, ← Complex.ofReal_mul, ← mul_assoc, inv_mul_cancel₀ ha.ne',
      one_mul]
  rw [calK_congr hψ]
  have h1 := calK_smul hc r (memLp_ev_calK hc (memLp_ev (memLp_cut_ofReal hgc)))
  have h2 := calK_calK hc (memLp_cut_ofReal hgc)
  filter_upwards [ae_restrict_of_ae h1,
    ae_restrict_of_ae_restrict_of_subset (Ioi_subset_Ioi zero_le_one) h2,
    ae_restrict_mem measurableSet_Ioi] with y hy1 hy2 hy3
  have hy : y ∉ Icc (0 : ℝ) 1 := fun h => (not_le.2 (show (1 : ℝ) < y from hy3)) h.2
  rw [hy1, Pi.smul_apply, hy2, indicator_of_notMem hy, Complex.ofReal_zero, smul_zero, Pi.zero_apply]

/-- **The mirror identity**: the compression `K` of `calK c` to `(1, ∞)` satisfies `K ψ = −τ ψ` almost everywhere
on `(1, ∞)`, with `τ = μ √(c/2π)`. -/
theorem mirror_identity (hc : 0 < c) (hgc : ContinuousOn g (Icc (-1 : ℝ) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) :
    ∀ᵐ y ∂(volume.restrict (Ioi 1)),
      calK c ((Ioi 1).indicator fun x => (psi c g x : ℂ)) y
        = ((-(μ * √(c / (2 * π)) * psi c g y) : ℝ) : ℂ) := by
  set ψc : ℝ → ℂ := fun x => (psi c g x : ℂ) with hψc
  have hm := memLp_psi hc hgc heven
  have hsplit : (Ioi 1).indicator ψc + (Iic 1).indicator ψc = ψc := by
    have := indicator_self_add_compl (Ioi (1 : ℝ)) ψc
    rwa [compl_Ioi] at this
  have hadd := calK_add hc (memLp_ev (hm.indicator (measurableSet_Ioi (a := (1 : ℝ))).nullMeasurableSet))
    (memLp_ev (hm.indicator (measurableSet_Iic (a := (1 : ℝ))).nullMeasurableSet))
  rw [hsplit] at hadd
  filter_upwards [ae_restrict_of_ae hadd, calK_psi_eq_zero hc hgc heven,
    ae_restrict_of_ae (calK_low hc hgc heven hμ)] with y h1 h2 h3
  rw [Pi.add_apply] at h1
  rw [Pi.zero_apply] at h2
  push_cast at h3 ⊢
  linear_combination h2 - h1 - h3

/-- `(c/2π) ∫₀^∞ ψ² = ∫₀¹ g²`, by unitarity of `calK c` on the cut. -/
theorem norm_psi_sq (hc : 0 < c) (hgc : ContinuousOn g (Icc (-1 : ℝ) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) :
    c / (2 * π) * ∫ x in Ioi 0, psi c g x ^ 2 = ∫ x in (0 : ℝ)..1, g x ^ 2 := by
  have h := norm_calK hc (memLp_cut_ofReal hgc)
  have hL' : ∫ y in Ioi 0, ‖calK c (fun x => (((Icc (0 : ℝ) 1).indicator g x : ℝ) : ℂ)) y‖ ^ 2
      = c / (2 * π) * ∫ x in Ioi 0, psi c g x ^ 2 := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (calK_cut hc hgc heven)] with y hy
    rw [hy, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow,
      Real.sq_sqrt (by positivity)]
  have hR : ∫ y in Ioi 0, ‖(((Icc (0 : ℝ) 1).indicator g y : ℝ) : ℂ)‖ ^ 2 = ∫ x in (0 : ℝ)..1, g x ^ 2 := by
    have e : ∀ y, ‖(((Icc (0 : ℝ) 1).indicator g y : ℝ) : ℂ)‖ ^ 2
        = (Icc (0 : ℝ) 1).indicator (fun x => g x ^ 2) y := by
      intro y
      by_cases hy : y ∈ Icc (0 : ℝ) 1
      · rw [indicator_of_mem hy, indicator_of_mem hy, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      · rw [indicator_of_notMem hy, indicator_of_notMem hy]; simp
    simp only [e]
    rw [setIntegral_indicator measurableSet_Icc, Ioi_inter_Icc_eq,
      intervalIntegral.integral_of_le zero_le_one]
  rw [← hL', h, hR]

/-- **Unitarity on the low part**: `τ² ∫₀^∞ ψ² = ∫₀¹ ψ²`, with `τ = μ √(c/2π)`. -/
theorem tau_sq_mul (hc : 0 < c) (hgc : ContinuousOn g (Icc (-1 : ℝ) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) :
    (μ * √(c / (2 * π))) ^ 2 * ∫ x in Ioi 0, psi c g x ^ 2 = ∫ x in (0 : ℝ)..1, psi c g x ^ 2 := by
  have hm := memLp_psi hc hgc heven
  have h := norm_calK hc (hm.indicator (measurableSet_Iic (a := (1 : ℝ))).nullMeasurableSet)
  have hL' : ∫ y in Ioi 0, ‖calK c ((Iic 1).indicator fun x => (psi c g x : ℂ)) y‖ ^ 2
      = (μ * √(c / (2 * π))) ^ 2 * ∫ x in Ioi 0, psi c g x ^ 2 := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (calK_low hc hgc heven hμ)] with y hy
    rw [hy, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
  have hR : ∫ y in Ioi 0, ‖(Iic 1).indicator (fun x => (psi c g x : ℂ)) y‖ ^ 2
      = ∫ x in (0 : ℝ)..1, psi c g x ^ 2 := by
    have e : ∀ y, ‖(Iic 1).indicator (fun x => (psi c g x : ℂ)) y‖ ^ 2
        = (Iic 1).indicator (fun x => psi c g x ^ 2) y := by
      intro y
      by_cases hy : y ∈ Iic (1 : ℝ)
      · rw [indicator_of_mem hy, indicator_of_mem hy, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      · rw [indicator_of_notMem hy, indicator_of_notMem hy]; simp
    simp only [e]
    rw [setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic,
      intervalIntegral.integral_of_le zero_le_one]
  rw [← hL', h, hR]

/-- A nonzero value of `g` makes `∫₀^∞ ψ²` positive. -/
theorem integral_psi_sq_pos (hc : 0 < c) (hgc : ContinuousOn g (Icc (-1 : ℝ) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0) :
    0 < ∫ x in Ioi 0, psi c g x ^ 2 := by
  obtain ⟨s, hs, hgs⟩ := hg0
  have hc01 : ContinuousOn g (Icc (0 : ℝ) 1) := hgc.mono (Icc_subset_Icc (by norm_num) le_rfl)
  obtain ⟨t, ht, hgt⟩ : ∃ t ∈ Icc (0 : ℝ) 1, g t ≠ 0 := by
    rcases le_total 0 s with h0 | h0
    · exact ⟨s, ⟨h0, hs.2⟩, hgs⟩
    · exact ⟨-s, ⟨by linarith, by linarith [hs.1]⟩, by rwa [heven s hs]⟩
  have hJ : 0 < ∫ x in (0 : ℝ)..1, g x ^ 2 := by
    have := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (f := fun _ => (0 : ℝ)) (g := fun x => g x ^ 2) zero_lt_one continuousOn_const
      (hc01.pow 2) (fun x _ => sq_nonneg (g x))
      ⟨t, ht, lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hgt))⟩
    simpa using this
  have h := norm_psi_sq hc hgc heven
  have hk : 0 < c / (2 * π) := by positivity
  by_contra hle
  push Not at hle
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hk.le hle]

/-- **The mirror eigenvalue is at most `1` in size**: `|μ √(c/2π)| ≤ 1` when `g ≢ 0` on `[−1, 1]`. -/
theorem abs_tau_le_one (hc : 0 < c) (hgc : ContinuousOn g (Icc (-1 : ℝ) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s)
    (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0) :
    |μ * √(c / (2 * π))| ≤ 1 := by
  have hI := integral_psi_sq_pos hc hgc heven hg0
  have hm := memLp_psi hc hgc heven
  have hInt : IntegrableOn (fun x => psi c g x ^ 2) (Ioi 0) := by
    have := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).1 hm
    refine this.congr (ae_of_all _ fun x => ?_)
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hle : ∫ x in (0 : ℝ)..1, psi c g x ^ 2 ≤ ∫ x in Ioi 0, psi c g x ^ 2 := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    exact setIntegral_mono_set hInt (ae_of_all _ fun _ => sq_nonneg _)
      (Filter.Eventually.of_forall fun _ hx => Ioc_subset_Ioi_self hx)
  have h := tau_sq_mul hc hgc heven hμ
  rw [← sq_le_one_iff_abs_le_one]
  by_contra hgt
  push Not at hgt
  nlinarith

end Cvs.Prolate.RungMirrorIdentity
