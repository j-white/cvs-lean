import Mathlib
import Cvs.Zeta.Convexity.AuxiliaryGrowth
import Cvs.Zeta.Convexity.CriticalLineThirdExponent
import Cvs.Zeta.Convexity.ZetaImaginaryAxis
import Cvs.Zeta.ConvexityAuxDiffContOnCl
import Cvs.Zeta.ConvexityAuxDifferentiable
import Cvs.Zeta.ConvexityEdgeConstant
import Cvs.Zeta.ConvexityEvenBranch
import Cvs.Zeta.ConvexityNearEdgeParams
import Cvs.Zeta.ConvexityPhragmenLindelof
import Cvs.Zeta.ConvexityZetaEdges

/-!
# The classical convexity bound: `‖ζ(½+it)‖ ≤ C_ε·(1+|t|)^{1/4+ε}`

‖ζ(½+it)‖ ≤ C_ε·(1+|t|)^{1/4+ε} for every `ε > 0`, `|t| ≥ 1` .
-/

open Complex

namespace Cvs.Zeta.Convexity.CriticalLineQuarterExponent
open Cvs.ZetaGrowth

variable {ε : ℝ}

/-- **The far edge at `σ = 0`, in the `Ca·(1+|t|)^a` shape**, with `a = 1/2 + ε`. -/
theorem zeta₀_edge_zero (hε : 0 < ε) {t : ℝ} (ht : 1 ≤ |t|) :
    ‖riemannZeta₀ ((t : ℂ) * I)‖
      ≤ ((7 + 1 / ε) / Real.sqrt (2 * Real.pi) + 1) * (1 + |t|) ^ (1/2 + ε) := by
  have ht0 : (0 : ℝ) < |t| := lt_of_lt_of_le zero_lt_one ht
  have hb1 : (1 : ℝ) ≤ 1 + |t| := by linarith
  have hb0 : (0 : ℝ) < 1 + |t| := by linarith
  have hpi : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  -- the two factors
  have hsq : Real.sqrt (|t| / (2 * Real.pi)) ≤ (1 + |t|) ^ (1/2 : ℝ) / Real.sqrt (2 * Real.pi) := by
    rw [Real.sqrt_div' _ (by positivity), ← Real.sqrt_eq_rpow]
    exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt (by linarith)) hpi.le
  have hlog : (7 : ℝ) + Real.log |t| ≤ (7 + 1 / ε) * (1 + |t|) ^ ε := by
    have hpow1 : (1 : ℝ) ≤ (1 + |t|) ^ ε := Real.one_le_rpow hb1 (le_of_lt hε)
    have hl : Real.log |t| ≤ (1 + |t|) ^ ε / ε := by
      refine le_trans (Real.log_le_log ht0 (show |t| ≤ 1 + |t| by linarith)) ?_
      exact Cvs.Zeta.Convexity.CriticalLineThirdExponent.log_le_rpow_div hε hb1
    have h2 : Real.log |t| ≤ (1 / ε) * (1 + |t|) ^ ε := by
      rw [one_div, inv_mul_eq_div]; exact hl
    nlinarith
  have hz := Cvs.ZetaGrowth.norm_zeta_zero_line ht
  have hlognn : (0 : ℝ) ≤ 7 + Real.log |t| := by
    have : (0 : ℝ) ≤ Real.log |t| := Real.log_nonneg ht
    linarith
  have hzc : ‖riemannZeta ((t : ℂ) * I)‖
      ≤ ((7 + 1 / ε) / Real.sqrt (2 * Real.pi)) * (1 + |t|) ^ (1/2 + ε) := by
    refine le_trans hz ?_
    have hstep : Real.sqrt (|t| / (2 * Real.pi)) * (7 + Real.log |t|)
        ≤ ((1 + |t|) ^ (1/2 : ℝ) / Real.sqrt (2 * Real.pi)) * ((7 + 1 / ε) * (1 + |t|) ^ ε) :=
      mul_le_mul hsq hlog hlognn (by positivity)
    refine le_trans hstep (le_of_eq ?_)
    rw [Real.rpow_add hb0]
    ring
  have him : ((t : ℂ) * I).im = t := by simp
  have hz₀ := Cvs.ArchScore.norm_zeta₀_le (s := (t : ℂ) * I) (by rw [him]; exact ht) hzc
  have hone : (1 : ℝ) ≤ (1 + |t|) ^ (1/2 + ε) := Real.one_le_rpow hb1 (by positivity)
  nlinarith

/-! ### The ladder at `α = 0`, `β = 1` -/

theorem params_nonneg (hε : 0 < ε) {σ : ℝ} (h2 : σ ≤ 1) :
    0 ≤ (1/2 + ε) + (-1/2 : ℝ) * σ := by linarith

noncomputable def A (ε : ℝ) : ℂ → ℂ := Cvs.Zeta.ConvexityAuxDifferentiable.aux riemannZeta₀ 1 7 (1/2 + ε) (-1/2)

theorem growth_A (hε : 0 < ε) :
    ∃ e < Real.pi / (1 - (0 : ℝ)), ∃ B,
      (A ε) =O[Filter.comap (fun z : ℂ => |z.im|) Filter.atTop
        ⊓ Filter.principal (Cvs.Zeta.ConvexityAuxDifferentiable.strip 0 1)]
        fun z : ℂ => Real.exp (B * Real.exp (e * |z.im|)) := by
  have hEpos : (0 : ℝ) < Real.exp (|(-1/2 : ℝ)| * (Real.pi * (1 + 1) / 2)) := Real.exp_pos _
  refine Cvs.ZetaGrowth.isBigO_expexp_of_exp (M := (Cvs.ZetaGrowth.zetaStripC + 1)
      * Real.exp (|(-1/2 : ℝ)| * (Real.pi * (1 + 1) / 2)))
    (A := Real.pi / 2) (by norm_num) ?_ (by positivity) ?_
  · have := Cvs.ZetaGrowth.zetaStripC_nonneg
    positivity
  · intro z hz him
    obtain ⟨hz1, hz2⟩ := hz
    have hc : (0 : ℝ) ≤ z.re + 1 := by linarith
    have hβ : z.re ≤ 1 := le_of_lt hz2
    have hp : (0 : ℝ) ≤ (1/2 + ε) + (-1/2 : ℝ) * z.re := params_nonneg hε hβ
    have haux := Cvs.ZetaGrowth.norm_aux_le_of_ge_one (f := riemannZeta₀) (c := 1) (K := 7)
      (a' := 1/2 + ε) (b' := -1/2) (β := 1) (by norm_num) hc hβ him hp
    have hz₀ := Cvs.ZetaGrowth.norm_zeta₀_exp (by linarith) (by linarith) him
    calc ‖A ε z‖ ≤ ‖riemannZeta₀ z‖ * Real.exp (|(-1/2 : ℝ)| * (Real.pi * (1 + 1) / 2)) := haux
      _ ≤ ((Cvs.ZetaGrowth.zetaStripC + 1) * Real.exp (Real.pi / 2 * |z.im|))
            * Real.exp (|(-1/2 : ℝ)| * (Real.pi * (1 + 1) / 2)) :=
          mul_le_mul_of_nonneg_right hz₀ (le_of_lt hEpos)
      _ = ((Cvs.ZetaGrowth.zetaStripC + 1) * Real.exp (|(-1/2 : ℝ)| * (Real.pi * (1 + 1) / 2)))
            * Real.exp (Real.pi / 2 * |z.im|) := by ring

theorem exists_near_axis_bound (ε : ℝ) {α : ℝ} (hα : 0 ≤ α + 1) (hβ : α ≤ 1) :
    ∃ C : ℝ, ∀ z : ℂ, z.re = α → |z.im| ≤ 1 → ‖A ε z‖ ≤ C := by
  set S : Set ℂ := (fun t : ℝ => (α : ℂ) + (t : ℂ) * I) '' Set.Icc (-1) 1 with hS
  have hSc : IsCompact S := isCompact_Icc.image (by fun_prop)
  have hcont : ContinuousOn (A ε) S := by
    intro z hz
    obtain ⟨t, _, rfl⟩ := hz
    have hre : ((α : ℂ) + (t : ℂ) * I).re = α := by simp
    have hok : Cvs.ArchScore.closedOK 1 1 ((α : ℂ) + (t : ℂ) * I) :=
      ⟨by rw [hre]; linarith, by rw [hre]; exact hβ⟩
    exact ((Cvs.ArchScore.differentiableAt_aux' (by norm_num) hok
      (differentiable_riemannZeta₀ _)).continuousAt).continuousWithinAt
  obtain ⟨C, hC⟩ := hSc.exists_bound_of_continuousOn hcont
  refine ⟨C, fun z hzre hzim => hC z ⟨z.im, abs_le.mp hzim, (Cvs.ArchScore.edge_param hzre).symm⟩⟩

theorem edge_bound_left (hε : 0 < ε) : ∃ C : ℝ, ∀ z : ℂ, z.re = 0 → ‖A ε z‖ ≤ C := by
  obtain ⟨C₀, hC₀⟩ := exists_near_axis_bound ε (α := 0) (by norm_num) (by norm_num)
  set Ca : ℝ := (7 + 1 / ε) / Real.sqrt (2 * Real.pi) + 1 with hCa
  have hCa0 : 0 ≤ Ca := by
    have hpi : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    rw [hCa]; positivity
  set C₁ : ℝ := Ca * 2 ^ (1/2 + ε) * Real.exp (|(-1/2 : ℝ)| * (Real.pi * (1 + 1) / 2)) with hC₁
  refine ⟨max C₀ C₁, fun z hzre => ?_⟩
  rcases le_or_gt |z.im| 1 with him | him
  · exact le_trans (hC₀ z hzre him) (le_max_left _ _)
  · have him1 : (1 : ℝ) ≤ |z.im| := le_of_lt him
    have hzeq : z = ((0 : ℝ) : ℂ) + (z.im : ℂ) * I := Cvs.ArchScore.edge_param hzre
    have hedge : ‖riemannZeta₀ z‖ ≤ Ca * (1 + |z.im|) ^ (1/2 + ε) := by
      have h := zeta₀_edge_zero hε (t := z.im) him1
      have hz' : ((z.im : ℝ) : ℂ) * I = z := by
        conv_rhs => rw [hzeq]
        push_cast
        ring
      rw [hz'] at h
      exact h
    have hb := Cvs.ArchScore.edge_const_even (f := riemannZeta₀) (c := 1) (K := 7) (a := 1/2 + ε)
      (b' := -1/2) (Ca := Ca) (β := 1) (by norm_num) (by positivity) hCa0
      (by rw [hzre]; norm_num) (by rw [hzre]; norm_num) him1 hedge
    have hval : ‖A ε z‖ = ‖riemannZeta₀ z‖ * Real.exp (-(1/2 + ε) * (Cvs.ArchScore.evenLog 1 7 z).re
        + (-1/2 : ℝ) * z.im * (Cvs.ArchScore.evenLog 1 7 z).im) := by
      rw [A, Cvs.ArchScore.norm_aux_even]
      congr 2
      rw [hzre]; ring
    rw [hval]
    exact le_trans hb (le_max_right _ _)

theorem edge_bound_right (hε : 0 < ε) : ∃ C : ℝ, ∀ z : ℂ, z.re = 1 → ‖A ε z‖ ≤ C := by
  obtain ⟨C₀, hC₀⟩ := exists_near_axis_bound ε (α := 1) (by norm_num) (by norm_num)
  set Cb : ℝ := 6 + 1 / ε with hCb
  have hCb0 : 0 ≤ Cb := by rw [hCb]; positivity
  set C₁ : ℝ := Cb * 2 ^ ε * Real.exp (|(-1/2 : ℝ)| * (Real.pi * (1 + 1) / 2)) with hC₁
  refine ⟨max C₀ C₁, fun z hzre => ?_⟩
  rcases le_or_gt |z.im| 1 with him | him
  · exact le_trans (hC₀ z hzre him) (le_max_left _ _)
  · have him1 : (1 : ℝ) ≤ |z.im| := le_of_lt him
    have hzeq : z = ((1 : ℝ) : ℂ) + (z.im : ℂ) * I := Cvs.ArchScore.edge_param hzre
    have hedge : ‖riemannZeta₀ z‖ ≤ Cb * (1 + |z.im|) ^ ε := by
      have h := Cvs.Zeta.Convexity.CriticalLineThirdExponent.zeta₀_edge_one hε (t := z.im) him1
      have hz' : (1 : ℂ) + (z.im : ℂ) * I = z := by rw [hzeq]; norm_num
      rw [hz'] at h
      exact h
    have hb := Cvs.ArchScore.edge_const_even (f := riemannZeta₀) (c := 1) (K := 7) (a := ε)
      (b' := -1/2) (Ca := Cb) (β := 1) (by norm_num) (le_of_lt hε) hCb0
      (by rw [hzre]; norm_num) (by rw [hzre]) him1 hedge
    have hval : ‖A ε z‖ = ‖riemannZeta₀ z‖ * Real.exp (-ε * (Cvs.ArchScore.evenLog 1 7 z).re
        + (-1/2 : ℝ) * z.im * (Cvs.ArchScore.evenLog 1 7 z).im) := by
      rw [A, Cvs.ArchScore.norm_aux_even]
      congr 2
      rw [hzre]; ring
    rw [hval]
    exact le_trans hb (le_max_right _ _)

theorem aux_bounded (hε : 0 < ε) :
    ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → ‖A ε z‖ ≤ C := by
  obtain ⟨Cl, hCl⟩ := edge_bound_left hε
  obtain ⟨Cr, hCr⟩ := edge_bound_right hε
  obtain ⟨e, he, B, hO⟩ := growth_A hε
  refine ⟨max Cl Cr, fun z h1 h2 => ?_⟩
  exact Cvs.ArchScore.norm_aux_le_of_edges (f := riemannZeta₀) (c := 1) (K := 7)
    (α := 0) (β := 1) (a' := 1/2 + ε) (b' := -1/2)
    (Cvs.ArchScore.diffContOnCl_aux (by norm_num) (by norm_num)
      (fun s _ => differentiable_riemannZeta₀ s))
    ⟨e, he, B, hO⟩
    (fun w hw => le_trans (hCl w hw) (le_max_left _ _))
    (fun w hw => le_trans (hCr w hw) (le_max_right _ _)) h1 h2

end Cvs.Zeta.Convexity.CriticalLineQuarterExponent
