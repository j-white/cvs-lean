import Mathlib
import Cvs.Zeta.Convexity.AuxiliaryGrowth
import Cvs.Zeta.Convexity.EdgeConstants
import Cvs.Zeta.ConvexityAuxDiffContOnCl
import Cvs.Zeta.ConvexityAuxDifferentiable
import Cvs.Zeta.ConvexityEdgeConstant
import Cvs.Zeta.ConvexityEvenBranch
import Cvs.Zeta.ConvexityNearEdgeParams
import Cvs.Zeta.ConvexityPhragmenLindelof

/-!
# The convexity ladder closes: `‖ζ(½+it)‖ ≤ C·(1+|t|)^{1/2}`, unconditionally
-/

open Complex

namespace Cvs.Zeta.Convexity.CriticalLineHalfExponent
open Cvs.ZetaGrowth

/-- Abbreviation for the auxiliary at `ζ₀` with `ConvexityNearEdgeParams`'s parameters. -/
noncomputable def A : ℂ → ℂ := Cvs.Zeta.ConvexityAuxDifferentiable.aux riemannZeta₀ 1 7 (3/4) (-1/2)

/-- **The near-axis part of an edge is bounded, by compactness.**  `aux ζ₀` is differentiable
on the closed strip (`ConvexityAuxDiffContOnCl`), the segment `{σ} × [-1,1]` is compact, and a continuous function
on a compact set is bounded.  This is why the final constant is existential. -/
theorem exists_near_axis_bound {α : ℝ} (hα : 0 ≤ α + 1) (hβ : α ≤ 3/2) :
    ∃ C : ℝ, ∀ z : ℂ, z.re = α → |z.im| ≤ 1 → ‖A z‖ ≤ C := by
  set S : Set ℂ := (fun t : ℝ => (α : ℂ) + (t : ℂ) * I) '' Set.Icc (-1) 1 with hS
  have hSc : IsCompact S := isCompact_Icc.image (by fun_prop)
  have hcont : ContinuousOn A S := by
    intro z hz
    obtain ⟨t, _, rfl⟩ := hz
    have hre : ((α : ℂ) + (t : ℂ) * I).re = α := by simp
    have hok : Cvs.ArchScore.closedOK 1 (3/2) ((α : ℂ) + (t : ℂ) * I) :=
      ⟨by rw [hre]; linarith, by rw [hre]; exact hβ⟩
    exact ((Cvs.ArchScore.differentiableAt_aux' (by norm_num) hok
      (differentiable_riemannZeta₀ _)).continuousAt).continuousWithinAt
  obtain ⟨C, hC⟩ := hSc.exists_bound_of_continuousOn hcont
  refine ⟨C, fun z hzre hzim => ?_⟩
  refine hC z ⟨z.im, ?_, ?_⟩
  · exact abs_le.mp hzim
  · exact (Cvs.ArchScore.edge_param hzre).symm

/-- **The far edge `σ = -1/2`.**  `EdgeConstants` gives `‖ζ₀‖ ≤ π⁻¹((1+|t|)/2)·zetaEdge + 1`, which is
`Ca·(1+|t|)¹` with `Ca = π⁻¹·zetaEdge/2 + 1`; the exponent `1` is `ConvexityNearEdgeParams.params_left`. -/
theorem edge_bound_left : ∃ C : ℝ, ∀ z : ℂ, z.re = -1/2 → ‖A z‖ ≤ C := by
  obtain ⟨C₀, hC₀⟩ := exists_near_axis_bound (α := -1/2) (by norm_num) (by norm_num)
  set Ca : ℝ := Real.pi⁻¹ * Cvs.ZetaGrowth.zetaEdge / 2 + 1 with hCa
  have hCa0 : 0 ≤ Ca := by
    have := Cvs.ZetaGrowth.zetaEdge_nonneg
    have hpi : (0:ℝ) < Real.pi⁻¹ := by positivity
    rw [hCa]; positivity
  set C₁ : ℝ := Ca * 2 ^ (1 : ℝ) * Real.exp (|(-1/2 : ℝ)| * (Real.pi * (3/2 + 1) / 2)) with hC₁
  refine ⟨max C₀ C₁, fun z hzre => ?_⟩
  rcases le_or_gt |z.im| 1 with him | him
  · exact le_trans (hC₀ z hzre him) (le_max_left _ _)
  · have him1 : (1 : ℝ) ≤ |z.im| := le_of_lt him
    have hzeq : z = ((-1/2 : ℝ) : ℂ) + (z.im : ℂ) * I := Cvs.ArchScore.edge_param hzre
    have hedge : ‖riemannZeta₀ z‖ ≤ Ca * (1 + |z.im|) ^ (1 : ℝ) := by
      have h := Cvs.ZetaGrowth.zeta₀_edge_left (t := z.im) him1
      have hz' : ((-1 : ℂ)) / 2 + (z.im : ℂ) * I = z := by
        rw [hzeq]; norm_num
      rw [hz'] at h
      have hone : (1 : ℝ) ≤ 1 + |z.im| := by linarith [abs_nonneg z.im]
      rw [Real.rpow_one]
      have hzE := Cvs.ZetaGrowth.zetaEdge_nonneg
      have hpi : (0:ℝ) < Real.pi := Real.pi_pos
      nlinarith [h, hone, hzE]
    have hb := Cvs.ArchScore.edge_const_even (f := riemannZeta₀) (c := 1) (K := 7) (a := 1)
      (b' := -1/2) (Ca := Ca) (β := 3/2) (by norm_num) (by norm_num) hCa0
      (by rw [hzre]; norm_num) (by rw [hzre]; norm_num) him1 hedge
    have hval : ‖A z‖ = ‖riemannZeta₀ z‖ * Real.exp (-1 * (Cvs.ArchScore.evenLog 1 7 z).re
        + (-1/2) * z.im * (Cvs.ArchScore.evenLog 1 7 z).im) := by
      rw [A, Cvs.ArchScore.norm_aux_even]
      congr 2
      rw [hzre]; norm_num
    rw [hval]
    exact le_trans hb (le_max_right _ _)

/-- **The near edge `σ = 3/2`.**  `EdgeConstants` gives `‖ζ₀‖ ≤ zetaEdge + 1`, an exponent of `0` —
`ConvexityNearEdgeParams.params_right`. -/
theorem edge_bound_right : ∃ C : ℝ, ∀ z : ℂ, z.re = 3/2 → ‖A z‖ ≤ C := by
  obtain ⟨C₀, hC₀⟩ := exists_near_axis_bound (α := 3/2) (by norm_num) (by norm_num)
  set Cb : ℝ := Cvs.ZetaGrowth.zetaEdge + 1 with hCb
  have hCb0 : 0 ≤ Cb := by
    have := Cvs.ZetaGrowth.zetaEdge_nonneg; rw [hCb]; linarith
  set C₁ : ℝ := Cb * 2 ^ (0 : ℝ) * Real.exp (|(-1/2 : ℝ)| * (Real.pi * (3/2 + 1) / 2)) with hC₁
  refine ⟨max C₀ C₁, fun z hzre => ?_⟩
  rcases le_or_gt |z.im| 1 with him | him
  · exact le_trans (hC₀ z hzre him) (le_max_left _ _)
  · have him1 : (1 : ℝ) ≤ |z.im| := le_of_lt him
    have hzeq : z = ((3/2 : ℝ) : ℂ) + (z.im : ℂ) * I := Cvs.ArchScore.edge_param hzre
    have hedge : ‖riemannZeta₀ z‖ ≤ Cb * (1 + |z.im|) ^ (0 : ℝ) := by
      have h := Cvs.ZetaGrowth.zeta₀_edge_right (t := z.im) him1
      have hz' : (3 : ℂ) / 2 + (z.im : ℂ) * I = z := by
        rw [hzeq]; norm_num
      rw [hz'] at h
      rw [Real.rpow_zero, mul_one]
      exact h
    have hb := Cvs.ArchScore.edge_const_even (f := riemannZeta₀) (c := 1) (K := 7) (a := 0)
      (b' := -1/2) (Ca := Cb) (β := 3/2) (by norm_num) (by norm_num) hCb0
      (by rw [hzre]; norm_num) (by rw [hzre]) him1 hedge
    have hval : ‖A z‖ = ‖riemannZeta₀ z‖ * Real.exp (-0 * (Cvs.ArchScore.evenLog 1 7 z).re
        + (-1/2) * z.im * (Cvs.ArchScore.evenLog 1 7 z).im) := by
      rw [A, Cvs.ArchScore.norm_aux_even]
      congr 2
      rw [hzre]; norm_num
    rw [hval]
    exact le_trans hb (le_max_right _ _)

/-- **The Phragmén–Lindelöf call.**  Every hypothesis now has a supplier: `ConvexityAuxDiffContOnCl` the
differentiability, `AuxiliaryGrowth` the growth, and the two edge bounds above. -/
theorem aux_bounded : ∃ C : ℝ, ∀ z : ℂ, -1/2 ≤ z.re → z.re ≤ 3/2 → ‖A z‖ ≤ C := by
  obtain ⟨Cl, hCl⟩ := edge_bound_left
  obtain ⟨Cr, hCr⟩ := edge_bound_right
  obtain ⟨e, he, B, hO⟩ := Cvs.ZetaGrowth.growth_aux_zeta₀
  refine ⟨max Cl Cr, fun z h1 h2 => ?_⟩
  exact Cvs.ArchScore.norm_aux_le_of_edges (f := riemannZeta₀) (c := 1) (K := 7)
    (α := -1/2) (β := 3/2) (a' := 3/4) (b' := -1/2)
    (Cvs.ArchScore.diffContOnCl_aux (by norm_num) (by norm_num)
      (fun s _ => differentiable_riemannZeta₀ s))
    ⟨e, he, B, hO⟩
    (fun w hw => le_trans (hCl w hw) (le_max_left _ _))
    (fun w hw => le_trans (hCr w hw) (le_max_right _ _)) h1 h2

end Cvs.Zeta.Convexity.CriticalLineHalfExponent
