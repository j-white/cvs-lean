import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.CosineTransformVirial
import Cvs.Prolate.SlepianCommutingRelation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The scale generator between two eigenfunctions: a Cauchy weight on the edge values

For even `C¹` eigenfunctions `ψ_c g = μg`, `ψ_c h = νh` on `[−1, 1]` with `μ + ν ≠ 0`,
`∫ g · ∂_c ψ_c h = μν/(c(μ + ν)) · (2g(1)h(1) − ∫gh)`. The kernel of `∂_c ψ_c` is symmetric, so the two one-sided
virial integrals are tied by `ν∫ξgh′ = μ∫ξhg′`, and their sum is the edge term. On the rungs the scale generator is a
Cauchy matrix `2μⱼμₖ/(μⱼ + μₖ)` times the edge values, less `μ/2` on the diagonal (Cvs.Prolate.CosineTransformVirial is the diagonal).
-/

noncomputable section

open Real Set MeasureTheory Filter Topology
open scoped Interval

namespace Cvs.Prolate.ScaleGeneratorCauchyWeight

open Cvs.Prolate.SlepianCommutingRelation Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.EvenRungsByIndex Cvs.Prolate.CosineTransformVirial

/-- The kernel of `∂_c ψ_c` at `(ξ, s)`. -/
def dK (c ξ s : ℝ) : ℝ := -(ξ * s * sin (c * ξ * s))

theorem dK_symm (c ξ s : ℝ) : dK c ξ s = dK c s ξ := by
  unfold dK; rw [show c * s * ξ = c * ξ * s by ring]; ring

theorem kint_eq (h : ℝ → ℝ) (c ξ : ℝ) :
    kint h (fun c s => -(ξ * s * sin (c * ξ * s))) c = ∫ s in (-1 : ℝ)..1, h s * dK c ξ s := rfl

/-- **The scale generator is symmetric**: `∫ g · ∂_c ψ_c h = ∫ h · ∂_c ψ_c g`. -/
theorem symm_pair {g h : ℝ → ℝ} (hgc : ContinuousOn g (Icc (-1) 1)) (hhc : ContinuousOn h (Icc (-1) 1)) (c : ℝ) :
    ∫ ξ in (-1 : ℝ)..1, g ξ * kint h (fun c s => -(ξ * s * sin (c * ξ * s))) c
      = ∫ ξ in (-1 : ℝ)..1, h ξ * kint g (fun c s => -(ξ * s * sin (c * ξ * s))) c := by
  simp_rw [kint_eq, ← intervalIntegral.integral_const_mul]
  have hK : Continuous fun p : ℝ × ℝ => dK c p.1 p.2 := by unfold dK; fun_prop
  have hcont : ContinuousOn (Function.uncurry fun ξ s => g ξ * (h s * dK c ξ s)) (Icc (-1 : ℝ) 1 ×ˢ Icc (-1) 1) :=
    (hgc.comp continuousOn_fst (fun p hp => (mem_prod.1 hp).1)).mul
      ((hhc.comp continuousOn_snd (fun p hp => (mem_prod.1 hp).2)).mul hK.continuousOn)
  have hint : IntegrableOn (Function.uncurry fun ξ s => g ξ * (h s * dK c ξ s))
      (uIoc (-1 : ℝ) 1 ×ˢ uIoc (-1) 1) := by
    rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact (hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  rw [intervalIntegral_intervalIntegral_swap hint]
  refine intervalIntegral.integral_congr fun s _ => intervalIntegral.integral_congr fun ξ _ => ?_
  rw [dK_symm c ξ s]; ring

/-- **One-sided virial**: `∫ g · ∂_c ψ_c h = (ν/c)∫ ξ g h′` when `ψ_c h = νh` on `[−1, 1]`. -/
theorem virial_left {g h h₁ : ℝ → ℝ} {c ν : ℝ} (hc : c ≠ 0)
    (hh : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h (h₁ s) s) (heig : ∀ s ∈ Icc (-1 : ℝ) 1, psi c h s = ν * h s) :
    ∫ ξ in (-1 : ℝ)..1, g ξ * kint h (fun c s => -(ξ * s * sin (c * ξ * s))) c
      = ν / c * ∫ ξ in (-1 : ℝ)..1, ξ * g ξ * h₁ ξ := by
  have hhc : ContinuousOn h (uIcc (-1) 1) := fun s hs => (hh s hs).continuousAt.continuousWithinAt
  have hpt : ∀ ξ ∈ Ioo (-1 : ℝ) 1,
      g ξ * kint h (fun c s => -(ξ * s * sin (c * ξ * s))) c = ν / c * (ξ * g ξ * h₁ ξ) := by
    intro ξ hξ
    have hξI : ξ ∈ uIcc (-1 : ℝ) 1 := by
      rw [uIcc_of_le (by norm_num)]; exact Ioo_subset_Icc_self hξ
    have hev : psi c h =ᶠ[𝓝 ξ] fun s => ν * h s :=
      Filter.eventually_of_mem (Ioo_mem_nhds hξ.1 hξ.2) fun s hs => heig s (Ioo_subset_Icc_self hs)
    have hd2 : HasDerivAt (psi c h) (ν * h₁ ξ) ξ := ((hh ξ hξI).const_mul ν).congr_of_eventuallyEq hev
    have hu := (hasDerivAt_psi_freq hhc c ξ).unique hd2
    have hs := scale_generator h c ξ
    rw [hu] at hs
    have : kint h (fun c s => -(ξ * s * sin (c * ξ * s))) c = ξ * (ν * h₁ ξ) / c := by
      rw [eq_div_iff hc, mul_comm]; exact hs
    rw [this]; field_simp
  have hae : ∀ᵐ ξ ∂(volume : Measure ℝ), ξ ∈ Ι (-1 : ℝ) 1 →
      g ξ * kint h (fun c s => -(ξ * s * sin (c * ξ * s))) c = ν / c * (ξ * g ξ * h₁ ξ) := by
    have h1 : ∀ᵐ ξ ∂(volume : Measure ℝ), ξ ≠ 1 := by
      rw [ae_iff]; simp [measure_singleton]
    filter_upwards [h1] with ξ hξ1 hξ
    rw [uIoc_of_le (by norm_num)] at hξ
    exact hpt ξ ⟨hξ.1, lt_of_le_of_ne hξ.2 hξ1⟩
  rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_const_mul]

/-- The edge term: `∫ ξ g h′ + ∫ ξ h g′ = 2g(1)h(1) − ∫gh` for even `g`, `h`. -/
theorem edge_sum {g g₁ h h₁ : ℝ → ℝ} (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁c : ContinuousOn g₁ (uIcc (-1) 1)) (hh : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h (h₁ s) s)
    (hh₁c : ContinuousOn h₁ (uIcc (-1) 1)) (hge : g (-1) = g 1) (hhe : h (-1) = h 1) :
    (∫ ξ in (-1 : ℝ)..1, ξ * g ξ * h₁ ξ) + (∫ ξ in (-1 : ℝ)..1, ξ * h ξ * g₁ ξ)
      = 2 * g 1 * h 1 - ∫ ξ in (-1 : ℝ)..1, g ξ * h ξ := by
  have hgc : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  have hhc : ContinuousOn h (uIcc (-1) 1) := fun s hs => (hh s hs).continuousAt.continuousWithinAt
  have hF : ∀ x ∈ uIcc (-1 : ℝ) 1,
      HasDerivAt (fun x => x * g x * h x) (g x * h x + (x * g x * h₁ x + x * h x * g₁ x)) x := by
    intro x hx
    have := ((hasDerivAt_id x).mul (hg x hx)).mul (hh x hx)
    refine this.congr_deriv ?_; simp; ring
  have hi0 : IntervalIntegrable (fun x => g x * h x) volume (-1) 1 := (hgc.mul hhc).intervalIntegrable
  have hi1 : IntervalIntegrable (fun x => x * g x * h₁ x) volume (-1) 1 :=
    ((continuousOn_id.mul hgc).mul hh₁c).intervalIntegrable
  have hi2 : IntervalIntegrable (fun x => x * h x * g₁ x) volume (-1) 1 :=
    ((continuousOn_id.mul hhc).mul hg₁c).intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hF (hi0.add (hi1.add hi2))
  rw [intervalIntegral.integral_add hi0 (hi1.add hi2), intervalIntegral.integral_add hi1 hi2, hge, hhe] at hFTC
  linarith

/-- **The scale generator between two eigenfunctions**:
`∫ g · ∂_c ψ_c h = μν/(c(μ + ν)) · (2g(1)h(1) − ∫gh)`. -/
theorem pair_virial {g g₁ h h₁ : ℝ → ℝ} {c μ ν : ℝ} (hc : c ≠ 0) (hμν : μ + ν ≠ 0)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁c : ContinuousOn g₁ (uIcc (-1) 1))
    (hh : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h (h₁ s) s) (hh₁c : ContinuousOn h₁ (uIcc (-1) 1))
    (hge : g (-1) = g 1) (hhe : h (-1) = h 1)
    (heg : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) (heh : ∀ s ∈ Icc (-1 : ℝ) 1, psi c h s = ν * h s) :
    ∫ ξ in (-1 : ℝ)..1, g ξ * kint h (fun c s => -(ξ * s * sin (c * ξ * s))) c
      = μ * ν / (c * (μ + ν)) * (2 * g 1 * h 1 - ∫ ξ in (-1 : ℝ)..1, g ξ * h ξ) := by
  have hI : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hgc : ContinuousOn g (Icc (-1) 1) := fun s hs =>
    (hg s (hI ▸ hs)).continuousAt.continuousWithinAt
  have hhc : ContinuousOn h (Icc (-1) 1) := fun s hs =>
    (hh s (hI ▸ hs)).continuousAt.continuousWithinAt
  have hA := virial_left (g := g) hc hh heh
  have hB := virial_left (g := h) hc hg heg
  have hS := symm_pair hgc hhc c
  have hE := edge_sum hg hg₁c hh hh₁c hge hhe
  set A := ∫ ξ in (-1 : ℝ)..1, ξ * g ξ * h₁ ξ
  set B := ∫ ξ in (-1 : ℝ)..1, ξ * h ξ * g₁ ξ
  set T := 2 * g 1 * h 1 - ∫ ξ in (-1 : ℝ)..1, g ξ * h ξ
  have hνA : ν * A = μ * B := by
    have := hA.symm.trans (hS.trans hB)
    field_simp at this; linarith
  have hAval : A = μ * T / (μ + ν) := by
    rw [eq_div_iff hμν]; linear_combination hνA + μ * hE
  rw [hA, hAval]; field_simp

end Cvs.Prolate.ScaleGeneratorCauchyWeight
