import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Slepian's commuting relation: the finite cosine transform of an angular prolate is radial

With `L_x = ∂_x(1 − x²)∂_x − c²x²`, the kernel `K(ξ, s) = cos(cξs)` has `L_s K = L_ξ K`; and for `g` with
`(1 − s²)`-weighted derivatives on `[−1, 1]`, `∫ g · L_s K = ∫ (L_s g) · K`. Hence if `L_s g = −χ g` on `[−1, 1]`,
`ψ(ξ) = ∫_{−1}^{1} g(s) cos(cξs) ds` solves `((ξ² − 1)ψ')' + (c²ξ² − χ)ψ = 0` for every `ξ`.
-/

namespace Cvs.Prolate.SlepianCommutingRelation

open Real intervalIntegral Set
open scoped Interval

/-- **The kernel identity** `L_s cos(cξs) = L_ξ cos(cξs)`, written out. -/
theorem kernel_sym (c ξ s : ℝ) :
    (1 - s ^ 2) * (-(c ^ 2 * ξ ^ 2 * cos (c * ξ * s))) - 2 * s * (-(c * ξ * sin (c * ξ * s)))
        - c ^ 2 * s ^ 2 * cos (c * ξ * s)
      = (1 - ξ ^ 2) * (-(c ^ 2 * s ^ 2 * cos (c * ξ * s))) - 2 * ξ * (-(c * s * sin (c * ξ * s)))
        - c ^ 2 * ξ ^ 2 * cos (c * ξ * s) := by ring

/-- **Two integrations by parts with the weight `1 − s²`**: for `g, K` with derivatives `g₁, g₂, K₁, K₂` on
`[−1, 1]`, `∫ g ((1−s²)K₂ − 2sK₁) = ∫ ((1−s²)g₂ − 2sg₁) K`. -/
theorem ibp_weighted {g g₁ g₂ K K₁ K₂ : ℝ → ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hK : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt K (K₁ s) s) (hK₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt K₁ (K₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1)) (hK₂c : ContinuousOn K₂ (uIcc (-1) 1)) :
    ∫ s in (-1 : ℝ)..1, g s * ((1 - s ^ 2) * K₂ s - 2 * s * K₁ s)
      = ∫ s in (-1 : ℝ)..1, ((1 - s ^ 2) * g₂ s - 2 * s * g₁ s) * K s := by
  -- `W := (1 − s²)(g K₁ − g₁ K)` has derivative `g·L K − (L g)·K`
  have hW : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (fun s => (1 - s ^ 2) * (g s * K₁ s - g₁ s * K s))
      (g s * ((1 - s ^ 2) * K₂ s - 2 * s * K₁ s) - ((1 - s ^ 2) * g₂ s - 2 * s * g₁ s) * K s) s := by
    intro s hs
    have hp : HasDerivAt (fun s : ℝ => 1 - s ^ 2) (-(2 * s)) s := by
      simpa using ((hasDerivAt_pow 2 s).const_sub 1)
    have := hp.mul (((hg s hs).mul (hK₁ s hs)).sub ((hg₁ s hs).mul (hK s hs)))
    refine this.congr_deriv ?_
    simp only [Pi.sub_apply, Pi.mul_apply]
    ring
  have hc : ∀ f : ℝ → ℝ, (∀ s ∈ uIcc (-1 : ℝ) 1, DifferentiableAt ℝ f s) → ContinuousOn f (uIcc (-1) 1) :=
    fun f hf s hs => (hf s hs).continuousAt.continuousWithinAt
  have gc := hc g fun s hs => (hg s hs).differentiableAt
  have g₁c := hc g₁ fun s hs => (hg₁ s hs).differentiableAt
  have Kc := hc K fun s hs => (hK s hs).differentiableAt
  have K₁c := hc K₁ fun s hs => (hK₁ s hs).differentiableAt
  have hint : IntervalIntegrable (fun s => g s * ((1 - s ^ 2) * K₂ s - 2 * s * K₁ s)
      - ((1 - s ^ 2) * g₂ s - 2 * s * g₁ s) * K s) MeasureTheory.volume (-1) 1 := by
    apply ContinuousOn.intervalIntegrable
    exact (gc.mul (((continuousOn_const.sub (continuousOn_id.pow 2)).mul hK₂c).sub
      ((continuousOn_const.mul continuousOn_id).mul K₁c))).sub
      ((((continuousOn_const.sub (continuousOn_id.pow 2)).mul hg₂c).sub
      ((continuousOn_const.mul continuousOn_id).mul g₁c)).mul Kc)
  have hFTC := integral_eq_sub_of_hasDerivAt hW hint
  simp only [one_pow, sub_self, zero_mul, neg_sq] at hFTC
  rw [intervalIntegral.integral_sub] at hFTC
  · linarith
  · exact (gc.mul (((continuousOn_const.sub (continuousOn_id.pow 2)).mul hK₂c).sub
      ((continuousOn_const.mul continuousOn_id).mul K₁c))).intervalIntegrable
  · exact ((((continuousOn_const.sub (continuousOn_id.pow 2)).mul hg₂c).sub
      ((continuousOn_const.mul continuousOn_id).mul g₁c)).mul Kc).intervalIntegrable

/-- A kernel integral `∫_{−1}^{1} g(s) k(ξ, s) ds`. -/
noncomputable def kint (g : ℝ → ℝ) (k : ℝ → ℝ → ℝ) (ξ : ℝ) : ℝ := ∫ s in (-1 : ℝ)..1, g s * k ξ s

/-- **Differentiation under the integral** for a kernel with `|∂_ξ k| ≤ C` on `s ∈ [−1, 1]`. -/
theorem hasDerivAt_kint {g : ℝ → ℝ} {k k' : ℝ → ℝ → ℝ} {C : ℝ} (hg : ContinuousOn g (uIcc (-1) 1))
    (hk : ∀ s, Continuous fun ξ => k ξ s) (hkc : ∀ ξ, Continuous (k ξ)) (hk'c : ∀ ξ, Continuous (k' ξ))
    (hd : ∀ ξ s, HasDerivAt (fun ξ => k ξ s) (k' ξ s) ξ) (hb : ∀ ξ s, |s| ≤ 1 → |k' ξ s| ≤ C) (ξ₀ : ℝ) :
    HasDerivAt (kint g k) (kint g k' ξ₀) ξ₀ := by
  have hgi : IntervalIntegrable g MeasureTheory.volume (-1) 1 := hg.intervalIntegrable
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := MeasureTheory.volume)
    (a := -1) (b := 1) (F := fun ξ s => g s * k ξ s) (F' := fun ξ s => g s * k' ξ s) (x₀ := ξ₀)
    (bound := fun s => |g s| * C) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun ξ => ((hgi.mul_continuousOn (hkc ξ).continuousOn).def').aestronglyMeasurable)
    (hgi.mul_continuousOn (hkc ξ₀).continuousOn)
    ((hgi.mul_continuousOn (hk'c ξ₀).continuousOn).def').aestronglyMeasurable
    (Filter.Eventually.of_forall fun s hs ξ _ => by
      have hs1 : |s| ≤ 1 := by
        rw [uIoc_of_le (by norm_num)] at hs; exact abs_le.mpr ⟨hs.1.le, hs.2⟩
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hb ξ s hs1) (abs_nonneg _))
    (hgi.abs.mul_const C)
    (Filter.Eventually.of_forall fun s _ ξ _ => (hd ξ s).const_mul (g s))
  exact key.2

/-- **Slepian's relation.** -/
theorem radial_ode {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0) (ξ : ℝ) :
    (ξ ^ 2 - 1) * kint g (fun ξ s => -(c ^ 2 * s ^ 2 * cos (c * ξ * s))) ξ
      + 2 * ξ * kint g (fun ξ s => -(c * s * sin (c * ξ * s))) ξ
      + (c ^ 2 * ξ ^ 2 - χ) * kint g (fun ξ s => cos (c * ξ * s)) ξ = 0 := by
  have hgc : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  have hg₁c : ContinuousOn g₁ (uIcc (-1) 1) := fun s hs => (hg₁ s hs).continuousAt.continuousWithinAt
  unfold kint
  -- the angular side, by parts
  have hK : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (fun s => cos (c * ξ * s)) (-(c * ξ * sin (c * ξ * s))) s := by
    intro s _
    have := ((hasDerivAt_id s).const_mul (c * ξ)).cos
    refine this.congr_deriv ?_; simp; ring
  have hK₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (fun s => -(c * ξ * sin (c * ξ * s)))
      (-(c ^ 2 * ξ ^ 2 * cos (c * ξ * s))) s := by
    intro s _
    have := (((hasDerivAt_id s).const_mul (c * ξ)).sin.const_mul (c * ξ)).neg
    refine this.congr_deriv ?_; simp; ring
  have ibp := ibp_weighted hg hg₁ hK hK₁ hg₂c (by fun_prop)
  have hi : ∀ f : ℝ → ℝ, Continuous f → IntervalIntegrable (fun s => g s * f s) MeasureTheory.volume (-1) 1 :=
    fun f hf => hgc.intervalIntegrable.mul_continuousOn hf.continuousOn
  -- rewrite the radial combination pointwise through the kernel identity
  have e : ∀ s ∈ uIcc (-1 : ℝ) 1,
      (ξ ^ 2 - 1) * (g s * -(c ^ 2 * s ^ 2 * cos (c * ξ * s))) + 2 * ξ * (g s * -(c * s * sin (c * ξ * s)))
        + (c ^ 2 * ξ ^ 2 - χ) * (g s * cos (c * ξ * s))
      = -(g s * ((1 - s ^ 2) * -(c ^ 2 * ξ ^ 2 * cos (c * ξ * s)) - 2 * s * -(c * ξ * sin (c * ξ * s))))
        + ((1 - s ^ 2) * g₂ s - 2 * s * g₁ s) * cos (c * ξ * s) := by
    intro s hs
    have h := hang s hs
    have hk := kernel_sym c ξ s
    have : ((1 - s ^ 2) * g₂ s - 2 * s * g₁ s) = c ^ 2 * s ^ 2 * g s - χ * g s := by linarith
    rw [this]
    linear_combination (-(g s)) * hk
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add, ← intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_congr e]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_neg, ibp]
    · ring
    · exact (hgc.mul (by fun_prop)).neg.intervalIntegrable
    · exact ((((continuousOn_const.sub (continuousOn_id.pow 2)).mul hg₂c).sub
        ((continuousOn_const.mul continuousOn_id).mul hg₁c)).mul (by fun_prop)).intervalIntegrable
  · exact ((hi _ (by fun_prop)).const_mul _).add ((hi _ (by fun_prop)).const_mul _)
  · exact (hi _ (by fun_prop)).const_mul _
  · exact (hi _ (by fun_prop)).const_mul _
  · exact (hi _ (by fun_prop)).const_mul _

end Cvs.Prolate.SlepianCommutingRelation
