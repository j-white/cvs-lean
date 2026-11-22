import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.SlepianCommutingRelation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Christoffel–Darboux identity of the finite cosine transform

For angular solutions `g` at `χ` and `h` at `χ'` that are eigenfunctions of `psi c` with eigenvalues `μ`, `μ'`:
`c²(μ'² − μ²)∫_{−1}^{1} s² g h = (χ' − χ) μ μ' (g(1)h(1) + g(−1)h(−1))/2`. The proof is one Fubini swap with
`Cvs.L2a.AngularProlateTailPositive.psi_system`, Green's identity on `[−1, 1]`, and the angular equation at `s = ±1`.
-/

noncomputable section

open Real Set intervalIntegral MeasureTheory Filter Topology Cvs.Prolate.SlepianCommutingRelation Cvs.L2a.AngularProlateTailPositive
open scoped Interval

namespace Cvs.Prolate.CosineChristoffelDarboux

theorem one_mem_uIcc : (1 : ℝ) ∈ uIcc (-1 : ℝ) 1 := by rw [uIcc_of_le (by norm_num)]; exact ⟨by norm_num, le_rfl⟩

theorem neg_one_mem_uIcc : (-1 : ℝ) ∈ uIcc (-1 : ℝ) 1 := by
  rw [uIcc_of_le (by norm_num)]; exact ⟨le_rfl, by norm_num⟩

/-- **Edge relation at `s = 1`**: the angular equation at `s = 1` reads `2g'(1) = (χ − c²) g(1)`. -/
theorem edge_one {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0) :
    2 * g₁ 1 = (χ - c ^ 2) * g 1 := by
  have h := hang 1 one_mem_uIcc
  simp only [one_pow, sub_self, zero_mul, mul_one, zero_sub] at h
  linarith

/-- **Edge relation at `s = −1`**: `2g'(−1) = (c² − χ) g(−1)`. -/
theorem edge_neg_one {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0) :
    2 * g₁ (-1) = (c ^ 2 - χ) * g (-1) := by
  have h := hang (-1) neg_one_mem_uIcc
  have e : ((-1 : ℝ)) ^ 2 = 1 := by norm_num
  rw [e] at h
  simp only [sub_self, zero_mul, mul_one, zero_sub] at h
  linarith

theorem continuousOn_of_hasDerivAt {f f' : ℝ → ℝ} (hf : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt f (f' s) s) :
    ContinuousOn f (Icc (-1) 1) := fun s hs =>
  (hf s (by rwa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)])).continuousAt.continuousWithinAt

/-- **One Fubini swap** for the cosine kernel on `[−1, 1]²`. -/
theorem swap_cos {u v : ℝ → ℝ} (c : ℝ) (hu : ContinuousOn u (Icc (-1) 1)) (hv : ContinuousOn v (Icc (-1) 1)) :
    ∫ x in (-1 : ℝ)..1, u x * (∫ s in (-1 : ℝ)..1, v s * cos (c * x * s))
      = ∫ s in (-1 : ℝ)..1, v s * (∫ x in (-1 : ℝ)..1, u x * cos (c * s * x)) := by
  set F : ℝ → ℝ → ℝ := fun x s => u x * (v s * cos (c * x * s)) with hF
  have hcont : ContinuousOn F.uncurry (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => u p.1) (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) :=
      hu.comp continuous_fst.continuousOn (fun p hp => hp.1)
    have h2 : ContinuousOn (fun p : ℝ × ℝ => v p.2) (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) :=
      hv.comp continuous_snd.continuousOn (fun p hp => hp.2)
    have h3 : Continuous (fun p : ℝ × ℝ => cos (c * p.1 * p.2)) := by fun_prop
    exact h1.mul (h2.mul h3.continuousOn)
  have hint : IntegrableOn F.uncurry (uIoc (-1 : ℝ) 1 ×ˢ uIoc (-1 : ℝ) 1) := by
    have hc := hcont.integrableOn_compact (μ := volume) (isCompact_Icc.prod isCompact_Icc)
    refine hc.mono_set ?_
    rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self
  have hsw := intervalIntegral_intervalIntegral_swap hint
  have hL : ∀ x, u x * (∫ s in (-1 : ℝ)..1, v s * cos (c * x * s)) = ∫ s in (-1 : ℝ)..1, F x s := by
    intro x; rw [hF]; simp only; rw [intervalIntegral.integral_const_mul]
  have hR : ∀ s, v s * (∫ x in (-1 : ℝ)..1, u x * cos (c * s * x)) = ∫ x in (-1 : ℝ)..1, F x s := by
    intro s
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [hF]
    rw [show c * s * x = c * x * s by ring]
    ring
  simp_rw [hL, hR]
  exact hsw

/-- **The second derivative of the transform on `(−1, 1)`**: if `psi c h = μ' h` on `[−1, 1]`, then for
`s ∈ (−1, 1)`, `c² ∫ x² h(x) cos(csx) dx = −μ' h''(s)`. -/
theorem second_deriv_eq {h h₁ h₂ : ℝ → ℝ} {c χ μ' : ℝ}
    (hh : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h (h₁ s) s) (hh₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h₁ (h₂ s) s)
    (hh₂c : ContinuousOn h₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * h₂ s - 2 * s * h₁ s - c ^ 2 * s ^ 2 * h s + χ * h s = 0)
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c h s = μ' * h s) :
    ∀ s ∈ Ioo (-1 : ℝ) 1, c ^ 2 * (∫ x in (-1 : ℝ)..1, x ^ 2 * h x * cos (c * s * x)) = -(μ' * h₂ s) := by
  obtain ⟨d1, d2, -⟩ := psi_system hh hh₁ hh₂c hang
  have hI : ∀ s ∈ Ioo (-1 : ℝ) 1, s ∈ uIcc (-1 : ℝ) 1 := fun s hs => by
    rw [uIcc_of_le (by norm_num)]; exact Ioo_subset_Icc_self hs
  intro s hs
  -- first derivative: `D1 s = μ' h₁ s`
  have hev : psi c h =ᶠ[𝓝 s] fun x => μ' * h x := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with x hx using hμ x (Ioo_subset_Icc_self hx)
  have hD1 : ∀ x ∈ Ioo (-1 : ℝ) 1,
      kint h (fun ξ s => -(c * s * sin (c * ξ * s))) x = μ' * h₁ x := by
    intro x hx
    have hev' : psi c h =ᶠ[𝓝 x] fun y => μ' * h y := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy using hμ y (Ioo_subset_Icc_self hy)
    exact (d1 x).unique (((hh x (hI x hx)).const_mul μ').congr_of_eventuallyEq hev')
  have hev1 : (kint h fun ξ s => -(c * s * sin (c * ξ * s))) =ᶠ[𝓝 s] fun x => μ' * h₁ x := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with x hx using hD1 x hx
  have hD2 : kint h (fun ξ s => -(c ^ 2 * s ^ 2 * cos (c * ξ * s))) s = μ' * h₂ s :=
    (d2 s).unique (((hh₁ s (hI s hs)).const_mul μ').congr_of_eventuallyEq hev1)
  have hk : kint h (fun ξ s => -(c ^ 2 * s ^ 2 * cos (c * ξ * s))) s
      = -(c ^ 2 * ∫ x in (-1 : ℝ)..1, x ^ 2 * h x * cos (c * s * x)) := by
    unfold kint
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun x _ => ?_
    ring
  rw [hk] at hD2
  linarith

/-- The interval integral over `[−1, 1]` only sees `(−1, 1)`. -/
theorem integral_congr_Ioo {f₁ f₂ : ℝ → ℝ} (h : ∀ s ∈ Ioo (-1 : ℝ) 1, f₁ s = f₂ s) :
    ∫ s in (-1 : ℝ)..1, f₁ s = ∫ s in (-1 : ℝ)..1, f₂ s := by
  rw [intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_of_le (by norm_num),
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo h

/-- **Half of the identity**: `c² μ'² ∫ s² g h = −μ μ' ∫ h g''`. -/
theorem half_identity {g g₁ g₂ h h₁ : ℝ → ℝ} {c χ μ μ' : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hh : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h (h₁ s) s)
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) (hμ' : ∀ s ∈ Icc (-1 : ℝ) 1, psi c h s = μ' * h s) :
    c ^ 2 * μ' ^ 2 * (∫ s in (-1 : ℝ)..1, s ^ 2 * g s * h s) = -(μ * μ') * ∫ s in (-1 : ℝ)..1, h s * g₂ s := by
  have hgc := continuousOn_of_hasDerivAt hg
  have hhc := continuousOn_of_hasDerivAt hh
  have hsd := second_deriv_eq hg hg₁ hg₂c hang hμ
  have e0 : μ' * (∫ s in (-1 : ℝ)..1, s ^ 2 * g s * h s) = ∫ s in (-1 : ℝ)..1, s ^ 2 * g s * (μ' * h s) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    ring
  have e1 : ∫ s in (-1 : ℝ)..1, s ^ 2 * g s * (μ' * h s)
      = ∫ x in (-1 : ℝ)..1, (x ^ 2 * g x) * (∫ s in (-1 : ℝ)..1, h s * cos (c * x * s)) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le (by norm_num)] at hx
    have := hμ' x hx
    simp only [psi, kint] at this
    rw [← this]
  have e2 := swap_cos c ((continuousOn_id.pow 2).mul hgc) hhc
  have e3 : c ^ 2 * (∫ s in (-1 : ℝ)..1, h s * (∫ x in (-1 : ℝ)..1, (id x ^ 2 * g x) * cos (c * s * x)))
      = ∫ s in (-1 : ℝ)..1, h s * (-(μ * g₂ s)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply integral_congr_Ioo
    intro s hs
    rw [← hsd s hs]
    simp only [id]
    ring
  have e4 : ∫ s in (-1 : ℝ)..1, h s * (-(μ * g₂ s)) = -μ * ∫ s in (-1 : ℝ)..1, h s * g₂ s := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    ring
  have key : c ^ 2 * (μ' * (∫ s in (-1 : ℝ)..1, s ^ 2 * g s * h s)) = -μ * ∫ s in (-1 : ℝ)..1, h s * g₂ s := by
    rw [e0, e1]
    simp only [Pi.mul_apply, Pi.pow_apply, id] at e2
    rw [e2]
    simp only [id] at e3
    rw [e3, e4]
  calc c ^ 2 * μ' ^ 2 * (∫ s in (-1 : ℝ)..1, s ^ 2 * g s * h s)
      = μ' * (c ^ 2 * (μ' * (∫ s in (-1 : ℝ)..1, s ^ 2 * g s * h s))) := by ring
    _ = -(μ * μ') * ∫ s in (-1 : ℝ)..1, h s * g₂ s := by rw [key]; ring

/-- **Green's identity on `[−1, 1]`**: `∫ (g h'' − h g'') = [g h' − h g']_{−1}^{1}`. -/
theorem green {g g₁ g₂ h h₁ h₂ : ℝ → ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hh : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h (h₁ s) s) (hh₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h₁ (h₂ s) s)
    (hh₂c : ContinuousOn h₂ (uIcc (-1) 1)) :
    ∫ s in (-1 : ℝ)..1, (g s * h₂ s - h s * g₂ s)
      = (g 1 * h₁ 1 - h 1 * g₁ 1) - (g (-1) * h₁ (-1) - h (-1) * g₁ (-1)) := by
  have hd : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (fun s => g s * h₁ s - h s * g₁ s) (g s * h₂ s - h s * g₂ s) s := by
    intro s hs
    have := ((hg s hs).mul (hh₁ s hs)).sub ((hh s hs).mul (hg₁ s hs))
    refine this.congr_deriv ?_
    ring
  have hgc : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  have hhc : ContinuousOn h (uIcc (-1) 1) := fun s hs => (hh s hs).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable (fun s => g s * h₂ s - h s * g₂ s) volume (-1) 1 :=
    ((hgc.mul hh₂c).sub (hhc.mul hg₂c)).intervalIntegrable
  rw [integral_eq_sub_of_hasDerivAt hd hint]

/-- **ORD-A: the Christoffel–Darboux identity of the finite cosine transform.** For angular solutions `g` at `χ`
and `h` at `χ'`, `C²` on `[−1, 1]`, with `psi c g = μ g` and `psi c h = μ' h` on `[−1, 1]`:
`c² (μ'² − μ²) ∫_{−1}^{1} s² g h = (χ' − χ) μ μ' (g(1) h(1) + g(−1) h(−1)) / 2`. -/
theorem cd_identity {g g₁ g₂ h h₁ h₂ : ℝ → ℝ} {c χ χ' μ μ' : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hh : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h (h₁ s) s) (hh₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h₁ (h₂ s) s)
    (hh₂c : ContinuousOn h₂ (uIcc (-1) 1))
    (hang' : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * h₂ s - 2 * s * h₁ s - c ^ 2 * s ^ 2 * h s + χ' * h s = 0)
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) (hμ' : ∀ s ∈ Icc (-1 : ℝ) 1, psi c h s = μ' * h s) :
    c ^ 2 * (μ' ^ 2 - μ ^ 2) * (∫ s in (-1 : ℝ)..1, s ^ 2 * g s * h s)
      = (χ' - χ) * μ * μ' * (g 1 * h 1 + g (-1) * h (-1)) / 2 := by
  have H1 := half_identity hg hg₁ hg₂c hang hh hμ hμ'
  have H2 := half_identity hh hh₁ hh₂c hang' hg hμ' hμ
  have hsym : (∫ s in (-1 : ℝ)..1, s ^ 2 * h s * g s) = ∫ s in (-1 : ℝ)..1, s ^ 2 * g s * h s :=
    intervalIntegral.integral_congr fun x _ => by ring
  rw [hsym] at H2
  have hG := green hg hg₁ hg₂c hh hh₁ hh₂c
  have hgc : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  have hhc : ContinuousOn h (uIcc (-1) 1) := fun s hs => (hh s hs).continuousAt.continuousWithinAt
  have hsplit : ∫ s in (-1 : ℝ)..1, (g s * h₂ s - h s * g₂ s)
      = (∫ s in (-1 : ℝ)..1, g s * h₂ s) - ∫ s in (-1 : ℝ)..1, h s * g₂ s :=
    intervalIntegral.integral_sub (hgc.mul hh₂c).intervalIntegrable (hhc.mul hg₂c).intervalIntegrable
  have e1 := edge_one hang
  have e2 := edge_one hang'
  have e3 := edge_neg_one hang
  have e4 := edge_neg_one hang'
  rw [hsplit] at hG
  -- H1: c²μ'²A = −μμ'∫h g₂ ; H2: c²μ²A = −μ'μ ∫ g h₂
  have : c ^ 2 * (μ' ^ 2 - μ ^ 2) * (∫ s in (-1 : ℝ)..1, s ^ 2 * g s * h s)
      = μ * μ' * ((g 1 * h₁ 1 - h 1 * g₁ 1) - (g (-1) * h₁ (-1) - h (-1) * g₁ (-1))) := by
    rw [← hG]; linear_combination H1 - H2
  rw [this]
  linear_combination (μ * μ' / 2) * (g 1 * e2 - h 1 * e1 - g (-1) * e4 + h (-1) * e3)

end Cvs.Prolate.CosineChristoffelDarboux
