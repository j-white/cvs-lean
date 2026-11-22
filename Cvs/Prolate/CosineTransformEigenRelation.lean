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
# The eigen relation: the cosine transform of an angular solution is a multiple of it

Two solutions of `(1 − s²)u'' − 2su' − c²s²u + χu = 0` that are `C²` up to `s = ±1` have Wronskian
`(1 − s²)(uv' − u'v) ≡ 0`, and a solution with zero data at an interior point vanishes on `[−1, 1]` (Mathlib's ODE
uniqueness on compact subintervals of `(−1, 1)`). Since `psi c g` solves the same equation (Cvs.L2a.AngularProlateTailPositive), `psi c g = μ g`.
-/

namespace Cvs.Prolate.CosineTransformEigenRelation

open Real Set Cvs.Prolate.SlepianCommutingRelation Cvs.L2a.AngularProlateTailPositive

/-- **The Wronskian vanishes**: two angular solutions, `C²` on `[−1, 1]`, have `(1 − s²)(uv' − u'v) = 0` there. -/
theorem wronskian_eq_zero {c χ : ℝ} {u u₁ u₂ v v₁ v₂ : ℝ → ℝ}
    (hu : ∀ s ∈ Icc (-1 : ℝ) 1, HasDerivAt u (u₁ s) s) (hu₁ : ∀ s ∈ Icc (-1 : ℝ) 1, HasDerivAt u₁ (u₂ s) s)
    (hv : ∀ s ∈ Icc (-1 : ℝ) 1, HasDerivAt v (v₁ s) s) (hv₁ : ∀ s ∈ Icc (-1 : ℝ) 1, HasDerivAt v₁ (v₂ s) s)
    (hue : ∀ s ∈ Icc (-1 : ℝ) 1, (1 - s ^ 2) * u₂ s - 2 * s * u₁ s - c ^ 2 * s ^ 2 * u s + χ * u s = 0)
    (hve : ∀ s ∈ Icc (-1 : ℝ) 1, (1 - s ^ 2) * v₂ s - 2 * s * v₁ s - c ^ 2 * s ^ 2 * v s + χ * v s = 0) :
    ∀ s ∈ Icc (-1 : ℝ) 1, (1 - s ^ 2) * (u s * v₁ s - u₁ s * v s) = 0 := by
  intro s hs
  have hW : ∀ x ∈ uIcc s 1, HasDerivAt (fun x => (1 - x ^ 2) * (u x * v₁ x - u₁ x * v x)) 0 x := by
    intro x hx
    rw [uIcc_of_le hs.2] at hx
    have hx' : x ∈ Icc (-1 : ℝ) 1 := ⟨hs.1.trans hx.1, hx.2⟩
    have hp : HasDerivAt (fun s : ℝ => 1 - s ^ 2) (-(2 * x)) x := by
      simpa using ((hasDerivAt_pow 2 x).const_sub 1)
    have := hp.mul (((hu x hx').mul (hv₁ x hx')).sub ((hu₁ x hx').mul (hv x hx')))
    refine this.congr_deriv ?_
    simp only [Pi.sub_apply, Pi.mul_apply]
    linear_combination u x * hve x hx' - v x * hue x hx'
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hW intervalIntegrable_const
  simp only [intervalIntegral.integral_zero, one_pow, sub_self, zero_mul, zero_sub] at h
  linarith

/-- **Uniqueness**: an angular solution with `h(s₀) = h'(s₀) = 0` at some `s₀ ∈ (−1, 1)` vanishes on `(−1, 1)`. -/
theorem eq_zero_of_initial {c χ s₀ : ℝ} {h h₁ h₂ : ℝ → ℝ}
    (hh : ∀ s ∈ Ioo (-1 : ℝ) 1, HasDerivAt h (h₁ s) s) (hh₁ : ∀ s ∈ Ioo (-1 : ℝ) 1, HasDerivAt h₁ (h₂ s) s)
    (he : ∀ s ∈ Ioo (-1 : ℝ) 1, (1 - s ^ 2) * h₂ s - 2 * s * h₁ s - c ^ 2 * s ^ 2 * h s + χ * h s = 0)
    (hs₀ : s₀ ∈ Ioo (-1 : ℝ) 1) (h0 : h s₀ = 0) (h10 : h₁ s₀ = 0) :
    ∀ s ∈ Ioo (-1 : ℝ) 1, h s = 0 := by
  intro t ht
  have hm : max |t| |s₀| < 1 := max_lt (abs_lt.2 ⟨ht.1, ht.2⟩) (abs_lt.2 ⟨hs₀.1, hs₀.2⟩)
  set r := (1 + max |t| |s₀|) / 2 with hr
  have htr : |t| < r := by have := le_max_left |t| |s₀|; rw [hr]; linarith
  have hsr : |s₀| < r := by have := le_max_right |t| |s₀|; rw [hr]; linarith
  have hr0 : 0 ≤ r := (abs_nonneg t).trans htr.le
  have hr1 : r < 1 := by rw [hr]; linarith
  have hr2 : 0 < 1 - r ^ 2 := by nlinarith
  set A := (2 + c ^ 2 + |χ|) / (1 - r ^ 2) with hA
  have hA0 : 0 ≤ A := div_nonneg (by positivity) hr2.le
  let V : ℝ → ℝ × ℝ → ℝ × ℝ := fun x p => (p.2, (2 * x * p.2 + (c ^ 2 * x ^ 2 - χ) * p.1) / (1 - x ^ 2))
  have hsub : ∀ x ∈ Ioo (-r) r, x ∈ Ioo (-1 : ℝ) 1 := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hx2 : ∀ x ∈ Ioo (-r) r, x ^ 2 ≤ r ^ 2 := fun x hx => by
    have : |x| ≤ r := abs_le.2 ⟨hx.1.le, hx.2.le⟩
    nlinarith [sq_abs x, abs_nonneg x]
  have hlip : ∀ x ∈ Ioo (-r) r, LipschitzOnWith (Real.toNNReal (1 + A)) (V x) univ := by
    intro x hx
    apply LipschitzWith.lipschitzOnWith
    apply LipschitzWith.of_dist_le_mul
    intro p q
    rw [Real.coe_toNNReal _ (by linarith)]
    simp only [Prod.dist_eq, Real.dist_eq, V]
    have hxr := hx2 x hx
    have hx1 : |x| ≤ 1 := abs_le.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hpos : 0 < 1 - x ^ 2 := by linarith
    set D := max |p.1 - q.1| |p.2 - q.2|
    have hD1 : |p.1 - q.1| ≤ D := le_max_left _ _
    have hD2 : |p.2 - q.2| ≤ D := le_max_right _ _
    have hD0 : 0 ≤ D := (abs_nonneg _).trans hD1
    refine max_le (by nlinarith) ?_
    have hdiff : (2 * x * p.2 + (c ^ 2 * x ^ 2 - χ) * p.1) / (1 - x ^ 2)
        - (2 * x * q.2 + (c ^ 2 * x ^ 2 - χ) * q.1) / (1 - x ^ 2)
        = (2 * x * (p.2 - q.2) + (c ^ 2 * x ^ 2 - χ) * (p.1 - q.1)) / (1 - x ^ 2) := by
      field_simp; ring
    have hnum : |2 * x * (p.2 - q.2) + (c ^ 2 * x ^ 2 - χ) * (p.1 - q.1)| ≤ (2 + c ^ 2 + |χ|) * D := by
      have hcx : |c ^ 2 * x ^ 2 - χ| ≤ c ^ 2 + |χ| := by
        have : x ^ 2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
        calc |c ^ 2 * x ^ 2 - χ| ≤ |c ^ 2 * x ^ 2| + |χ| := abs_sub _ _
          _ ≤ c ^ 2 + |χ| := by
            rw [abs_of_nonneg (by positivity)]; nlinarith [sq_nonneg c]
      calc |2 * x * (p.2 - q.2) + (c ^ 2 * x ^ 2 - χ) * (p.1 - q.1)|
          ≤ |2 * x * (p.2 - q.2)| + |(c ^ 2 * x ^ 2 - χ) * (p.1 - q.1)| := abs_add_le _ _
        _ = 2 * |x| * |p.2 - q.2| + |c ^ 2 * x ^ 2 - χ| * |p.1 - q.1| := by
            rw [abs_mul, abs_mul, abs_mul, abs_two]
        _ ≤ 2 * 1 * D + (c ^ 2 + |χ|) * D := by
            gcongr
        _ = (2 + c ^ 2 + |χ|) * D := by ring
    rw [hdiff, abs_div, abs_of_pos hpos]
    calc |2 * x * (p.2 - q.2) + (c ^ 2 * x ^ 2 - χ) * (p.1 - q.1)| / (1 - x ^ 2)
        ≤ (2 + c ^ 2 + |χ|) * D / (1 - r ^ 2) :=
          div_le_div₀ (by positivity) hnum hr2 (by linarith)
      _ = A * D := by rw [hA]; ring
      _ ≤ (1 + A) * D := by nlinarith
  have hf : ∀ x ∈ Ioo (-r) r, HasDerivAt (fun x => (h x, h₁ x)) (V x (h x, h₁ x)) x ∧
      (h x, h₁ x) ∈ (univ : Set (ℝ × ℝ)) := by
    intro x hx
    refine ⟨((hh x (hsub x hx)).prodMk (hh₁ x (hsub x hx))).congr_deriv ?_, trivial⟩
    have hpos : 1 - x ^ 2 ≠ 0 := by have := hx2 x hx; nlinarith
    have := he x (hsub x hx)
    simp only [V, Prod.mk.injEq, true_and]
    rw [eq_div_iff hpos]
    linarith
  have hg : ∀ x ∈ Ioo (-r) r, HasDerivAt (fun _ => ((0 : ℝ), (0 : ℝ))) (V x (0, 0)) x ∧
      ((0 : ℝ), (0 : ℝ)) ∈ (univ : Set (ℝ × ℝ)) := by
    intro x _
    refine ⟨(hasDerivAt_const x _).congr_deriv ?_, trivial⟩
    simp [V]
    rfl
  have key := ODE_solution_unique_of_mem_Ioo hlip ⟨by linarith [(abs_lt.1 hsr).1], (abs_lt.1 hsr).2⟩ hf hg
    (by simp [h0, h10])
  exact congrArg Prod.fst (key ⟨(abs_lt.1 htr).1, (abs_lt.1 htr).2⟩)

/-- **Proportionality**: if `v(s₀) ≠ 0` at some `s₀ ∈ (−1, 1)`, an angular solution `u` is `(u(s₀)/v(s₀)) · v` on
`[−1, 1]`. -/
theorem eq_mul_of_ne_zero {c χ s₀ : ℝ} {u u₁ u₂ v v₁ v₂ : ℝ → ℝ}
    (hu : ∀ s ∈ Icc (-1 : ℝ) 1, HasDerivAt u (u₁ s) s) (hu₁ : ∀ s ∈ Icc (-1 : ℝ) 1, HasDerivAt u₁ (u₂ s) s)
    (hv : ∀ s ∈ Icc (-1 : ℝ) 1, HasDerivAt v (v₁ s) s) (hv₁ : ∀ s ∈ Icc (-1 : ℝ) 1, HasDerivAt v₁ (v₂ s) s)
    (hue : ∀ s ∈ Icc (-1 : ℝ) 1, (1 - s ^ 2) * u₂ s - 2 * s * u₁ s - c ^ 2 * s ^ 2 * u s + χ * u s = 0)
    (hve : ∀ s ∈ Icc (-1 : ℝ) 1, (1 - s ^ 2) * v₂ s - 2 * s * v₁ s - c ^ 2 * s ^ 2 * v s + χ * v s = 0)
    (hs₀ : s₀ ∈ Ioo (-1 : ℝ) 1) (hv0 : v s₀ ≠ 0) :
    ∀ s ∈ Icc (-1 : ℝ) 1, u s = u s₀ / v s₀ * v s := by
  set μ := u s₀ / v s₀
  have hIoo : ∀ s ∈ Ioo (-1 : ℝ) 1, s ∈ Icc (-1 : ℝ) 1 := fun s hs => Ioo_subset_Icc_self hs
  have hz := eq_zero_of_initial (c := c) (χ := χ) (h := fun s => u s - μ * v s) (h₁ := fun s => u₁ s - μ * v₁ s)
    (h₂ := fun s => u₂ s - μ * v₂ s)
    (fun s hs => (hu s (hIoo s hs)).sub ((hv s (hIoo s hs)).const_mul μ))
    (fun s hs => (hu₁ s (hIoo s hs)).sub ((hv₁ s (hIoo s hs)).const_mul μ))
    (fun s hs => by linear_combination hue s (hIoo s hs) - μ * hve s (hIoo s hs)) hs₀
    (by simp only [μ]; field_simp; ring)
    (by
      have hW := wronskian_eq_zero hu hu₁ hv hv₁ hue hve s₀ (hIoo s₀ hs₀)
      have hp : 1 - s₀ ^ 2 ≠ 0 := by nlinarith [hs₀.1, hs₀.2]
      have hW' : u s₀ * v₁ s₀ - u₁ s₀ * v s₀ = 0 := (mul_eq_zero.1 hW).resolve_left hp
      simp only [μ]; field_simp; linarith)
  have hcont : ∀ f f' : ℝ → ℝ, (∀ s ∈ Icc (-1 : ℝ) 1, HasDerivAt f (f' s) s) → ContinuousOn f (Icc (-1) 1) :=
    fun f f' hf s hs => (hf s hs).continuousAt.continuousWithinAt
  have heq : EqOn (fun s => u s - μ * v s) (fun _ => (0 : ℝ)) (Icc (-1) 1) :=
    EqOn.of_subset_closure hz ((hcont u u₁ hu).sub ((hcont v v₁ hv).const_smul μ)) continuousOn_const
      Ioo_subset_Icc_self (by rw [closure_Ioo (by norm_num)])
  intro s hs
  have := heq hs
  simp only at this
  linarith

/-- **The eigen relation**: for `g` solving the angular equation and `C²` on `[−1, 1]`, there is `μ` with
`psi c g s = μ · g s` on `[−1, 1]`. -/
theorem eigen_relation {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0) :
    ∃ μ : ℝ, ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s := by
  obtain ⟨h1, h2, h3⟩ := psi_system hg hg₁ hg₂c hang
  have hI : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  rw [hI] at hg hg₁ hang
  by_cases hex : ∃ s₀ ∈ Ioo (-1 : ℝ) 1, g s₀ ≠ 0
  · obtain ⟨s₀, hs₀, hg0⟩ := hex
    exact ⟨_, eq_mul_of_ne_zero (fun s _ => h1 s) (fun s _ => h2 s) hg hg₁
      (fun s _ => by linear_combination -(h3 s)) hang hs₀ hg0⟩
  · push Not at hex
    have hgc : ContinuousOn g (Icc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
    have hg0 : EqOn g (fun _ => (0 : ℝ)) (Icc (-1) 1) :=
      EqOn.of_subset_closure hex hgc continuousOn_const Ioo_subset_Icc_self (by rw [closure_Ioo (by norm_num)])
    refine ⟨0, fun s _ => ?_⟩
    rw [zero_mul]
    unfold psi kint
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun x hx => by
      rw [hI] at hx; simp only [hg0 hx, zero_mul])]
    simp

end Cvs.Prolate.CosineTransformEigenRelation
