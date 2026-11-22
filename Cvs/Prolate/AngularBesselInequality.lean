import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.CosineTransformEigenRelation
import Cvs.Prolate.CosineTransformSignLaw
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.RungMirrorIdentity
import Cvs.Prolate.SlepianCommutingRelation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Angular Bessel: orthogonality, the centre value and the mass of a normalised rung

Angular solutions at distinct levels are orthogonal on `[−1, 1]`; `∫ h = μ h(0)`; Bessel's inequality for the
constant `1` gives `Σ λₙ hₙ(0)² ≤ c/π` with `λ = (μ√(c/2π))²`; a normalised even rung has `∫₁^∞ ψ² = (π/c)(1 − λ)`;
the normalised ground state has `h₀(0)² ≥ ½`; and a rung with `χ ≥ 0` has positive mass on every `[1, X]`, `X > 1`.
-/

noncomputable section

open MeasureTheory Set Real Cvs.Prolate.SlepianCommutingRelation Cvs.L2a.AngularProlateTailPositive

namespace Cvs.Prolate.AngularBesselInequality

/-- **Angular orthogonality**: angular solutions `g` at `χ` and `h` at `χ' ≠ χ`, differentiable twice on `[−1, 1]`,
have `∫_{−1}^{1} g h = 0`. The flux `(1 − s²)(g h' − h g')` has derivative `(χ − χ') g h` and vanishes at `±1`. -/
theorem integral_mul_eq_zero {g g₁ g₂ h h₁ h₂ : ℝ → ℝ} {c χ χ' : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hh : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h (h₁ s) s) (hh₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h₁ (h₂ s) s)
    (hang' : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * h₂ s - 2 * s * h₁ s - c ^ 2 * s ^ 2 * h s + χ' * h s = 0)
    (hne : χ ≠ χ') :
    ∫ s in (-1 : ℝ)..1, g s * h s = 0 := by
  have hd : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (fun s => (1 - s ^ 2) * (g s * h₁ s - h s * g₁ s))
      ((χ - χ') * (g s * h s)) s := by
    intro s hs
    have hp : HasDerivAt (fun s : ℝ => 1 - s ^ 2) (-(2 * s)) s := by
      simpa using ((hasDerivAt_pow 2 s).const_sub 1)
    have := hp.mul (((hg s hs).mul (hh₁ s hs)).sub ((hh s hs).mul (hg₁ s hs)))
    refine this.congr_deriv ?_
    simp only [Pi.mul_apply, Pi.sub_apply]
    linear_combination g s * hang' s hs - h s * hang s hs
  have hgc : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  have hhc : ContinuousOn h (uIcc (-1) 1) := fun s hs => (hh s hs).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable (fun s => (χ - χ') * (g s * h s)) volume (-1) 1 :=
    (continuousOn_const.mul (hgc.mul hhc)).intervalIntegrable
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  rw [intervalIntegral.integral_const_mul] at hF
  norm_num at hF
  rcases hF with h0 | h0
  · exact absurd (sub_eq_zero.mp h0) hne
  · exact h0

/-- **The integral is the centre value**: `psi c g = μ g` on `[−1, 1]` gives `∫_{−1}^{1} g = μ g(0)`. -/
theorem integral_eq_mu_mul {g : ℝ → ℝ} {c μ : ℝ} (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) :
    ∫ s in (-1 : ℝ)..1, g s = μ * g 0 := by
  rw [← hμ 0 ⟨by norm_num, by norm_num⟩]
  unfold psi kint
  simp

/-- `(∫_{−1}^{1} g)² = (2π/c) λ g(0)²` with `λ = (μ√(c/2π))²`, for `c > 0`. -/
theorem integral_sq_eq {g : ℝ → ℝ} {c μ : ℝ} (hc : 0 < c)
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) :
    (∫ s in (-1 : ℝ)..1, g s) ^ 2 = 2 * π / c * (μ * √(c / (2 * π))) ^ 2 * g 0 ^ 2 := by
  have h1 : 2 * π / c * (μ ^ 2 * (c / (2 * π))) = μ ^ 2 := by field_simp
  rw [integral_eq_mu_mul hμ, show (μ * √(c / (2 * π))) ^ 2 = μ ^ 2 * (c / (2 * π)) by
    rw [mul_pow, Real.sq_sqrt (by positivity)]]
  linear_combination (-(g 0 ^ 2)) * h1

/-- **Bessel's inequality on `[−1, 1]`** for a finite family orthonormal there: `Σᵢ (∫ f hᵢ)² ≤ ∫ f²`. -/
theorem sum_sq_integral_le {ι : Type*} [DecidableEq ι] (S : Finset ι) (h : ι → ℝ → ℝ) {f : ℝ → ℝ}
    (hf : ContinuousOn f (uIcc (-1) 1)) (hh : ∀ i ∈ S, ContinuousOn (h i) (uIcc (-1) 1))
    (horth : ∀ i ∈ S, ∀ j ∈ S, ∫ s in (-1 : ℝ)..1, h i s * h j s = if i = j then 1 else 0) :
    ∑ i ∈ S, (∫ s in (-1 : ℝ)..1, f s * h i s) ^ 2 ≤ ∫ s in (-1 : ℝ)..1, f s ^ 2 := by
  classical
  set a : ι → ℝ := fun i => ∫ s in (-1 : ℝ)..1, f s * h i s with ha
  have hI : ∀ {φ : ℝ → ℝ}, ContinuousOn φ (uIcc (-1) 1) → IntervalIntegrable φ volume (-1) 1 :=
    fun hφ => hφ.intervalIntegrable
  have e : ∀ x, (f x - ∑ i ∈ S, a i * h i x) ^ 2 = f x ^ 2 - 2 * ∑ i ∈ S, a i * (f x * h i x)
      + ∑ i ∈ S, ∑ j ∈ S, a i * a j * (h i x * h j x) := by
    intro x
    have h1 : f x * ∑ i ∈ S, a i * h i x = ∑ i ∈ S, a i * (f x * h i x) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    have h2 : (∑ i ∈ S, a i * h i x) ^ 2 = ∑ i ∈ S, ∑ j ∈ S, a i * a j * (h i x * h j x) := by
      rw [sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [sub_sq, ← h2, ← h1]; ring
  have hcS : ContinuousOn (fun x => ∑ i ∈ S, a i * h i x) (uIcc (-1) 1) :=
    continuousOn_finsetSum _ fun i hi => continuousOn_const.mul (hh i hi)
  have hnn : 0 ≤ ∫ s in (-1 : ℝ)..1, (f s - ∑ i ∈ S, a i * h i s) ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun x _ => sq_nonneg _
  have hfh : ∀ i ∈ S, ContinuousOn (fun x => f x * h i x) (uIcc (-1) 1) := fun i hi => hf.mul (hh i hi)
  have hhh : ∀ i ∈ S, ∀ j ∈ S, ContinuousOn (fun x => h i x * h j x) (uIcc (-1) 1) :=
    fun i hi j hj => (hh i hi).mul (hh j hj)
  have hexp : ∫ s in (-1 : ℝ)..1, (f s - ∑ i ∈ S, a i * h i s) ^ 2
      = (∫ s in (-1 : ℝ)..1, f s ^ 2) - ∑ i ∈ S, a i ^ 2 := by
    simp_rw [e]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum, intervalIntegral.integral_finsetSum]
    · have hA : ∀ i ∈ S, ∫ s in (-1 : ℝ)..1, a i * (f s * h i s) = a i ^ 2 := fun i _ => by
        rw [intervalIntegral.integral_const_mul, sq]
      rw [Finset.sum_congr rfl hA]
      have hC : ∀ i ∈ S, ∫ s in (-1 : ℝ)..1, ∑ j ∈ S, a i * a j * (h i s * h j s) = a i ^ 2 := by
        intro i hi
        rw [intervalIntegral.integral_finsetSum (f := fun j s => a i * a j * (h i s * h j s)) fun j hj =>
          hI (continuousOn_const.mul (hhh i hi j hj))]
        simp_rw [intervalIntegral.integral_const_mul]
        have hD : ∀ j ∈ S, a i * a j * (∫ s in (-1 : ℝ)..1, h i s * h j s) = if i = j then a i * a j else 0 :=
          fun j hj => by rw [horth i hi j hj]; split_ifs <;> simp
        rw [Finset.sum_congr rfl hD, Finset.sum_ite_eq S i (fun j => a i * a j)]
        simp [hi, sq]
      rw [Finset.sum_congr rfl hC]
      ring
    · exact fun i hi => hI (continuousOn_finsetSum _ fun j hj => continuousOn_const.mul (hhh i hi j hj))
    · exact fun i hi => hI (continuousOn_const.mul (hfh i hi))
    · exact hI (hf.pow 2)
    · exact hI (continuousOn_const.mul (continuousOn_finsetSum _ fun i hi => continuousOn_const.mul (hfh i hi)))
    · exact hI ((hf.pow 2).sub (continuousOn_const.mul
        (continuousOn_finsetSum _ fun i hi => continuousOn_const.mul (hfh i hi))))
    · exact hI (continuousOn_finsetSum _ fun i hi =>
        continuousOn_finsetSum _ fun j hj => continuousOn_const.mul (hhh i hi j hj))
  linarith

/-- **Normalised angular solutions at distinct levels are orthonormal on `[−1, 1]`.** -/
theorem orthonormal_of_angular {ι : Type*} [DecidableEq ι] (S : Finset ι) {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hχ : Set.InjOn χ S) (hnorm : ∀ i ∈ S, ∫ s in (-1 : ℝ)..1, g i s ^ 2 = 1) :
    ∀ i ∈ S, ∀ j ∈ S, ∫ s in (-1 : ℝ)..1, g i s * g j s = if i = j then 1 else 0 := by
  intro i hi j hj
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    simpa only [sq] using hnorm i hi
  · rw [if_neg hij]
    exact integral_mul_eq_zero (hg i) (hg₁ i) (hang i) (hg j) (hg₁ j) (hang j)
      fun h => hij (hχ hi hj h)

/-- **Angular Bessel**: for normalised angular solutions at distinct levels with `psi c gᵢ = μᵢ gᵢ`,
`Σᵢ λᵢ gᵢ(0)² ≤ c/π`, `λᵢ = (μᵢ√(c/2π))²`. Bessel's inequality for the constant `1`, with `∫ gᵢ = μᵢ gᵢ(0)`. -/
theorem sum_lam_mul_sq_le {ι : Type*} (S : Finset ι) {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ μ : ι → ℝ} (hc : 0 < c)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hχ : Set.InjOn χ S) (hnorm : ∀ i ∈ S, ∫ s in (-1 : ℝ)..1, g i s ^ 2 = 1)
    (hμ : ∀ i ∈ S, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (g i) s = μ i * g i s) :
    ∑ i ∈ S, (μ i * √(c / (2 * π))) ^ 2 * g i 0 ^ 2 ≤ c / π := by
  classical
  have hB := sum_sq_integral_le S g (f := fun _ => 1) continuousOn_const
    (fun i _ s hs => (hg i s hs).continuousAt.continuousWithinAt)
    (orthonormal_of_angular S hg hg₁ hang hχ hnorm)
  simp only [one_mul, one_pow, intervalIntegral.integral_const, smul_eq_mul, mul_one] at hB
  have e : ∀ i ∈ S, (∫ s in (-1 : ℝ)..1, g i s) ^ 2
      = 2 * π / c * ((μ i * √(c / (2 * π))) ^ 2 * g i 0 ^ 2) := fun i hi => by
    rw [integral_sq_eq hc (hμ i hi)]; ring
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum] at hB
  have h2 : (1 : ℝ) - -1 = 2 := by norm_num
  rw [h2] at hB
  rw [div_mul_eq_mul_div, div_le_iff₀ hc] at hB
  rw [le_div_iff₀ pi_pos]
  linarith

/-- For even `g` continuous on `[−1, 1]`, `∫_{−1}^{1} g² = 2 ∫₀¹ g²`. -/
theorem integral_sq_even {g : ℝ → ℝ} (hgc : ContinuousOn g (Icc (-1 : ℝ) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) :
    ∫ s in (-1 : ℝ)..1, g s ^ 2 = 2 * ∫ s in (0 : ℝ)..1, g s ^ 2 := by
  have hc2 : ContinuousOn (fun s => g s ^ 2) (Icc (-1 : ℝ) 1) := hgc.pow 2
  have hi1 : IntervalIntegrable (fun s => g s ^ 2) volume (-1) 0 :=
    (hc2.mono (by rw [uIcc_of_le (by norm_num)]; exact Icc_subset_Icc le_rfl (by norm_num))).intervalIntegrable
  have hi2 : IntervalIntegrable (fun s => g s ^ 2) volume 0 1 :=
    (hc2.mono (by rw [uIcc_of_le (by norm_num)]; exact Icc_subset_Icc (by norm_num) le_rfl)).intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  have hneg : ∫ s in (-1 : ℝ)..0, g s ^ 2 = ∫ s in (0 : ℝ)..1, g s ^ 2 := by
    have := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1) (fun s => g s ^ 2)
    simp only [neg_zero] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le zero_le_one] at hs
    simp only [heven s ⟨by linarith [hs.1], hs.2⟩]
  rw [hneg]; ring

/-- **The mass of a normalised rung**: for even `g` with `∫_{−1}^{1} g² = 1` and `psi c g = μ g`,
`∫₁^∞ ψ² = (π/c)(1 − λ)` with `λ = (μ√(c/2π))²`. -/
theorem mass_eq {g : ℝ → ℝ} {c μ : ℝ} (hc : 0 < c) (hgc : ContinuousOn g (Icc (-1 : ℝ) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s)
    (hnorm : ∫ s in (-1 : ℝ)..1, g s ^ 2 = 1) :
    ∫ ξ in Ioi 1, psi c g ξ ^ 2 = π / c * (1 - (μ * √(c / (2 * π))) ^ 2) := by
  have hN := Cvs.Prolate.RungMirrorIdentity.norm_psi_sq hc hgc heven
  have hT := Cvs.Prolate.RungMirrorIdentity.tau_sq_mul hc hgc heven hμ
  have hhalf : ∫ x in (0 : ℝ)..1, g x ^ 2 = 1 / 2 := by
    have := integral_sq_even hgc heven; rw [hnorm] at this; linarith
  rw [hhalf] at hN
  have hm := Cvs.Prolate.RungMirrorIdentity.memLp_psi hc hgc heven
  have hInt : IntegrableOn (fun x => psi c g x ^ 2) (Ioi 0) := by
    have := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).1 hm
    refine this.congr (ae_of_all _ fun x => ?_)
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hsplit : ∫ x in Ioi 0, psi c g x ^ 2 = (∫ x in (0 : ℝ)..1, psi c g x ^ 2) + ∫ x in Ioi 1, psi c g x ^ 2 := by
    rw [intervalIntegral.integral_of_le zero_le_one, ← setIntegral_union (Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi (hInt.mono_set Ioc_subset_Ioi_self) (hInt.mono_set (Ioi_subset_Ioi zero_le_one)),
      Ioc_union_Ioi_eq_Ioi zero_le_one]
  set A := ∫ x in Ioi 0, psi c g x ^ 2
  have hA : A = π / c := by
    have hk : c / (2 * π) ≠ 0 := by positivity
    field_simp at hN ⊢
    linarith
  rw [← hT] at hsplit
  have : ∫ x in Ioi 1, psi c g x ^ 2 = A - (μ * √(c / (2 * π))) ^ 2 * A := by linarith
  rw [this, hA]; ring

/-- **The normalised ground state has `h₀(0)² ≥ ½`**: it has no zero and `h₀(1) h₀` decreases on `[0, 1]`
(Cvs.Prolate.EdgeCentreSign), so `1 = 2 ∫₀¹ h₀² ≤ 2 h₀(0)²`. -/
theorem half_le_ground_sq {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s)
    (h0 : (Cvs.Prolate.EdgeCentreSign.evenSpec (Cvs.Prolate.RegularSolutionEdge.sqC c) ∩ Iio χ).ncard = 0)
    (hnorm : ∫ s in (-1 : ℝ)..1, g s ^ 2 = 1) :
    1 / 2 ≤ g 0 ^ 2 := by
  have hI : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hgc : ContinuousOn g (Icc (-1 : ℝ) 1) := fun s hs =>
    (hg s (by rwa [hI])).continuousAt.continuousWithinAt
  have hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : ∫ s in (-1 : ℝ)..1, g s ^ 2 = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun s hs => by
        rw [hI] at hs; simp [hcon s hs]]
      simp
    linarith
  have hpos := Cvs.Prolate.EdgeCentreSign.ground_pos hg hg₁ hang heven hg0 h0
  have hanti := Cvs.Prolate.EdgeCentreSign.ground_antitoneOn hg hg₁ hang heven hg0 h0
  have hle : ∀ s ∈ Icc (0 : ℝ) 1, g s ^ 2 ≤ g 0 ^ 2 := by
    intro s hs
    have hs' : s ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hs.1], hs.2⟩
    have h1 : g 1 * g s ≤ g 1 * g 0 := hanti ⟨le_rfl, zero_le_one⟩ hs hs.1
    have h2 : 0 < g s * g 1 := hpos s hs'
    have h3 : (g 1 * g s) ^ 2 ≤ (g 1 * g 0) ^ 2 := by
      have : 0 ≤ g 1 * g s := by linarith [mul_comm (g s) (g 1)]
      exact pow_le_pow_left₀ this h1 2
    have hg1 : 0 < g 1 ^ 2 := by
      have : g 1 ≠ 0 := fun h => by rw [h, mul_zero] at h2; exact lt_irrefl 0 h2
      positivity
    rw [mul_pow, mul_pow] at h3
    exact le_of_mul_le_mul_left h3 hg1
  have hint : ∫ s in (0 : ℝ)..1, g s ^ 2 ≤ g 0 ^ 2 := by
    have := intervalIntegral.integral_mono_on zero_le_one
      (ContinuousOn.intervalIntegrable_of_Icc zero_le_one ((hgc.mono (Icc_subset_Icc (by norm_num) le_rfl)).pow 2))
      (intervalIntegrable_const (μ := volume)) hle
    simpa using this
  have := integral_sq_even hgc heven
  rw [hnorm] at this
  linarith

/-- **Positive mass from the edge** (hM): an even angular solution `g ≢ 0` with `χ ≥ 0` and `c > 0` has
`0 < ∫₁^X ψ²` for every `X > 1`, since `ψ(1) = μ g(1) ≠ 0` (Cvs.Prolate.CosineTransformSignLaw.mu_sign) and `ψ` is continuous. -/
theorem mass_pos_of_edge {g g₁ g₂ : ℝ → ℝ} {c χ X : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0)
    (hc : 0 < c) (hχ : 0 ≤ χ) (hX : 1 < X) :
    0 < ∫ ξ in (1 : ℝ)..X, psi c g ξ ^ 2 := by
  obtain ⟨μ, hμ⟩ := Cvs.Prolate.CosineTransformEigenRelation.eigen_relation hg hg₁ hg₂c hang
  have hm := Cvs.Prolate.CosineTransformSignLaw.mu_sign hc hχ hg hg₁ hg₂c hang heven hg0 hμ
  have h1 : psi c g 1 ≠ 0 := by
    rw [hμ 1 ⟨by norm_num, le_rfl⟩]
    intro h
    rcases mul_eq_zero.mp h with h' | h'
    · rw [h', zero_mul] at hm; exact lt_irrefl 0 hm
    · rw [h', mul_zero, mul_zero] at hm; exact lt_irrefl 0 hm
  obtain ⟨hψ, -, -⟩ := psi_system hg hg₁ hg₂c hang
  have hcont : ContinuousOn (fun ξ => psi c g ξ ^ 2) (Icc 1 X) :=
    fun ξ _ => ((hψ ξ).continuousAt.pow 2).continuousWithinAt
  have := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (f := fun _ => (0 : ℝ)) (g := fun ξ => psi c g ξ ^ 2) hX continuousOn_const hcont
    (fun ξ _ => sq_nonneg _) ⟨1, ⟨le_rfl, hX.le⟩, by positivity⟩
  simpa using this

/-- **hM on a family**: every rung of a family of even angular solutions `gᵢ ≢ 0` with `χᵢ ≥ 0` has
`0 < ∫₁^X ψᵢ²`, the form Cvs.L2a.PerLevelFarLeak, Cvs.L2a.RungSpanLowMass and Cvs.L2a.LowConstantUniform take. -/
theorem hM_of_angular {ι : Type*} {g g₁ g₂ : ι → ℝ → ℝ} {c X : ℝ} {χ : ι → ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s) (hg0 : ∀ i, ∃ s ∈ Icc (-1 : ℝ) 1, g i s ≠ 0)
    (hc : 0 < c) (hχ0 : ∀ i, 0 ≤ χ i) (hX : 1 < X) :
    ∀ i, 0 < ∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2 := fun i =>
  mass_pos_of_edge (hg i) (hg₁ i) (hg₂c i) (hang i) (heven i) (hg0 i) hc (hχ0 i) hX

end Cvs.Prolate.AngularBesselInequality
