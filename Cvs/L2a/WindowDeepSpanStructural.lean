import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.PrimeTailLimitProfiles
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowFormDeepSpan
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.RegularSolutionEdge
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.Xi.EImageWindowPoisson

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# SPINE-L2a(5) on structural hypotheses, `g₂ ∈ C[−1, 1]` from the angular equation

On `(−1, 1)` the angular equation gives `g₂ = N/(1 − s²)`, `N = 2sg₁ + (c²s² − χ)g`. At `s = 1`, `N(1) = 0`, so
`g₂(s) = −(slope N 1 s)/(1 + s) → −N′(1)/2`, and the derivative-limit theorem for `g₁` makes this limit `g₂(1)`;
`s ↦ −s` gives `s = −1`. With Cvs.L2a.PrimeTailLimitProfiles the deep window bound of Cvs.L2a.WindowFormDeepSpan then needs neither `hE1` nor `ContinuousOn g₂`.
-/
noncomputable section

namespace Cvs.L2a.WindowDeepSpanStructural

open Real Set Filter Topology
open Cvs.L2a.AngularProlateTailPositive (psi)

/-! ### `g₂` is continuous on `[−1, 1]` -/

section Regularity

variable {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}

/-- The numerator `N(s) = 2sg₁(s) + (c²s² − χ)g(s)` of `g₂ = N/(1 − s²)` has derivative
`2g₁ + 2sg₂ + 2c²sg + (c²s² − χ)g₁`. -/
theorem hasDerivAt_num {s : ℝ} (hd : HasDerivAt g (g₁ s) s) (hd₁ : HasDerivAt g₁ (g₂ s) s) :
    HasDerivAt (fun t => 2 * t * g₁ t + (c ^ 2 * t ^ 2 - χ) * g t)
      (2 * g₁ s + 2 * s * g₂ s + 2 * c ^ 2 * s * g s + (c ^ 2 * s ^ 2 - χ) * g₁ s) s := by
  have h1 : HasDerivAt (fun t => 2 * t) 2 s := by simpa using (hasDerivAt_id s).const_mul 2
  have h2 : HasDerivAt (fun t => c ^ 2 * t ^ 2 - χ) (c ^ 2 * (2 * s)) s := by
    simpa using ((hasDerivAt_pow 2 s).const_mul (c ^ 2)).sub_const χ
  exact ((h1.mul hd₁).add (h2.mul hd)).congr_deriv (by ring)

/-- At the right end, `g₂` is left-continuous: `g₂(s) → g₂(1)` as `s → 1⁻`. -/
theorem continuousWithinAt_Iic_one (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0) :
    ContinuousWithinAt g₂ (Iic 1) 1 := by
  have h1 : (1 : ℝ) ∈ uIcc (-1 : ℝ) 1 := by simp
  have hIoo : ∀ s ∈ Ioo (-1 : ℝ) 1, s ∈ uIcc (-1 : ℝ) 1 := fun s hs => by
    rw [uIcc_of_le (by norm_num)]; exact Ioo_subset_Icc_self hs
  set N : ℝ → ℝ := fun t => 2 * t * g₁ t + (c ^ 2 * t ^ 2 - χ) * g t with hN
  set N' := 2 * g₁ 1 + 2 * 1 * g₂ 1 + 2 * c ^ 2 * 1 * g 1 + (c ^ 2 * 1 ^ 2 - χ) * g₁ 1
  have hNd : HasDerivAt N N' 1 := hasDerivAt_num (hg 1 h1) (hg₁ 1 h1)
  have hN1 : N 1 = 0 := by have := hang 1 h1; simp only [hN]; linarith
  have hslope : Tendsto (slope N 1) (𝓝[<] 1) (𝓝 N') :=
    (hasDerivAt_iff_tendsto_slope.mp hNd).mono_left (nhdsWithin_mono _ fun _ h => ne_of_lt h)
  have hlim : Tendsto g₂ (𝓝[<] 1) (𝓝 (-N' / (1 + 1))) := by
    have hden : Tendsto (fun s : ℝ => 1 + s) (𝓝[<] 1) (𝓝 (1 + 1)) :=
      (tendsto_const_nhds.add tendsto_id).mono_left nhdsWithin_le_nhds
    refine (hslope.neg.div hden (by norm_num)).congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (show (-1 : ℝ) < 1 by norm_num)] with s hs
    have hs1 : s - 1 ≠ 0 := by linarith [hs.2]
    have hs2 : 1 + s ≠ 0 := by linarith [hs.1]
    have he := hang s (hIoo s hs)
    simp only [Pi.div_apply]
    rw [slope_def_field, hN1]
    simp only [hN]
    field_simp
    linear_combination he
  have hderiv : HasDerivWithinAt g₁ (-N' / (1 + 1)) (Iic 1) 1 := by
    refine hasDerivWithinAt_Iic_of_tendsto_deriv (s := Ioo (-1) 1)
      (fun s hs => (hg₁ s (hIoo s hs)).differentiableAt.differentiableWithinAt)
      (hg₁ 1 h1).continuousAt.continuousWithinAt (Ioo_mem_nhdsLT (by norm_num)) (hlim.congr' ?_)
    filter_upwards [Ioo_mem_nhdsLT (show (-1 : ℝ) < 1 by norm_num)] with s hs
    exact ((hg₁ s (hIoo s hs)).deriv).symm
  have heq : g₂ 1 = -N' / (1 + 1) :=
    (uniqueDiffWithinAt_Iic 1).eq_deriv _ (hg₁ 1 h1).hasDerivWithinAt hderiv
  rw [← continuousWithinAt_Iio_iff_Iic, ContinuousWithinAt, heq]
  exact hlim

/-- **`g₂ ∈ C[−1, 1]` from the angular equation**: a twice-differentiable solution of
`(1 − s²)g₂ − 2sg₁ − c²s²g + χg = 0` on `[−1, 1]` has `g₂` continuous there. -/
theorem continuousOn_of_angular (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0) :
    ContinuousOn g₂ (uIcc (-1) 1) := by
  have hU : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hneg : ∀ s ∈ uIcc (-1 : ℝ) 1, -s ∈ uIcc (-1 : ℝ) 1 := fun s hs => by
    rw [hU] at hs ⊢; exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
  intro s hs
  rw [hU] at hs
  rcases eq_or_lt_of_le hs.2 with h1 | h1
  · -- `s = 1`
    subst h1
    exact (continuousWithinAt_Iic_one hg hg₁ hang).mono (by rw [hU]; exact Icc_subset_Iic_self)
  rcases eq_or_lt_of_le hs.1 with h0 | h0
  · -- `s = −1`, by the reflection `s ↦ −s`, which preserves the equation
    subst h0
    have hr := continuousWithinAt_Iic_one (g := fun t => g (-t)) (g₁ := fun t => -g₁ (-t))
      (g₂ := fun t => g₂ (-t)) (c := c) (χ := χ)
      (fun t ht => ((hg (-t) (hneg t ht)).comp t (hasDerivAt_neg' t)).congr_deriv (by ring))
      (fun t ht => ((hg₁ (-t) (hneg t ht)).comp t (hasDerivAt_neg' t)).neg.congr_deriv (by ring))
      (fun t ht => by have := hang (-t) (hneg t ht); linear_combination this)
    have hr' : ContinuousWithinAt (fun t => g₂ (-t)) (Iic 1) (-(-1)) := by rwa [neg_neg]
    have hc : ContinuousWithinAt (fun t : ℝ => -t) (Ici (-1)) (-1) := continuous_neg.continuousWithinAt
    have hmaps : MapsTo (fun t : ℝ => -t) (Ici (-1)) (Iic 1) := fun t ht => by
      simp only [mem_Iic, mem_Ici] at ht ⊢; linarith
    have hcomp := hr'.comp hc hmaps
    simp only [Function.comp_def, neg_neg] at hcomp
    exact hcomp.mono (by rw [hU]; exact Icc_subset_Ici_self)
  · -- interior: `g₂ = N/(1 − s²)` near `s`
    have hmem : ∀ t ∈ Ioo (-1 : ℝ) 1, t ∈ uIcc (-1 : ℝ) 1 := fun t ht => by
      rw [hU]; exact Ioo_subset_Icc_self ht
    have hev : (fun t => (2 * t * g₁ t + (c ^ 2 * t ^ 2 - χ) * g t) / (1 - t ^ 2)) =ᶠ[𝓝 s] g₂ := by
      filter_upwards [Ioo_mem_nhds h0 h1] with t ht
      have hd : 1 - t ^ 2 ≠ 0 := by nlinarith [ht.1, ht.2]
      have he := hang t (hmem t ht)
      field_simp
      linear_combination -he
    have hs' : s ∈ uIcc (-1 : ℝ) 1 := hmem s ⟨h0, h1⟩
    have hcont : ContinuousAt (fun t => (2 * t * g₁ t + (c ^ 2 * t ^ 2 - χ) * g t) / (1 - t ^ 2)) s := by
      have hden : ContinuousAt (fun t : ℝ => 1 - t ^ 2) s := by fun_prop
      have hne : (1 : ℝ) - s ^ 2 ≠ 0 := by nlinarith
      have h₁c := (hg₁ s hs').continuousAt
      have h₀c := (hg s hs').continuousAt
      have hnum : ContinuousAt (fun t => 2 * t * g₁ t + (c ^ 2 * t ^ 2 - χ) * g t) s := by fun_prop
      exact hnum.div₀ hden hne
    exact (hcont.congr hev).continuousWithinAt

end Regularity

/-! ### SPINE-L2a(5) on structural hypotheses -/

section Spine

open Cvs.L2a.WindowFormDeepSpan (c0 Hx)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **SPINE-L2a(5)**: `WindowFormDeepSpan`'s deep window bound past `c₀` with neither `hE1` nor continuity of `h₂, g₂`;
the hypotheses are the deep family's structure: angular equation, parity, norms, eigenvalues, counts. -/
theorem L2a_window_deep_closed (i₀ : ι) {h h₁ h₂ : ι → ℝ → ℝ} {g g₁ g₂ : ℝ → ℝ} {c χg μg : ℝ} {χ μ : ι → ℝ}
    (b : ι → ℝ) {m : ℕ} {P R : ℕ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (h i) (h₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (h₁ i) (h₂ i s) s)
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * h₂ i s - 2 * s * h₁ i s - c ^ 2 * s ^ 2 * h i s + χ i * h i s = 0)
    (hc : c0 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hσ : ∀ i, 5 * c ≤ c ^ 2 - χ i) (hχi : Function.Injective χ)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, h i (-s) = h i s) (hnorm : ∀ i, ∫ s in (-1 : ℝ)..1, h i s ^ 2 = 1)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (h i) s = μ i * h i s)
    (hground : (Cvs.Prolate.EdgeCentreSign.evenSpec (Cvs.Prolate.RegularSolutionEdge.sqC c) ∩ Iio (χ i₀)).ncard = 0)
    (hidx : ∀ i, Even (Cvs.Prolate.EdgeCentreSign.evenSpec (Cvs.Prolate.RegularSolutionEdge.sqC c) ∩ Iio (χ i)).ncard)
    (hJ : (Fintype.card ι : ℝ) ≤ c / 4 + 1)
    (hm : 1 ≤ m) (hcount : ∀ i, i ≠ i₀ →
      m ≤ (Cvs.Prolate.EdgeCentreSign.evenSpec (Cvs.Prolate.RegularSolutionEdge.sqC c) ∩ Iio (χ i)).ncard)
    (hgd : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hgd₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hgang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χg * g s = 0)
    (hgeven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hgnorm : ∫ s in (-1 : ℝ)..1, g s ^ 2 = 1)
    (hgμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μg * g s)
    (hgcount : (Cvs.Prolate.EdgeCentreSign.evenSpec (Cvs.Prolate.RegularSolutionEdge.sqC c) ∩ Iio χg).ncard = m)
    (hpole : ∑ i, b i * ∫ s in (-1 : ℝ)..1, h i s = 0)
    (hP : 1 / (2 * π / c) ≤ P) (hR : Real.log (1 / (2 * π / c)) ≤ R * Real.log 2) :
    π / (8 * c * Hx c * (1 + 2 * c / (π * (μ i₀ * √(c / (2 * π))) ^ 2))) * (1 - (μg * √(c / (2 * π))) ^ 2)
        * ∫ θ, Cvs.Xi.EImageWindowPoisson.window (2 * π / c) (fun s => ∑ i, b i * h i s) θ ^ 2
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Cvs.L2a.TailLogScaleTest.logScale
          (Cvs.Xi.EImageWindowPoisson.window (2 * π / c) fun s => ∑ i, b i * h i s)) :=
  Cvs.L2a.PrimeTailLimitProfiles.L2a_window_deep' i₀ b hg hg₁ (fun i => continuousOn_of_angular (hg i) (hg₁ i) (hang i))
    hang hc hχ0 hσ hχi heven hnorm hμ hground hidx hJ hm hcount hgd hgd₁
    (continuousOn_of_angular hgd hgd₁ hgang) hgang hgeven hgnorm hgμ hgcount hpole hP hR

end Spine

end Cvs.L2a.WindowDeepSpanStructural
