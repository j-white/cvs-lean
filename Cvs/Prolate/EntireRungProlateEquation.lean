import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.RungProfileEntireExtension

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The prolate equation for the entire extension of a rung

The entire extension `H_k(z) = ψ_{h_k}(z)/μ_k` of a rung agrees with `h_k` on `[−1, 1]`, so its first two complex
derivatives restrict to `h_k′, h_k″` on `(−1, 1)`. The entire function `(1 − z²)H″ − 2zH′ + (χ_k − c²z²)H` then
vanishes on `(−1, 1)`, hence everywhere by the identity theorem.
-/

noncomputable section

open Real Set Complex Filter Topology
open Cvs.Prolate.EvenRungsByIndex (rung rung₁ rung₂ muR lev IsLevelIdx rung_spec psi_rung)

namespace Cvs.Prolate.EntireRungProlateEquation
open Cvs.ZeroCounting

/-- The entire extension `H_k(z) = ψ_{h_k}(z)/μ_k` of the rung `h_k` at bandwidth `c`. -/
def Hk (c : ℝ) (k : ℕ) (z : ℂ) : ℂ := Cvs.Prolate.RungProfileEntireExtension.psiC c (rung c k) z / muR c k

/-- `H_k` is entire. -/
theorem differentiable_Hk {c : ℝ} {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) : Differentiable ℂ (Hk c k) :=
  (Cvs.Prolate.RungProfileEntireExtension.differentiable_psiC c (Cvs.Prolate.RungProfileEntireExtension.intervalIntegrable_rung h)).div_const _

/-- `H_k = h_k` on `[−1, 1]`. -/
theorem Hk_ofReal {c : ℝ} {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) (hμ : muR c k ≠ 0) {s : ℝ}
    (hs : s ∈ Icc (-1 : ℝ) 1) : Hk c k s = (rung c k s : ℂ) := by
  unfold Hk
  rw [Cvs.Prolate.RungProfileEntireExtension.psiC_ofReal, psi_rung h s hs]
  have e : ((muR c k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hμ
  push_cast
  field_simp

/-- The real derivative of `t ↦ F(t)` at a real point is the complex derivative of an entire `F`. -/
theorem deriv_ofReal_eq {F : ℂ → ℂ} (hF : Differentiable ℂ F) {f f₁ : ℝ → ℝ} {t : ℝ} {U : Set ℝ}
    (hU : U ∈ 𝓝 t) (hFf : ∀ y ∈ U, F y = (f y : ℂ)) (hf : HasDerivAt f (f₁ t) t) :
    deriv F t = (f₁ t : ℂ) := by
  have h1 : HasDerivAt (fun y : ℝ => F y) (deriv F t) t := (hF t).hasDerivAt.comp_ofReal
  have h2 : HasDerivAt (fun y : ℝ => F y) (f₁ t : ℂ) t :=
    (hf.ofReal_comp).congr_of_eventuallyEq (Filter.eventually_of_mem hU fun y hy => hFf y hy)
  exact h1.unique h2

/-- **The prolate equation for the entire extension**: `(1 − z²)H_k″ − 2zH_k′ + (χ_k − c²z²)H_k = 0` on `ℂ`. -/
theorem ode_Hk {c : ℝ} {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) (hμ : muR c k ≠ 0) (z : ℂ) :
    (1 - z ^ 2) * deriv (deriv (Hk c k)) z - 2 * z * deriv (Hk c k) z + (lev c k - c ^ 2 * z ^ 2) * Hk c k z = 0 := by
  obtain ⟨hg, hg₁, -, hang, -, -⟩ := rung_spec h
  set F := Hk c k with hFd
  have hF : Differentiable ℂ F := differentiable_Hk h
  have hF' : Differentiable ℂ (deriv F) := fun w =>
    ((hF.differentiableOn.deriv isOpen_univ) w (mem_univ w)).differentiableAt (isOpen_univ.mem_nhds (mem_univ w))
  have hF'' : Differentiable ℂ (deriv (deriv F)) := fun w =>
    ((hF'.differentiableOn.deriv isOpen_univ) w (mem_univ w)).differentiableAt (isOpen_univ.mem_nhds (mem_univ w))
  have hI : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hIoo : ∀ y ∈ Ioo (-1 : ℝ) 1, y ∈ uIcc (-1 : ℝ) 1 := fun y hy => by rw [hI]; exact Ioo_subset_Icc_self hy
  -- first derivative on `(−1, 1)`
  have hd1 : ∀ t ∈ Ioo (-1 : ℝ) 1, deriv F t = (rung₁ c k t : ℂ) := fun t ht =>
    deriv_ofReal_eq hF (isOpen_Ioo.mem_nhds ht) (fun y hy => Hk_ofReal h hμ (Ioo_subset_Icc_self hy))
      (hg t (hIoo t ht))
  have hd2 : ∀ t ∈ Ioo (-1 : ℝ) 1, deriv (deriv F) t = (rung₂ c k t : ℂ) := fun t ht =>
    deriv_ofReal_eq hF' (isOpen_Ioo.mem_nhds ht) (fun y hy => hd1 y hy) (hg₁ t (hIoo t ht))
  set E : ℂ → ℂ := fun w => (1 - w ^ 2) * deriv (deriv F) w - 2 * w * deriv F w + (lev c k - c ^ 2 * w ^ 2) * F w
    with hEd
  have hE : Differentiable ℂ E := by
    simp only [hEd]
    exact (((differentiable_const _).sub (differentiable_id.pow 2)).mul hF'').sub
      (((differentiable_const _).mul differentiable_id).mul hF') |>.add
      (((differentiable_const _).sub ((differentiable_const _).mul (differentiable_id.pow 2))).mul hF)
  have hEt : ∀ t ∈ Ioo (-1 : ℝ) 1, E t = 0 := fun t ht => by
    simp only [hEd]
    rw [hd1 t ht, hd2 t ht, show F (t : ℂ) = (rung c k t : ℂ) from Hk_ofReal h hμ (Ioo_subset_Icc_self ht)]
    have := hang t (hIoo t ht)
    have e : ((((1 - t ^ 2) * rung₂ c k t - 2 * t * rung₁ c k t - c ^ 2 * t ^ 2 * rung c k t
        + lev c k * rung c k t : ℝ)) : ℂ) = 0 := by rw [this]; simp
    push_cast at e
    linear_combination e
  -- frequently near `0`
  have hfreq : ∃ᶠ w in 𝓝[≠] (0 : ℂ), E w = (0 : ℂ → ℂ) w := by
    set u : ℕ → ℂ := fun n => ((1 / ((n : ℝ) + 2) : ℝ) : ℂ) with hud
    have hu0 : Tendsto u atTop (𝓝 0) := by
      have h2 : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
        tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
      have : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 2) : ℝ)) atTop (𝓝 0) := by
        simpa [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp h2
      have := (Complex.continuous_ofReal.tendsto 0).comp this
      simpa [hud, Function.comp_def] using this
    have hune : ∀ n, u n ∈ ({0}ᶜ : Set ℂ) := fun n => by
      simp only [hud, mem_compl_iff, mem_singleton_iff, Complex.ofReal_eq_zero]
      positivity
    have hu : Tendsto u atTop (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨hu0, Eventually.of_forall hune⟩
    refine hu.frequently (Frequently.of_forall fun n => ?_)
    have hmem : (1 / ((n : ℝ) + 2) : ℝ) ∈ Ioo (-1 : ℝ) 1 := by
      have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      constructor
      · have : 0 < 1 / ((n : ℝ) + 2) := by positivity
        linarith
      · rw [div_lt_one h2]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    simpa [hud] using hEt _ hmem
  have hEq := AnalyticOnNhd.eq_of_frequently_eq (analyticOnNhd_univ_iff_differentiable.2 hE)
    (analyticOnNhd_univ_iff_differentiable.2 (differentiable_const (0 : ℂ))) hfreq
  exact congrFun hEq z

end Cvs.Prolate.EntireRungProlateEquation

end
