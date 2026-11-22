import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.Envelope.RungExteriorLaw
import Cvs.Prolate.EvenRungParseval
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.SincTopIsRung

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Karnik–Romberg–Davenport count on the rungs, from the count for the sinc operator

The time–band limiting operator on `L²[−1, 1]` has kernel `(c/π)·sinc(c(s − t))`. An even `g` with `ψ_c g = μ g`
is its eigenfunction with eigenvalue `(c/2π)μ²`, since `sinc(c d) = ½∫_{−1}^{1} cos(c d v) dv`. The rungs `h_{4j}`
are orthonormal on `[−1, 1]`, so Karnik–Romberg–Davenport Theorem 3 bounds their count in `(ε, 1 − ε)`.
-/

noncomputable section

open Real Set Filter Finset MeasureTheory
open Cvs.Prolate.EvenRungsByIndex (IsLevelIdx rung rung_spec lamR muR psi_rung continuousOn_rung)
open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.Prolate.SincTopIsRung (clampExt clampExt_of_mem continuous_clampExt clampExt_neg psi_clampExt)

namespace Cvs.Prolate.SincOperatorEigenCount
open Cvs.ZeroCounting

/-! ### The sinc kernel -/

/-- The kernel `sin(c(s − t))/(π(s − t))` of the time–band limiting operator on `[−1, 1]`. -/
def sincKer (c s t : ℝ) : ℝ := c / π * sinc (c * (s - t))

/-- `∫_{−1}^{1} cos(a v) dv = 2 sinc a`. -/
theorem integral_cos_mul (a : ℝ) : ∫ v in (-1 : ℝ)..1, cos (a * v) = 2 * sinc a := by
  by_cases ha : a = 0
  · subst ha; norm_num
  · rw [intervalIntegral.integral_comp_mul_left (fun v => cos v) ha, integral_cos, smul_eq_mul,
      sinc_of_ne_zero ha, mul_neg, mul_one, sin_neg]
    field_simp
    ring

/-- The odd moment `∫_{−1}^{1} G(t) sin(a t) dt` of an even `G` vanishes. -/
theorem integral_even_mul_sin {G : ℝ → ℝ} (heven : ∀ t, G (-t) = G t) (a : ℝ) :
    ∫ t in (-1 : ℝ)..1, G t * sin (a * t) = 0 := by
  have h := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 1) (fun t => G t * sin (a * t))
  simp only [neg_neg, heven, mul_neg, sin_neg, intervalIntegral.integral_neg] at h
  linarith

/-- **An even eigenfunction of the finite cosine transform is an eigenfunction of the sinc operator**:
`∫_{−1}^{1} (c/π)sinc(c(s − t)) g(t) dt = (c/2π)μ² g(s)` when `ψ_c g = μ g` on `[−1, 1]`. -/
theorem integral_sincKer_mul {c μ : ℝ} {g : ℝ → ℝ} (hg : ContinuousOn g (Icc (-1) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hpsi : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s)
    {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    ∫ t in (-1 : ℝ)..1, sincKer c s t * g t = c / (2 * π) * μ ^ 2 * g s := by
  set G := clampExt g with hGdef
  have hGc : Continuous G := continuous_clampExt hg
  have hGe : ∀ t, G (-t) = G t := clampExt_neg heven
  have hIcc : ∀ {t : ℝ}, t ∈ uIcc (-1 : ℝ) 1 → t ∈ Icc (-1 : ℝ) 1 := fun ht => by
    rwa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
  have hpsiG : ∀ v ∈ Icc (-1 : ℝ) 1, ∫ t in (-1 : ℝ)..1, G t * cos (c * v * t) = μ * G v := by
    intro v hv
    have := psi_clampExt (c := c) (h := g) v
    rw [show psi c G v = ∫ t in (-1 : ℝ)..1, G t * cos (c * v * t) from rfl] at this
    rw [this, hpsi v hv, hGdef, clampExt_of_mem hv]
  -- step 1: replace `g` by `G` and write the kernel as an integral
  have e1 : ∫ t in (-1 : ℝ)..1, sincKer c s t * g t
      = ∫ t in (-1 : ℝ)..1, ∫ v in (-1 : ℝ)..1, c / (2 * π) * (G t * cos (c * (s - t) * v)) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_cos_mul,
      hGdef, clampExt_of_mem (hIcc ht), sincKer]
    field_simp
  -- step 2: swap the order
  have hF : Continuous (fun p : ℝ × ℝ => c / (2 * π) * (G p.1 * cos (c * (s - p.1) * p.2))) := by
    fun_prop
  have hint : Integrable (Function.uncurry fun t v : ℝ => c / (2 * π) * (G t * cos (c * (s - t) * v)))
      ((volume.restrict (Ioc (-1 : ℝ) 1)).prod (volume.restrict (Ioc (-1 : ℝ) 1))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have e2 : ∫ t in (-1 : ℝ)..1, ∫ v in (-1 : ℝ)..1, c / (2 * π) * (G t * cos (c * (s - t) * v))
      = ∫ v in (-1 : ℝ)..1, ∫ t in (-1 : ℝ)..1, c / (2 * π) * (G t * cos (c * (s - t) * v)) := by
    simp only [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact integral_integral_swap hint
  -- step 3: the inner integral is `cos(csv)·μG(v)`
  have e3 : ∀ v ∈ uIcc (-1 : ℝ) 1, ∫ t in (-1 : ℝ)..1, c / (2 * π) * (G t * cos (c * (s - t) * v))
      = c / (2 * π) * (μ * (G v * cos (c * s * v))) := by
    intro v hv
    have hexp : ∀ t, G t * cos (c * (s - t) * v)
        = cos (c * s * v) * (G t * cos (c * v * t)) + sin (c * s * v) * (G t * sin (c * v * t)) := by
      intro t
      rw [show c * (s - t) * v = c * s * v - c * v * t by ring, cos_sub]
      ring
    have hi1 : IntervalIntegrable (fun t => cos (c * s * v) * (G t * cos (c * v * t))) volume (-1) 1 :=
      (by fun_prop : Continuous fun t => cos (c * s * v) * (G t * cos (c * v * t))).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun t => sin (c * s * v) * (G t * sin (c * v * t))) volume (-1) 1 :=
      (by fun_prop : Continuous fun t => sin (c * s * v) * (G t * sin (c * v * t))).intervalIntegrable _ _
    rw [intervalIntegral.integral_const_mul]
    simp only [hexp]
    rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, hpsiG v (hIcc hv), integral_even_mul_sin hGe]
    ring
  -- step 4: the outer integral is `μ ψ_c G(s) = μ² g(s)`
  rw [e1, e2, intervalIntegral.integral_congr e3, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  have e4 : ∫ v in (-1 : ℝ)..1, G v * cos (c * s * v) = μ * g s := by
    rw [hpsiG s hs, hGdef, clampExt_of_mem hs]
  rw [e4]
  ring

/-! ### The rungs -/

/-- **The rung `h_k` is an eigenfunction of the sinc operator with eigenvalue `λ_k`.** -/
theorem integral_sincKer_mul_rung {c : ℝ} (hc : 0 < c) {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ)
    {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    ∫ t in (-1 : ℝ)..1, sincKer c s t * rung c k t = lamR c k * rung c k s := by
  obtain ⟨-, -, -, -, heven, -⟩ := rung_spec h
  rw [integral_sincKer_mul (continuousOn_rung h) heven (psi_rung h) hs,
    Cvs.Prolate.Envelope.RungExteriorLaw.lamR_eq hc]
  ring

/-- **The rungs are orthonormal on `[−1, 1]`.** -/
theorem integral_rung_mul_rung_eq {c : ℝ} {k k' : ℕ} (h : ∃ χ, IsLevelIdx c k χ) (h' : ∃ χ, IsLevelIdx c k' χ) :
    ∫ s in (-1 : ℝ)..1, rung c k s * rung c k' s = if k = k' then 1 else 0 := by
  split_ifs with hk
  · subst hk
    obtain ⟨-, -, -, -, -, hn⟩ := rung_spec h
    simpa only [sq] using hn
  · exact Cvs.Prolate.EvenRungParseval.integral_rung_mul_rung (k := ⟨k, h⟩) (j := ⟨k', h'⟩)
      fun he => hk (congrArg Subtype.val he)

end Cvs.Prolate.SincOperatorEigenCount

end
