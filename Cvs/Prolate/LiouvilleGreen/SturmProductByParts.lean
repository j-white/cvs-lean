import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The product of solutions of two Sturm–Liouville equations integrates by parts exactly

For `fᵢ' = uᵢ/pᵢ`, `uᵢ' = −qᵢ fᵢ` (`i = 1, 2`), `Z = f₁u₂`, `V = u₁f₂` satisfy
`p₁Z' − p₂V' = D f₁f₂` with `D = p₂q₁ − p₁q₂`, so `∫ σ f₁f₂ = [σ(p₁Z − p₂V)/D] − ∫ (σp₁/D)' Z + ∫ (σp₂/D)' V`
wherever `D ≠ 0`: the non-resonant cross terms gain the frequency mismatch `D`, with no phase function.
-/

namespace Cvs.Prolate.LiouvilleGreen.SturmProductByParts

open intervalIntegral Real Set

variable {f₁ u₁ p₁ q₁ f₂ u₂ p₂ q₂ : ℝ → ℝ}

/-- **The cross identity**: `p₁ (f₁u₂)' − p₂ (u₁f₂)' = (p₂q₁ − p₁q₂) f₁f₂`. -/
theorem cross_identity {t : ℝ} (hp₁ : p₁ t ≠ 0) (hp₂ : p₂ t ≠ 0)
    (hf₁ : HasDerivAt f₁ (u₁ t / p₁ t) t) (hu₁ : HasDerivAt u₁ (-(q₁ t * f₁ t)) t)
    (hf₂ : HasDerivAt f₂ (u₂ t / p₂ t) t) (hu₂ : HasDerivAt u₂ (-(q₂ t * f₂ t)) t) :
    HasDerivAt (fun s => f₁ s * u₂ s) (u₁ t / p₁ t * u₂ t + f₁ t * -(q₂ t * f₂ t)) t ∧
    HasDerivAt (fun s => u₁ s * f₂ s) (-(q₁ t * f₁ t) * f₂ t + u₁ t * (u₂ t / p₂ t)) t ∧
    p₁ t * (u₁ t / p₁ t * u₂ t + f₁ t * -(q₂ t * f₂ t))
      - p₂ t * (-(q₁ t * f₁ t) * f₂ t + u₁ t * (u₂ t / p₂ t))
      = (p₂ t * q₁ t - p₁ t * q₂ t) * (f₁ t * f₂ t) := by
  refine ⟨hf₁.fun_mul hu₂, hu₁.fun_mul hf₂, ?_⟩
  field_simp
  ring

/-- **The cross product integrates by parts.** On `[s, t]`, with `D = p₂q₁ − p₁q₂ ≠ 0`, `σp₁/D` and
`σp₂/D` differentiable with continuous derivatives `α`, `β`, and the pieces continuous,
`∫ σ f₁f₂ = [(σp₁/D) f₁u₂ − (σp₂/D) u₁f₂]_s^t − ∫ α f₁u₂ + ∫ β u₁f₂`. -/
theorem integral_cross {σ α β : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (hp₁ : ∀ r ∈ Icc s t, p₁ r ≠ 0) (hp₂ : ∀ r ∈ Icc s t, p₂ r ≠ 0)
    (hD : ∀ r ∈ Icc s t, p₂ r * q₁ r - p₁ r * q₂ r ≠ 0)
    (hf₁ : ∀ r ∈ Icc s t, HasDerivAt f₁ (u₁ r / p₁ r) r)
    (hu₁ : ∀ r ∈ Icc s t, HasDerivAt u₁ (-(q₁ r * f₁ r)) r)
    (hf₂ : ∀ r ∈ Icc s t, HasDerivAt f₂ (u₂ r / p₂ r) r)
    (hu₂ : ∀ r ∈ Icc s t, HasDerivAt u₂ (-(q₂ r * f₂ r)) r)
    (hA : ∀ r ∈ Icc s t, HasDerivAt (fun r => σ r * p₁ r / (p₂ r * q₁ r - p₁ r * q₂ r)) (α r) r)
    (hB : ∀ r ∈ Icc s t, HasDerivAt (fun r => σ r * p₂ r / (p₂ r * q₁ r - p₁ r * q₂ r)) (β r) r)
    (hαc : ContinuousOn α (Icc s t)) (hβc : ContinuousOn β (Icc s t))
    (hc : ContinuousOn (fun r => σ r * (f₁ r * f₂ r)) (Icc s t))
    (hq₁ : ContinuousOn q₁ (Icc s t)) (hq₂ : ContinuousOn q₂ (Icc s t))
    (hpc₁ : ContinuousOn p₁ (Icc s t)) (hpc₂ : ContinuousOn p₂ (Icc s t)) :
    ∫ r in s..t, σ r * (f₁ r * f₂ r)
      = (σ t * p₁ t / (p₂ t * q₁ t - p₁ t * q₂ t) * (f₁ t * u₂ t)
          - σ t * p₂ t / (p₂ t * q₁ t - p₁ t * q₂ t) * (u₁ t * f₂ t))
        - (σ s * p₁ s / (p₂ s * q₁ s - p₁ s * q₂ s) * (f₁ s * u₂ s)
          - σ s * p₂ s / (p₂ s * q₁ s - p₁ s * q₂ s) * (u₁ s * f₂ s))
        - (∫ r in s..t, α r * (f₁ r * u₂ r)) + ∫ r in s..t, β r * (u₁ r * f₂ r) := by
  have hI : uIcc s t = Icc s t := uIcc_of_le hst
  have cont : ∀ f : ℝ → ℝ, (∀ r ∈ Icc s t, DifferentiableAt ℝ f r) → ContinuousOn f (Icc s t) :=
    fun f hf r hr => (hf r hr).continuousAt.continuousWithinAt
  have hf₁c := cont f₁ fun r hr => (hf₁ r hr).differentiableAt
  have hu₁c := cont u₁ fun r hr => (hu₁ r hr).differentiableAt
  have hf₂c := cont f₂ fun r hr => (hf₂ r hr).differentiableAt
  have hu₂c := cont u₂ fun r hr => (hu₂ r hr).differentiableAt
  set A := fun r => σ r * p₁ r / (p₂ r * q₁ r - p₁ r * q₂ r)
  set B := fun r => σ r * p₂ r / (p₂ r * q₁ r - p₁ r * q₂ r)
  -- the antiderivative
  have hderiv : ∀ r ∈ uIcc s t, HasDerivAt (fun r => A r * (f₁ r * u₂ r) - B r * (u₁ r * f₂ r))
      (α r * (f₁ r * u₂ r) - β r * (u₁ r * f₂ r) + σ r * (f₁ r * f₂ r)) r := by
    intro r hr; rw [hI] at hr
    obtain ⟨hZ, hV, hid⟩ := cross_identity (hp₁ r hr) (hp₂ r hr) (hf₁ r hr) (hu₁ r hr)
      (hf₂ r hr) (hu₂ r hr)
    have h := ((hA r hr).fun_mul hZ).fun_sub ((hB r hr).fun_mul hV)
    refine h.congr_deriv ?_
    have hDr := hD r hr
    simp only [A, B]
    have e : σ r * p₁ r / (p₂ r * q₁ r - p₁ r * q₂ r) * (u₁ r / p₁ r * u₂ r + f₁ r * -(q₂ r * f₂ r))
        - σ r * p₂ r / (p₂ r * q₁ r - p₁ r * q₂ r) * (-(q₁ r * f₁ r) * f₂ r + u₁ r * (u₂ r / p₂ r))
        = σ r * (f₁ r * f₂ r) := by
      have e2 : σ r * p₁ r / (p₂ r * q₁ r - p₁ r * q₂ r) * (u₁ r / p₁ r * u₂ r + f₁ r * -(q₂ r * f₂ r))
          - σ r * p₂ r / (p₂ r * q₁ r - p₁ r * q₂ r) * (-(q₁ r * f₁ r) * f₂ r + u₁ r * (u₂ r / p₂ r))
          = σ r * (p₁ r * (u₁ r / p₁ r * u₂ r + f₁ r * -(q₂ r * f₂ r))
            - p₂ r * (-(q₁ r * f₁ r) * f₂ r + u₁ r * (u₂ r / p₂ r))) / (p₂ r * q₁ r - p₁ r * q₂ r) := by
        ring
      rw [e2, hid, div_eq_iff hDr]
      ring
    linear_combination e
  have iα : IntervalIntegrable (fun r => α r * (f₁ r * u₂ r)) MeasureTheory.volume s t :=
    (hαc.mul (hf₁c.mul hu₂c)).intervalIntegrable_of_Icc hst
  have iβ : IntervalIntegrable (fun r => β r * (u₁ r * f₂ r)) MeasureTheory.volume s t :=
    (hβc.mul (hu₁c.mul hf₂c)).intervalIntegrable_of_Icc hst
  have iσ : IntervalIntegrable (fun r => σ r * (f₁ r * f₂ r)) MeasureTheory.volume s t :=
    hc.intervalIntegrable_of_Icc hst
  have hFTC := integral_eq_sub_of_hasDerivAt hderiv ((iα.sub iβ).add iσ)
  rw [intervalIntegral.integral_add (iα.sub iβ) iσ, intervalIntegral.integral_sub iα iβ] at hFTC
  simp only [A, B] at hFTC
  linarith

end Cvs.Prolate.LiouvilleGreen.SturmProductByParts
