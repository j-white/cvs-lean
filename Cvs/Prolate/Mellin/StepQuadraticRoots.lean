import Mathlib
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Exact identities for the two roots of the step quadratic

For a nonzero root `ρ` of `Q_s(y) = (s+2)y² + qy − (s+1)` put `ρ₂ = −(s+1)/((s+2)ρ)`. Then `ρ + ρ₂ = −q/(s+2)`,
`Q_s(y) = (s+2)(y − ρ)(y − ρ₂)`, `1 − ρ = (1 + q)/((s+2)(1 − ρ₂))`, and if `ρ'` is a root at `s + 2`,
`ρ' − ρ = (2(1 − ρ'²) − (q' − q)ρ')/((s+2)(ρ' − ρ₂))` and `1 + (s+2)ρρ'/(s+1) = (ρ₂ − ρ')/ρ₂`. For `ζ = √(τ²+1) − τ`,
`ζ(τ') − ζ(τ) = −(τ' − τ)(ζ + ζ')/(√(τ²+1) + √(τ'²+1))`.
-/

noncomputable section

open Complex

namespace Cvs.Prolate.Mellin.StepQuadraticRoots

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity (csqrt csqrt_sq)

/-- The step quadratic `Q_s(y) = (s+2)y² + qy − (s+1)`. -/
def Qs (s q y : ℂ) : ℂ := (s + 2) * y ^ 2 + q * y - (s + 1)

/-- The companion root `ρ₂ = −(s+1)/((s+2)ρ)`. -/
def comp (s ρ : ℂ) : ℂ := -(s + 1) / ((s + 2) * ρ)

variable {s q ρ : ℂ}

theorem add_comp (hs2 : s + 2 ≠ 0) (hρ : ρ ≠ 0) (h : Qs s q ρ = 0) : ρ + comp s ρ = -q / (s + 2) := by
  unfold Qs at h; unfold comp
  field_simp
  linear_combination h

theorem mul_comp (hs2 : s + 2 ≠ 0) (hρ : ρ ≠ 0) : (s + 2) * ρ * comp s ρ = -(s + 1) := by
  unfold comp; field_simp

/-- **Factorisation**: `Q_s(y) = (s+2)(y − ρ)(y − ρ₂)`. -/
theorem Qs_eq (hs2 : s + 2 ≠ 0) (hρ : ρ ≠ 0) (h : Qs s q ρ = 0) (y : ℂ) :
    Qs s q y = (s + 2) * (y - ρ) * (y - comp s ρ) := by
  have h1 := add_comp hs2 hρ h
  have h2 := mul_comp hs2 hρ
  have e : q = -(s + 2) * (ρ + comp s ρ) := by rw [h1]; field_simp
  unfold Qs
  rw [e]
  linear_combination -h2

/-- **The distance of the root from `1`**: `1 − ρ = (1 + q)/((s+2)(1 − ρ₂))`. -/
theorem one_sub_root (hs2 : s + 2 ≠ 0) (hρ : ρ ≠ 0) (h : Qs s q ρ = 0) (h1 : 1 - comp s ρ ≠ 0) :
    1 - ρ = (1 + q) / ((s + 2) * (1 - comp s ρ)) := by
  have e := Qs_eq hs2 hρ h 1
  have e1 : Qs s q 1 = 1 + q := by unfold Qs; ring
  rw [e1] at e
  rw [e]
  field_simp

/-- **The step difference of the root**: if `Q_{s+2}(ρ') = 0` with `q' = q(s+2)`, then
`ρ' − ρ = (2(1 − ρ'²) − (q' − q)ρ')/((s+2)(ρ' − ρ₂))`. -/
theorem root_step (hs2 : s + 2 ≠ 0) (hρ : ρ ≠ 0) (h : Qs s q ρ = 0) {q' ρ' : ℂ} (h' : Qs (s + 2) q' ρ' = 0)
    (hd : ρ' - comp s ρ ≠ 0) :
    ρ' - ρ = (2 * (1 - ρ' ^ 2) - (q' - q) * ρ') / ((s + 2) * (ρ' - comp s ρ)) := by
  have e := Qs_eq hs2 hρ h ρ'
  have e1 : Qs s q ρ' = 2 * (1 - ρ' ^ 2) - (q' - q) * ρ' := by
    unfold Qs at h' ⊢; linear_combination h'
  rw [e1] at e
  rw [e]
  field_simp

/-- **`1 + A` by Vieta**: `1 + (s+2)ρρ'/(s+1) = (ρ₂ − ρ')/ρ₂`. -/
theorem one_add_A (hs1 : s + 1 ≠ 0) (hs2 : s + 2 ≠ 0) (hρ : ρ ≠ 0) (ρ' : ℂ) :
    1 + (s + 2) * ρ * ρ' / (s + 1) = (comp s ρ - ρ') / comp s ρ := by
  have hc : comp s ρ ≠ 0 := by
    unfold comp; exact div_ne_zero (neg_ne_zero.mpr hs1) (mul_ne_zero hs2 hρ)
  unfold comp at hc ⊢
  field_simp
  ring

/-- **The `ζ`-difference**: `ζ(τ') − ζ(τ) = −(τ' − τ)(ζ(τ) + ζ(τ'))/(√(τ²+1) + √(τ'²+1))`. -/
theorem zeta_sub (t t' : ℂ) (hd : csqrt (t ^ 2 + 1) + csqrt (t' ^ 2 + 1) ≠ 0) :
    (csqrt (t' ^ 2 + 1) - t') - (csqrt (t ^ 2 + 1) - t)
      = -(t' - t) * ((csqrt (t ^ 2 + 1) - t) + (csqrt (t' ^ 2 + 1) - t'))
          / (csqrt (t ^ 2 + 1) + csqrt (t' ^ 2 + 1)) := by
  have h1 := csqrt_sq (t ^ 2 + 1)
  have h2 := csqrt_sq (t' ^ 2 + 1)
  rw [eq_div_iff hd]
  linear_combination h2 - h1

/-- **The `τ`-difference**: `(ω' − χ/ω') − (ω − χ/ω) = (ω' − ω)(1 + χ/(ωω'))`. -/
theorem tau_num_sub {ω ω' χ : ℂ} (hω : ω ≠ 0) (hω' : ω' ≠ 0) :
    (ω' - χ / ω') - (ω - χ / ω) = (ω' - ω) * (1 + χ / (ω * ω')) := by
  field_simp; ring

end Cvs.Prolate.Mellin.StepQuadraticRoots
