import Mathlib
import Cvs.Prolate.Mellin.FrozenRootClosedBounds
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.StepQuadraticRoots

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The companion root and the root gap in closed form

With `√(τ²+1) = a + ib` and `|Im τ| ≤ 1`: `a ≥ |Re τ|` and `|b| ≤ |Im τ|`. The companion of `ρ* = ωζ/(s+2)` is
`ρ₂ = −ω(√(τ²+1) + τ)/(s+2)`, the gap is `ρ* − ρ₂ = 2ω√(τ²+1)/(s+2)`, and
`ω(√(τ²+1) + τ)/(s+2) = ω√(τ²+1)/(s+2) + ((s+1)(s+2) − χ)/(2c(s+2))`.
-/

noncomputable section

open Complex

namespace Cvs.Prolate.Mellin.CompanionRootGap

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity (csqrt csqrt_sq re_csqrt_nonneg omega omega_sq tau zeta rhoStar)
open Cvs.Prolate.Mellin.FrozenRootClosedBounds (csqrt_parts re_csqrt_pos)
open Cvs.Prolate.Mellin.StepQuadraticRoots (comp)

/-- **`a ≥ |Re τ|`** when `|Im τ| ≤ 1`. -/
theorem abs_re_le_re_csqrt {t : ℂ} (ht : t.im ^ 2 ≤ 1) : |t.re| ≤ (csqrt (t ^ 2 + 1)).re := by
  obtain ⟨h1, -⟩ := csqrt_parts t
  have ha := re_csqrt_nonneg (t ^ 2 + 1)
  have hsq : t.re ^ 2 ≤ (csqrt (t ^ 2 + 1)).re ^ 2 := by
    nlinarith [sq_nonneg (csqrt (t ^ 2 + 1)).im]
  exact abs_le_of_sq_le_sq' hsq ha |>.2 |> fun h => by
    rw [abs_le]; exact ⟨by nlinarith [abs_le_of_sq_le_sq' hsq ha], h⟩

/-- **`|b| ≤ |Im τ|`** when `|Im τ| < 1`. -/
theorem abs_im_csqrt_le {t : ℂ} (ht : t.im ^ 2 < 1) : |(csqrt (t ^ 2 + 1)).im| ≤ |t.im| := by
  obtain ⟨-, h2⟩ := csqrt_parts t
  have ha := re_csqrt_pos ht
  have hx := abs_re_le_re_csqrt ht.le
  have e : |(csqrt (t ^ 2 + 1)).im| * (csqrt (t ^ 2 + 1)).re = |t.re| * |t.im| := by
    rw [← abs_of_pos ha, ← abs_mul, ← abs_mul, mul_comm, h2]
  have : |(csqrt (t ^ 2 + 1)).im| * (csqrt (t ^ 2 + 1)).re ≤ |t.im| * (csqrt (t ^ 2 + 1)).re := by
    rw [e, mul_comm |t.re|]; exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
  exact le_of_mul_le_mul_right this ha

/-- `ζ (√(τ²+1) + τ) = 1`. -/
theorem zeta_mul_conj (c χ : ℝ) (s : ℂ) :
    zeta c χ s * (csqrt (tau c χ s ^ 2 + 1) + tau c χ s) = 1 := by
  unfold zeta
  have := csqrt_sq (tau c χ s ^ 2 + 1)
  linear_combination this

/-- **The companion root**: `ρ₂ = −ω(√(τ²+1) + τ)/(s+2)`. -/
theorem comp_rhoStar {c χ : ℝ} {s : ℂ} (hs : s + 3 / 2 ≠ 0) (hs2 : s + 2 ≠ 0) (hω : omega s ≠ 0) :
    comp s (rhoStar c χ s) = -(omega s * (csqrt (tau c χ s ^ 2 + 1) + tau c χ s)) / (s + 2) := by
  have hζ : zeta c χ s ≠ 0 := Cvs.Prolate.Mellin.FrozenRootErrorIdentity.zeta_ne_zero c χ s
  have h1 := zeta_mul_conj c χ s
  have hω2 := omega_sq hs
  have e : comp s (rhoStar c χ s) = -(s + 1) / (omega s * zeta c χ s) := by
    unfold comp rhoStar; field_simp
  rw [e, div_eq_div_iff (mul_ne_zero hω hζ) hs2]
  linear_combination (omega s) ^ 2 * h1 + hω2

/-- **The root gap**: `ρ* − ρ₂ = 2ω√(τ²+1)/(s+2)`. -/
theorem rhoStar_sub_comp {c χ : ℝ} {s : ℂ} (hs : s + 3 / 2 ≠ 0) (hs2 : s + 2 ≠ 0) (hω : omega s ≠ 0) :
    rhoStar c χ s - comp s (rhoStar c χ s) = 2 * omega s * csqrt (tau c χ s ^ 2 + 1) / (s + 2) := by
  rw [comp_rhoStar hs hs2 hω]
  unfold rhoStar zeta
  field_simp
  ring

/-- **The companion root, split**: `ω(√(τ²+1) + τ)/(s+2) = ω√(τ²+1)/(s+2) + ((s+1)(s+2) − χ)/(2c(s+2))`. -/
theorem omega_W {c χ : ℝ} (hc : c ≠ 0) {s : ℂ} (hs : s + 3 / 2 ≠ 0) (hs2 : s + 2 ≠ 0) (hω : omega s ≠ 0) :
    omega s * (csqrt (tau c χ s ^ 2 + 1) + tau c χ s) / (s + 2)
      = omega s * csqrt (tau c χ s ^ 2 + 1) / (s + 2) + ((s + 1) * (s + 2) - χ) / (2 * c * (s + 2)) := by
  have hω2 := omega_sq hs
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  unfold tau
  rw [← hω2]
  field_simp

end Cvs.Prolate.Mellin.CompanionRootGap
