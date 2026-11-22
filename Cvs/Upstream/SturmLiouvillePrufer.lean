import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Prüfer form of a Sturm–Liouville pair

For `ψ' = u/p`, `u' = −qψ` with `a² = pq`, `a' = wq` and the energy `E = aψ² + u²/a`, the point
`(X, Y) = (√a ψ/√E, −u/(√a √E))` lies on the unit circle and rotates at the exact rate
`Θ' = a/p + wq uψ/(aE)`: `X' = −Θ'Y`, `Y' = Θ'X`. Hence `ψ = √(E/a) cos Θ` for any `Θ` with that derivative
and the right initial angle: the phase of a rung, with the Liouville–Green rate as its leading term.
-/

namespace Cvs.Upstream.SturmLiouvillePrufer

open Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact

variable {ψ u p q a w : ℝ → ℝ}

/-- The Prüfer rate `Θ' = a/p + wq uψ/(aE)`. -/
noncomputable def rate (p a w q ψ u : ℝ → ℝ) (t : ℝ) : ℝ :=
  a t / p t + w t * q t * (u t * ψ t) / (a t * energy a ψ u t)

/-- The cosine coordinate `X = √a ψ/√E`. -/
noncomputable def X (a ψ u : ℝ → ℝ) (t : ℝ) : ℝ := √(a t) * ψ t / √(energy a ψ u t)

/-- The sine coordinate `Y = −u/(√a √E)`. -/
noncomputable def Y (a ψ u : ℝ → ℝ) (t : ℝ) : ℝ := -(u t / (√(a t) * √(energy a ψ u t)))

/-- **The energy's derivative**: `E' = wq(ψ² − u²/a²)`. -/
theorem hasDerivAt_energy {t : ℝ} (ha : 0 < a t) (hp : p t ≠ 0) (hapq : a t ^ 2 = p t * q t)
    (hψ : HasDerivAt ψ (u t / p t) t) (hu : HasDerivAt u (-(q t * ψ t)) t)
    (haw : HasDerivAt a (w t * q t) t) :
    HasDerivAt (energy a ψ u) (w t * q t * (ψ t ^ 2 - u t ^ 2 / a t ^ 2)) t := by
  have h1 := haw.fun_mul (hψ.fun_mul hψ)
  have h2 := (hu.fun_mul hu).fun_div haw ha.ne'
  have hf : energy a ψ u = fun s => a s * (ψ s * ψ s) + u s * u s / a s := by
    funext s; unfold energy; ring
  rw [hf]
  refine (h1.fun_add h2).congr_deriv ?_
  have hq : q t = a t ^ 2 / p t := by rw [hapq]; field_simp
  rw [hq]
  field_simp
  ring

/-- `X² + Y² = 1` where the energy is positive. -/
theorem X_sq_add_Y_sq {t : ℝ} (ha : 0 < a t) (hE : 0 < energy a ψ u t) :
    X a ψ u t ^ 2 + Y a ψ u t ^ 2 = 1 := by
  unfold X Y
  have hsa : √(a t) ^ 2 = a t := sq_sqrt ha.le
  have hsE : √(energy a ψ u t) ^ 2 = energy a ψ u t := sq_sqrt hE.le
  have hsa0 : √(a t) ≠ 0 := (sqrt_pos.mpr ha).ne'
  have hsE0 : √(energy a ψ u t) ≠ 0 := (sqrt_pos.mpr hE).ne'
  have hEdef : energy a ψ u t = a t * ψ t ^ 2 + u t ^ 2 / a t := by unfold energy; ring
  have hD : a t ^ 2 * ψ t ^ 2 + u t ^ 2 ≠ 0 := by
    have : a t ^ 2 * ψ t ^ 2 + u t ^ 2 = a t * energy a ψ u t := by rw [hEdef]; field_simp
    rw [this]; positivity
  rw [neg_sq, div_pow, div_pow, mul_pow, mul_pow, hsa, hsE, hEdef]
  field_simp

/-- **The rotation**: `X' = −Θ' Y`. -/
theorem hasDerivAt_X {t : ℝ} (ha : 0 < a t) (hp : p t ≠ 0) (hapq : a t ^ 2 = p t * q t)
    (hE : 0 < energy a ψ u t)
    (hψ : HasDerivAt ψ (u t / p t) t) (hu : HasDerivAt u (-(q t * ψ t)) t)
    (haw : HasDerivAt a (w t * q t) t) :
    HasDerivAt (X a ψ u) (-(rate p a w q ψ u t * Y a ψ u t)) t := by
  have hE' := hasDerivAt_energy ha hp hapq hψ hu haw
  have hs := haw.sqrt ha.ne'
  have hr := hE'.sqrt hE.ne'
  have hsE0 : √(energy a ψ u t) ≠ 0 := (sqrt_pos.mpr hE).ne'
  have h := (hs.fun_mul hψ).fun_div hr hsE0
  refine h.congr_deriv ?_
  unfold rate Y
  have hq : q t = a t ^ 2 / p t := by rw [hapq]; field_simp
  have hEdef : energy a ψ u t = a t * ψ t ^ 2 + u t ^ 2 / a t := by unfold energy; ring
  set s := √(a t) with hsdef
  set r := √(energy a ψ u t) with hrdef
  have hs0 : s ≠ 0 := (sqrt_pos.mpr ha).ne'
  have hr0 : r ≠ 0 := hsE0
  have hsa : s ^ 2 = a t := sq_sqrt ha.le
  have hrE : r ^ 2 = energy a ψ u t := sq_sqrt hE.le
  have hcon : r ^ 2 = s ^ 2 * ψ t ^ 2 + u t ^ 2 / s ^ 2 := by rw [hrE, hEdef, ← hsa]
  rw [hq, ← hrE, ← hsa]
  linear_combination (norm := skip) (w t * s ^ 3 * ψ t / (2 * p t * r ^ 3)) * hcon
  field_simp
  ring

/-- **The rotation**: `Y' = Θ' X`. -/
theorem hasDerivAt_Y {t : ℝ} (ha : 0 < a t) (hp : p t ≠ 0) (hapq : a t ^ 2 = p t * q t)
    (hE : 0 < energy a ψ u t)
    (hψ : HasDerivAt ψ (u t / p t) t) (hu : HasDerivAt u (-(q t * ψ t)) t)
    (haw : HasDerivAt a (w t * q t) t) :
    HasDerivAt (Y a ψ u) (rate p a w q ψ u t * X a ψ u t) t := by
  have hE' := hasDerivAt_energy ha hp hapq hψ hu haw
  have hs := haw.sqrt ha.ne'
  have hr := hE'.sqrt hE.ne'
  have hsa0 : √(a t) ≠ 0 := (sqrt_pos.mpr ha).ne'
  have hsE0 : √(energy a ψ u t) ≠ 0 := (sqrt_pos.mpr hE).ne'
  have h := (hu.fun_div (hs.fun_mul hr) (mul_ne_zero hsa0 hsE0)).neg
  refine h.congr_deriv ?_
  unfold rate X
  have hq : q t = a t ^ 2 / p t := by rw [hapq]; field_simp
  have hEdef : energy a ψ u t = a t * ψ t ^ 2 + u t ^ 2 / a t := by unfold energy; ring
  set s := √(a t) with hsdef
  set r := √(energy a ψ u t) with hrdef
  have hs0 : s ≠ 0 := hsa0
  have hr0 : r ≠ 0 := hsE0
  have hsa : s ^ 2 = a t := sq_sqrt ha.le
  have hrE : r ^ 2 = energy a ψ u t := sq_sqrt hE.le
  have hcon : r ^ 2 = s ^ 2 * ψ t ^ 2 + u t ^ 2 / s ^ 2 := by rw [hrE, hEdef, ← hsa]
  rw [hq, ← hrE, ← hsa]
  linear_combination (norm := skip) (w t * s * u t / (2 * p t * r ^ 3)) * hcon
  field_simp
  ring

end Cvs.Upstream.SturmLiouvillePrufer
