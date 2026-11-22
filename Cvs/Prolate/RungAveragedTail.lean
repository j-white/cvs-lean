import Mathlib
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Upstream.SturmLiouvillePrufer

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The averaged tail of a rung

In Prüfer form `ψ² = (E/a)X²` with `X² + Y² = 1` and `(XY)′ = Θ′(X² − Y²)`, `Θ′ = (a/p)(1 + ε)`, `ε = w·uψ/E`, so
`ψ² = E/(2a) + (E/(2q))(XY)′ − (E/(2q))(ε/(1 + ε))(XY)′` pointwise: half the pointwise envelope, an exact derivative,
and a term of relative size `ε`. Integrated over `[b, t]` with `E ≤ G`, `w ≤ W < 2` and `|ε| ≤ w/2`,
`∫_b^t ψ² ≤ (G/(4c))log((b+1)/(b−1))·(1 + (W/2)(1 + W/2)/(1 − W/2)) + G/(c²(b² − 1))`: `RungGramFloorAtInfinity`'s tail bound halved.
-/

namespace Cvs.Prolate.RungAveragedTail

open Real Set intervalIntegral MeasureTheory Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Upstream.SturmLiouvillePrufer

/-- **The pointwise decomposition of `ψ²`** in Prüfer form. -/
theorem psi_sq_decomp {p a w q ψ u : ℝ → ℝ} {t : ℝ} (ha : 0 < a t) (hp : p t ≠ 0) (hq : q t ≠ 0)
    (hapq : a t ^ 2 = p t * q t) (hE : 0 < energy a ψ u t)
    (hε : 1 + w t * (u t * ψ t) / energy a ψ u t ≠ 0) :
    ψ t ^ 2 = energy a ψ u t / (2 * a t)
      + energy a ψ u t / (2 * q t) * (rate p a w q ψ u t * (X a ψ u t ^ 2 - Y a ψ u t ^ 2))
      - energy a ψ u t / (2 * q t) * ((w t * (u t * ψ t) / energy a ψ u t)
          / (1 + w t * (u t * ψ t) / energy a ψ u t)) * (rate p a w q ψ u t * (X a ψ u t ^ 2 - Y a ψ u t ^ 2)) := by
  have hXY := X_sq_add_Y_sq (ψ := ψ) (u := u) ha hE
  have hsa : √(a t) ^ 2 = a t := Real.sq_sqrt ha.le
  have hsE : √(energy a ψ u t) ^ 2 = energy a ψ u t := Real.sq_sqrt hE.le
  have hX2 : X a ψ u t ^ 2 = a t * ψ t ^ 2 / energy a ψ u t := by
    unfold X; rw [div_pow, mul_pow, hsa, hsE]
  have hY2 : Y a ψ u t ^ 2 = u t ^ 2 / (a t * energy a ψ u t) := by
    unfold Y; rw [neg_sq, div_pow, mul_pow, hsa, hsE]
  -- `q/a = a/p` from `a² = pq`, and `rate = (a/p)(1 + ε)`
  have hqa : q t / a t = a t / p t := by
    rw [div_eq_div_iff ha.ne' hp]; nlinarith [hapq]
  set ε := w t * (u t * ψ t) / energy a ψ u t with hεd
  set E := energy a ψ u t with hEd
  set D := X a ψ u t ^ 2 - Y a ψ u t ^ 2 with hDd
  have hrate : rate p a w q ψ u t = a t / p t * (1 + ε) := by
    unfold rate
    have e : w t * q t * (u t * ψ t) / (a t * E) = q t / a t * ε := by rw [hεd]; field_simp
    rw [e, hqa]; ring
  have hD : D = 2 * (a t * ψ t ^ 2 / E) - 1 := by rw [hDd, ← hX2]; linarith
  have key : E / (2 * a t) * (1 + D) = ψ t ^ 2 := by
    rw [hD]; field_simp; ring
  have hcomb : E / (2 * q t) * (rate p a w q ψ u t * D) - E / (2 * q t) * (ε / (1 + ε)) * (rate p a w q ψ u t * D)
      = E / (2 * a t) * D := by
    rw [hrate]
    have h1 : E / (2 * q t) * (a t / p t * (1 + ε) * D) - E / (2 * q t) * (ε / (1 + ε)) * (a t / p t * (1 + ε) * D)
        = E / (2 * q t) * (a t / p t) * D := by field_simp; ring
    rw [h1, ← hqa]; field_simp
  linarith [key, hcomb]

/-- **`|XY| ≤ ½`.** -/
theorem abs_XY_le_half {a ψ u : ℝ → ℝ} {t : ℝ} (ha : 0 < a t) (hE : 0 < energy a ψ u t) :
    |X a ψ u t * Y a ψ u t| ≤ 1 / 2 := by
  have h := X_sq_add_Y_sq (ψ := ψ) (u := u) ha hE
  rw [abs_mul]
  nlinarith [sq_nonneg (|X a ψ u t| - |Y a ψ u t|), sq_abs (X a ψ u t), sq_abs (Y a ψ u t)]

/-- **`(XY)′ = Θ′(X² − Y²)`.** -/
theorem hasDerivAt_XY {p a w q ψ u : ℝ → ℝ} {t : ℝ} (ha : 0 < a t) (hp : p t ≠ 0) (hapq : a t ^ 2 = p t * q t)
    (hE : 0 < energy a ψ u t) (hψ : HasDerivAt ψ (u t / p t) t) (hu : HasDerivAt u (-(q t * ψ t)) t)
    (haw : HasDerivAt a (w t * q t) t) :
    HasDerivAt (fun s => X a ψ u s * Y a ψ u s)
      (rate p a w q ψ u t * (X a ψ u t ^ 2 - Y a ψ u t ^ 2)) t := by
  have := (hasDerivAt_X ha hp hapq hE hψ hu haw).mul (hasDerivAt_Y ha hp hapq hE hψ hu haw)
  refine this.congr_deriv ?_
  ring

/-- **`|ε| ≤ w/2`** for `ε = w·uψ/E`. -/
theorem abs_eps_le {a ψ u : ℝ → ℝ} {w t : ℝ} (ha : 0 < a t) (hE : 0 < energy a ψ u t) (hw : 0 ≤ w) :
    |w * (u t * ψ t) / energy a ψ u t| ≤ w / 2 := by
  have h := two_mul_abs_le_energy (ψ := ψ) (u := u) ha
  rw [abs_div, abs_mul, abs_of_pos hE, abs_of_nonneg hw, div_le_iff₀ hE]
  rw [mul_comm (u t)] 
  nlinarith [abs_nonneg (ψ t * u t)]

/-- **`Θ′ = (a/p)(1 + ε)`.** -/
theorem rate_eq {p a w q ψ u : ℝ → ℝ} {t : ℝ} (ha : 0 < a t) (hp : p t ≠ 0) (hapq : a t ^ 2 = p t * q t)
    (hE : 0 < energy a ψ u t) :
    rate p a w q ψ u t = a t / p t * (1 + w t * (u t * ψ t) / energy a ψ u t) := by
  have hqa : q t / a t = a t / p t := by
    rw [div_eq_div_iff ha.ne' hp]; nlinarith [hapq]
  unfold rate
  have e : w t * q t * (u t * ψ t) / (a t * energy a ψ u t)
      = q t / a t * (w t * (u t * ψ t) / energy a ψ u t) := by field_simp
  rw [e, hqa]; ring

/-- **The `ε`-term pointwise**: at most `(E/(2a))·(w/2)(1 + w/2)/(1 − w/2)`. -/
theorem eps_term_le {E a p q w ε D r : ℝ} (hE : 0 < E) (ha : 0 < a) (hp : 0 < p) (hq : 0 < q)
    (hapq : a ^ 2 = p * q) (hw0 : 0 ≤ w) (hw2 : w < 2) (hε : |ε| ≤ w / 2) (hD : |D| ≤ 1)
    (hr : r = a / p * (1 + ε)) :
    |E / (2 * q) * (ε / (1 + ε)) * (r * D)| ≤ E / (2 * a) * (w / 2 * (1 + w / 2) / (1 - w / 2)) := by
  have hη : w / 2 < 1 := by linarith
  have h1ε : 1 - w / 2 ≤ 1 + ε := by linarith [neg_le_abs ε, hε]
  have h1ε' : 0 < 1 + ε := by linarith
  have hεq : |ε / (1 + ε)| ≤ (w / 2) / (1 - w / 2) := by
    rw [abs_div, abs_of_pos h1ε', div_le_div_iff₀ h1ε' (by linarith)]
    nlinarith [abs_nonneg ε]
  have hr' : |r| ≤ a / p * (1 + w / 2) := by
    rw [hr, abs_mul, abs_of_pos (div_pos ha hp), abs_of_pos h1ε']
    exact mul_le_mul_of_nonneg_left (by linarith [le_abs_self ε]) (div_pos ha hp).le
  have hEq : 0 ≤ E / (2 * q) := by positivity
  calc |E / (2 * q) * (ε / (1 + ε)) * (r * D)|
      = E / (2 * q) * |ε / (1 + ε)| * (|r| * |D|) := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hEq]
    _ ≤ E / (2 * q) * ((w / 2) / (1 - w / 2)) * (a / p * (1 + w / 2) * 1) := by
        gcongr
    _ = E / (2 * a) * (w / 2 * (1 + w / 2) / (1 - w / 2)) := by
        have hq' : q = a ^ 2 / p := by rw [eq_div_iff hp.ne']; linarith [hapq]
        subst hq'
        field_simp

end Cvs.Prolate.RungAveragedTail
