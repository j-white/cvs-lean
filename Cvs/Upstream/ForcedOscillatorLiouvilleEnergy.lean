import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The corrected Liouville energy of a forced oscillator

For `e′ = u/P`, `u′ = −Qe + F`, `a² = PQ` and `k = a′/Q`, the energy `Ẽ = ae² + u²/a + keu` has
`Ẽ′ = 2uF/a + k′eu + keF`: the oscillating term `a′(e² − u²/a²)` of `ae² + u²/a` is cancelled exactly. With
`d = 1 − |k|/2 > 0` and `E = ae² + u²/a`, `dE ≤ Ẽ` and `Ẽ′ ≤ (|k′|/(2d))Ẽ + |F|(|k| + 2)√(Ẽ/(da))`.
-/

namespace Cvs.Upstream.ForcedOscillatorLiouvilleEnergy

open Real

/-- **The corrected Liouville energy's derivative.** -/
theorem hasDerivAt_liouvilleEnergy {e u a k P Q F : ℝ → ℝ} {e' u' a' k' : ℝ} {x : ℝ}
    (he : HasDerivAt e e' x) (hu : HasDerivAt u u' x) (ha : HasDerivAt a a' x) (hk : HasDerivAt k k' x)
    (ha0 : a x ≠ 0) (hP0 : P x ≠ 0) (he' : e' = u x / P x) (hu' : u' = -(Q x * e x) + F x)
    (haPQ : a x ^ 2 = P x * Q x) (hkx : k x = a' / Q x) :
    HasDerivAt (fun x => a x * e x ^ 2 + u x ^ 2 / a x + k x * e x * u x)
      (2 * u x * F x / a x + k' * e x * u x + k x * e x * F x) x := by
  have hQ0 : Q x ≠ 0 := by
    intro h; rw [h, mul_zero] at haPQ; exact ha0 (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp haPQ)
  have h := ((ha.mul (he.pow 2)).add ((hu.pow 2).div ha ha0)).add ((hk.mul he).mul hu)
  refine h.congr_deriv ?_
  have hQ : Q x = a x ^ 2 / P x := by field_simp; linarith
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.add_apply, Pi.div_apply, Nat.cast_ofNat,
    show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  rw [he', hu', hkx, hQ]
  field_simp
  ring

/-- **`dE ≤ Ẽ`**, `d = 1 − |k|/2`. -/
theorem mul_energy_le {a e u k : ℝ} (ha : 0 < a) :
    (1 - |k| / 2) * (a * e ^ 2 + u ^ 2 / a) ≤ a * e ^ 2 + u ^ 2 / a + k * e * u := by
  have hsq : 2 * |e * u| ≤ a * e ^ 2 + u ^ 2 / a := by
    have h0 : 0 ≤ (a * |e| - |u|) ^ 2 / a := by positivity
    have e1 : (a * |e| - |u|) ^ 2 / a = a * e ^ 2 + u ^ 2 / a - 2 * |e * u| := by
      rw [abs_mul]; field_simp
      rw [show (a * |e| - |u|) ^ 2 = a ^ 2 * |e| ^ 2 + |u| ^ 2 - a * |e| * |u| * 2 by ring, sq_abs, sq_abs]
    linarith
  have hk : -(k * e * u) ≤ |k| * |e * u| := by
    rw [← abs_mul, show k * e * u = k * (e * u) by ring]; exact neg_le_abs _
  have : |k| * |e * u| ≤ |k| * ((a * e ^ 2 + u ^ 2 / a) / 2) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  nlinarith

/-- **The corrected energy's growth law**: with `d = 1 − |k|/2 > 0`,
`2uF/a + k′eu + keF ≤ (|k′|/(2d))Ẽ + |F|(|k| + 2)√(Ẽ/(da))`. -/
theorem liouville_deriv_le {a e u k k' F : ℝ} (ha : 0 < a) (hk : |k| < 2) :
    2 * u * F / a + k' * e * u + k * e * F
      ≤ |k'| / (2 * (1 - |k| / 2)) * (a * e ^ 2 + u ^ 2 / a + k * e * u)
        + |F| * (|k| + 2) * √((a * e ^ 2 + u ^ 2 / a + k * e * u) / ((1 - |k| / 2) * a)) := by
  set E := a * e ^ 2 + u ^ 2 / a with hE
  set Et := a * e ^ 2 + u ^ 2 / a + k * e * u with hEt
  have hd : 0 < 1 - |k| / 2 := by linarith
  have hE0 : 0 ≤ E := by positivity
  have hdE : (1 - |k| / 2) * E ≤ Et := mul_energy_le ha
  have hEle : E ≤ Et / (1 - |k| / 2) := by rw [le_div_iff₀ hd]; linarith
  have hsq : 2 * |e * u| ≤ E := by
    have h0 : 0 ≤ (a * |e| - |u|) ^ 2 / a := by positivity
    have e1 : (a * |e| - |u|) ^ 2 / a = a * e ^ 2 + u ^ 2 / a - 2 * |e * u| := by
      rw [abs_mul]; field_simp
      rw [show (a * |e| - |u|) ^ 2 = a ^ 2 * |e| ^ 2 + |u| ^ 2 - a * |e| * |u| * 2 by ring, sq_abs, sq_abs]
    linarith
  -- `|e|, |u|/a ≤ √(E/a) ≤ √(Ẽ/(da))`
  have hEa : E / a ≤ Et / ((1 - |k| / 2) * a) := by
    rw [div_le_div_iff₀ ha (by positivity)]
    nlinarith
  have hS : √(E / a) ≤ √(Et / ((1 - |k| / 2) * a)) := Real.sqrt_le_sqrt hEa
  have he : |e| ≤ √(E / a) := by
    apply Real.abs_le_sqrt
    rw [le_div_iff₀ ha, hE]
    have : 0 ≤ u ^ 2 / a := by positivity
    nlinarith
  have hu : |u| / a ≤ √(E / a) := by
    rw [div_le_iff₀ ha]
    have h1 : |u| ≤ √(a * E) := by
      apply Real.abs_le_sqrt
      rw [hE]
      have : a * (u ^ 2 / a) = u ^ 2 := by field_simp
      nlinarith [sq_nonneg e, mul_nonneg ha.le (mul_nonneg ha.le (sq_nonneg e))]
    calc |u| ≤ √(a * E) := h1
      _ = √(E / a) * a := by
          rw [show a * E = (E / a) * a ^ 2 by field_simp, Real.sqrt_mul (by positivity), Real.sqrt_sq ha.le]
  -- the three terms
  have t1 : k' * e * u ≤ |k'| / (2 * (1 - |k| / 2)) * Et := by
    have : k' * e * u ≤ |k'| * (E / 2) := by
      calc k' * e * u ≤ |k' * e * u| := le_abs_self _
        _ = |k'| * |e * u| := by rw [mul_assoc, abs_mul]
        _ ≤ |k'| * (E / 2) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    refine this.trans ?_
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [abs_nonneg k']
  have t2 : 2 * u * F / a + k * e * F ≤ |F| * (|k| + 2) * √(Et / ((1 - |k| / 2) * a)) := by
    have : 2 * u * F / a + k * e * F ≤ |F| * (2 * (|u| / a) + |k| * |e|) := by
      calc 2 * u * F / a + k * e * F ≤ |2 * u * F / a + k * e * F| := le_abs_self _
        _ ≤ |2 * u * F / a| + |k * e * F| := abs_add_le _ _
        _ = |F| * (2 * (|u| / a) + |k| * |e|) := by
            simp only [abs_div, abs_mul, abs_of_pos ha, abs_two]; field_simp
    have inner : 2 * (|u| / a) + |k| * |e| ≤ (|k| + 2) * √(Et / ((1 - |k| / 2) * a)) :=
      calc 2 * (|u| / a) + |k| * |e| ≤ 2 * √(E / a) + |k| * √(E / a) := by gcongr
        _ = (|k| + 2) * √(E / a) := by ring
        _ ≤ (|k| + 2) * √(Et / ((1 - |k| / 2) * a)) := mul_le_mul_of_nonneg_left hS (by positivity)
    calc 2 * u * F / a + k * e * F ≤ |F| * (2 * (|u| / a) + |k| * |e|) := this
      _ ≤ |F| * ((|k| + 2) * √(Et / ((1 - |k| / 2) * a))) := mul_le_mul_of_nonneg_left inner (abs_nonneg _)
      _ = |F| * (|k| + 2) * √(Et / ((1 - |k| / 2) * a)) := by ring
  linarith

end Cvs.Upstream.ForcedOscillatorLiouvilleEnergy
