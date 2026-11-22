import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
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
# The Prüfer amplitude and its variation

The amplitude `A = √(E/a)` of the Prüfer form `ψ = A cos Θ` (Cvs.Upstream.SturmLiouvillePrufer) is differentiable wherever `a > 0`, `E > 0`,
and since `E' = w q (ψ² − u²/a²)` with `|ψ² − u²/a²| ≤ E/a` and `a' = w q`, its logarithmic derivative is bounded by
the relative rate of the coefficients: `|A'| ≤ |w| (a/p) A`. The variation `∫|A'|` of the amplitude over a window is
therefore at most `∫ |w| (a/p) A`, the datum `V` of the tests of Cvs.Upstream.FirstDerivativeTestVariation and Cvs.Upstream.SecondDerivativeWindowTest in terms of `w` and the frequency.
-/

namespace Cvs.Prolate.LiouvilleGreen.PruferAmplitudeVariation

open Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Upstream.SturmLiouvillePrufer

variable {p a w q ψ u : ℝ → ℝ}

/-- The Prüfer amplitude `A = √(E/a)`. -/
noncomputable def ampl (a ψ u : ℝ → ℝ) (t : ℝ) : ℝ := √(energy a ψ u t / a t)

/-- The derivative of the amplitude: `A' = (E' a − E a')/(2 a² A)`. -/
noncomputable def ampl' (a w q ψ u : ℝ → ℝ) (t : ℝ) : ℝ :=
  (w t * q t * (ψ t ^ 2 - u t ^ 2 / a t ^ 2) * a t - energy a ψ u t * (w t * q t)) / a t ^ 2
    / (2 * ampl a ψ u t)

/-- **The amplitude is differentiable** where `a > 0` and `E > 0`. -/
theorem hasDerivAt_ampl {t : ℝ} (ha : 0 < a t) (hp : p t ≠ 0) (hapq : a t ^ 2 = p t * q t)
    (hE : 0 < energy a ψ u t)
    (hψ : HasDerivAt ψ (u t / p t) t) (hu : HasDerivAt u (-(q t * ψ t)) t)
    (haw : HasDerivAt a (w t * q t) t) :
    HasDerivAt (ampl a ψ u) (ampl' a w q ψ u t) t := by
  have hEd := hasDerivAt_energy (p := p) (q := q) (w := w) ha hp hapq hψ hu haw
  have hq : HasDerivAt (fun t => energy a ψ u t / a t)
      ((w t * q t * (ψ t ^ 2 - u t ^ 2 / a t ^ 2) * a t - energy a ψ u t * (w t * q t)) / a t ^ 2) t :=
    hEd.div haw ha.ne'
  have hpos : energy a ψ u t / a t ≠ 0 := (div_pos hE ha).ne'
  have := hq.sqrt hpos
  unfold ampl ampl'
  convert this using 1
  all_goals rfl

/-- `|ψ² − u²/a²| ≤ E/a`: both terms of the energy are at most the energy. -/
theorem abs_sq_sub_le {t : ℝ} (ha : 0 < a t) :
    |ψ t ^ 2 - u t ^ 2 / a t ^ 2| ≤ energy a ψ u t / a t := by
  unfold energy
  have h1 : 0 ≤ u t ^ 2 / a t ^ 2 := by positivity
  have h2 : 0 ≤ ψ t ^ 2 := sq_nonneg _
  have e : (a t * ψ t ^ 2 + u t ^ 2 / a t) / a t = ψ t ^ 2 + u t ^ 2 / a t ^ 2 := by
    field_simp
  rw [e, abs_le]
  constructor <;> linarith

/-- **The amplitude's logarithmic derivative is bounded by the coefficients' relative rate**:
`|A'| ≤ |w| (a/p) A`. -/
theorem abs_ampl'_le {t : ℝ} (ha : 0 < a t) (hp : 0 < p t) (hapq : a t ^ 2 = p t * q t)
    (hE : 0 < energy a ψ u t) :
    |ampl' a w q ψ u t| ≤ |w t| * (a t / p t) * ampl a ψ u t := by
  have hA : 0 < ampl a ψ u t := Real.sqrt_pos.mpr (div_pos hE ha)
  have hq : q t = a t ^ 2 / p t := by rw [eq_div_iff hp.ne', hapq]; ring
  have hq0 : 0 < q t := by rw [hq]; positivity
  have hsub := abs_sq_sub_le (ψ := ψ) (u := u) ha
  -- `A² = E/a`
  have hA2 : ampl a ψ u t ^ 2 = energy a ψ u t / a t := Real.sq_sqrt (div_pos hE ha).le
  unfold ampl'
  rw [abs_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < a t ^ 2),
    abs_of_pos (by positivity : (0 : ℝ) < 2 * ampl a ψ u t)]
  -- the numerator: `|E' a − E a'| ≤ |w| q (E/a) a + E |w| q = 2 |w| q E`
  have hnum : |w t * q t * (ψ t ^ 2 - u t ^ 2 / a t ^ 2) * a t - energy a ψ u t * (w t * q t)|
      ≤ 2 * |w t| * q t * energy a ψ u t := by
    calc |w t * q t * (ψ t ^ 2 - u t ^ 2 / a t ^ 2) * a t - energy a ψ u t * (w t * q t)|
        ≤ |w t * q t * (ψ t ^ 2 - u t ^ 2 / a t ^ 2) * a t| + |energy a ψ u t * (w t * q t)| := abs_sub _ _
      _ = |w t| * q t * |ψ t ^ 2 - u t ^ 2 / a t ^ 2| * a t + energy a ψ u t * (|w t| * q t) := by
          rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos hq0, abs_of_pos ha, abs_of_pos hE]
      _ ≤ |w t| * q t * (energy a ψ u t / a t) * a t + energy a ψ u t * (|w t| * q t) := by
          gcongr
      _ = 2 * |w t| * q t * energy a ψ u t := by field_simp; ring
  calc |w t * q t * (ψ t ^ 2 - u t ^ 2 / a t ^ 2) * a t - energy a ψ u t * (w t * q t)| / a t ^ 2
        / (2 * ampl a ψ u t)
      ≤ 2 * |w t| * q t * energy a ψ u t / a t ^ 2 / (2 * ampl a ψ u t) := by gcongr
    _ = |w t| * (q t / a t) * (energy a ψ u t / a t) / ampl a ψ u t := by field_simp
    _ = |w t| * (q t / a t) * ampl a ψ u t := by
        rw [← hA2]
        try field_simp
    _ = |w t| * (a t / p t) * ampl a ψ u t := by
        congr 2
        rw [hq]; field_simp

end Cvs.Prolate.LiouvilleGreen.PruferAmplitudeVariation
