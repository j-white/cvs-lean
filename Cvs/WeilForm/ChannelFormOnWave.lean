import Mathlib
import Cvs.Finite.ExponentialKernelLocalises
import Cvs.WeilForm.ChannelKernelCosineEigen

/-!
# A channel's quadratic form on a wave

The channel kernel's form on a centred cosine is the resolvent multiple of its norm, corrected by
the boundary factor.
-/

set_option maxHeartbeats 1600000

noncomputable section

namespace Cvs.WeilForm.ChannelFormOnWave

open Cvs.Finite.ExponentialKernelLocalises Cvs.WeilForm.ChannelKernelCosineEigen

variable {b t L : ℝ}

/-- The boundary weight paired against the wave. -/
def edgeMass (b t L : ℝ) : ℝ :=
  ∫ s in (0:ℝ)..L, (Real.exp (-b * s) + Real.exp (b * (s - L))) * wave t L s

/-- **A channel's form on a wave.**  The resolvent multiple of the norm, less the boundary factor
times the edge mass. -/
theorem quadForm_wave (hbt : b ^ 2 + t ^ 2 ≠ 0) :
    (∫ s in (0:ℝ)..L, wave t L s * convSplit b L (wave t L) s)
      = 2 * b / (b ^ 2 + t ^ 2) * (∫ s in (0:ℝ)..L, wave t L s ^ 2)
        - (b * Real.cos (t * (L / 2)) - t * Real.sin (t * (L / 2))) / (b ^ 2 + t ^ 2)
          * edgeMass b t L := by
  have hcw : Continuous (wave t L) := by unfold wave; fun_prop
  have h1 : Continuous fun s => wave t L s * (2 * b / (b ^ 2 + t ^ 2) * wave t L s) := by fun_prop
  have h2 : Continuous fun s => wave t L s *
      ((Real.exp (-b * s) + Real.exp (b * (s - L)))
        * (b * Real.cos (t * (L / 2)) - t * Real.sin (t * (L / 2))) / (b ^ 2 + t ^ 2)) := by
    fun_prop
  rw [intervalIntegral.integral_congr (g := fun s => wave t L s *
        (2 * b / (b ^ 2 + t ^ 2) * wave t L s)
      - wave t L s * ((Real.exp (-b * s) + Real.exp (b * (s - L)))
        * (b * Real.cos (t * (L / 2)) - t * Real.sin (t * (L / 2))) / (b ^ 2 + t ^ 2)))
      (fun s _ => by rw [convSplit_wave hbt]; ring),
    intervalIntegral.integral_sub (h1.intervalIntegrable _ _) (h2.intervalIntegrable _ _)]
  congr 1
  · rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun s _ => by ring
  · rw [edgeMass, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun s _ => by ring

/-- **The wave's norm.** -/
theorem integral_wave_sq (ht : t ≠ 0) (L : ℝ) :
    (∫ s in (0:ℝ)..L, wave t L s ^ 2) = L / 2 + Real.sin (t * L) / (2 * t) := by
  have hder : ∀ s : ℝ, HasDerivAt
      (fun s : ℝ => s / 2 + Real.sin (2 * t * (s - L / 2)) / (4 * t)) (wave t L s ^ 2) s := by
    intro s
    have harg : HasDerivAt (fun s : ℝ => 2 * t * (s - L / 2)) (2 * t) s := by
      simpa using ((hasDerivAt_id s).sub_const (L / 2)).const_mul (2 * t)
    have h1 : HasDerivAt (fun s : ℝ => s / 2) (1 / 2) s := by
      simpa using (hasDerivAt_id s).div_const 2
    have h2 := (harg.sin.div_const (4 * t))
    refine (h1.add h2).congr_deriv ?_
    rw [wave, Real.cos_sq]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hder s)
    (by apply Continuous.intervalIntegrable; unfold wave; fun_prop)]
  have e1 : 2 * t * (L - L / 2) = t * L := by ring
  have e2 : 2 * t * (0 - L / 2) = -(t * L) := by ring
  rw [e1, e2, Real.sin_neg]
  field_simp
  ring

/-- **The edge mass is the two moments at the ends.**  It needs no new computation: the backward
half is `Cvs.WeilForm.ChannelKernelCosineEigen`'s right moment at `0`, the forward half its left moment at `L`. -/
theorem edgeMass_eq_moments :
    edgeMass b t L
      = rightMoment b L (wave t L) 0 + Real.exp (-b * L) * leftMoment b (wave t L) L := by
  have hc1 : Continuous fun s => Real.exp (-b * s) * wave t L s := by unfold wave; fun_prop
  have hc2 : Continuous fun s => Real.exp (b * (s - L)) * wave t L s := by unfold wave; fun_prop
  rw [edgeMass, intervalIntegral.integral_congr
      (g := fun s => Real.exp (-b * s) * wave t L s + Real.exp (b * (s - L)) * wave t L s)
      (fun s _ => by ring),
    intervalIntegral.integral_add (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)]
  congr 1
  rw [leftMoment, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  have he : Real.exp (b * (s - L)) = Real.exp (-b * L) * Real.exp (b * s) := by
    rw [← Real.exp_add]; ring_nf
  rw [he]; ring

/-- **The edge mass in closed form.** -/
theorem edgeMass_eq (hbt : b ^ 2 + t ^ 2 ≠ 0) :
    edgeMass b t L
      = (rightAnti b t L L - rightAnti b t L 0) / (b ^ 2 + t ^ 2)
        + Real.exp (-b * L) * ((leftAnti b t L L - leftAnti b t L 0) / (b ^ 2 + t ^ 2)) := by
  rw [edgeMass_eq_moments, rightMoment_wave hbt, leftMoment_wave hbt]

end Cvs.WeilForm.ChannelFormOnWave
