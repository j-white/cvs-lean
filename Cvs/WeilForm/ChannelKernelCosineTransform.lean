import Mathlib

/-!
# The channel kernel's cosine transform

The half-line transform of a decaying exponential against a cosine is the resolvent value
`b/(b²+t²)`.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Filter Topology Set

namespace Cvs.WeilForm.ChannelKernelCosineTransform

variable {b t : ℝ}

/-- The antiderivative of `e^{−bx} cos(tx)`. -/
def anti (b t : ℝ) (x : ℝ) : ℝ :=
  Real.exp (-b * x) * (-b * Real.cos (t * x) + t * Real.sin (t * x)) / (b ^ 2 + t ^ 2)

theorem hasDerivAt_anti (hbt : b ^ 2 + t ^ 2 ≠ 0) (x : ℝ) :
    HasDerivAt (anti b t) (Real.exp (-b * x) * Real.cos (t * x)) x := by
  have harg : HasDerivAt (fun x : ℝ => t * x) t x := by simpa using (hasDerivAt_id x).const_mul t
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (-b * x)) (Real.exp (-b * x) * -b) x := by
    simpa using ((hasDerivAt_id x).const_mul (-b)).exp
  have hin := (harg.cos.const_mul (-b)).add (harg.sin.const_mul t)
  refine ((hexp.mul hin).div_const (b ^ 2 + t ^ 2)).congr_deriv ?_
  simp only [Pi.add_apply]
  field_simp
  ring

/-- **The half-line transform.** -/
theorem integral_Ioi_exp_cos (hb : 0 < b) (t : ℝ) :
    (∫ x in Ioi (0:ℝ), Real.exp (-b * x) * Real.cos (t * x)) = b / (b ^ 2 + t ^ 2) := by
  have hbt : b ^ 2 + t ^ 2 ≠ 0 := by positivity
  have hbt' : (0:ℝ) < b ^ 2 + t ^ 2 := by positivity
  have hint : IntegrableOn (fun x => Real.exp (-b * x) * Real.cos (t * x)) (Ioi (0:ℝ)) := by
    refine Integrable.mono' (exp_neg_integrableOn_Ioi 0 hb)
      ((by fun_prop : Continuous fun x => Real.exp (-b * x) * Real.cos (t * x)).aestronglyMeasurable.restrict)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-b * x) * |Real.cos (t * x)| ≤ Real.exp (-b * x) * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_pos _).le
      _ = Real.exp (-b * x) := by ring
  have hexp0 : Tendsto (fun x : ℝ => Real.exp (-b * x)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => b * x) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hb tendsto_id
    have h2 : Tendsto (fun x : ℝ => -(b * x)) atTop atBot := tendsto_neg_atTop_atBot.comp h1
    exact (Real.tendsto_exp_atBot.comp h2).congr fun x => by rw [Function.comp_apply, neg_mul]
  have htend : Tendsto (anti b t) atTop (𝓝 0) := by
    have hg : Tendsto (fun x : ℝ => Real.exp (-b * x) * ((b + |t|) / (b ^ 2 + t ^ 2)))
        atTop (𝓝 0) := by
      have h := hexp0.mul_const ((b + |t|) / (b ^ 2 + t ^ 2))
      rwa [zero_mul] at h
    refine squeeze_zero_norm (fun x => ?_) hg
    have h1 : |(-b) * Real.cos (t * x) + t * Real.sin (t * x)| ≤ b + |t| := by
      have hc := Real.abs_cos_le_one (t * x)
      have hs := Real.abs_sin_le_one (t * x)
      rw [abs_le] at hc hs ⊢
      constructor <;> nlinarith [le_abs_self t, neg_abs_le t, hb.le, hc.1, hc.2, hs.1, hs.2]
    calc ‖anti b t x‖
        = Real.exp (-b * x) * |(-b) * Real.cos (t * x) + t * Real.sin (t * x)|
            / (b ^ 2 + t ^ 2) := by
          rw [anti, norm_div, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_pos (Real.exp_pos _), abs_of_pos hbt']
      _ ≤ Real.exp (-b * x) * (b + |t|) / (b ^ 2 + t ^ 2) := by
          gcongr
      _ = Real.exp (-b * x) * ((b + |t|) / (b ^ 2 + t ^ 2)) := by ring
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hasDerivAt_anti hbt x) hint htend]
  rw [anti]
  simp
  field_simp

/-- **The channel kernel's cosine transform.**  `∫ e^{−b|x|} cos(tx) dx = 2b/(b²+t²)`, the
resolvent value that is the symbol of the `b`-channel. -/
theorem integral_exp_neg_abs_cos (hb : 0 < b) (t : ℝ) :
    (∫ x : ℝ, Real.exp (-b * |x|) * Real.cos (t * x)) = 2 * b / (b ^ 2 + t ^ 2) := by
  have heq : ∀ x : ℝ, Real.exp (-b * |x|) * Real.cos (t * x)
      = (fun y => Real.exp (-b * y) * Real.cos (t * y)) |x| := by
    intro x
    rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩ <;> simp only [h]
    rw [show t * -x = -(t * x) from by ring, Real.cos_neg]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall heq),
    integral_comp_abs (f := fun y => Real.exp (-b * y) * Real.cos (t * y)),
    integral_Ioi_exp_cos hb]
  ring

end Cvs.WeilForm.ChannelKernelCosineTransform
