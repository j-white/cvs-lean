import Mathlib
import Cvs.Prolate.Mellin.LawRatioFunctionalDefect

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Mellin–Plancherel for the tail, and the total spectral mass of a rung

For measurable `f` with `|f(w)| ≤ K/w` on `w > 1`: `∫_ℝ |∫₁^∞ w^{−1/2+it} f(w) dw|² dt = 2π ∫₁^∞ f²`.
For the rung of index `k`: `(1/2π) ∫_ℝ |mg(½+it) D_k(½+it)|² dt = (π/c)(1 − λ_k)` (`AngularBesselInequality`'s mass).
-/

noncomputable section

open Complex Set MeasureTheory Filter Topology
open scoped FourierTransform

namespace Cvs.Prolate.Mellin.TailMellinPlancherel

/-- The log-scale tail `G(u) = 1_{u>0} e^{u/2} f(e^u)`. -/
def logTail (f : ℝ → ℝ) : ℝ → ℂ :=
  (Ioi (0 : ℝ)).indicator fun u => ((Real.exp (u / 2) * f (Real.exp u) : ℝ) : ℂ)

theorem measurable_logTail {f : ℝ → ℝ} (hf : Measurable f) : Measurable (logTail f) :=
  (Complex.measurable_ofReal.comp ((Real.measurable_exp.comp (measurable_id.div_const 2)).mul
    (hf.comp Real.measurable_exp))).indicator measurableSet_Ioi

theorem norm_logTail_sq (f : ℝ → ℝ) (u : ℝ) :
    ‖logTail f u‖ ^ 2 = (Ioi (0 : ℝ)).indicator (fun u => Real.exp u * f (Real.exp u) ^ 2) u := by
  unfold logTail
  by_cases hu : u ∈ Ioi (0 : ℝ)
  · rw [indicator_of_mem hu, indicator_of_mem hu, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow,
      ← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (u / 2) = u by push_cast; ring]
  · rw [indicator_of_notMem hu, indicator_of_notMem hu]; simp

theorem integral_norm_sq_logTail (f : ℝ → ℝ) :
    ∫ u, ‖logTail f u‖ ^ 2 = ∫ w in Ioi 1, f w ^ 2 := by
  simp only [norm_logTail_sq]
  rw [integral_indicator measurableSet_Ioi]
  have := integral_comp_exp_Ioi (fun w => f w ^ 2) 0
  rw [Real.exp_zero] at this
  rw [← this]
  rfl

/-- **The Mellin transform on the critical line is the Fourier transform of the log-scale tail.** -/
theorem mellin_eq_fourier_logTail (f : ℝ → ℝ) (t : ℝ) :
    ∫ w : ℝ in Ioi 1, (w : ℂ) ^ (1 / 2 + t * I - 1) * (f w : ℂ) = 𝓕 (logTail f) (-(t / (2 * Real.pi))) := by
  rw [Real.fourier_real_eq]
  unfold logTail
  have e : ∀ v : ℝ, 𝐞 (-(v * -(t / (2 * Real.pi)))) • (Ioi (0 : ℝ)).indicator
      (fun u => ((Real.exp (u / 2) * f (Real.exp u) : ℝ) : ℂ)) v
      = (Ioi (0 : ℝ)).indicator (fun v => 𝐞 (-(v * -(t / (2 * Real.pi))))
          • ((Real.exp (v / 2) * f (Real.exp v) : ℝ) : ℂ)) v := fun v => by
    by_cases hv : v ∈ Ioi (0 : ℝ) <;> simp [hv]
  simp only [e]
  rw [integral_indicator measurableSet_Ioi]
  have h := integral_comp_exp_Ioi (fun w : ℝ => (w : ℂ) ^ (1 / 2 + t * I - 1) * (f w : ℂ)) 0
  rw [Real.exp_zero] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [Complex.real_smul, Circle.smul_def, Real.fourierChar_apply,
    Cvs.Prolate.Mellin.LawRatioFunctionalDefect.ofReal_cpow_eq_exp (Real.exp_pos x), Real.log_exp]
  push_cast
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hR : cexp (2 * (Real.pi : ℂ) * -((x : ℂ) * -((t : ℂ) / (2 * Real.pi))) * I)
      * (cexp ((x : ℂ) / 2) * (f (Real.exp x) : ℂ))
      = cexp ((x : ℂ) + (1 / 2 + t * I - 1) * x) * (f (Real.exp x) : ℂ) := by
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    field_simp
    ring
  rw [smul_eq_mul, hR, ← mul_assoc, ← Complex.exp_add]

end Cvs.Prolate.Mellin.TailMellinPlancherel
