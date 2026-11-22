import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.L2a.NonresonantCrossIntegral

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Mellin kernel is a Sturm–Liouville solution, and it sits below the tail's gap

`y = cos(ξ log t)/√t` and `sin(ξ log t)/√t` solve `(t² y')' + (ξ² + ¼) y = 0`, so a mode's Mellin transform is a
cross integral of two Sturm–Liouville solutions (Cvs.Prolate.LiouvilleGreen.SturmProductByParts). Against the prolate mode `ψ(mt)`,
`D = (c²m⁴t⁴ − (χ + w)m²t² + w)/m²`, `w = ξ² + ¼`, is positive for `m t ≥ 1` whenever `w + χ < c²`: the gap, exactly;
the pole is `w = 0`.
-/

namespace Cvs.Prolate.Mellin.MellinKernelSturmLiouville

open Real Cvs.L2a.NonresonantCrossIntegral

/-- The cosine Mellin kernel `cos(ξ log t)/√t`. -/
noncomputable def ky (ξ t : ℝ) : ℝ := cos (ξ * log t) / √t
/-- Its flux `t² y' = −√t (ξ sin(ξ log t) + cos(ξ log t)/2)`. -/
noncomputable def ku (ξ t : ℝ) : ℝ := -(√t * (ξ * sin (ξ * log t) + cos (ξ * log t) / 2))

/-- `y' = u/t²`. -/
theorem hasDerivAt_ky {ξ t : ℝ} (ht : 0 < t) : HasDerivAt (ky ξ) (ku ξ t / t ^ 2) t := by
  have hl : HasDerivAt (fun s => ξ * log s) (ξ * t⁻¹) t := (hasDerivAt_log ht.ne').const_mul ξ
  have hc := hl.cos
  have hs := hasDerivAt_sqrt ht.ne'
  have hst : 0 < √t := sqrt_pos.mpr ht
  have h := hc.div hs hst.ne'
  have e : ky ξ = fun s => cos (ξ * log s) / √s := rfl
  rw [e]
  refine h.congr_deriv ?_
  unfold ku
  have hsq : √t * √t = t := mul_self_sqrt ht.le
  have h4 : √t ^ 4 = t ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_sqrt ht.le]
  field_simp
  rw [h4, sq_sqrt ht.le]
  ring

/-- `u' = −(ξ² + ¼) y`. -/
theorem hasDerivAt_ku {ξ t : ℝ} (ht : 0 < t) : HasDerivAt (ku ξ) (-((ξ ^ 2 + 1 / 4) * ky ξ t)) t := by
  have hl : HasDerivAt (fun s => ξ * log s) (ξ * t⁻¹) t := (hasDerivAt_log ht.ne').const_mul ξ
  have hs := hasDerivAt_sqrt ht.ne'
  have h := (hs.mul ((hl.sin.const_mul ξ).add (hl.cos.div_const 2))).neg
  have e : ku ξ = fun s => -(√s * (ξ * sin (ξ * log s) + cos (ξ * log s) / 2)) := rfl
  rw [e]
  refine h.congr_deriv ?_
  unfold ky
  simp only [Pi.add_apply]
  have hst : 0 < √t := sqrt_pos.mpr ht
  have hsq : √t * √t = t := mul_self_sqrt ht.le
  field_simp
  rw [sq_sqrt ht.le]
  ring

/-- The sine Mellin kernel `sin(ξ log t)/√t`. -/
noncomputable def kys (ξ t : ℝ) : ℝ := sin (ξ * log t) / √t
/-- Its flux `√t (ξ cos(ξ log t) − sin(ξ log t)/2)`. -/
noncomputable def kus (ξ t : ℝ) : ℝ := √t * (ξ * cos (ξ * log t) - sin (ξ * log t) / 2)

theorem hasDerivAt_kys {ξ t : ℝ} (ht : 0 < t) : HasDerivAt (kys ξ) (kus ξ t / t ^ 2) t := by
  have hl : HasDerivAt (fun s => ξ * log s) (ξ * t⁻¹) t := (hasDerivAt_log ht.ne').const_mul ξ
  have hs := hasDerivAt_sqrt ht.ne'
  have hst : 0 < √t := sqrt_pos.mpr ht
  have h := hl.sin.div hs hst.ne'
  have e : kys ξ = fun s => sin (ξ * log s) / √s := rfl
  rw [e]
  refine h.congr_deriv ?_
  unfold kus
  have hsq : √t * √t = t := mul_self_sqrt ht.le
  have h4 : √t ^ 4 = t ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_sqrt ht.le]
  field_simp
  rw [h4, sq_sqrt ht.le]
  ring

theorem hasDerivAt_kus {ξ t : ℝ} (ht : 0 < t) : HasDerivAt (kus ξ) (-((ξ ^ 2 + 1 / 4) * kys ξ t)) t := by
  have hl : HasDerivAt (fun s => ξ * log s) (ξ * t⁻¹) t := (hasDerivAt_log ht.ne').const_mul ξ
  have hs := hasDerivAt_sqrt ht.ne'
  have h := hs.mul ((hl.cos.const_mul ξ).sub (hl.sin.div_const 2))
  have e : kus ξ = fun s => √s * (ξ * cos (ξ * log s) - sin (ξ * log s) / 2) := rfl
  rw [e]
  refine h.congr_deriv ?_
  unfold kys
  simp only [Pi.sub_apply]
  have hst : 0 < √t := sqrt_pos.mpr ht
  have hsq : √t * √t = t := mul_self_sqrt ht.le
  field_simp
  rw [sq_sqrt ht.le]
  ring

/-- **The gap**: against the Euler partner (`p = t²`, `q = w`), the prolate mode's `D` is positive when
`1 ≤ m²t²`, `0 ≤ w`, `0 ≤ χ` and `w + χ < c²`. -/
theorem D_euler_pos {c χ m w t : ℝ} (hm : m ≠ 0) (hX : 1 ≤ m ^ 2 * t ^ 2) (hw : 0 ≤ w) (_hχ : 0 ≤ χ)
    (hgap : w + χ < c ^ 2) :
    0 < t ^ 2 * qm c χ m t - pm m t * w := by
  unfold pm qm
  have hm2 : 0 < m ^ 2 := by positivity
  rw [show t ^ 2 * (c ^ 2 * m ^ 2 * t ^ 2 - χ) - (m ^ 2 * t ^ 2 - 1) / m ^ 2 * w
      = ((m ^ 2 * t ^ 2) * (c ^ 2 * (m ^ 2 * t ^ 2) - χ - w) + w) / m ^ 2 by field_simp; ring]
  apply div_pos _ hm2
  have : c ^ 2 * (m ^ 2 * t ^ 2) - χ - w > 0 := by nlinarith
  nlinarith

/-- `D` against the Euler partner, and its derivative. -/
noncomputable def DE (c χ m w t : ℝ) : ℝ := t ^ 2 * qm c χ m t - pm m t * w
/-- `D'`. -/
noncomputable def dDE (c χ m w t : ℝ) : ℝ := 2 * t * qm c χ m t + t ^ 2 * (2 * c ^ 2 * m ^ 2 * t) - 2 * t * w

theorem hasDerivAt_DE {c χ m w : ℝ} (hm : m ≠ 0) (t : ℝ) : HasDerivAt (DE c χ m w) (dDE c χ m w t) t := by
  have := ((hasDerivAt_pow 2 t).mul (hasDerivAt_qm (c := c) (χ := χ) m t)).sub
    ((hasDerivAt_pm hm t).mul_const w)
  refine this.congr_deriv ?_; unfold dDE; simp

/-- **The kernel side is monotone**: `(t²)' D − t² D' = −2t(c²m⁴t⁴ − w)/m²`. -/
theorem numB_euler {c χ m w : ℝ} (hm : m ≠ 0) (t : ℝ) :
    2 * t * DE c χ m w t - t ^ 2 * dDE c χ m w t = -(2 * t * (c ^ 2 * m ^ 4 * t ^ 4 - w) / m ^ 2) := by
  unfold DE dDE pm qm; field_simp; ring

/-- **The mode side**: `p' D − p D' = −2t(c²(m²t² − 1)² − (c² − χ))/m²`, nonpositive once
`c²(m²t² − 1)² ≥ c² − χ`. -/
theorem numA_euler {c χ m w : ℝ} (hm : m ≠ 0) (t : ℝ) :
    2 * t * DE c χ m w t - pm m t * dDE c χ m w t
      = -(2 * t * (c ^ 2 * (m ^ 2 * t ^ 2 - 1) ^ 2 - (c ^ 2 - χ)) / m ^ 2) := by
  unfold DE dDE pm qm; field_simp; ring

end Cvs.Prolate.Mellin.MellinKernelSturmLiouville
