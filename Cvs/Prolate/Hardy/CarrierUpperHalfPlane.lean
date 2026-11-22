import Mathlib
import Cvs.Prolate.Hardy.CosineSynthesisPlancherel
import Cvs.Prolate.Hardy.ExteriorSincColumns
import Cvs.Prolate.Hardy.HardyExtensionOperator

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The carrier `w = e^{ibS}` on the closed upper half-plane

`S(z) = i√(−i(z − a))√(−i(z + a))` satisfies `S² = z² − a²` and `Im S ≥ 0` for `Im z ≥ 0`, is continuous there and
holomorphic inside; so `|w e^{−ibz}| ≤ 1`, `|w| ≤ 1` on `ℝ`, and on `I` the boundary value `w = e^{−b Im S}` is real.
-/

noncomputable section

open Real Set MeasureTheory
open Complex (I)

namespace Cvs.Prolate.Hardy.CarrierUpperHalfPlane
open Cvs.ZeroCounting

open Cvs.Prolate.Hardy.HardyExtensionOperator (sS wC wR wInvI)
open Cvs.Prolate.Hardy.CosineSynthesisPlancherel (cI)

/-- The principal square root of a point of the closed right half-plane has `|Im| ≤ Re`. -/
theorem abs_im_sqrt_le {w : ℂ} (hw : 0 ≤ w.re) : |(Complex.sqrt w).im| ≤ (Complex.sqrt w).re := by
  have hre : (Complex.sqrt w).re = √((‖w‖ + w.re) / 2) := by
    rw [Complex.sqrt_eq_real_add_ite]; split_ifs <;> simp
  have him : |(Complex.sqrt w).im| = √((‖w‖ - w.re) / 2) := by
    rw [Complex.sqrt_eq_real_add_ite]
    split_ifs <;> simp <;> positivity
  rw [hre, him]
  exact Real.sqrt_le_sqrt (by linarith)

theorem sqrt_sq (w : ℂ) : Complex.sqrt w ^ 2 = w := Complex.cpow_ofNat_inv_pow w 2

/-- `S² = z² − a²`. -/
theorem sS_sq (z : ℂ) : sS z ^ 2 = z ^ 2 - ((1 / 2 : ℝ) : ℂ) ^ 2 := by
  have h1 := sqrt_sq (-I * (z - 1 / 2))
  have h2 := sqrt_sq (-I * (z + 1 / 2))
  have e : sS z ^ 2 = I ^ 2 * Complex.sqrt (-I * (z - 1 / 2)) ^ 2 * Complex.sqrt (-I * (z + 1 / 2)) ^ 2 := by
    rw [sS]; ring
  rw [e, h1, h2]
  push_cast
  linear_combination ((I ^ 2 - 1) * (z ^ 2 - 1 / 4)) * Complex.I_sq

/-- `Im S ≥ 0` on the closed upper half-plane. -/
theorem im_sS_nonneg {z : ℂ} (hz : 0 ≤ z.im) : 0 ≤ (sS z).im := by
  set p := Complex.sqrt (-I * (z - 1 / 2))
  set q := Complex.sqrt (-I * (z + 1 / 2))
  have hp : |p.im| ≤ p.re := abs_im_sqrt_le (by simp [Complex.mul_re]; exact hz)
  have hq : |q.im| ≤ q.re := abs_im_sqrt_le (by simp [Complex.mul_re]; exact hz)
  have e : (sS z).im = p.re * q.re - p.im * q.im := by
    simp only [sS]
    change (I * p * q).im = _
    simp [Complex.mul_im, Complex.mul_re]; ring
  rw [e]
  have h1 : p.im * q.im ≤ |p.im| * |q.im| := by rw [← abs_mul]; exact le_abs_self _
  have h2 : |p.im| * |q.im| ≤ p.re * q.re :=
    mul_le_mul hp hq (abs_nonneg _) ((abs_nonneg _).trans hp)
  linarith

theorem continuousOn_sS : ContinuousOn sS {z : ℂ | 0 ≤ z.im} := by
  intro z hz
  have hz' : 0 ≤ z.im := hz
  refine ContinuousAt.continuousWithinAt ?_
  have r1 : 0 ≤ (-I * (z - 1 / 2)).re := by simp [Complex.mul_re]; exact hz'
  have r2 : 0 ≤ (-I * (z + 1 / 2)).re := by simp [Complex.mul_re]; exact hz'
  have c1 : ContinuousAt Complex.sqrt (-I * (z - 1 / 2)) := Complex.continuousAt_sqrt (Or.inl r1)
  have c2 : ContinuousAt Complex.sqrt (-I * (z + 1 / 2)) := Complex.continuousAt_sqrt (Or.inl r2)
  have e1 : ContinuousAt (fun z : ℂ => -I * (z - 1 / 2)) z := by fun_prop
  have e2 : ContinuousAt (fun z : ℂ => -I * (z + 1 / 2)) z := by fun_prop
  have d1 : ContinuousAt (fun z : ℂ => Complex.sqrt (-I * (z - 1 / 2))) z :=
    ContinuousAt.comp (f := fun z : ℂ => -I * (z - 1 / 2)) (g := Complex.sqrt) c1 e1
  have d2 : ContinuousAt (fun z : ℂ => Complex.sqrt (-I * (z + 1 / 2))) z :=
    ContinuousAt.comp (f := fun z : ℂ => -I * (z + 1 / 2)) (g := Complex.sqrt) c2 e2
  have d0 : ContinuousAt (fun _ : ℂ => I) z := continuousAt_const
  have h := (d0.mul d1).mul d2
  exact h

theorem differentiableOn_sS : DifferentiableOn ℂ sS {z : ℂ | 0 < z.im} := by
  intro z hz
  have hz' : 0 < z.im := hz
  refine DifferentiableAt.differentiableWithinAt ?_
  have m1 : -I * (z - 1 / 2) ∈ Complex.slitPlane := Or.inl (by simp [Complex.mul_re]; exact hz')
  have m2 : -I * (z + 1 / 2) ∈ Complex.slitPlane := Or.inl (by simp [Complex.mul_re]; exact hz')
  have d1 : DifferentiableAt ℂ (fun z : ℂ => Complex.sqrt (-I * (z - 1 / 2))) z :=
    DifferentiableAt.comp (f := fun z : ℂ => -I * (z - 1 / 2)) z (Complex.hasDerivAt_sqrt m1).differentiableAt
      (by fun_prop)
  have d2 : DifferentiableAt ℂ (fun z : ℂ => Complex.sqrt (-I * (z + 1 / 2))) z :=
    DifferentiableAt.comp (f := fun z : ℂ => -I * (z + 1 / 2)) z (Complex.hasDerivAt_sqrt m2).differentiableAt
      (by fun_prop)
  exact ((differentiableAt_const _).mul d1).mul d2

/-- The normalized carrier `Φ_b(z) = w(z) e^{−ibz}`, bounded holomorphic on the upper half-plane. -/
def carrierPhi (b : ℝ) (z : ℂ) : ℂ := wC b z * Complex.exp (-(I * b * z))

theorem norm_carrierPhi_le {b : ℝ} (hb : 0 ≤ b) {z : ℂ} (hz : 0 ≤ z.im) : ‖carrierPhi b z‖ ≤ 1 :=
  Cvs.Prolate.Hardy.ExteriorSincColumns.norm_exp_mul_exp_le hb (sS_sq z) (im_sS_nonneg hz)

theorem continuousOn_carrierPhi (b : ℝ) : ContinuousOn (carrierPhi b) {z : ℂ | 0 ≤ z.im} := by
  have h1 : ContinuousOn (fun z => wC b z) {z : ℂ | 0 ≤ z.im} :=
    Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul continuousOn_sS)
  exact h1.mul (Continuous.continuousOn (by fun_prop))

theorem differentiableOn_carrierPhi (b : ℝ) : DifferentiableOn ℂ (carrierPhi b) {z : ℂ | 0 < z.im} := by
  have h1 : DifferentiableOn ℂ (fun z => wC b z) {z : ℂ | 0 < z.im} :=
    (differentiableOn_const _ |>.mul differentiableOn_sS).cexp
  exact h1.mul (Differentiable.differentiableOn (by fun_prop))

/-- `w(x) = Φ_b(x) e^{ibx}` on `ℝ`. -/
theorem wR_eq (b x : ℝ) : wR b x = carrierPhi b x * Complex.exp (I * b * x) := by
  rw [carrierPhi, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]; rfl

theorem continuous_wR (b : ℝ) : Continuous (wR b) := by
  have h : ContinuousOn (fun z => wC b z) {z : ℂ | 0 ≤ z.im} :=
    Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul continuousOn_sS)
  exact h.comp_continuous Complex.continuous_ofReal (fun x => by simp)

theorem norm_wR_le {b : ℝ} (hb : 0 ≤ b) (x : ℝ) : ‖wR b x‖ ≤ 1 := by
  rw [wR, wC, Complex.norm_exp]
  have : (I * b * sS x).re = -b * (sS x).im := by simp [Complex.mul_re, Complex.mul_im]
  rw [this, Real.exp_le_one_iff]
  have := im_sS_nonneg (z := (x : ℂ)) (by simp)
  nlinarith

/-- On `I`, `S(x)` is purely imaginary with `0 ≤ Im S ≤ a`. -/
theorem sS_on_I {x : ℝ} (hx : x ∈ cI) : (sS x).re = 0 ∧ 0 ≤ (sS x).im ∧ (sS x).im ≤ 1 / 2 := by
  have h := sS_sq x
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [sq, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im] at hre him
  have hx2 : x ^ 2 ≤ 1 / 4 := by
    obtain ⟨h1, h2⟩ := hx; nlinarith
  have him0 : 0 ≤ (sS x).im := im_sS_nonneg (by simp)
  set p := (sS x).re
  set q := (sS x).im
  have hpq : p * q = 0 := by linarith
  have hsq : p ^ 2 - q ^ 2 = x ^ 2 - 1 / 4 := by nlinarith
  have hp : p = 0 := by
    rcases mul_eq_zero.1 hpq with h | h
    · exact h
    · rw [h] at hsq; nlinarith [sq_nonneg p]
  refine ⟨hp, him0, ?_⟩
  rw [hp] at hsq
  nlinarith

theorem wR_on_I {b : ℝ} {x : ℝ} (hx : x ∈ cI) : wR b x = (Real.exp (-b * (sS x).im) : ℂ) := by
  obtain ⟨h1, -, -⟩ := sS_on_I hx
  rw [wR, wC, Complex.ofReal_exp]
  congr 1
  have e : sS x = (sS x).im * I := by
    apply Complex.ext <;> simp [h1]
  rw [e]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  simp

theorem wR_ne_zero (b x : ℝ) : wR b x ≠ 0 := Complex.exp_ne_zero _

theorem norm_wInvI_le {b : ℝ} (hb : 0 ≤ b) (x : ℝ) : ‖wInvI b x‖ ≤ Real.exp (b / 2) := by
  by_cases hx : x ∈ cI
  · rw [wInvI, indicator_of_mem hx, wR_on_I hx, ← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs,
      ← Real.exp_neg, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
    obtain ⟨-, h0, h1⟩ := sS_on_I hx
    nlinarith
  · rw [wInvI, indicator_of_notMem hx, norm_zero]; exact (Real.exp_pos _).le

theorem memLp_wR {b : ℝ} (hb : 0 ≤ b) : MemLp (wR b) ⊤ (volume : Measure ℝ) :=
  memLp_top_of_bound (continuous_wR b).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (norm_wR_le hb))

theorem memLp_wInvI {b : ℝ} (hb : 0 ≤ b) : MemLp (wInvI b) ⊤ (volume : Measure ℝ) := by
  refine memLp_top_of_bound ?_ (Real.exp (b / 2)) (Filter.Eventually.of_forall (norm_wInvI_le hb))
  exact ((continuous_wR b).measurable.inv.indicator measurableSet_Icc).aestronglyMeasurable

/-- On `I`, `1/w` is real. -/
theorem wInvI_im (b x : ℝ) : (wInvI b x).im = 0 := by
  by_cases hx : x ∈ cI
  · rw [wInvI, indicator_of_mem hx, wR_on_I hx, ← Complex.ofReal_inv, Complex.ofReal_im]
  · rw [wInvI, indicator_of_notMem hx, Complex.zero_im]

end Cvs.Prolate.Hardy.CarrierUpperHalfPlane

end
