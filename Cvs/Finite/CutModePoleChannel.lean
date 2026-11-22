import Mathlib
import Cvs.Finite.DiagonalCutSymbol

/-!
# The pole channel of the cut modes, in closed form at every scale
For a frequency with `cos(ωL) = 1` and `sin(ωL) = 0` (every `ω = 2πm/L`, including `ω = 0`), the
pole integrals `∫_{x>0} (e^{−x/2} + e^{x/2})·h(x)` of `cosCut`, `sinCut` and `vcosCut` are rational
functions of `e^{±L/2}`, `L` and `ω`: with `D_a = a² + ω²`, `a = ±1/2`, the cosine gives
`∑_a a(e^{aL} − 1)/D_a`, the sine `∑_a ω(1 − e^{aL})/D_a`, and the ramp-weighted cosine
`∑_a (aL e^{aL} D_a − (a² − ω²)(e^{aL} − 1))/D_a²`.
-/

noncomputable section

open Real MeasureTheory Set

namespace Cvs.Finite.CutModePoleChannel

/-- The antiderivative of `e^{ax} cos ωx`. -/
def Fc (a ω x : ℝ) : ℝ := Real.exp (a * x) * (a * Real.cos (ω * x) + ω * Real.sin (ω * x)) / (a ^ 2 + ω ^ 2)
/-- The antiderivative of `e^{ax} sin ωx`. -/
def Fs (a ω x : ℝ) : ℝ := Real.exp (a * x) * (a * Real.sin (ω * x) - ω * Real.cos (ω * x)) / (a ^ 2 + ω ^ 2)
/-- The antiderivative of `x e^{ax} cos ωx`. -/
def Fv (a ω x : ℝ) : ℝ :=
  Real.exp (a * x) * (x * (a * Real.cos (ω * x) + ω * Real.sin (ω * x)) / (a ^ 2 + ω ^ 2)
    - ((a ^ 2 - ω ^ 2) * Real.cos (ω * x) + 2 * a * ω * Real.sin (ω * x)) / (a ^ 2 + ω ^ 2) ^ 2)

theorem hasDerivAt_exp_mul (a x : ℝ) : HasDerivAt (fun x => Real.exp (a * x)) (Real.exp (a * x) * a) x := by
  simpa using ((hasDerivAt_id x).const_mul a).exp

theorem hasDerivAt_cos_mul (ω x : ℝ) :
    HasDerivAt (fun x => Real.cos (ω * x)) (-Real.sin (ω * x) * ω) x := by
  simpa using ((hasDerivAt_id x).const_mul ω).cos

theorem hasDerivAt_sin_mul (ω x : ℝ) :
    HasDerivAt (fun x => Real.sin (ω * x)) (Real.cos (ω * x) * ω) x := by
  simpa using ((hasDerivAt_id x).const_mul ω).sin

theorem hasDerivAt_Fc {a ω : ℝ} (hD : a ^ 2 + ω ^ 2 ≠ 0) (x : ℝ) :
    HasDerivAt (Fc a ω) (Real.exp (a * x) * Real.cos (ω * x)) x := by
  have h := ((hasDerivAt_exp_mul a x).mul (((hasDerivAt_cos_mul ω x).const_mul a).add
    ((hasDerivAt_sin_mul ω x).const_mul ω))).div_const (a ^ 2 + ω ^ 2)
  refine h.congr_deriv ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  field_simp
  ring

theorem hasDerivAt_Fs {a ω : ℝ} (hD : a ^ 2 + ω ^ 2 ≠ 0) (x : ℝ) :
    HasDerivAt (Fs a ω) (Real.exp (a * x) * Real.sin (ω * x)) x := by
  have h := ((hasDerivAt_exp_mul a x).mul (((hasDerivAt_sin_mul ω x).const_mul a).sub
    ((hasDerivAt_cos_mul ω x).const_mul ω))).div_const (a ^ 2 + ω ^ 2)
  refine h.congr_deriv ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  field_simp
  ring

theorem hasDerivAt_Fv {a ω : ℝ} (hD : a ^ 2 + ω ^ 2 ≠ 0) (x : ℝ) :
    HasDerivAt (Fv a ω) (x * (Real.exp (a * x) * Real.cos (ω * x))) x := by
  have hin1 : HasDerivAt (fun x => x * (a * Real.cos (ω * x) + ω * Real.sin (ω * x)) / (a ^ 2 + ω ^ 2))
      ((1 * (a * Real.cos (ω * x) + ω * Real.sin (ω * x))
        + x * (a * (-Real.sin (ω * x) * ω) + ω * (Real.cos (ω * x) * ω))) / (a ^ 2 + ω ^ 2)) x :=
    ((hasDerivAt_id x).mul (((hasDerivAt_cos_mul ω x).const_mul a).add
      ((hasDerivAt_sin_mul ω x).const_mul ω))).div_const _
  have hin2 : HasDerivAt
      (fun x => ((a ^ 2 - ω ^ 2) * Real.cos (ω * x) + 2 * a * ω * Real.sin (ω * x)) / (a ^ 2 + ω ^ 2) ^ 2)
      (((a ^ 2 - ω ^ 2) * (-Real.sin (ω * x) * ω) + 2 * a * ω * (Real.cos (ω * x) * ω))
        / (a ^ 2 + ω ^ 2) ^ 2) x :=
    (((hasDerivAt_cos_mul ω x).const_mul _).add ((hasDerivAt_sin_mul ω x).const_mul _)).div_const _
  have h := (hasDerivAt_exp_mul a x).mul (hin1.sub hin2)
  refine h.congr_deriv ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  field_simp
  ring

/-- A cut function's pole integral is the interval integral of its uncut form. -/
theorem poleInt_cut {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ} (hf : Continuous f) {F : ℝ → ℝ}
    (hF : ∀ x, HasDerivAt F ((Real.exp (-(x / 2)) + Real.exp (x / 2)) * f x) x) :
    (∫ x in Ioi (0:ℝ), (Real.exp (-(x / 2)) + Real.exp (x / 2)) * (if x ≤ L then f x else 0))
      = F L - F 0 := by
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Ioc_subset_Ioi_self : Ioc (0:ℝ) L ⊆ Ioi 0) (fun x hx => ?_)]
  · rw [setIntegral_congr_fun measurableSet_Ioc (fun x hx => by
        simp only [if_pos (mem_Ioc.mp hx).2] :
      EqOn (fun x => (Real.exp (-(x / 2)) + Real.exp (x / 2)) * (if x ≤ L then f x else 0))
        (fun x => (Real.exp (-(x / 2)) + Real.exp (x / 2)) * f x) (Ioc 0 L)),
      ← intervalIntegral.integral_of_le hL.le]
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hF x) ?_
    exact (Continuous.continuousOn (by fun_prop)).intervalIntegrable
  · simp only [mem_sdiff, mem_Ioi, mem_Ioc, not_and, not_le] at hx
    rw [if_neg (not_le.mpr (hx.2 hx.1)), mul_zero]

theorem exp_half_eq (x : ℝ) : Real.exp (x / 2) = Real.exp ((1 / 2) * x) := by ring_nf
theorem exp_neg_half_eq (x : ℝ) : Real.exp (-(x / 2)) = Real.exp ((-1 / 2) * x) := by ring_nf

/-- **The pole integral of the cut sine.** -/
theorem poleInt_sinCut {L ω : ℝ} (hL : 0 < L) (hs : Real.sin (ω * L) = 0) (hc : Real.cos (ω * L) = 1) :
    (∫ x in Ioi (0:ℝ), (Real.exp (-(x / 2)) + Real.exp (x / 2)) * Cvs.Finite.DiagonalCutSymbol.sinCut L ω x)
      = ω * (1 - Real.exp ((-1 / 2) * L)) / ((-1 / 2) ^ 2 + ω ^ 2)
        + ω * (1 - Real.exp ((1 / 2) * L)) / ((1 / 2) ^ 2 + ω ^ 2) := by
  have hD1 : ((-1 / 2 : ℝ)) ^ 2 + ω ^ 2 ≠ 0 := by positivity
  have hD2 : ((1 / 2 : ℝ)) ^ 2 + ω ^ 2 ≠ 0 := by positivity
  have h := poleInt_cut hL (f := fun x => Real.sin (ω * x)) (by fun_prop)
    (F := fun x => Fs (-1 / 2) ω x + Fs (1 / 2) ω x) (fun x => by
      refine ((hasDerivAt_Fs hD1 x).add (hasDerivAt_Fs hD2 x)).congr_deriv ?_
      rw [exp_neg_half_eq, exp_half_eq]; ring)
  unfold Cvs.Finite.DiagonalCutSymbol.sinCut
  rw [h]
  unfold Fs
  simp only [mul_zero, Real.exp_zero, Real.cos_zero, Real.sin_zero, hs, hc]
  field_simp
  ring

end Cvs.Finite.CutModePoleChannel
