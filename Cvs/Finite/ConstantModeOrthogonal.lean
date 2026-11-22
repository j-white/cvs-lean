import Mathlib
import Cvs.WeilForm.CrossModeElementClosedForm

/-!
# The constant mode is orthogonal to every positive mode

    ∫₀^L cos(2πm(x+v)/L)·cos(0·(x+w)) dx = 0   for m ≥ 1

the cross case `Cvs.WeilForm.ShiftSumModeDiagonal.integral_shift_cross` cannot state, since it needs both indices positive.
A positive mode integrates to zero over a full period whatever the displacement.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real

namespace Cvs.Finite.ConstantModeOrthogonal

/-- **A positive mode integrates to zero over a full period.** -/
theorem integral_mode_cross_zero {L : ℝ} (hL : 0 < L) {m : ℕ} (hm : 0 < m) (v w : ℝ) :
    (∫ x in (0:ℝ)..L, Real.cos (2 * π * m / L * (x + v))
        * Real.cos (2 * π * (0:ℕ) / L * (x + w))) = 0 := by
  have hpi := Real.pi_pos
  have hc : 2 * π * (m : ℝ) / L ≠ 0 := by
    have hm' : (0:ℝ) < (m : ℝ) := by exact_mod_cast hm
    positivity
  have hrw : ∀ x : ℝ, Real.cos (2 * π * (m : ℝ) / L * (x + v))
      * Real.cos (2 * π * ((0:ℕ) : ℝ) / L * (x + w))
      = Real.cos (2 * π * (m : ℝ) / L * x + 2 * π * (m : ℝ) / L * v) := by
    intro x
    norm_num
    ring_nf
  rw [intervalIntegral.integral_congr (fun x _ => hrw x),
    Cvs.WeilForm.CrossModeElementClosedForm.integral_cos_affine hc (2 * π * (m : ℝ) / L * v) L]
  have hper : Real.sin (2 * π * (m : ℝ) / L * L + 2 * π * (m : ℝ) / L * v)
      = Real.sin (2 * π * (m : ℝ) / L * v) := by
    have hLne : L ≠ 0 := ne_of_gt hL
    have harg : 2 * π * (m : ℝ) / L * L + 2 * π * (m : ℝ) / L * v
        = 2 * π * (m : ℝ) / L * v + (m : ℝ) * (2 * π) := by
      field_simp
      ring
    rw [harg, Real.sin_add_nat_mul_two_pi]
  rw [hper]
  simp

end Cvs.Finite.ConstantModeOrthogonal
