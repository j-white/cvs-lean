import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Cvs.Xi.PhiKernelIdentitySums
import Cvs.Xi.PhiThetaDifferentialOperator

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The theta sum decays exponentially on the half line

Past the origin the exponent `π e^{2u} n²` dominates both its own halves, so each term carries a
factor `e^{−(π/2)e^{2u}}` with a summable remainder, and the sum inherits it. Since `e^{2u}` is at
least `1 + 2u`, that factor beats the `e^{u/2}` in front, leaving a plain exponential with negative
rate.
-/

noncomputable section

open Real Filter Topology

namespace Cvs.Xi.ThetaSumExponentialDecay

open Cvs.Xi.RiemannPhiKernel Cvs.Xi.PhiThetaDifferentialOperator Cvs.Xi.PhiKernelIdentitySums

/-- The tail of the dominating series, summed away from the origin. -/
theorem summable_dom :
    Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 4 + 1)
      * exp (-(π / 2 * ((n + 1 : ℕ) : ℝ) ^ 2))) :=
  (summable_nat_add_iff 1).mpr (summable_quartic_exp (by positivity))

/-- The dominating constant. -/
def domConst : ℝ :=
  ∑' n : ℕ, (((n + 1 : ℕ) : ℝ) ^ 4 + 1) * exp (-(π / 2 * ((n + 1 : ℕ) : ℝ) ^ 2))

theorem domConst_nonneg : 0 ≤ domConst :=
  tsum_nonneg fun n => by positivity

/-- **The exponent splits**: past the origin each half of `π e^{2u} m²` is paid separately. -/
theorem exp_split {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    exp (-(π * exp (2 * u) * ((n + 1 : ℕ) : ℝ) ^ 2))
      ≤ exp (-(π / 2 * exp (2 * u))) * exp (-(π / 2 * ((n + 1 : ℕ) : ℝ) ^ 2)) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  have hE : (1 : ℝ) ≤ exp (2 * u) := Real.one_le_exp (by linarith)
  have hm : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr n.succ_ne_zero
  have hm2 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
  have hpi := Real.pi_pos
  nlinarith [mul_nonneg (sub_nonneg.mpr hE) (sub_nonneg.mpr hm2),
    mul_nonneg hpi.le (mul_nonneg (sub_nonneg.mpr hE) (sub_nonneg.mpr hm2))]

/-- **Termwise decay.** -/
theorem thetaTerm_le_decay {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    thetaTerm (n + 1) u
      ≤ (exp (u / 2) * exp (-(π / 2 * exp (2 * u))))
        * ((((n + 1 : ℕ) : ℝ) ^ 4 + 1) * exp (-(π / 2 * ((n + 1 : ℕ) : ℝ) ^ 2))) := by
  have hb := abs_thetaTerm_le (n + 1) u
  rw [abs_of_pos (thetaTerm_pos (n + 1) u)] at hb
  refine hb.trans ?_
  have hsplit := exp_split hu n
  have hq : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 4 + 1 := by positivity
  have he : (0 : ℝ) < exp (u / 2) := Real.exp_pos _
  have hmul : (((n + 1 : ℕ) : ℝ) ^ 4 + 1) * exp (-(π * exp (2 * u) * ((n + 1 : ℕ) : ℝ) ^ 2))
      ≤ (((n + 1 : ℕ) : ℝ) ^ 4 + 1)
        * (exp (-(π / 2 * exp (2 * u))) * exp (-(π / 2 * ((n + 1 : ℕ) : ℝ) ^ 2))) :=
    mul_le_mul_of_nonneg_left hsplit hq
  calc exp (u / 2) * ((((n + 1 : ℕ) : ℝ) ^ 4 + 1)
          * exp (-(π * exp (2 * u) * ((n + 1 : ℕ) : ℝ) ^ 2)))
      ≤ exp (u / 2) * ((((n + 1 : ℕ) : ℝ) ^ 4 + 1)
          * (exp (-(π / 2 * exp (2 * u))) * exp (-(π / 2 * ((n + 1 : ℕ) : ℝ) ^ 2)))) :=
        mul_le_mul_of_nonneg_left hmul he.le
    _ = _ := by ring

/-- **The theta sum carries the same factor.** -/
theorem thetaSum_le {u : ℝ} (hu : 0 ≤ u) :
    thetaSum u ≤ (exp (u / 2) * exp (-(π / 2 * exp (2 * u)))) * domConst := by
  have hsum := summable_thetaTerm_shift u
  have hdom := summable_dom
  have hle := Summable.tsum_le_tsum (thetaTerm_le_decay hu) hsum
    (hdom.mul_left (exp (u / 2) * exp (-(π / 2 * exp (2 * u)))))
  rwa [tsum_mul_left] at hle

/-- **The prefactor is beaten**, because `e^{2u}` is at least `1 + 2u`. -/
theorem exp_prefactor_le (u : ℝ) :
    exp (u / 2) * exp (-(π / 2 * exp (2 * u))) ≤ exp (-(π / 2)) * exp (-((π - 1 / 2) * u)) := by
  rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have hE : 1 + 2 * u ≤ exp (2 * u) := by
    have := Real.add_one_le_exp (2 * u); linarith
  have hpi := Real.pi_pos
  nlinarith

theorem thetaSum_nonneg (u : ℝ) : 0 ≤ thetaSum u := by
  unfold thetaSum
  exact tsum_nonneg fun n => (thetaTerm_pos _ u).le

/-- **The theta sum tends to zero.** -/
theorem tendsto_thetaSum : Tendsto thetaSum atTop (𝓝 0) := by
  have hr : 0 < π - 1 / 2 := by linarith [Real.pi_gt_three]
  have h1 : Tendsto (fun u : ℝ => -((π - 1 / 2) * u)) atTop atBot :=
    Filter.tendsto_neg_atBot_iff.mpr (Filter.Tendsto.const_mul_atTop hr Filter.tendsto_id)
  have hexp : Tendsto (fun u : ℝ => exp (-((π - 1 / 2) * u))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp h1
  have hbig := hexp.const_mul (exp (-(π / 2)) * domConst)
  rw [mul_zero] at hbig
  refine squeeze_zero' (Eventually.of_forall thetaSum_nonneg) ?_ hbig
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
  refine (thetaSum_le hu).trans ?_
  exact (mul_le_mul_of_nonneg_right (exp_prefactor_le u) domConst_nonneg).trans
    (le_of_eq (by ring))

end Cvs.Xi.ThetaSumExponentialDecay
