import Mathlib
import Cvs.WeilForm.PoleTermRankTwo

/-!
# The pole term on the even subspace, and which way it moves

On `A = B` the rank-two pole term is the positive rank one `2A²`, and `A(|a|) ≥ |A(a)|`, so
under `a ↦ |a|` it rises while a Dirichlet form falls.  RH.md §3.23 carries the reduction.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real Finset

namespace Cvs.WeilForm.PoleTermEvenRankOne

open Cvs.WeilForm.PoleTermRankTwo

/-- **On the even subspace the pole term is a positive rank one.**  `Cvs.WeilForm.PoleTermRankTwo` gives `2AB`; where
the two functionals agree that is `2A²`. -/
theorem poleForm_even {ι : Type*} (s : Finset ι) (x a : ι → ℝ)
    (h : plusFun s x a = minusFun s x a) :
    poleForm s x a = 2 * (plusFun s x a) ^ 2 := by
  rw [poleForm_eq, h]
  ring

/-- Hence it is nonnegative there — the pole term helps, on the subspace where the ground
state lives. -/
theorem poleForm_even_nonneg {ι : Type*} (s : Finset ι) (x a : ι → ℝ)
    (h : plusFun s x a = minusFun s x a) :
    0 ≤ poleForm s x a := by
  rw [poleForm_even s x a h]
  positivity

/-- **And it moves the wrong way.**  `|A(a)| ≤ A(|a|)`, so replacing `a` by `|a|` cannot
decrease the rank one. -/
theorem abs_plusFun_le {ι : Type*} (s : Finset ι) (x a : ι → ℝ) :
    |plusFun s x a| ≤ plusFun s x (fun i => |a i|) := by
  unfold plusFun
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]

/-- So the rank one rises under `a ↦ |a|`. -/
theorem plusFun_sq_le_abs {ι : Type*} (s : Finset ι) (x a : ι → ℝ) :
    (plusFun s x a) ^ 2 ≤ (plusFun s x (fun i => |a i|)) ^ 2 := by
  have h := abs_plusFun_le s x a
  have h0 : (0:ℝ) ≤ |plusFun s x a| := abs_nonneg _
  nlinarith [sq_abs (plusFun s x a)]

/-- **The reduction, named.**  The total falls under `a ↦ |a|` exactly when the Dirichlet
decrease dominates the rank-one increase — Connes' step (a), restated and not proved. -/
theorem total_le_iff {ι : Type*} (s : Finset ι) (x a : ι → ℝ)
    (Qdir : (ι → ℝ) → ℝ) :
    Qdir (fun i => |a i|) + 2 * (plusFun s x (fun i => |a i|)) ^ 2
        ≤ Qdir a + 2 * (plusFun s x a) ^ 2
      ↔ 2 * (plusFun s x (fun i => |a i|)) ^ 2 - 2 * (plusFun s x a) ^ 2
        ≤ Qdir a - Qdir (fun i => |a i|) := by
  constructor <;> intro h <;> linarith

end Cvs.WeilForm.PoleTermEvenRankOne
