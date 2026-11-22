import Mathlib
import Cvs.Finite.SymmetricModeSet

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A two-mode restriction on actual low-head damping

The constant and first cosine modes force a lower bound on the tail reserve
in the scalar-damped low-head inequality, for every choice of normal.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Real Matrix Finset
namespace Cvs.WeilForm.TwoModeLowHeadDamping
open Cvs.Finite.SymmetricModeSet (Idx mode negI)

/-- The even coefficients of a constant plus first cosine. -/
def twoMode (N : ℕ) (α β : ℝ) : Idx N → ℝ
  | none => α
  | some (k,_) => if (k : ℕ)=0 then β else 0

theorem twoMode_even (N : ℕ) (α β : ℝ) (i : Idx N) :
    twoMode N α β (negI N i)=twoMode N α β i := by
  cases i <;> rfl

theorem twoMode_pair {N : ℕ} (hN : 0<N) (α β : ℝ) (n : Idx N → ℝ) :
    twoMode N α β ⬝ᵥ n=α*n none+
      β*(n (some (⟨0,hN⟩,true))+n (some (⟨0,hN⟩,false))) := by
  obtain ⟨N,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hN)
  simp [dotProduct, twoMode, Fintype.sum_option, Fintype.sum_prod_type,
    Fin.sum_univ_succ]
  ring

end Cvs.WeilForm.TwoModeLowHeadDamping
