import Mathlib

/-!
# A minimiser has definite parity

    Q = Q_even + Q_odd,   Q_even ≥ λ_E·m_E,   Q_odd ≥ λ_O·m_O,   m_E + m_O = 1

If `λ_E < λ_O` then a vector achieving `λ_E` carries no odd mass at all.  So the global
ground state does not mix the sectors — it is even or odd, never both.
-/

set_option maxHeartbeats 1600000

noncomputable section

namespace Cvs.StepA.MinimiserDefiniteParity

/-- **The lighter sector takes everything.**  A block-diagonal form whose sectors have
different floors puts its minimiser wholly in the lower one. -/
theorem mass_eq_zero_of_lt {lamE lamO mE mO QE QO : ℝ} (hlt : lamE < lamO)
    (hmO : 0 ≤ mO) (hunit : mE + mO = 1)
    (hQE : lamE * mE ≤ QE) (hQO : lamO * mO ≤ QO) (hmin : QE + QO ≤ lamE) :
    mO = 0 := by
  have hchain : lamE + (lamO - lamE) * mO ≤ QE + QO := by
    have : lamE * mE + lamO * mO = lamE + (lamO - lamE) * mO := by
      have hmE : mE = 1 - mO := by linarith
      rw [hmE]
      ring
    linarith [hQE, hQO, this]
  have hle : (lamO - lamE) * mO ≤ 0 := by linarith
  have hpos : 0 < lamO - lamE := by linarith
  by_contra hne
  have hmOpos : 0 < mO := lt_of_le_of_ne hmO (Ne.symm hne)
  nlinarith [hle, hpos, hmOpos]

/-- **The same, read as a parity statement.**  With the even sector strictly lower, a global
minimiser is purely even. -/
theorem even_of_lt {lamE lamO mE mO QE QO : ℝ} (hlt : lamE < lamO)
    (hmO : 0 ≤ mO) (hunit : mE + mO = 1)
    (hQE : lamE * mE ≤ QE) (hQO : lamO * mO ≤ QO) (hmin : QE + QO ≤ lamE) :
    mE = 1 := by
  have := mass_eq_zero_of_lt hlt hmO hunit hQE hQO hmin
  linarith

end Cvs.StepA.MinimiserDefiniteParity
