import Mathlib
import Cvs.Finite.TruncationZeroFreeOffAxes

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Frequencies carried by the sum

The window spans a whole number of periods of every carried frequency, so a sum of two of them
spans one too, and two such frequencies cancel exactly when their labels do. Recentring at a
carried frequency contributes a half-turn for each unit of its label.
-/

noncomputable section

open Real

namespace Cvs.Finite.GridFrequencySums

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A sum of two carried frequencies still spans a whole number of periods. -/
theorem exp_omega_add_mul {L : ℝ} (hL : L ≠ 0) (mode : ι → ℤ) (i j : ι) :
    Complex.exp (Complex.I * (((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i : ℝ) : ℂ)
        + ((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode j : ℝ) : ℂ)) * (L : ℂ)) = 1 := by
  have h : Complex.I * (((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i : ℝ) : ℂ)
        + ((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode j : ℝ) : ℂ)) * (L : ℂ)
      = ((mode i + mode j : ℤ) : ℂ) * (2 * ((π : ℝ) : ℂ) * Complex.I) := by
    simp only [Cvs.Finite.TruncationZeroFreeOffAxes.omega]
    have hLC : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
    push_cast
    field_simp
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

/-- Two carried frequencies cancel exactly when their labels do. -/
theorem omega_add_eq_zero_iff {L : ℝ} (hL : L ≠ 0) (mode : ι → ℤ) (i j : ι) :
    ((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i : ℝ) : ℂ)
        + ((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode j : ℝ) : ℂ) = 0
      ↔ mode i + mode j = 0 := by
  have hLC : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
  have hpi : ((π : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hc0 : (2 * ((π : ℝ) : ℂ) / (L : ℂ)) ≠ 0 :=
    div_ne_zero (mul_ne_zero two_ne_zero hpi) hLC
  have hfac : ((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i : ℝ) : ℂ)
        + ((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode j : ℝ) : ℂ)
      = (2 * ((π : ℝ) : ℂ) / (L : ℂ)) * ((mode i + mode j : ℤ) : ℂ) := by
    simp only [Cvs.Finite.TruncationZeroFreeOffAxes.omega]
    push_cast
    ring
  rw [hfac, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h hc0
    · exact_mod_cast h
  · intro h
    exact Or.inr (by exact_mod_cast congrArg (fun n : ℤ => (n : ℂ)) h)

/-- The half-turn the midpoint contributes at a carried frequency. -/
theorem phase_at_grid {L : ℝ} (hL : L ≠ 0) (mode : ι → ℤ) (j : ι) :
    Complex.exp (-(Complex.I * ((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode j : ℝ) : ℂ) * (L : ℂ) / 2))
      = (-1 : ℂ) ^ (mode j) := by
  have hLC : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
  have harg : -(Complex.I * ((Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode j : ℝ) : ℂ) * (L : ℂ) / 2)
      = ((mode j : ℤ) : ℂ) * (-(((π : ℝ) : ℂ)) * Complex.I) := by
    simp only [Cvs.Finite.TruncationZeroFreeOffAxes.omega]
    push_cast
    field_simp
  have hbase : Complex.exp (-(((π : ℝ) : ℂ)) * Complex.I) = -1 := by
    rw [show -(((π : ℝ) : ℂ)) * Complex.I = -(((π : ℝ) : ℂ) * Complex.I) from by ring,
      Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  rw [harg, Complex.exp_int_mul, hbase]

end Cvs.Finite.GridFrequencySums
