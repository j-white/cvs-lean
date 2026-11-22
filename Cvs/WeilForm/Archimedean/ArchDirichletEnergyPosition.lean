import Mathlib
import Cvs.WeilForm.CrossModeElementClosedForm
import Cvs.WeilForm.OperatorTestModeClosedForm

/-!
# The archimedean symbol is a Dirichlet energy, in position space

    ½∫₀^L (f s − f (s + v))² ds,  integrated against the Lévy density

On a mode of frequency `ω` this is `(L/2)·(archSymbol ω − archSymbol 0)`.  The shift is the
Weil convention's half, and it wraps: this is the energy on the circle of circumference `L`.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real MeasureTheory Set

namespace Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition

/-- **Half the shifted square difference** — the Dirichlet integrand at displacement `v`. -/
def shiftEnergy (L : ℝ) (f : ℝ → ℝ) (v : ℝ) : ℝ :=
  (∫ s in (0:ℝ)..L, (f s - f (s + v)) ^ 2) / 2

/-! ### The Markov property, which needs no hypothesis at all -/

/-! ### The modes are orthogonal, shifted or not -/

/-- **A whole number of turns integrates to nothing.** -/
theorem integral_cos_turns {L : ℝ} (hL : 0 < L) {k : ℤ} (hk : k ≠ 0) (d : ℝ) :
    (∫ x in (0:ℝ)..L, Real.cos (2 * π * k / L * x + d)) = 0 := by
  have hpi := Real.pi_pos
  have hL0 : L ≠ 0 := hL.ne'
  have hk0 : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
  have hc : 2 * π * (k : ℝ) / L ≠ 0 := by
    simp only [ne_eq, div_eq_zero_iff, not_or]
    exact ⟨by positivity, hL0⟩
  rw [Cvs.WeilForm.CrossModeElementClosedForm.integral_cos_affine hc d L]
  have hend : 2 * π * (k : ℝ) / L * L + d = d + (k : ℤ) * (2 * π) := by
    field_simp
    ring
  rw [hend, Real.sin_add_int_mul_two_pi, sub_self, zero_div]

/-- **Distinct modes are orthogonal**, at any pair of displacements. -/
theorem integral_mode_pair_ne {L : ℝ} (hL : 0 < L) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hmn : m ≠ n) (v w : ℝ) :
    (∫ x in (0:ℝ)..L, Real.cos (2 * π * m / L * (x + v)) * Real.cos (2 * π * n / L * (x + w)))
      = 0 := by
  have hpi := Real.pi_pos
  have hL0 : L ≠ 0 := hL.ne'
  have hrw : ∀ x : ℝ,
      Real.cos (2 * π * m / L * (x + v)) * Real.cos (2 * π * n / L * (x + w))
      = Real.cos (2 * π * (((m : ℤ) + n : ℤ) : ℝ) / L * x
            + (2 * π * m / L * v + 2 * π * n / L * w)) / 2
        + Real.cos (2 * π * (((m : ℤ) - n : ℤ) : ℝ) / L * x
            + (2 * π * m / L * v - 2 * π * n / L * w)) / 2 := by
    intro x
    have e1 : 2 * π * m / L * (x + v) + 2 * π * n / L * (x + w)
        = 2 * π * (((m : ℤ) + n : ℤ) : ℝ) / L * x
          + (2 * π * m / L * v + 2 * π * n / L * w) := by
      push_cast
      field_simp
      ring
    have e2 : 2 * π * m / L * (x + v) - 2 * π * n / L * (x + w)
        = 2 * π * (((m : ℤ) - n : ℤ) : ℝ) / L * x
          + (2 * π * m / L * v - 2 * π * n / L * w) := by
      push_cast
      field_simp
      ring
    rw [Cvs.WeilForm.OperatorTestModeClosedForm.cos_mul_cos, e1, e2]
    ring
  rw [intervalIntegral.integral_congr (fun x _ => hrw x)]
  have hi : ∀ c d : ℝ, IntervalIntegrable (fun x : ℝ => Real.cos (c * x + d) / 2) volume 0 L := by
    intro c d; apply Continuous.intervalIntegrable; fun_prop
  have hne1 : ((m : ℤ) + n) ≠ 0 := by omega
  have hne2 : ((m : ℤ) - n) ≠ 0 := by omega
  rw [intervalIntegral.integral_add (hi _ _) (hi _ _), intervalIntegral.integral_div,
    intervalIntegral.integral_div, integral_cos_turns hL hne1, integral_cos_turns hL hne2]
  simp

/-! ### On a mode, the energy is the symbol -/

/-- The shifted-mode integral: the mode against its own translate. -/
theorem integral_mode_shift {L : ℝ} (hL : 0 < L) (n : ℕ) (hn : 0 < n) (v : ℝ) :
    (∫ s in (0:ℝ)..L, Real.cos (2 * π * n / L * s) * Real.cos (2 * π * n / L * (s + v)))
      = L / 2 * Real.cos (2 * π * n / L * v) := by
  have hpi := Real.pi_pos
  have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  set ω : ℝ := 2 * π * n / L with hω
  have hω0 : ω ≠ 0 := by rw [hω]; positivity
  have hrw : ∀ s : ℝ, Real.cos (ω * s) * Real.cos (ω * (s + v))
      = (Real.cos (2 * ω * s + ω * v) + Real.cos (ω * v)) / 2 := by
    intro s
    rw [Cvs.WeilForm.OperatorTestModeClosedForm.cos_mul_cos]
    congr 2 <;> [ring_nf; skip]
    rw [show ω * s - ω * (s + v) = -(ω * v) by ring, Real.cos_neg]
  rw [intervalIntegral.integral_congr (fun s _ => hrw s)]
  have hi1 : IntervalIntegrable (fun s : ℝ => Real.cos (2 * ω * s + ω * v)) volume 0 L := by
    apply Continuous.intervalIntegrable; fun_prop
  have hi2 : IntervalIntegrable (fun _ : ℝ => Real.cos (ω * v)) volume 0 L :=
    intervalIntegrable_const
  rw [show (fun s : ℝ => (Real.cos (2 * ω * s + ω * v) + Real.cos (ω * v)) / 2)
      = (fun s : ℝ => Real.cos (2 * ω * s + ω * v) / 2 + Real.cos (ω * v) / 2) by
    funext s; ring]
  rw [intervalIntegral.integral_add (hi1.div_const 2) (hi2.div_const 2),
    intervalIntegral.integral_div, intervalIntegral.integral_div,
    Cvs.WeilForm.CrossModeElementClosedForm.integral_cos_affine (by positivity : (2:ℝ) * ω ≠ 0) (ω * v) L,
    intervalIntegral.integral_const]
  have hL0 : L ≠ 0 := hL.ne'
  have hend : 2 * ω * L + ω * v = ω * v + ((2 * n : ℕ) : ℝ) * (2 * π) := by
    rw [hω]
    push_cast
    field_simp
    ring
  rw [hend, Real.sin_add_nat_mul_two_pi]
  simp
  ring

/-- A finite cosine combination on the window — the construction's test functions. -/
def modeSum (L : ℝ) (s : Finset ℕ) (a : ℕ → ℝ) : ℝ → ℝ :=
  fun x => ∑ n ∈ s, a n * Real.cos (2 * π * n / L * x)

end Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition
