import Mathlib

/-!
# Cauchy–Schwarz for integrals

The discriminant of a nonnegative quadratic in the shift parameter.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Finset

namespace Cvs.Upstream.CauchySchwarzInterval

variable {f g : ℝ → ℝ}

/-- **The scalar discriminant.**  A quadratic nonnegative on the whole line has nonpositive
discriminant. -/
theorem disc_le {A B C : ℝ} (hC : 0 ≤ C) (h : ∀ t : ℝ, 0 ≤ A + 2 * B * t + C * t ^ 2) :
    B ^ 2 ≤ A * C := by
  rcases eq_or_lt_of_le hC with hC0 | hCpos
  · have hB : B = 0 := by
      by_contra hne
      have hb := h (-(A + 1) / (2 * B))
      rw [← hC0, zero_mul, add_zero] at hb
      have hcalc : 2 * B * (-(A + 1) / (2 * B)) = -(A + 1) := by field_simp
      rw [hcalc] at hb
      linarith
    rw [hB, ← hC0]
    norm_num
  · have := h (-B / C)
    field_simp at this
    nlinarith [this, hCpos]

/-- **Cauchy–Schwarz on a window.**  The same discriminant argument, for interval integrals, where
continuity supplies every integrability side condition. -/
theorem intervalIntegral_mul_sq_le {L : ℝ} (hL : (0:ℝ) ≤ L) (hfc : Continuous f)
    (hgc : Continuous g) :
    (∫ x in (0:ℝ)..L, f x * g x) ^ 2
      ≤ (∫ x in (0:ℝ)..L, f x ^ 2) * ∫ x in (0:ℝ)..L, g x ^ 2 := by
  have hCnn : 0 ≤ ∫ x in (0:ℝ)..L, g x ^ 2 :=
    intervalIntegral.integral_nonneg hL fun x _ => sq_nonneg _
  refine disc_le hCnn fun t => ?_
  have hnn : (0:ℝ) ≤ ∫ x in (0:ℝ)..L, (f x + t * g x) ^ 2 :=
    intervalIntegral.integral_nonneg hL fun x _ => sq_nonneg _
  have hexp : (∫ x in (0:ℝ)..L, (f x + t * g x) ^ 2)
      = (∫ x in (0:ℝ)..L, f x ^ 2) + 2 * t * (∫ x in (0:ℝ)..L, f x * g x)
        + t ^ 2 * ∫ x in (0:ℝ)..L, g x ^ 2 := by
    have hf2c : Continuous fun x : ℝ => f x ^ 2 := by fun_prop
    have hA : Continuous fun x : ℝ => 2 * t * (f x * g x) := by fun_prop
    have hB : Continuous fun x : ℝ => t ^ 2 * g x ^ 2 := by fun_prop
    have hin : Continuous fun x : ℝ => 2 * t * (f x * g x) + t ^ 2 * g x ^ 2 := hA.add hB
    rw [intervalIntegral.integral_congr
      (g := fun x : ℝ => f x ^ 2 + (2 * t * (f x * g x) + t ^ 2 * g x ^ 2))
      (fun x _ => by ring),
      intervalIntegral.integral_add (hf2c.intervalIntegrable _ _)
        (hin.intervalIntegrable _ _),
      intervalIntegral.integral_add (hA.intervalIntegrable _ _) (hB.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    ring
  rw [hexp] at hnn
  linarith [hnn]

end Cvs.Upstream.CauchySchwarzInterval
