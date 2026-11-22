import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# A bounded kernel gives a bounded integral operator

    `|K| ≤ M` on `[0,L]²`   ⟹   `|∫₀^L K s u · f u du| ≤ M·√L·‖f‖₂`

the estimate that makes a uniform kernel approximation converge in operator norm.
-/

noncomputable section

open MeasureTheory

namespace Cvs.Upstream.BoundedKernelIntegralOperator

/-- **Cauchy–Schwarz on the window.**  Non-negativity of `∫(|f| − c)²` for every `c` is a
quadratic in `c` with no real root below zero, and its discriminant is the bound. -/
theorem sq_integral_abs_le {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℝ}
    (h1 : IntervalIntegrable (fun u => |f u|) volume 0 L)
    (h2 : IntervalIntegrable (fun u => (f u) ^ 2) volume 0 L) :
    (∫ u in (0:ℝ)..L, |f u|) ^ 2 ≤ L * ∫ u in (0:ℝ)..L, (f u) ^ 2 := by
  rcases eq_or_lt_of_le hL with h | hLpos
  · simp [← h]
  -- the quadratic in `c`, non-negative because it integrates a square
  have key : ∀ c : ℝ, 0 ≤ (∫ u in (0:ℝ)..L, (f u) ^ 2)
      - 2 * c * (∫ u in (0:ℝ)..L, |f u|) + c ^ 2 * L := by
    intro c
    have hsq : (0:ℝ) ≤ ∫ u in (0:ℝ)..L, (|f u| - c) ^ 2 :=
      intervalIntegral.integral_nonneg hL fun u _ => sq_nonneg _
    have hexp : (∫ u in (0:ℝ)..L, (|f u| - c) ^ 2)
        = (∫ u in (0:ℝ)..L, (f u) ^ 2) - 2 * c * (∫ u in (0:ℝ)..L, |f u|) + c ^ 2 * L := by
      have hpt : ∀ u : ℝ, (|f u| - c) ^ 2 = (f u) ^ 2 - 2 * c * |f u| + c ^ 2 := by
        intro u; rw [show (|f u| - c) ^ 2 = |f u| ^ 2 - 2 * c * |f u| + c ^ 2 by ring, sq_abs]
      simp only [hpt]
      rw [intervalIntegral.integral_add (h2.sub (h1.const_mul _))
          (intervalIntegrable_const (c := c ^ 2)),
        intervalIntegral.integral_sub h2 (h1.const_mul _), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const]
      simp [mul_comm]
    linarith [hexp ▸ hsq]
  have h := key ((∫ u in (0:ℝ)..L, |f u|) / L)
  generalize hAv : (∫ u in (0:ℝ)..L, |f u|) = A at h ⊢
  generalize hBv : (∫ u in (0:ℝ)..L, (f u) ^ 2) = B at h ⊢
  have hid : L * (B - 2 * (A / L) * A + (A / L) ^ 2 * L) = L * B - A ^ 2 := by
    field_simp; ring
  nlinarith [mul_nonneg hLpos.le h, hid]

end Cvs.Upstream.BoundedKernelIntegralOperator
