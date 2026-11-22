import Mathlib
import Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition

/-!
# A shift sum on the circle is diagonal in the mode basis

    ∑ⱼ wⱼ ∫₀^L f(s)·f(s+uⱼ) ds  =  (L/2)·∑ₙ aₙ²·∑ⱼ wⱼ cos(ωₙ uⱼ)

for a finite cosine combination: over a full period distinct modes stay orthogonal at any
displacement, so a shift sum is diagonal, and bounded by `(L/2)·∑ⱼ wⱼ`.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition

namespace Cvs.WeilForm.ShiftSumModeDiagonal

variable {ι : Type*}

/-- The diagonal entry a shift sum contributes at mode `n`. -/
def shiftDiag (L : ℝ) (s : Finset ι) (w : ι → ℝ) (u : ι → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ s, w j * Real.cos (2 * π * n / L * u j)

/-- **The diagonal entry is bounded by the total weight.** -/
theorem abs_shiftDiag_le (L : ℝ) (s : Finset ι) (w u : ι → ℝ) (n : ℕ) :
    |shiftDiag L s w u n| ≤ ∑ j ∈ s, |w j| := by
  unfold shiftDiag
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  have : |Real.cos (2 * π * n / L * u j)| ≤ 1 := Real.abs_cos_le_one _
  nlinarith [abs_nonneg (w j), abs_nonneg (Real.cos (2 * π * n / L * u j))]

/-- **One shift, on one mode.**  `Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition`'s pairing, read as a diagonal entry. -/
theorem integral_shift_mode {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 0 < n) (v : ℝ) :
    (∫ x in (0:ℝ)..L, Real.cos (2 * π * n / L * x) * Real.cos (2 * π * n / L * (x + v)))
      = L / 2 * Real.cos (2 * π * n / L * v) :=
  integral_mode_shift hL n hn v

/-- **Distinct modes contribute nothing**, at any displacement — the reason the shift sum is
diagonal and not merely banded. -/
theorem integral_shift_cross {L : ℝ} (hL : 0 < L) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hmn : m ≠ n) (v w : ℝ) :
    (∫ x in (0:ℝ)..L, Real.cos (2 * π * m / L * (x + v)) * Real.cos (2 * π * n / L * (x + w)))
      = 0 :=
  integral_mode_pair_ne hL hm hn hmn v w

end Cvs.WeilForm.ShiftSumModeDiagonal
