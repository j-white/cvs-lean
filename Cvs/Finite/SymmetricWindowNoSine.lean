import Mathlib
import Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition

/-!
# A symmetric window function has no sine content

    g (L−x) = g x  ⟹  ∫₀ᴸ g x · sin(2πnx/L) dx = 0,  and the cosine modes are symmetric

which is why the even sector is exactly what the cosine modes reach.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Filter

namespace Cvs.Finite.SymmetricWindowNoSine

/-- **The cosine modes are symmetric about the window's centre.** -/
theorem cos_mode_symm {L : ℝ} (hL : L ≠ 0) (n : ℕ) (x : ℝ) :
    Real.cos (2 * π * n / L * (L - x)) = Real.cos (2 * π * n / L * x) := by
  have hrw : 2 * π * (n : ℝ) / L * (L - x) = (n : ℝ) * (2 * π) - 2 * π * n / L * x := by
    field_simp
  rw [hrw, Real.cos_nat_mul_two_pi_sub]

/-- **A mode sum is symmetric about the window's centre.** -/
theorem modeSum_symm {L : ℝ} (hL : L ≠ 0) (s : Finset ℕ) (a : ℕ → ℝ) (x : ℝ) :
    Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L s a (L - x) = Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L s a x := by
  show (∑ n ∈ s, a n * Real.cos (2 * π * n / L * (L - x)))
    = ∑ n ∈ s, a n * Real.cos (2 * π * n / L * x)
  exact Finset.sum_congr rfl fun n _ => by rw [cos_mode_symm hL n x]

end Cvs.Finite.SymmetricWindowNoSine
