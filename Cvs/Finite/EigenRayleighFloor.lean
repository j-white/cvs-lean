import Mathlib

/-!
# An eigenvalue's Rayleigh identity, and the floor it obeys

    λ·‖η‖² = ∑ₙ Dₙηₙ² + c·⟨v,η⟩²

Pairing the eigen-equation with its own eigenvector.  With `c ≥ 0` and a diagonal bounded
below, no eigenvalue can sit under that bound.
-/

set_option maxHeartbeats 1600000

noncomputable section

namespace Cvs.Finite.EigenRayleighFloor

variable {ι : Type*}

/-- **The Rayleigh identity.**  Pairing the coordinate equation with `η` itself. -/
theorem rayleigh_of_eigen {D v η : ι → ℝ} {c lam : ℝ}
    (hEL : ∀ n : ι, (lam - D n) * η n = c * (∑' k : ι, v k * η k) * v n)
    (hnorm : Summable fun n : ι => (η n) ^ 2)
    (hD : Summable fun n : ι => D n * (η n) ^ 2) :
    lam * (∑' n : ι, (η n) ^ 2)
      = (∑' n : ι, D n * (η n) ^ 2) + c * (∑' n : ι, v n * η n) ^ 2 := by
  set S : ℝ := ∑' n : ι, v n * η n with hS
  have hpair : ∀ n : ι, (lam - D n) * (η n) ^ 2 = c * S * (v n * η n) := by
    intro n
    have := hEL n
    calc (lam - D n) * (η n) ^ 2 = ((lam - D n) * η n) * η n := by ring
      _ = (c * S * v n) * η n := by rw [this]
      _ = c * S * (v n * η n) := by ring
  have hleft : Summable fun n : ι => (lam - D n) * (η n) ^ 2 := by
    have := (hnorm.mul_left lam).sub hD
    refine this.congr fun n => ?_
    ring
  have hsum : ∑' n : ι, (lam - D n) * (η n) ^ 2 = c * S * S := by
    rw [tsum_congr hpair, tsum_mul_left, ← hS]
  have hsplit : ∑' n : ι, (lam - D n) * (η n) ^ 2
      = lam * (∑' n : ι, (η n) ^ 2) - ∑' n : ι, D n * (η n) ^ 2 := by
    rw [← tsum_mul_left, ← Summable.tsum_sub (hnorm.mul_left lam) hD]
    exact tsum_congr fun n => by ring
  rw [hsplit] at hsum
  have : lam * (∑' n : ι, (η n) ^ 2) = (∑' n : ι, D n * (η n) ^ 2) + c * S * S := by linarith
  rw [this]
  ring

/-- **No eigenvalue sits below the diagonal's floor.** -/
theorem le_of_eigen {D v η : ι → ℝ} {c lam D₀ : ℝ} (hc : 0 ≤ c) (hD₀ : ∀ n : ι, D₀ ≤ D n)
    (hEL : ∀ n : ι, (lam - D n) * η n = c * (∑' k : ι, v k * η k) * v n)
    (hnorm : Summable fun n : ι => (η n) ^ 2)
    (hD : Summable fun n : ι => D n * (η n) ^ 2)
    (hunit : ∑' n : ι, (η n) ^ 2 = 1) :
    D₀ ≤ lam := by
  have hray := rayleigh_of_eigen hEL hnorm hD
  rw [hunit, mul_one] at hray
  have hdiag : D₀ ≤ ∑' n : ι, D n * (η n) ^ 2 := by
    have hle : ∀ n : ι, D₀ * (η n) ^ 2 ≤ D n * (η n) ^ 2 := fun n =>
      mul_le_mul_of_nonneg_right (hD₀ n) (sq_nonneg _)
    have := Summable.tsum_le_tsum hle (hnorm.mul_left D₀) hD
    rwa [tsum_mul_left, hunit, mul_one] at this
  have hrank : 0 ≤ c * (∑' n : ι, v n * η n) ^ 2 := by positivity
  linarith

end Cvs.Finite.EigenRayleighFloor
