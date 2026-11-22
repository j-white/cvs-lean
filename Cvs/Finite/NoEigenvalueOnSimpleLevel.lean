import Mathlib

/-!
# An eigenvalue cannot sit on a simple diagonal level

    (λ − Dₙ)·ηₙ = c·⟨v,η⟩·vₙ,   {n : Dₙ = λ} = {m},   c·vₘ ≠ 0   ⟹   η = 0

so for a diagonal form perturbed by a rank one, any eigenvalue that meets the diagonal
spectrum must sit on a *degenerate* level.  This is the separation `an earlier result` consumes.
-/

set_option maxHeartbeats 1600000

noncomputable section

namespace Cvs.Finite.NoEigenvalueOnSimpleLevel

variable {ι : Type*} [Countable ι] [DecidableEq ι]

/-- **No eigenvector on a simple level.**  If the rank-one vector does not vanish there, an
eigenvalue of `D + c·v⊗v` cannot equal a diagonal entry whose level set is a single mode. -/
theorem no_eigen_on_simple_level {D v η : ι → ℝ} {c lam : ℝ} {m : ι}
    (heig : ∀ n : ι, (lam - D n) * η n = c * (∑' k : ι, v k * η k) * v n)
    (hlevel : ∀ n : ι, D n = lam → n = m) (hm : D m = lam) (hcv : c * v m ≠ 0) :
    η = 0 := by
  classical
  set S : ℝ := ∑' k : ι, v k * η k with hS
  -- at the level itself the left side vanishes, so the pairing does
  have hS0 : S = 0 := by
    have h := heig m
    rw [hm, sub_self, zero_mul] at h
    have : c * S * v m = 0 := h.symm
    have hfac : (c * v m) * S = 0 := by linarith [this]; 
    rcases mul_eq_zero.mp hfac with h1 | h1
    · exact absurd h1 hcv
    · exact h1
  -- then every coordinate off the level vanishes
  have hoff : ∀ n : ι, n ≠ m → η n = 0 := by
    intro n hn
    have h := heig n
    rw [hS0, mul_zero, zero_mul] at h
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd (hlevel n (by linarith [sub_eq_zero.mp h1])) hn
    · exact h1
  -- so the vector sits on one mode, and the pairing reads off its coefficient
  have hsingle : S = v m * η m := by
    rw [hS]
    refine tsum_eq_single m fun n hn => ?_
    rw [hoff n hn, mul_zero]
  have hzero : η m = 0 := by
    have hv : v m ≠ 0 := fun h => hcv (by rw [h, mul_zero])
    have : v m * η m = 0 := by rw [← hsingle, hS0]
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 hv
    · exact h1
  funext n
  by_cases h : n = m
  · rw [h]; simpa using hzero
  · simpa using hoff n h

end Cvs.Finite.NoEigenvalueOnSimpleLevel
