import Mathlib

/-!
# The secular function is strictly decreasing in a gap

    λ ↦ ∑ₙ vₙ²/(λ − Dₙ)

falls strictly as `λ` rises, so long as no `Dₙ` lies between the two points.  Hence at most
one eigenvalue of a rank-one perturbation sits between consecutive diagonal levels.
-/

set_option maxHeartbeats 1600000

noncomputable section

namespace Cvs.Finite.SecularDecreasingInGap

variable {ι : Type*}

/-- **One term falls**, on either side of the level: the difference of the two quotients is
`(λ₁ − λ₂)` over a positive product. -/
theorem term_lt {D v : ι → ℝ} {lam₁ lam₂ : ℝ} (hlt : lam₁ < lam₂) (n : ι)
    (hside : 0 < (lam₁ - D n) * (lam₂ - D n)) (hv : v n ≠ 0) :
    (v n) ^ 2 / (lam₂ - D n) < (v n) ^ 2 / (lam₁ - D n) := by
  have hne₁ : lam₁ - D n ≠ 0 := by
    intro h; rw [h, zero_mul] at hside; exact absurd hside (lt_irrefl 0)
  have hne₂ : lam₂ - D n ≠ 0 := by
    intro h; rw [h, mul_zero] at hside; exact absurd hside (lt_irrefl 0)
  have hvsq : 0 < (v n) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hv))
  have hid : (v n) ^ 2 / (lam₂ - D n) - (v n) ^ 2 / (lam₁ - D n)
      = (v n) ^ 2 * (lam₁ - lam₂) / ((lam₁ - D n) * (lam₂ - D n)) := by
    field_simp
    ring
  have hneg : (v n) ^ 2 * (lam₁ - lam₂) / ((lam₁ - D n) * (lam₂ - D n)) < 0 := by
    apply div_neg_of_neg_of_pos _ hside
    nlinarith [hvsq, hlt]
  linarith [hid, hneg]

/-- The same, without strictness, so it can be summed termwise. -/
theorem term_le {D v : ι → ℝ} {lam₁ lam₂ : ℝ} (hlt : lam₁ < lam₂) (n : ι)
    (hside : 0 < (lam₁ - D n) * (lam₂ - D n)) :
    (v n) ^ 2 / (lam₂ - D n) ≤ (v n) ^ 2 / (lam₁ - D n) := by
  by_cases hv : v n = 0
  · simp [hv]
  · exact (term_lt hlt n hside hv).le

/-- **The secular function falls strictly across a gap.** -/
theorem secular_lt {D v : ι → ℝ} {lam₁ lam₂ : ℝ} (hlt : lam₁ < lam₂)
    (hside : ∀ n : ι, 0 < (lam₁ - D n) * (lam₂ - D n))
    (hsum₁ : Summable fun n : ι => (v n) ^ 2 / (lam₁ - D n))
    (hsum₂ : Summable fun n : ι => (v n) ^ 2 / (lam₂ - D n))
    {m : ι} (hv : v m ≠ 0) :
    (∑' n : ι, (v n) ^ 2 / (lam₂ - D n)) < ∑' n : ι, (v n) ^ 2 / (lam₁ - D n) :=
  Summable.tsum_lt_tsum (i := m) (fun n => term_le hlt n (hside n))
    (term_lt hlt m (hside m) hv) hsum₂ hsum₁

/-! ### The secular equation, and what its monotonicity forbids -/

/-- **The secular equation.**  An eigenvalue off the diagonal spectrum satisfies
`c·∑ vₙ²/(λ − Dₙ) = 1`. -/
theorem secular_eq {D v η : ι → ℝ} {c lam : ℝ}
    (hEL : ∀ n : ι, (lam - D n) * η n = c * (∑' k : ι, v k * η k) * v n)
    (hden : ∀ n : ι, lam - D n ≠ 0) (hS : (∑' k : ι, v k * η k) ≠ 0) :
    c * (∑' n : ι, (v n) ^ 2 / (lam - D n)) = 1 := by
  set S : ℝ := ∑' k : ι, v k * η k with hSdef
  have hcoord : ∀ n : ι, v n * η n = c * S * ((v n) ^ 2 / (lam - D n)) := by
    intro n
    have hη : η n = c * S * v n / (lam - D n) := by
      rw [eq_div_iff (hden n)]
      linarith [hEL n]
    rw [hη]
    field_simp
  have hsum : S = c * S * ∑' n : ι, (v n) ^ 2 / (lam - D n) := by
    calc S = ∑' n : ι, v n * η n := hSdef
      _ = ∑' n : ι, c * S * ((v n) ^ 2 / (lam - D n)) := tsum_congr hcoord
      _ = c * S * ∑' n : ι, (v n) ^ 2 / (lam - D n) := tsum_mul_left
  have := mul_right_cancel₀ hS (by linarith [hsum] :
    (c * ∑' n : ι, (v n) ^ 2 / (lam - D n)) * S = 1 * S)
  linarith [this]

/-- **At most one eigenvalue in a gap.**  Two eigenvalues with no diagonal level between them
would give the secular function the same value twice. -/
theorem eq_of_secular {D v : ι → ℝ} {c lam₁ lam₂ : ℝ} (hlt : lam₁ < lam₂)
    (hside : ∀ n : ι, 0 < (lam₁ - D n) * (lam₂ - D n))
    (hsum₁ : Summable fun n : ι => (v n) ^ 2 / (lam₁ - D n))
    (hsum₂ : Summable fun n : ι => (v n) ^ 2 / (lam₂ - D n))
    {m : ι} (hv : v m ≠ 0) (hc : 0 < c)
    (h₁ : c * (∑' n : ι, (v n) ^ 2 / (lam₁ - D n)) = 1)
    (h₂ : c * (∑' n : ι, (v n) ^ 2 / (lam₂ - D n)) = 1) : False := by
  have hstrict := secular_lt hlt hside hsum₁ hsum₂ hv
  have : c * (∑' n : ι, (v n) ^ 2 / (lam₂ - D n))
      < c * ∑' n : ι, (v n) ^ 2 / (lam₁ - D n) :=
    mul_lt_mul_of_pos_left hstrict hc
  rw [h₁, h₂] at this
  exact absurd this (lt_irrefl 1)

end Cvs.Finite.SecularDecreasingInGap
