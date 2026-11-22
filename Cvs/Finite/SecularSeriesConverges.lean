import Mathlib
import Cvs.Finite.SecularDecreasingInGap

/-!
# The secular series converges

    ∑ₙ vₙ²/(λ − Dₙ)

Off a finite set the denominator exceeds one in size, so the terms are dominated by `vₙ²`.
Properness of the diagonal and square-summability of the rank-one vector are all it takes.
-/

set_option maxHeartbeats 1600000

noncomputable section

namespace Cvs.Finite.SecularSeriesConverges

variable {ι : Type*} [DecidableEq ι]

/-- **The secular series is summable.** -/
theorem summable_secular {D v : ι → ℝ} {lam : ℝ}
    (hv : Summable fun n : ι => (v n) ^ 2)
    (hfin : {n : ι | D n < lam + 1}.Finite) :
    Summable fun n : ι => (v n) ^ 2 / (lam - D n) := by
  classical
  set T : Finset ι := hfin.toFinset with hT
  have hhead : Summable fun n : ι => if n ∈ T then (v n) ^ 2 / (lam - D n) else 0 :=
    summable_of_ne_finset_zero (s := T) fun n hn => by simp [hn]
  have htail : Summable fun n : ι => if n ∈ T then (0:ℝ) else (v n) ^ 2 / (lam - D n) := by
    refine Summable.of_norm_bounded hv fun n => ?_
    by_cases h : n ∈ T
    · rw [if_pos h, norm_zero]
      positivity
    · have hge : lam + 1 ≤ D n := by
        have : n ∉ {n : ι | D n < lam + 1} := by simpa [hT] using h
        exact not_lt.mp (by simpa using this)
      have hden : 1 ≤ |lam - D n| := by
        rw [abs_of_nonpos (by linarith)]
        linarith
      have hpos : (0:ℝ) < |lam - D n| := by linarith
      simp only [h, if_false, Real.norm_eq_abs, abs_div]
      rw [div_le_iff₀ hpos, abs_of_nonneg (sq_nonneg (v n))]
      nlinarith [sq_nonneg (v n), hden]
  refine (hhead.add htail).congr fun n => ?_
  by_cases h : n ∈ T <;> simp [h]

/-- **The gap hypothesis, from the two lowest levels.**  If every level is either the bottom
one or at least the second, two points strictly between them have no level in between. -/
theorem side_of_between {D : ι → ℝ} {D₀ D₁ lam₁ lam₂ : ℝ}
    (hlevels : ∀ n : ι, D n = D₀ ∨ D₁ ≤ D n)
    (h₁ : D₀ < lam₁) (h₂ : lam₂ < D₁) (h₁₂ : lam₁ < lam₂) (n : ι) :
    0 < (lam₁ - D n) * (lam₂ - D n) := by
  rcases hlevels n with h | h
  · rw [h]
    have hb₁ : 0 < lam₁ - D₀ := by linarith
    have hb₂ : 0 < lam₂ - D₀ := by linarith
    positivity
  · have hb₁ : lam₁ - D n < 0 := by linarith
    have hb₂ : lam₂ - D n < 0 := by linarith
    nlinarith [hb₁, hb₂]

/-- **Isolation.**  Between the bottom level and the next, an eigenvalue is unique — so the
bottom of the perturbed form is isolated, not merely simple. -/
theorem unique_in_gap {D v : ι → ℝ} {D₀ D₁ c lam₁ lam₂ : ℝ} (hc : 0 < c)
    (hlevels : ∀ n : ι, D n = D₀ ∨ D₁ ≤ D n)
    (hv : Summable fun n : ι => (v n) ^ 2)
    (hfin₁ : {n : ι | D n < lam₁ + 1}.Finite) (hfin₂ : {n : ι | D n < lam₂ + 1}.Finite)
    {m : ι} (hvm : v m ≠ 0)
    (hlo₁ : D₀ < lam₁) (hhi₂ : lam₂ < D₁) (hlt : lam₁ < lam₂)
    (h₁ : c * (∑' n : ι, (v n) ^ 2 / (lam₁ - D n)) = 1)
    (h₂ : c * (∑' n : ι, (v n) ^ 2 / (lam₂ - D n)) = 1) : False :=
  Cvs.Finite.SecularDecreasingInGap.eq_of_secular hlt
    (side_of_between hlevels hlo₁ hhi₂ hlt)
    (summable_secular hv hfin₁) (summable_secular hv hfin₂) hvm hc h₁ h₂

end Cvs.Finite.SecularSeriesConverges
