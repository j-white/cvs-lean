import Mathlib
import Cvs.Finite.ProperDiagonalMinimum
import Cvs.Finite.SecularDecreasingInGap

/-!
# The minimiser's secular equation, and isolation

    ⟨v,η⟩ ≠ 0,   c·∑ vₙ²/(λ − Dₙ) = 1

A separated eigenvalue's eigenvector cannot be orthogonal to the rank-one vector, so it obeys
the secular equation — and then `Cvs.Finite.ProperDiagonalMinimum` leaves room for only one such eigenvalue in the gap.
-/

set_option maxHeartbeats 1600000

noncomputable section

namespace Cvs.Finite.MinimiserSecularIsolation

variable {ι : Type*} [DecidableEq ι]

/-- **A separated eigenvalue's eigenvector meets the rank one.** -/
theorem inner_ne_zero_of_eigen {D v η : ι → ℝ} {c lam : ℝ}
    (hEL : ∀ n : ι, (lam - D n) * η n = c * (∑' k : ι, v k * η k) * v n)
    (hsep : ∀ n : ι, lam ≠ D n) (hne : ∃ n : ι, η n ≠ 0) :
    (∑' k : ι, v k * η k) ≠ 0 := by
  intro hS
  obtain ⟨n, hn⟩ := hne
  have h := hEL n
  rw [hS, mul_zero, zero_mul] at h
  rcases mul_eq_zero.mp h with h1 | h1
  · exact hsep n (by linarith [sub_eq_zero.mp h1])
  · exact hn h1

/-- **So it obeys the secular equation.** -/
theorem secular_of_eigen {D v η : ι → ℝ} {c lam : ℝ}
    (hEL : ∀ n : ι, (lam - D n) * η n = c * (∑' k : ι, v k * η k) * v n)
    (hsep : ∀ n : ι, lam ≠ D n) (hne : ∃ n : ι, η n ≠ 0) :
    c * (∑' n : ι, (v n) ^ 2 / (lam - D n)) = 1 :=
  Cvs.Finite.SecularDecreasingInGap.secular_eq hEL (fun n => sub_ne_zero.mpr (hsep n))
    (inner_ne_zero_of_eigen hEL hsep hne)

/-- A point strictly inside the first gap meets no level. -/
theorem ne_diag_of_between {D : ι → ℝ} {n₀ m₁ : ι} {mu : ℝ}
    (hD₁ : ∀ n : ι, n ≠ n₀ → D m₁ ≤ D n) (hlo : D n₀ < mu) (hhi : mu < D m₁) (n : ι) :
    mu ≠ D n := by
  rcases Cvs.Finite.ProperDiagonalMinimum.levels_split hD₁ n with h | h
  · rw [h]; exact ne_of_gt hlo
  · exact ne_of_lt (lt_of_lt_of_le hhi h)

/-- **Isolation.**  Two eigenvalues strictly inside the first gap are the same eigenvalue. -/
theorem eq_of_both_in_gap {D v : ι → ℝ} {c : ℝ} (hc : 0 < c)
    (hproper : ∀ M : ℝ, {n : ι | D n < M}.Finite)
    (hvsum : Summable fun n : ι => (v n) ^ 2) {mv : ι} (hvm : v mv ≠ 0)
    {n₀ m₁ : ι} (hD₁ : ∀ n : ι, n ≠ n₀ → D m₁ ≤ D n)
    {lam mu : ℝ} {η η' : ι → ℝ}
    (hELa : ∀ n : ι, (lam - D n) * η n = c * (∑' k : ι, v k * η k) * v n)
    (hELb : ∀ n : ι, (mu - D n) * η' n = c * (∑' k : ι, v k * η' k) * v n)
    (hnea : ∃ n : ι, η n ≠ 0) (hneb : ∃ n : ι, η' n ≠ 0)
    (hloa : D n₀ < lam) (hhia : lam < D m₁)
    (hlob : D n₀ < mu) (hhib : mu < D m₁) :
    lam = mu := by
  have hseca := secular_of_eigen hELa (ne_diag_of_between hD₁ hloa hhia) hnea
  have hsecb := secular_of_eigen hELb (ne_diag_of_between hD₁ hlob hhib) hneb
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact Cvs.Finite.ProperDiagonalMinimum.unique_eigen_in_gap hc hproper hvsum hvm hD₁ h hloa hhib
      hseca hsecb
  · exact Cvs.Finite.ProperDiagonalMinimum.unique_eigen_in_gap hc hproper hvsum hvm hD₁ h hlob hhia
      hsecb hseca

end Cvs.Finite.MinimiserSecularIsolation
