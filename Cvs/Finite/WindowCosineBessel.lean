import Mathlib
import Cvs.Finite.ModePairingTable
import Cvs.Finite.WindowedModeSumDomain
import Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition

/-!
# The cosine coefficients, and Bessel's identity on the window

    ∫₀ᴸ (g − Sₛ)² = ∫₀ᴸ g² − (L/2)·∑_{n∈s} wₙ aₙ²,   wₙ = 2 for n = 0 and 1 otherwise

with `aₙ` the cosine coefficients, so the partial sums are the orthogonal projections.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Filter

namespace Cvs.Finite.WindowCosineBessel

variable {L : ℝ}

/-- The cosine coefficients of a window function. -/
def coef (L : ℝ) (g : ℝ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then (1 / L) * ∫ x in (0:ℝ)..L, g x
  else (2 / L) * ∫ x in (0:ℝ)..L, g x * Real.cos (2 * π * n / L * x)

/-- **The coefficient is the mode's overlap, with the constant mode weighted twice.** -/
theorem integral_mul_cos (hL : 0 < L) (g : ℝ → ℝ) (n : ℕ) :
    (∫ x in (0:ℝ)..L, g x * Real.cos (2 * π * n / L * x))
      = L / 2 * ((if n = 0 then 2 else 1) * coef L g n) := by
  rw [coef]
  by_cases hn : n = 0
  · subst hn
    rw [if_pos rfl, if_pos rfl]
    have hc : ∀ x : ℝ, g x * Real.cos (2 * π * (0:ℕ) / L * x) = g x := by
      intro x
      norm_num
    rw [intervalIntegral.integral_congr (fun x _ => hc x)]
    field_simp
  · rw [if_neg hn, if_neg hn]
    field_simp

/-- **Bessel's identity on the window.** -/
theorem integral_sub_modeSum_sq (hL : 0 < L) {g : ℝ → ℝ} (hgc : Continuous g)
    (s : Finset ℕ) :
    (∫ x in (0:ℝ)..L, (g x - Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L s (coef L g) x) ^ 2)
      = (∫ x in (0:ℝ)..L, g x ^ 2)
        - L / 2 * ∑ n ∈ s, (if n = 0 then 2 else 1) * coef L g n ^ 2 := by
  classical
  set a : ℕ → ℝ := coef L g with ha
  set S : ℝ → ℝ := Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L s a with hS
  have hSc : Continuous S := Cvs.Finite.WindowedModeSumDomain.continuous_modeSum L s a
  have hexp : ∀ x : ℝ, (g x - S x) ^ 2 = g x ^ 2 - 2 * (g x * S x) + S x ^ 2 := by
    intro x; ring
  have hi1 : IntervalIntegrable (fun x : ℝ => g x ^ 2) volume 0 L :=
    (hgc.pow 2).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun x : ℝ => 2 * (g x * S x)) volume 0 L :=
    ((continuous_const.mul (hgc.mul hSc))).intervalIntegrable _ _
  have hi3 : IntervalIntegrable (fun x : ℝ => S x ^ 2) volume 0 L :=
    ((hSc.pow 2)).intervalIntegrable _ _
  rw [intervalIntegral.integral_congr (fun x _ => hexp x),
    intervalIntegral.integral_add (hi1.sub hi2) hi3,
    intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul,
    Cvs.Finite.ModePairingTable.integral_modeSum_sq hL s a]
  -- the cross term
  have hcross : (∫ x in (0:ℝ)..L, g x * S x)
      = L / 2 * ∑ n ∈ s, (if n = 0 then 2 else 1) * a n ^ 2 := by
    have hpt : ∀ x : ℝ, g x * S x
        = ∑ n ∈ s, a n * (g x * Real.cos (2 * π * n / L * x)) := by
      intro x
      rw [hS]
      show g x * (∑ n ∈ s, a n * Real.cos (2 * π * n / L * x)) = _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    have hint : ∀ n : ℕ, IntervalIntegrable
        (fun x : ℝ => a n * (g x * Real.cos (2 * π * n / L * x))) volume 0 L := by
      intro n
      apply Continuous.intervalIntegrable
      fun_prop
    rw [intervalIntegral.integral_congr (fun x _ => hpt x),
      intervalIntegral.integral_finsetSum (fun n _ => hint n), Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [intervalIntegral.integral_const_mul, ha, integral_mul_cos hL g n, ← ha]
    ring
  rw [hcross]
  ring

/-- **Bessel's inequality on the window.** -/
theorem bessel (hL : 0 < L) {g : ℝ → ℝ} (hgc : Continuous g) (s : Finset ℕ) :
    L / 2 * ∑ n ∈ s, (if n = 0 then 2 else 1) * coef L g n ^ 2
      ≤ ∫ x in (0:ℝ)..L, g x ^ 2 := by
  have hnn : 0 ≤ ∫ x in (0:ℝ)..L, (g x - Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L s (coef L g) x) ^ 2 :=
    intervalIntegral.integral_nonneg hL.le (fun x _ => sq_nonneg _)
  rw [integral_sub_modeSum_sq hL hgc s] at hnn
  linarith

end Cvs.Finite.WindowCosineBessel
