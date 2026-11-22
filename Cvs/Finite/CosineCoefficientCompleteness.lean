import Mathlib
import Cvs.Finite.WindowCosineBessel
import Cvs.Finite.WindowFourierHalfCosine
import Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition

/-!
# Completeness: the cosine coefficients carry all of the energy

    HasSum (n ↦ wₙ·aₙ²) ((2/L)·∫₀ᴸ g²),  hence  ∫₀ᴸ (g − S_N)² → 0

Mathlib's interval Parseval, folded from `ℤ` onto `ℕ` through `Cvs.Finite.WindowFourierHalfCosine`'s bridge.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Filter Complex

namespace Cvs.Finite.CosineCoefficientCompleteness

variable {L : ℝ}

/-- **Parseval, in the project's own cosine coefficients.** -/
theorem hasSum_coef_sq (hL : 0 < L) {g : ℝ → ℝ} (hgc : Continuous g)
    (hg : ∀ x : ℝ, g (L - x) = g x) :
    HasSum (fun n : ℕ => (if n = 0 then 2 else 1) * Cvs.Finite.WindowCosineBessel.coef L g n ^ 2)
      ((2 / L) * ∫ x in (0:ℝ)..L, g x ^ 2) := by
  classical
  set G : ℝ → ℂ := fun x => (g x : ℂ) with hG
  set a : ℕ → ℝ := Cvs.Finite.WindowCosineBessel.coef L g with ha
  set f : ℤ → ℝ := fun k => ‖fourierCoeffOn hL G k‖ ^ 2 with hf
  -- Mathlib's Parseval on the interval
  have hL2 : MemLp G 2 ((volume : Measure ℝ).restrict (Set.Ioc 0 L)) := by
    have hmeas : AEStronglyMeasurable G ((volume : Measure ℝ).restrict (Set.Ioc 0 L)) := by
      rw [hG]
      exact (Complex.continuous_ofReal.comp hgc).aestronglyMeasurable
    refine (memLp_two_iff_integrable_sq_norm hmeas).mpr ?_
    have hcont : Continuous (fun x : ℝ => ‖G x‖ ^ 2) := by
      rw [hG]; fun_prop
    exact hcont.integrableOn_Ioc
  have hpar := hasSum_sq_fourierCoeffOn hL hL2
  rw [← hf] at hpar
  -- the coefficient, in real terms
  have hval : ∀ k : ℤ, f k = ((1 / L) * ∫ x in (0:ℝ)..L,
      g x * Real.cos (2 * π * k / L * x)) ^ 2 := by
    intro k
    rw [hf]
    simp only
    rw [hG, Cvs.Finite.WindowFourierHalfCosine.fourierCoeffOn_eq hL hgc hg k, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  have hcosabs : ∀ k : ℤ, ∀ x : ℝ,
      Real.cos (2 * π * (k : ℝ) / L * x)
        = Real.cos (2 * π * ((k.natAbs : ℕ) : ℝ) / L * x) := by
    intro k x
    have habs : ((k.natAbs : ℕ) : ℝ) = |(k : ℝ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [habs]
    rcases abs_cases ((k : ℝ)) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, show 2 * π * -((k : ℝ)) / L * x = -(2 * π * (k : ℝ) / L * x) by ring,
        Real.cos_neg]
  have hfabs : ∀ k : ℤ, f k
      = ((if k.natAbs = 0 then 2 else 1) * a k.natAbs / 2) ^ 2 := by
    intro k
    rw [hval k, intervalIntegral.integral_congr (fun x _ => by rw [hcosabs k x]),
      ha, Cvs.Finite.WindowCosineBessel.integral_mul_cos hL g k.natAbs]
    field_simp
  have hfe : ∀ k : ℤ, f (-k) = f k := by
    intro k
    rw [hfabs, hfabs, Int.natAbs_neg]
  -- fold the sum onto the naturals
  have hfold := hpar.nat_add_neg
  have hstep : ∀ n : ℕ, f n + f (-(n : ℤ)) = 2 * f n := fun n => by rw [hfe]; ring
  simp only [hstep] at hfold
  have hquad := hfold.mul_left 2
  have hpt := hasSum_ite_eq (0 : ℕ) (2 * f 0)
  have heq : (fun n : ℕ => (if n = 0 then 2 else 1) * a n ^ 2)
      = fun n : ℕ => 2 * (2 * f n) - (if n = 0 then 2 * f 0 else 0) := by
    funext n
    by_cases hn : n = 0
    · subst hn
      simp only [Nat.cast_zero]
      rw [hfabs 0]
      norm_num
      ring
    · rw [if_neg hn, if_neg hn, hfabs (n : ℤ), Int.natAbs_natCast, if_neg hn]
      ring
  have hnormG : ∀ x : ℝ, ‖G x‖ ^ 2 = g x ^ 2 := by
    intro x
    rw [hG]
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hval2 : (2 / L) * (∫ x in (0:ℝ)..L, g x ^ 2)
      = 2 * (((L - 0)⁻¹ • ∫ x in (0:ℝ)..L, ‖G x‖ ^ 2) + f 0) - 2 * f 0 := by
    rw [intervalIntegral.integral_congr (fun x _ => hnormG x), smul_eq_mul, sub_zero]
    have hL0 : L ≠ 0 := hL.ne'
    field_simp
    ring
  rw [heq, hval2]
  exact hquad.sub hpt

/-- **The cosine partial sums converge in `L²` on the window.** -/
theorem tendsto_integral_sub_modeSum (hL : 0 < L) {g : ℝ → ℝ} (hgc : Continuous g)
    (hg : ∀ x : ℝ, g (L - x) = g x) :
    Filter.Tendsto (fun N : ℕ => ∫ x in (0:ℝ)..L,
        (g x - Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L (Finset.range N)
          (Cvs.Finite.WindowCosineBessel.coef L g) x) ^ 2)
      Filter.atTop (nhds 0) := by
  have hsum := (hasSum_coef_sq hL hgc hg).tendsto_sum_nat
  have hscale := hsum.const_mul (L / 2)
  have hlim : L / 2 * ((2 / L) * ∫ x in (0:ℝ)..L, g x ^ 2)
      = ∫ x in (0:ℝ)..L, g x ^ 2 := by
    have hL0 : L ≠ 0 := hL.ne'
    field_simp
  rw [hlim] at hscale
  have hdiff := (tendsto_const_nhds
    (x := ∫ x in (0:ℝ)..L, g x ^ 2) (f := Filter.atTop (α := ℕ))).sub hscale
  rw [sub_self] at hdiff
  refine hdiff.congr (fun N => ?_)
  rw [Cvs.Finite.WindowCosineBessel.integral_sub_modeSum_sq hL hgc (Finset.range N)]

end Cvs.Finite.CosineCoefficientCompleteness
