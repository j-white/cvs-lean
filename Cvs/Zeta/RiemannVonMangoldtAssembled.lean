import Mathlib
import Cvs.Zeta.ArchimedeanChannelIsTheta
import Cvs.Zeta.ExplicitFormula.ArchimedeanChannelReal
import Cvs.Zeta.FoldedZeroCount
import Cvs.Zeta.PrimeChannelBounded
import Cvs.Zeta.RiemannSiegelTheta
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.VerticalFourChannels

/-!
# Riemann–von Mangoldt, assembled

Every channel is in place.
-/

noncomputable section

open Complex MeasureTheory Cvs.Zeta

namespace Cvs.ZeroCounting

/-- **The archimedean channel is even.** -/
theorem re_integral_gammaR_symm {T : ℝ} (hT : 0 ≤ T) :
    (∫ y in (-T)..T, logDeriv Gammaℝ ((2 : ℂ) + (y : ℂ) * I)).re
      = 2 * (∫ y in (0 : ℝ)..T, logDeriv Gammaℝ ((2 : ℂ) + (y : ℂ) * I)).re := by
  set g : ℝ → ℂ := fun t => logDeriv Gammaℝ ((2 : ℂ) + (t : ℂ) * I) with hg
  have hcont : Continuous g := Cvs.ZeroCounting.continuous_logDeriv_gammaR_line
  have hsplit : (∫ y in (-T)..T, g y) = (∫ y in (-T)..(0:ℝ), g y) + ∫ y in (0:ℝ)..T, g y :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)).symm
  have hpt : ∀ y : ℝ, g (-y) = (starRingEnd ℂ) (g y) := by
    intro y
    have hre : (0 : ℝ) < ((2 : ℂ) + (y : ℂ) * I).re := by simp
    have hc : ((2 : ℂ) + ((-y : ℝ) : ℂ) * I)
        = (starRingEnd ℂ) ((2 : ℂ) + (y : ℂ) * I) := by
      apply Complex.ext <;> simp
    rw [hg]
    simp only
    rw [hc, Cvs.Zeta.ExplicitFormula.ArchimedeanChannelReal.logDeriv_gammaR_conj hre]
  have hleft : (∫ y in (-T)..(0:ℝ), g y) = (starRingEnd ℂ) (∫ y in (0:ℝ)..T, g y) := by
    rw [← intervalIntegral.intervalIntegral_conj]
    calc (∫ y in (-T)..(0:ℝ), g y)
        = ∫ y in (0:ℝ)..T, g (-y) := by
          rw [intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := T) g]
          norm_num
      _ = ∫ y in (0:ℝ)..T, (starRingEnd ℂ) (g y) := by simp_rw [hpt]
  rw [hsplit, hleft]
  simp [Complex.add_re, Complex.conj_re]
  ring

/-- **Riemann–von Mangoldt, in one statement.** -/
theorem exists_riemann_von_mangoldt :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 20 ≤ T →
      ∃ (T' : ℝ) (S : Finset ℂ) (m : ℂ → ℕ),
        T ≤ T' ∧ T' ≤ T + 1 ∧
        (∀ u : ℂ, u ∈ S ↔ (riemannXi u = 0 ∧ |u.im| < T')) ∧
        (∀ u : ℂ, (m u : ℤ) = MeromorphicOn.divisor riemannXi Set.univ u) ∧
        |Real.pi * (∑ ρ ∈ S, (m ρ : ℝ))
            - 2 * Cvs.ZeroCounting.theta T'
            - 2 * Real.arctan (T' / 2) - 2 * Real.arctan T'
            - 2 * ((∫ x in (1/2 : ℝ)..2, logDeriv Gammaℝ ((x : ℂ) + (T' : ℂ) * I)).im
                    - (∫ x in (1/2 : ℝ)..2, logDeriv Gammaℝ ((x : ℂ))).im)|
          ≤ C * (1 + Real.log |T|) ^ 2 := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := Cvs.Zeta.FoldedZeroCount.exists_zero_count_main_term
  obtain ⟨C₂, hC₂0, hC₂⟩ := Cvs.ZeroCounting.exists_bound_prime_channel
  refine ⟨C₁ + C₂, by linarith, fun T hT => ?_⟩
  obtain ⟨T', S, m, h1, h2, h3, h4, herr⟩ := hC₁ T hT
  refine ⟨T', S, m, h1, h2, h3, h4, ?_⟩
  have hT'0 : (0:ℝ) ≤ T' := by linarith
  -- the split, the halving, and the identification
  have hsplit := Cvs.ZeroCounting.re_vertical_split T'
  have hhalf := re_integral_gammaR_symm hT'0
  have hth := Cvs.ZeroCounting.re_integral_two_eq_theta_add hT'0
  -- the prime channel
  have hZ : |(∫ y in (-T')..T', logDeriv riemannZeta ((2 : ℂ) + (y : ℂ) * I)).re| ≤ C₂ :=
    le_trans (Complex.abs_re_le_norm _) (hC₂ T' hT'0)
  -- `(1 + log T)² ≥ 1`, so the constant channel is absorbed
  have hlog : (1:ℝ) ≤ (1 + Real.log |T|) ^ 2 := by
    have : (0:ℝ) ≤ Real.log |T| := Real.log_nonneg (by rw [abs_of_nonneg (by linarith)]; linarith)
    nlinarith
  rw [hhalf, hth] at hsplit
  have habs := abs_le.mp herr
  have hZ' := abs_le.mp hZ
  rw [abs_le]
  constructor <;> nlinarith [habs.1, habs.2, hZ'.1, hZ'.2, hlog, hC₁0, hC₂0]

end Cvs.ZeroCounting
