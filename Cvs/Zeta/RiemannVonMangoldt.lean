import Mathlib
import Cvs.Zeta.RiemannSiegelTheta
import Cvs.Zeta.RiemannVonMangoldtClean
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.ThetaAsymptotic

/-!
# The classical Riemann–von Mangoldt formula

Substituting `ThetaAsymptotic`'s unconditional `θ` asymptotic into `RiemannVonMangoldtClean`'s identity.
-/

noncomputable section

open Complex MeasureTheory Cvs.Zeta

namespace Cvs.ZeroCounting

/-- **Riemann–von Mangoldt, classical form.** -/
theorem exists_zero_count_asymptotic :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 20 ≤ T →
      ∃ (T' : ℝ) (S : Finset ℂ) (m : ℂ → ℕ),
        T ≤ T' ∧ T' ≤ T + 1 ∧
        (∀ u : ℂ, u ∈ S ↔ (riemannXi u = 0 ∧ |u.im| < T')) ∧
        (∀ u : ℂ, (m u : ℤ) = MeromorphicOn.divisor riemannXi Set.univ u) ∧
        |Real.pi * (∑ ρ ∈ S, (m ρ : ℝ))
            - (T' * Real.log (T' / (2 * Real.pi)) - T' + 2 * Real.pi)|
          ≤ C * (1 + Real.log (2 + T')) ^ 2 := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := Cvs.ZeroCounting.exists_riemann_von_mangoldt_clean
  obtain ⟨C₂, hC₂0, hC₂⟩ := RvMFull.theta_asymptotic_unconditional
  refine ⟨C₁ + 2 * C₂ + 2 * Real.pi, by positivity, fun T hT => ?_⟩
  obtain ⟨T', S, m, h1, h2, h3, h4, herr⟩ := hC₁ T hT
  refine ⟨T', S, m, h1, h2, h3, h4, ?_⟩
  have hT'20 : (20:ℝ) ≤ T' := by linarith
  set L : ℝ := 1 + Real.log (2 + T') with hL
  have hL1 : (1:ℝ) ≤ L := by
    have : (0:ℝ) ≤ Real.log (2 + T') := Real.log_nonneg (by linarith)
    rw [hL]; linarith
  have hL2 : L ≤ L ^ 2 := by nlinarith [hL1]
  -- the θ asymptotic at this height
  have hth := hC₂ T' (by linarith)
  have hthL : (1 + Real.log T') ≤ L := by
    rw [hL]
    have : Real.log T' ≤ Real.log (2 + T') := Real.log_le_log (by linarith) (by linarith)
    linarith
  -- the arctan pair lies in `[0, 2π]`
  have ha1 : 0 ≤ Real.arctan (T' / 2) := Real.arctan_nonneg.mpr (by linarith)
  have ha2 : 0 ≤ Real.arctan T' := Real.arctan_nonneg.mpr (by linarith)
  have hb1 : Real.arctan (T' / 2) ≤ Real.pi / 2 := (Real.arctan_lt_pi_div_two _).le
  have hb2 : Real.arctan T' ≤ Real.pi / 2 := (Real.arctan_lt_pi_div_two _).le
  have hpi0 : (0:ℝ) < Real.pi := Real.pi_pos
  -- combine
  have habs := abs_le.mp herr
  have hthabs := abs_le.mp hth
  have hCL : C₂ * (1 + Real.log T') ≤ C₂ * L ^ 2 := by
    have := mul_le_mul_of_nonneg_left (le_trans hthL hL2) hC₂0.le
    linarith
  have hpiL : 2 * Real.pi ≤ 2 * Real.pi * L ^ 2 := by nlinarith [hL1, hpi0]
  have hC1L : C₁ * L ^ 2 ≤ C₁ * L ^ 2 := le_refl _
  rw [abs_le]
  constructor <;> nlinarith [habs.1, habs.2, hthabs.1, hthabs.2, hCL, hpiL,
    ha1, ha2, hb1, hb2, hC₁0, hC₂0.le, hL1, hL2]

end Cvs.ZeroCounting
