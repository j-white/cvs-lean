import Mathlib
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.XiContourLimit
import Cvs.Zeta.XiVerticalFull

/-!
# The zero sum converges to the two vertical integrals

This closes the contour argument.
-/

open Complex

namespace Cvs.Zeta

private theorem norm_add_sub_le₃ (X Y Z : ℂ) : ‖X + Y - Z‖ ≤ ‖X‖ + ‖Y‖ + ‖Z‖ := by
  refine le_trans (norm_sub_le _ _) ?_
  gcongr
  exact norm_add_le _ _

/-- **The zero sum converges to the two vertical integrals.** -/
theorem zero_sum_tendsto_verticals {φ : ℂ → ℂ} {A : ℝ} (hA : 0 ≤ A)
    (hφd : Differentiable ℂ φ)
    (hφ : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → ‖φ z‖ ≤ A / (1 + |z.im|) ^ 3) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∃ (T' : ℝ) (S : Finset ℂ) (m : ℂ → ℕ),
        T ≤ T' ∧
        (∀ ρ ∈ S, riemannXi ρ = 0) ∧
        (∀ ρ ∈ S, -1 < ρ.re ∧ ρ.re < 2 ∧ -T' < ρ.im ∧ ρ.im < T') ∧
        (∀ u : ℂ, riemannXi u = 0 → |u.im| < T' → u ∈ S) ∧
        (∀ u : ℂ, (m u : ℤ) = MeromorphicOn.divisor riemannXi Set.univ u) ∧
        ‖2 * (Real.pi : ℂ) * I * ∑ ρ ∈ S, (m ρ : ℂ) * φ ρ
            - (I * (∫ y : ℝ, logDeriv riemannXi ((2 : ℂ) + y * I) * φ ((2 : ℂ) + y * I))
              - I * (∫ y : ℝ,
                  logDeriv riemannXi ((-1 : ℂ) + y * I) * φ ((-1 : ℂ) + y * I)))‖ < ε := by
  intro ε hε
  obtain ⟨C, hC0, hC⟩ := exists_contour_bound hA hφd hφ
  have hcont : Filter.Tendsto (fun T : ℝ => C * ((1 + Real.log T) ^ 2 / T ^ 3))
      Filter.atTop (nhds 0) := by
    simpa using tendsto_one_add_log_sq_div_cube.const_mul C
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp hcont (ε / 3) (by linarith)
  have hφ2 : ∀ y : ℝ, ‖φ ((2 : ℂ) + y * I)‖ ≤ A / (1 + |y|) ^ 3 := fun y => by
    have := hφ ((2 : ℂ) + y * I) (by norm_num) (by norm_num)
    simpa using this
  have hφm : ∀ y : ℝ, ‖φ ((-1 : ℂ) + y * I)‖ ≤ A / (1 + |y|) ^ 3 := fun y => by
    have := hφ ((-1 : ℂ) + y * I) (by norm_num) (by norm_num)
    simpa using this
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp (tendsto_vline_interval hA hφd.continuous hφ2)
    (ε / 3) (by linarith)
  obtain ⟨N₂, hN₂⟩ :=
    Metric.tendsto_atTop.mp (tendsto_vline_left_interval hA hφd.continuous hφm)
      (ε / 3) (by linarith)
  refine ⟨max 32 (max N₀ (max N₁ N₂)), fun T hT => ?_⟩
  have h32 : (32 : ℝ) ≤ T := le_trans (le_max_left _ _) hT
  have hTN₀ : N₀ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right 32 _)) hT
  have hTN₁ : N₁ ≤ T :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right 32 _)) hT
  have hTN₂ : N₂ ≤ T :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right 32 _)) hT
  obtain ⟨T', S, m, hT1, hT2, hS0, hSin, hScap, hSmult, hbd⟩ := hC T h32
  refine ⟨T', S, m, hT1, hS0, hSin, hScap, hSmult, ?_⟩
  -- the three errors
  have e0 : C * ((1 + Real.log T) ^ 2 / T ^ 3) < ε / 3 := by
    have := hN₀ T hTN₀
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at this
  have e1 : ‖(∫ y in (-T')..T', logDeriv riemannXi ((2 : ℂ) + y * I) * φ ((2 : ℂ) + y * I))
      - ∫ y : ℝ, logDeriv riemannXi ((2 : ℂ) + y * I) * φ ((2 : ℂ) + y * I)‖ < ε / 3 := by
    have := hN₁ T' (le_trans hTN₁ hT1)
    rwa [dist_eq_norm] at this
  have e2 : ‖(∫ y in (-T')..T', logDeriv riemannXi ((-1 : ℂ) + y * I) * φ ((-1 : ℂ) + y * I))
      - ∫ y : ℝ, logDeriv riemannXi ((-1 : ℂ) + y * I) * φ ((-1 : ℂ) + y * I)‖ < ε / 3 := by
    have := hN₂ T' (le_trans hTN₂ hT1)
    rwa [dist_eq_norm] at this
  -- assemble
  have hsplit : 2 * (Real.pi : ℂ) * I * ∑ ρ ∈ S, (m ρ : ℂ) * φ ρ
      - (I * (∫ y : ℝ, logDeriv riemannXi ((2 : ℂ) + y * I) * φ ((2 : ℂ) + y * I))
        - I * (∫ y : ℝ, logDeriv riemannXi ((-1 : ℂ) + y * I) * φ ((-1 : ℂ) + y * I)))
      = -(I * (∫ y in (-T')..T',
              logDeriv riemannXi ((2 : ℂ) + y * I) * φ ((2 : ℂ) + y * I))
            - I * (∫ y in (-T')..T',
              logDeriv riemannXi ((-1 : ℂ) + y * I) * φ ((-1 : ℂ) + y * I))
            - 2 * (Real.pi : ℂ) * I * ∑ ρ ∈ S, (m ρ : ℂ) * φ ρ)
        + I * ((∫ y in (-T')..T',
              logDeriv riemannXi ((2 : ℂ) + y * I) * φ ((2 : ℂ) + y * I))
            - ∫ y : ℝ, logDeriv riemannXi ((2 : ℂ) + y * I) * φ ((2 : ℂ) + y * I))
        - I * ((∫ y in (-T')..T',
              logDeriv riemannXi ((-1 : ℂ) + y * I) * φ ((-1 : ℂ) + y * I))
            - ∫ y : ℝ, logDeriv riemannXi ((-1 : ℂ) + y * I) * φ ((-1 : ℂ) + y * I)) := by
    ring
  rw [hsplit]
  refine lt_of_le_of_lt (norm_add_sub_le₃ _ _ _) ?_
  simp only [norm_neg, norm_mul, Complex.norm_I, one_mul]
  linarith [hbd]

end Cvs.Zeta
