import Mathlib
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.XiFoldedSum
import Cvs.Zeta.XiPrimeSide
import Cvs.Zeta.XiSplitFull

/-!
# An explicit formula of Guinand–Weil type

Zeros on the left; poles, archimedean factor and primes on the right:
-/

open Complex MeasureTheory ArithmeticFunction

namespace Cvs.Zeta

theorem integrable_phi_vline_full {φ : ℂ → ℂ} {A : ℝ} (hA : 0 ≤ A) (hφc : Continuous φ)
    (hφ : ∀ y : ℝ, ‖φ ((2 : ℂ) + y * I)‖ ≤ A / (1 + |y|) ^ 3) :
    Integrable fun y : ℝ => φ ((2 : ℂ) + y * I) := by
  have := integrable_vline_of_bounded (f := fun _ : ℂ => (1 : ℂ)) (C := 1) hA (by norm_num)
    continuous_const (fun _ => by simp) hφc hφ
  simpa using this

/-- **The explicit formula, in Guinand–Weil's shape.** -/
theorem guinand_weil_form {φ : ℂ → ℂ} {A : ℝ} (hA : 0 ≤ A)
    (hφd : Differentiable ℂ φ) (hφ : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → ‖φ z‖ ≤ A / (1 + |z.im|) ^ 3)
    (hsym : ∀ s : ℂ, φ (1 - s) = φ s) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∃ (T' : ℝ) (S : Finset ℂ) (m : ℂ → ℕ),
        T ≤ T' ∧
        (∀ ρ ∈ S, riemannXi ρ = 0) ∧
        (∀ ρ ∈ S, -1 < ρ.re ∧ ρ.re < 2 ∧ -T' < ρ.im ∧ ρ.im < T') ∧
        (∀ u : ℂ, riemannXi u = 0 → |u.im| < T' → u ∈ S) ∧
        (∀ u : ℂ, (m u : ℤ) = MeromorphicOn.divisor riemannXi Set.univ u) ∧
        ‖(Real.pi : ℂ) * ∑ ρ ∈ S, (m ρ : ℂ) * φ ρ
            - ((∫ y : ℝ, 1 / ((2 : ℂ) + y * I) * φ ((2 : ℂ) + y * I))
              + (∫ y : ℝ, 1 / (((2 : ℂ) + y * I) - 1) * φ ((2 : ℂ) + y * I))
              + (∫ y : ℝ, logDeriv Gammaℝ ((2 : ℂ) + y * I) * φ ((2 : ℂ) + y * I))
              - ∑' n : ℕ, (Λ n : ℂ)
                  * ∫ y : ℝ, ((n : ℂ) ^ (-((2 : ℂ) + y * I))) * φ ((2 : ℂ) + y * I))‖
          < ε := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := zero_sum_tendsto_vline hA hφd hφ hsym ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  obtain ⟨T', S, m, h1, h2, hin, h3, hmu, h4⟩ := hT₀ T hT
  refine ⟨T', S, m, h1, h2, hin, h3, hmu, ?_⟩
  have hφ2 : ∀ y : ℝ, ‖φ ((2 : ℂ) + y * I)‖ ≤ A / (1 + |y|) ^ 3 := fun y => by
    have := hφ ((2 : ℂ) + y * I) (by norm_num) (by norm_num)
    simpa using this
  have hprime := integral_logDeriv_riemannZeta_vline_prime (φ := φ)
    (integrable_phi_vline_full hA hφd.continuous hφ2)
  simp only [vline] at hprime
  rw [integral_vline_split_full hA hφd.continuous hφ2, hprime] at h4
  convert h4 using 3

end Cvs.Zeta
