import Mathlib
import Cvs.Zeta.GuinandWeilForm
import Cvs.Zeta.RiemannXi

/-!
# The prime side in Fourier shape

`Cvs.Zeta.GuinandWeilForm` states the prime side as `Σ_n Λ(n)·∫_ℝ n^{−s}·φ`.
-/

open Complex MeasureTheory ArithmeticFunction

namespace Cvs.Zeta

/-- The Fourier transform of the test function along the line `Re s = 2`. -/
noncomputable def fourierVline (φ : ℂ → ℂ) (t : ℝ) : ℂ :=
  ∫ y : ℝ, Complex.exp (-((y : ℂ) * (t : ℂ)) * I) * φ ((2 : ℂ) + y * I)

/-- `n^{−(2+iy)} = n^{−2}·e^{−iy log n}` — the Dirichlet kernel splits into a modulus and a
character. -/
theorem cpow_neg_vline {n : ℕ} (hn : n ≠ 0) (y : ℝ) :
    ((n : ℂ) ^ (-((2 : ℂ) + y * I)))
      = ((n : ℂ) ^ (-2 : ℂ))
        * Complex.exp (-((y : ℂ) * ((Real.log n : ℝ) : ℂ)) * I) := by
  have hn0 : ((n : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hsplit : -((2 : ℂ) + (y : ℂ) * I) = (-2 : ℂ) + (-((y : ℂ) * I)) := by ring
  rw [hsplit, Complex.cpow_add _ _ hn0]
  congr 1
  rw [Complex.cpow_def_of_ne_zero hn0]
  congr 1
  have hlog : Complex.log ((n : ℂ)) = ((Real.log n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hnpos.le]
  rw [hlog]
  ring

theorem integral_cpow_vline (φ : ℂ → ℂ) {n : ℕ} (hn : n ≠ 0) :
    (∫ y : ℝ, ((n : ℂ) ^ (-((2 : ℂ) + y * I))) * φ ((2 : ℂ) + y * I))
      = ((n : ℂ) ^ (-2 : ℂ)) * fourierVline φ (Real.log n) := by
  rw [fourierVline, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [cpow_neg_vline hn y]
  ring

/-- **The prime side as a Fourier sum.**  This is the shape the classical Guinand–Weil
statement is written in: each prime power contributes `Λ(n)·n^{−2}` times the transform of
the test function evaluated at `log n`. -/
theorem prime_side_fourier (φ : ℂ → ℂ) :
    (∑' n : ℕ, (Λ n : ℂ) * ∫ y : ℝ, ((n : ℂ) ^ (-((2 : ℂ) + y * I))) * φ ((2 : ℂ) + y * I))
      = ∑' n : ℕ, (Λ n : ℂ) * ((n : ℂ) ^ (-2 : ℂ)) * fourierVline φ (Real.log n) := by
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [integral_cpow_vline φ hn, mul_assoc]

/-- **The explicit formula with the prime side in Fourier shape.** ‖ π·Σ_ρ m_ρ φ(ρ) − [ ∫_ℝ φ/s +
∫_ℝ φ/(s−1) + ∫_ℝ (Γ_ℝ)'/Γ_ℝ·φ − Σ_n Λ(n)·n^{−2}·φ̂(log n) ] ‖ < ε with `φ̂` the transform
along the line. -/
theorem guinand_weil_fourier {φ : ℂ → ℂ} {A : ℝ} (hA : 0 ≤ A)
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
              - ∑' n : ℕ, (Λ n : ℂ) * ((n : ℂ) ^ (-2 : ℂ))
                  * fourierVline φ (Real.log n))‖
          < ε := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := guinand_weil_form hA hφd hφ hsym ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  obtain ⟨T', S, m, h1, h2, hin, h3, hmu, h4⟩ := hT₀ T hT
  exact ⟨T', S, m, h1, h2, hin, h3, hmu, by rwa [← prime_side_fourier]⟩

end Cvs.Zeta
