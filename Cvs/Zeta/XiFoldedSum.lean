import Mathlib
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.XiVertical
import Cvs.Zeta.XiZeroSumLimit

/-!
# Folding the two verticals into one

`φ(1 − s) = φ(s)` is the standard symmetry hypothesis on a Guinand–Weil test function.
-/

open Complex MeasureTheory

namespace Cvs.Zeta

/-- **Under the functional-equation symmetry of the test function, the left vertical is minus the
right.** `φ(1 − s) = φ(s)` is the standard hypothesis on a Guinand–Weil test function. -/
theorem integral_vline_left_eq_neg {φ : ℂ → ℂ} (hsym : ∀ s : ℂ, φ (1 - s) = φ s) :
    (∫ y : ℝ, logDeriv riemannXi ((-1 : ℂ) + y * I) * φ ((-1 : ℂ) + y * I))
      = - ∫ y : ℝ, logDeriv riemannXi ((2 : ℂ) + y * I) * φ ((2 : ℂ) + y * I) := by
  set g : ℝ → ℂ :=
    fun t => logDeriv riemannXi ((2 : ℂ) + t * I) * φ ((2 : ℂ) + t * I) with hg
  have hpt : ∀ y : ℝ,
      logDeriv riemannXi ((-1 : ℂ) + y * I) * φ ((-1 : ℂ) + y * I) = -(g (-y)) := by
    intro y
    have hc : ((-1 : ℂ) + (y : ℂ) * I) = 1 - ((2 : ℂ) + ((-y : ℝ) : ℂ) * I) := by
      push_cast; ring
    rw [hg]
    simp only
    rw [hc, logDeriv_riemannXi_one_sub, hsym]
    ring
  have hrefl : (∫ y : ℝ, g (-y)) = ∫ y : ℝ, g y :=
    (MeasureTheory.Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
      (MeasurableEquiv.neg ℝ).measurableEmbedding g
  calc (∫ y : ℝ, logDeriv riemannXi ((-1 : ℂ) + y * I) * φ ((-1 : ℂ) + y * I))
      = ∫ y : ℝ, -(g (-y)) := by simp_rw [hpt]
    _ = - ∫ y : ℝ, g (-y) := integral_neg _
    _ = - ∫ y : ℝ, g y := by rw [hrefl]

/-- **The folded zero sum.** With `φ` symmetric under `s ↦ 1 − s`, the two verticals collapse and
the contour identity becomes ‖ π·Σ_ρ m_ρ φ(ρ) − ∫_ℝ ξ'/ξ(2+iy)·φ(2+iy) dy ‖ < ε. -/
theorem zero_sum_tendsto_vline {φ : ℂ → ℂ} {A : ℝ} (hA : 0 ≤ A)
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
            - ∫ y : ℝ, logDeriv riemannXi ((2 : ℂ) + y * I) * φ ((2 : ℂ) + y * I)‖ < ε := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := zero_sum_tendsto_verticals hA hφd hφ ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  obtain ⟨T', S, m, h1, h2, hin, h3, hmu, h4⟩ := hT₀ T hT
  refine ⟨T', S, m, h1, h2, hin, h3, hmu, ?_⟩
  rw [integral_vline_left_eq_neg hsym] at h4
  have hkey : 2 * (Real.pi : ℂ) * I * ∑ ρ ∈ S, (m ρ : ℂ) * φ ρ
      - (I * (∫ y : ℝ, logDeriv riemannXi ((2 : ℂ) + y * I) * φ ((2 : ℂ) + y * I))
        - I * -(∫ y : ℝ, logDeriv riemannXi ((2 : ℂ) + y * I) * φ ((2 : ℂ) + y * I)))
      = (2 * I) * ((Real.pi : ℂ) * ∑ ρ ∈ S, (m ρ : ℂ) * φ ρ
        - ∫ y : ℝ, logDeriv riemannXi ((2 : ℂ) + y * I) * φ ((2 : ℂ) + y * I)) := by
    ring
  rw [hkey, norm_mul] at h4
  simp only [norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one] at h4
  linarith [norm_nonneg ((Real.pi : ℂ) * ∑ ρ ∈ S, (m ρ : ℂ) * φ ρ
    - ∫ y : ℝ, logDeriv riemannXi ((2 : ℂ) + y * I) * φ ((2 : ℂ) + y * I))]

end Cvs.Zeta
