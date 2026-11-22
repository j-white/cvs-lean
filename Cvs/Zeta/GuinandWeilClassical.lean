import Mathlib
import Cvs.Zeta.ContourShift
import Cvs.Zeta.CriticalParam
import Cvs.Zeta.FourierShift
import Cvs.Zeta.GuinandWeilFourier
import Cvs.Zeta.RiemannXi

/-!
# Guinand–Weil in the classical variables

‖ π·Σ_ρ m_ρ·h(−i(ρ−½)) − [ ∫φ/s + ∫φ/(s−1) + ∫(Γ_ℝ)'/Γ_ℝ·φ − Σ_n Λ(n)·n^{−1/2}·ĥ(log n) ] ‖ <
ε
-/

open Complex ArithmeticFunction

namespace Cvs.Zeta

/-- `n^{−2}·e^{(3/2)·log n} = n^{−1/2}` for `n ≥ 1`. -/
theorem prime_coeff_eq {n : ℕ} (hn : n ≠ 0) :
    ((n : ℂ) ^ (-2 : ℂ)) * Complex.exp (((3 / 2 * Real.log n : ℝ) : ℂ))
      = (((n : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) := by
  have hpos : (0 : ℝ) < (n : ℝ) := by positivity
  have h1 : ((n : ℂ) ^ (-2 : ℂ)) = (((n : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hpos.le]
    norm_num
  have h2 : Complex.exp (((3 / 2 * Real.log n : ℝ) : ℂ))
      = (((n : ℝ) ^ (3 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp, Real.rpow_def_of_pos hpos]
    ring_nf
  rw [h1, h2, ← Complex.ofReal_mul]
  congr 1
  rw [← Real.rpow_add hpos]
  norm_num

/-- **Guinand–Weil in the classical variables.** ‖ π·Σ_ρ m_ρ·h(−i(ρ−½)) − [ ∫φ/s + ∫φ/(s−1) +
∫(Γ_ℝ)'/Γ_ℝ·φ − Σ_n Λ(n)·n^{−1/2}·ĥ(log n) ] ‖ < ε with `φ = ofCritical h`, the sum over all
zeros of `ξ` with `|Im ρ| < T'`. -/
theorem guinand_weil_classical {h : ℂ → ℂ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hhd : Differentiable ℂ h) (heven : ∀ w : ℂ, h (-w) = h w)
    (hdecay : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 →
      ‖ofCritical h z‖ ≤ A / (1 + |z.im|) ^ 3)
    (hstrip : StripDecayRe h B (3 / 2)) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∃ (T' : ℝ) (S : Finset ℂ) (m : ℂ → ℕ),
        T ≤ T' ∧
        (∀ ρ ∈ S, riemannXi ρ = 0) ∧
        (∀ ρ ∈ S, -1 < ρ.re ∧ ρ.re < 2 ∧ -T' < ρ.im ∧ ρ.im < T') ∧
        (∀ u : ℂ, riemannXi u = 0 → |u.im| < T' → u ∈ S) ∧
        (∀ u : ℂ, (m u : ℤ) = MeromorphicOn.divisor riemannXi Set.univ u) ∧
        ‖(Real.pi : ℂ) * ∑ ρ ∈ S, (m ρ : ℂ) * h (-I * (ρ - 1 / 2))
            - ((∫ y : ℝ, 1 / ((2 : ℂ) + y * I) * ofCritical h ((2 : ℂ) + y * I))
              + (∫ y : ℝ, 1 / (((2 : ℂ) + y * I) - 1) * ofCritical h ((2 : ℂ) + y * I))
              + (∫ y : ℝ, logDeriv Gammaℝ ((2 : ℂ) + y * I) * ofCritical h ((2 : ℂ) + y * I))
              - ∑' n : ℕ, (Λ n : ℂ) * (((n : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ)
                  * fourierReal h (Real.log n))‖
          < ε := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := guinand_weil_fourier (φ := ofCritical h) hA
    (differentiable_ofCritical hhd) hdecay ((ofCritical_symm_iff h).mpr heven) ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  obtain ⟨T', S, m, h1, h2, hin, h3, hmu, h4⟩ := hT₀ T hT
  refine ⟨T', S, m, h1, h2, hin, h3, hmu, ?_⟩
  have hprime : (∑' n : ℕ, (Λ n : ℂ) * ((n : ℂ) ^ (-2 : ℂ))
        * fourierVline (ofCritical h) (Real.log n))
      = ∑' n : ℕ, (Λ n : ℂ) * (((n : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ)
        * fourierReal h (Real.log n) := by
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [fourierVline_ofCritical hhd hB hstrip, ← mul_assoc, mul_assoc (Λ n : ℂ),
        prime_coeff_eq hn]
  rw [hprime] at h4
  exact h4

end Cvs.Zeta
