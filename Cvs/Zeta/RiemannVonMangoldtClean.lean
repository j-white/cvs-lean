import Mathlib
import Cvs.Zeta.ArchimedeanChannelShift
import Cvs.Zeta.ArchimedeanLogBound
import Cvs.Zeta.ExplicitFormula.ArchimedeanChannelReal
import Cvs.Zeta.RiemannSiegelTheta
import Cvs.Zeta.RiemannVonMangoldtAssembled
import Cvs.Zeta.RiemannXi

/-!
# The corrections absorbed: Riemann–von Mangoldt in classical form
-/

noncomputable section

open Complex MeasureTheory Cvs.Zeta

namespace Cvs.ZeroCounting

/-- `Γ_ℝ'/Γ_ℝ` is real on the positive real axis. -/
theorem im_logDeriv_gammaR_real {x : ℝ} (hx : 0 < x) :
    (logDeriv Gammaℝ ((x : ℂ))).im = 0 := by
  have hre : (0 : ℝ) < ((x : ℂ)).re := by simpa using hx
  have h := Cvs.Zeta.ExplicitFormula.ArchimedeanChannelReal.logDeriv_gammaR_conj hre
  rw [Complex.conj_ofReal] at h
  have := congrArg Complex.im h
  simp only [Complex.conj_im] at this
  linarith

/-- `Γ_ℝ'/Γ_ℝ` is continuous on the real segment. -/
theorem continuous_logDeriv_gammaR_real :
    ContinuousOn (fun x : ℝ => logDeriv Gammaℝ ((x : ℂ))) (Set.uIcc (1/2 : ℝ) 2) := by
  intro x hx
  rw [Set.uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 2)] at hx
  refine ContinuousAt.continuousWithinAt ?_
  refine ContinuousAt.comp (f := fun t : ℝ => ((t : ℂ))) ?_ (by fun_prop)
  refine (Cvs.ZeroCounting.differentiableAt_logDeriv_gammaR ?_).continuousAt
  show (0 : ℝ) < ((x : ℂ)).re
  simp only [Complex.ofReal_re]
  linarith [hx.1]

/-- **The constant correction vanishes.** -/
theorem corr_zero : (∫ x in (1/2 : ℝ)..2, logDeriv Gammaℝ ((x : ℂ))).im = 0 := by
  have hcomm := ContinuousLinearMap.intervalIntegral_comp_comm Complex.imCLM
    (continuous_logDeriv_gammaR_real.intervalIntegrable (μ := volume))
  simp only [Complex.imCLM_apply] at hcomm
  rw [← hcomm]
  rw [intervalIntegral.integral_congr (g := fun _ : ℝ => (0:ℝ)) (fun x hx => ?_)]
  · simp
  · rw [Set.uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 2)] at hx
    exact im_logDeriv_gammaR_real (by linarith [hx.1])

/-- **Riemann–von Mangoldt, corrections absorbed.** -/
theorem exists_riemann_von_mangoldt_clean :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 20 ≤ T →
      ∃ (T' : ℝ) (S : Finset ℂ) (m : ℂ → ℕ),
        T ≤ T' ∧ T' ≤ T + 1 ∧
        (∀ u : ℂ, u ∈ S ↔ (riemannXi u = 0 ∧ |u.im| < T')) ∧
        (∀ u : ℂ, (m u : ℤ) = MeromorphicOn.divisor riemannXi Set.univ u) ∧
        |Real.pi * (∑ ρ ∈ S, (m ρ : ℝ)) - 2 * Cvs.ZeroCounting.theta T'
            - 2 * Real.arctan (T' / 2) - 2 * Real.arctan T'|
          ≤ C * (1 + Real.log (2 + T')) ^ 2 := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := Cvs.ZeroCounting.exists_riemann_von_mangoldt
  obtain ⟨C₂, hC₂0, hC₂⟩ := Cvs.ZeroCounting.exists_norm_logDeriv_gammaR_le
  refine ⟨C₁ + 3 * C₂, by linarith, fun T hT => ?_⟩
  obtain ⟨T', S, m, h1, h2, h3, h4, herr⟩ := hC₁ T hT
  refine ⟨T', S, m, h1, h2, h3, h4, ?_⟩
  have hT'20 : (20:ℝ) ≤ T' := by linarith
  -- the moving correction is `O(log T')`
  have hcorr : |(∫ x in (1/2 : ℝ)..2, logDeriv Gammaℝ ((x : ℂ) + (T' : ℂ) * I)).im|
      ≤ C₂ * (1 + Real.log (2 + T')) * (3/2) := by
    refine le_trans (Complex.abs_im_le_norm _) ?_
    have hb : ∀ x ∈ Set.uIoc (1/2 : ℝ) 2,
        ‖logDeriv Gammaℝ ((x : ℂ) + (T' : ℂ) * I)‖ ≤ C₂ * (1 + Real.log (2 + T')) := by
      intro x hx
      rw [Set.uIoc_of_le (by norm_num : (1/2 : ℝ) ≤ 2)] at hx
      have hb' := hC₂ ((x : ℂ) + (T' : ℂ) * I) (by simp; linarith [hx.1])
        (by simp; linarith [hx.2]) (by simp; rw [abs_of_nonneg (by linarith)]; linarith)
      simpa [abs_of_nonneg (by linarith : (0:ℝ) ≤ T')] using hb'
    calc ‖∫ x in (1/2 : ℝ)..2, logDeriv Gammaℝ ((x : ℂ) + (T' : ℂ) * I)‖
        ≤ (C₂ * (1 + Real.log (2 + T'))) * |(2:ℝ) - 1/2| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hb
      _ = C₂ * (1 + Real.log (2 + T')) * (3/2) := by norm_num
  rw [corr_zero] at herr
  -- monotonicity of the two log shapes
  have hL1 : (1:ℝ) ≤ 1 + Real.log (2 + T') := by
    have : (0:ℝ) ≤ Real.log (2 + T') := Real.log_nonneg (by linarith)
    linarith
  have hmono : (1 + Real.log |T|) ^ 2 ≤ (1 + Real.log (2 + T')) ^ 2 := by
    have hTabs : |T| = T := abs_of_nonneg (by linarith)
    have hlt : Real.log |T| ≤ Real.log (2 + T') := by
      rw [hTabs]; exact Real.log_le_log (by linarith) (by linarith)
    have h0 : (0:ℝ) ≤ Real.log |T| := by
      rw [hTabs]; exact Real.log_nonneg (by linarith)
    nlinarith [hlt, h0]
  have habs := abs_le.mp herr
  have hcabs := abs_le.mp hcorr
  have hA : C₁ * (1 + Real.log |T|) ^ 2 ≤ C₁ * (1 + Real.log (2 + T')) ^ 2 :=
    mul_le_mul_of_nonneg_left hmono hC₁0
  have hB : (1 + Real.log (2 + T')) ≤ (1 + Real.log (2 + T')) ^ 2 := by nlinarith [hL1]
  have hB2 : 3 * C₂ * (1 + Real.log (2 + T'))
      ≤ 3 * C₂ * (1 + Real.log (2 + T')) ^ 2 := by nlinarith [hB, hC₂0]
  rw [abs_le]
  constructor <;> nlinarith [habs.1, habs.2, hcabs.1, hcabs.2, hA, hB2]

end Cvs.ZeroCounting
