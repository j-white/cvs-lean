import Mathlib
import Cvs.Zeta.Digamma
import Cvs.Zeta.DigammaCriticalAsymptotic
import Cvs.Zeta.GaussKernel.ArchimedeanCutoffBound
import Cvs.Zeta.RiemannSiegelTheta
import Cvs.Zeta.ThetaDerivativeStationary

/-!
# `θ(T) = (T/2)·log(T/2πe) − T/2 + O(log T)`, unconditionally

`RVM.theta_asymptotic` integrates a carried digamma asymptotic into the classical main term
for `θ`; `RvMFull.hasym_holds` then discharges that hypothesis from `DigammaCriticalAsymptotic`, so the final
statement carries none.
-/

open Real intervalIntegral

namespace RVM

/-- The classical main term. -/
noncomputable def mainTerm (T : ℝ) : ℝ := (T / 2) * Real.log (T / (2 * π)) - T / 2

/-- `mainTerm` has derivative `½·log(u/2π)` for `u > 0`. -/
theorem hasDerivAt_mainTerm {u : ℝ} (hu : 0 < u) :
    HasDerivAt mainTerm (Real.log (u / (2 * π)) / 2) u := by
  have hπ : (0:ℝ) < 2 * π := by positivity
  have hu' : u ≠ 0 := ne_of_gt hu
  have hπ' : (2 * π : ℝ) ≠ 0 := ne_of_gt hπ
  have hlog : HasDerivAt (fun x : ℝ => Real.log (x / (2 * π))) (1 / u) u := by
    have h1 : HasDerivAt (fun x : ℝ => x / (2 * π)) (1 / (2 * π)) u := by
      exact (hasDerivAt_id' u).div_const (2 * π)
    have h2 := (Real.hasDerivAt_log (x := u / (2 * π)) (div_ne_zero hu' hπ')).comp u h1
    have heq : (u / (2 * π))⁻¹ * (1 / (2 * π)) = 1 / u := by
      rw [inv_div, div_mul_div_comm, mul_one, div_mul_cancel_right₀ hπ', one_div]
    rw [heq] at h2
    exact h2
  have hid : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) u := by
    exact (hasDerivAt_id' u).div_const 2
  have h : HasDerivAt mainTerm
      (1 / 2 * Real.log (u / (2 * π)) + u / 2 * (1 / u) - 1 / 2) u := (hid.mul hlog).sub hid
  have hval : 1 / 2 * Real.log (u / (2 * π)) + u / 2 * (1 / u) - 1 / 2
      = Real.log (u / (2 * π)) / 2 := by
    field_simp
    ring
  rwa [hval] at h

theorem continuousOn_logHalf {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (fun u : ℝ => Real.log (u / (2 * π)) / 2) (Set.uIcc a b) := by
  have hsub : Set.uIcc a b ⊆ {x : ℝ | x ≠ 0} := by
    rw [Set.uIcc_of_le hab]
    intro x hx
    exact ne_of_gt (lt_of_lt_of_le ha hx.1)
  apply ContinuousOn.div_const
  apply ContinuousOn.comp Real.continuousOn_log (by fun_prop)
  intro x hx
  have hπ : (0:ℝ) < 2 * π := by positivity
  have hx0 : x ≠ 0 := hsub hx
  simpa [div_ne_zero_iff, ne_of_gt hπ] using hx0

/-- FTC on `[a,b]` with `0 < a`: `mainTerm` is the exact antiderivative there. -/
theorem integral_logHalf {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ u in a..b, Real.log (u / (2 * π)) / 2 = mainTerm b - mainTerm a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact hasDerivAt_mainTerm (lt_of_lt_of_le ha hx.1)
  · exact (continuousOn_logHalf ha hab).intervalIntegrable

/-- The error integral is `O(log T)`. -/
theorem error_bound {C T : ℝ} (hC : 0 < C) (hT : 2 ≤ T)
    (h : ∀ u : ℝ, 2 ≤ u → |Cvs.Zeta.GaussKernel.ArchimedeanCutoffBound.archScore u - Real.log (u / (2 * π)) / 2| ≤ C / u) :
    |∫ u in (2:ℝ)..T, (Cvs.Zeta.GaussKernel.ArchimedeanCutoffBound.archScore u - Real.log (u / (2 * π)) / 2)|
      ≤ C * Real.log T := by
  have hbound : IntervalIntegrable (fun u : ℝ => C / u) MeasureTheory.volume 2 T := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro x hx
    rw [Set.uIcc_of_le hT] at hx
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) hx.1)
  have key := intervalIntegral.norm_integral_le_of_norm_le (a := (2:ℝ)) (b := T)
      (f := fun u : ℝ => Cvs.Zeta.GaussKernel.ArchimedeanCutoffBound.archScore u - Real.log (u / (2 * π)) / 2)
      (g := fun u : ℝ => C / u) hT
      (Filter.Eventually.of_forall (fun x hx => by
        simpa [Real.norm_eq_abs] using h x (le_of_lt hx.1))) hbound
  have hcalc : ∫ u in (2:ℝ)..T, C / u = C * (Real.log T - Real.log 2) := by
    simp_rw [div_eq_mul_inv]
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos (by norm_num)
      (lt_of_lt_of_le (by norm_num) hT)]
    rw [Real.log_div (by linarith) (by norm_num)]
  rw [Real.norm_eq_abs, hcalc] at key
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith [key, hC, hlog2]

theorem theta_asymptotic
    (hasym : ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 2 ≤ u →
      |Cvs.Zeta.GaussKernel.ArchimedeanCutoffBound.archScore u - Real.log (u / (2 * π)) / 2| ≤ C / u) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ T : ℝ, 2 ≤ T →
      |Cvs.ZeroCounting.theta T - ((T / 2) * Real.log (T / (2 * π)) - T / 2)|
        ≤ C' * (1 + Real.log T) := by
  obtain ⟨C, hC, h⟩ := hasym
  set K : ℝ := (∫ u in (0:ℝ)..(2:ℝ), Cvs.Zeta.GaussKernel.ArchimedeanCutoffBound.archScore u) - mainTerm 2 with hK
  refine ⟨|K| + C + 1, by positivity, ?_⟩
  intro T hT
  have hc : Continuous Cvs.Zeta.GaussKernel.ArchimedeanCutoffBound.archScore := Cvs.Zeta.ThetaDerivativeStationary.continuous_archScore
  -- split the integral
  have hsplit : Cvs.ZeroCounting.theta T
      = (∫ u in (0:ℝ)..(2:ℝ), Cvs.Zeta.GaussKernel.ArchimedeanCutoffBound.archScore u)
        + ∫ u in (2:ℝ)..T, Cvs.Zeta.GaussKernel.ArchimedeanCutoffBound.archScore u := by
    rw [Cvs.ZeroCounting.theta]
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable 0 2) (hc.intervalIntegrable 2 T)).symm
  have hdiff : ∫ u in (2:ℝ)..T, (Cvs.Zeta.GaussKernel.ArchimedeanCutoffBound.archScore u - Real.log (u / (2 * π)) / 2)
      = (∫ u in (2:ℝ)..T, Cvs.Zeta.GaussKernel.ArchimedeanCutoffBound.archScore u) - (mainTerm T - mainTerm 2) := by
    rw [intervalIntegral.integral_sub (hc.intervalIntegrable 2 T)
      ((continuousOn_logHalf (by norm_num) hT).intervalIntegrable),
      integral_logHalf (by norm_num) hT]
  have hrewrite : Cvs.ZeroCounting.theta T - mainTerm T
      = K + ∫ u in (2:ℝ)..T, (Cvs.Zeta.GaussKernel.ArchimedeanCutoffBound.archScore u - Real.log (u / (2 * π)) / 2) := by
    rw [hsplit, hdiff, hK]; ring
  have hbd := error_bound hC hT h
  have hlogT : (0:ℝ) ≤ Real.log T := Real.log_nonneg (by linarith)
  have : |Cvs.ZeroCounting.theta T - mainTerm T| ≤ |K| + C * Real.log T := by
    rw [hrewrite]
    exact (abs_add_le _ _).trans (by linarith)
  have hmain : ((T / 2) * Real.log (T / (2 * π)) - T / 2) = mainTerm T := rfl
  rw [hmain]
  nlinarith [this, hlogT, abs_nonneg K, hC]

end RVM

namespace RvMFull
open Real

/-- The two spellings of `¼ + iu/2` agree. -/
theorem arg_eq (u : ℝ) :
    ((1 / 4 : ℂ) + (u : ℂ) / 2 * Complex.I) = Cvs.Zeta.digammaArg u 0 := by
  simp only [Cvs.Zeta.digammaArg]
  push_cast
  ring

/-- `archScore u - ½log(u/2π) = ½(Re ψ(¼+iu/2) - log(u/2))`. -/
theorem archScore_sub {u : ℝ} (hu : 0 < u) :
    Cvs.Zeta.GaussKernel.ArchimedeanCutoffBound.archScore u - Real.log (u / (2 * π)) / 2
      = ((Complex.digamma (Cvs.Zeta.digammaArg u 0)).re - Real.log (u / 2)) / 2 := by
  have hlog : Real.log (u / (2 * π)) = Real.log (u / 2) - Real.log π := by
    rw [show u / (2 * π) = (u / 2) / π by ring,
      Real.log_div (by positivity) (ne_of_gt Real.pi_pos)]
  simp only [Cvs.Zeta.GaussKernel.ArchimedeanCutoffBound.archScore, arg_eq, hlog]
  ring

/-- The hypothesis `RVM.theta_asymptotic` carries, discharged. -/
theorem hasym_holds :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 2 ≤ u →
      |Cvs.Zeta.GaussKernel.ArchimedeanCutoffBound.archScore u - Real.log (u / (2 * π)) / 2| ≤ C / u := by
  refine ⟨57, by norm_num, fun u hu => ?_⟩
  have hu0 : (0 : ℝ) < u := by linarith
  have h := DigammaAsym.abs_re_digamma_sub_log_le u hu
  have hpos : (0 : ℝ) < 57 / u := by positivity
  rw [archScore_sub hu0, abs_div]
  have h2 : |(2 : ℝ)| = 2 := by norm_num
  rw [h2]
  linarith

/-- **`θ(T) = (T/2)·log(T/2πe) + O(log T)`, unconditionally.** -/
theorem theta_asymptotic_unconditional :
    ∃ C' : ℝ, 0 < C' ∧ ∀ T : ℝ, 2 ≤ T →
      |Cvs.ZeroCounting.theta T - ((T / 2) * Real.log (T / (2 * π)) - T / 2)|
        ≤ C' * (1 + Real.log T) :=
  RVM.theta_asymptotic hasym_holds

end RvMFull
