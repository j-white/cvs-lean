import Mathlib
import Cvs.Zeta.XiPrimeSide
import Cvs.Zeta.XiVertical

/-!
# The prime channel, expanded on a finite interval
-/

noncomputable section

open Complex MeasureTheory Cvs.Zeta ArithmeticFunction LSeries
open scoped ArithmeticFunction

namespace Cvs.ZeroCounting

/-- Each Dirichlet term is integrable on a bounded interval — it is continuous. -/
theorem integrableOn_term (n : ℕ) (T : ℝ) :
    IntegrableOn (fun y : ℝ => term (fun k => (Λ k : ℂ)) (vline y) n) (Set.Ioc (-T) T) :=
  (continuous_term_vline n).integrableOn_Ioc

/-- The norm is constant along the line, so its integral over `[-T,T]` is `2T·Λ(n)/n²`. -/
theorem integral_norm_term_Ioc (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ y in Set.Ioc (-T) T, ‖term (fun k => (Λ k : ℂ)) (vline y) n‖)
      = (2 * T) * ‖term (fun k => (Λ k : ℂ)) (2 : ℂ) n‖ := by
  simp_rw [norm_term_vline]
  rw [setIntegral_const, measureReal_def, Real.volume_Ioc,
    ENNReal.toReal_ofReal (by linarith)]
  rw [show T - -T = 2 * T by ring]
  simp

/-- Summability of the dominating series. -/
theorem summable_integral_norm_term {T : ℝ} (hT : 0 ≤ T) :
    Summable fun n : ℕ =>
      ∫ y in Set.Ioc (-T) T, ‖term (fun k => (Λ k : ℂ)) (vline y) n‖ := by
  simp_rw [integral_norm_term_Ioc _ hT]
  exact (summable_norm_term_vonMangoldt (by simp)).mul_left _

/-- **The prime channel, expanded.**  The Dirichlet sum and the interval integral commute. -/
theorem integral_logDeriv_zeta_interval {T : ℝ} (hT : 0 ≤ T) :
    (∫ y in (-T)..T, logDeriv riemannZeta ((2 : ℂ) + (y : ℂ) * I))
      = - ∑' n : ℕ, ∫ y in Set.Ioc (-T) T, term (fun k => (Λ k : ℂ)) (vline y) n := by
  have hle : (-T : ℝ) ≤ T := by linarith
  rw [intervalIntegral.integral_of_le hle]
  have hsum := integral_tsum_of_summable_integral_norm
    (μ := volume.restrict (Set.Ioc (-T) T))
    (F := fun (n : ℕ) (y : ℝ) => term (fun k => (Λ k : ℂ)) (vline y) n)
    (fun n => integrableOn_term n T) (summable_integral_norm_term hT)
  calc (∫ y in Set.Ioc (-T) T, logDeriv riemannZeta ((2 : ℂ) + (y : ℂ) * I))
      = ∫ y in Set.Ioc (-T) T, -(∑' n : ℕ, term (fun k => (Λ k : ℂ)) (vline y) n) := by
        refine setIntegral_congr_fun measurableSet_Ioc (fun y _ => ?_)
        rw [tsum_term_vline]
        simp only [vline]
        ring
    _ = - ∫ y in Set.Ioc (-T) T, ∑' n : ℕ, term (fun k => (Λ k : ℂ)) (vline y) n :=
        integral_neg _
    _ = - ∑' n : ℕ, ∫ y in Set.Ioc (-T) T, term (fun k => (Λ k : ℂ)) (vline y) n := by
        rw [← hsum]

end Cvs.ZeroCounting
