import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Cvs.Zeta.Hadamard
import Cvs.Zeta.HadamardProduct.GenusOneFactorLogDeriv
import Cvs.Zeta.Weierstrass

/-!
# The logarithmic derivative of the canonical product

(log ∏ₙ E₁(z/aₙ))' = ∑ₙ [ 1/(z-aₙ) + 1/aₙ ] (as a `HasSum`)
-/

open Complex Filter Topology

namespace Cvs.ZeroFree

variable {ι : Type*} {a : ι → ℂ}

theorem factor_ne_zero (h0 : ∀ n, a n ≠ 0) {z : ℂ} (hz : ∀ n, z ≠ a n) (n : ι) :
    Cvs.Zeta.weierstrassE1 (z / a n) ≠ 0 := by
  rw [Ne, Cvs.Zeta.weierstrassE1_eq_zero_iff]
  intro hc
  exact hz n ((div_eq_one_iff_eq (h0 n)).mp hc)

/-- **The logarithmic derivative of the canonical product is the sum over its zeros.** (log Π
E₁(z/aₙ))' = Σₙ [ 1/(z-aₙ) + 1/aₙ ] . -/
theorem hasSum_logDeriv_tprod (ha : Summable fun n => ‖a n‖⁻¹ ^ 2)
    (h0 : ∀ n, a n ≠ 0) {z : ℂ} (hz : ∀ n, z ≠ a n) :
    HasSum (fun n => 1 / (z - a n) + 1 / a n)
      (logDeriv (fun w : ℂ => ∏' n, Cvs.Zeta.weierstrassE1 (w / a n)) z) := by
  set R : ℝ := ‖z‖ + 1 with hR
  have hzs : z ∈ Metric.ball (0 : ℂ) R := by
    simp only [Metric.mem_ball, dist_zero_right, hR]
    linarith
  have hlu : TendstoLocallyUniformlyOn
      (fun (F : Finset ι) (w : ℂ) => ∏ n ∈ F, Cvs.Zeta.weierstrassE1 (w / a n))
      (fun w => ∏' n, Cvs.Zeta.weierstrassE1 (w / a n)) atTop (Metric.ball (0 : ℂ) R) :=
    Cvs.Zeta.hasProdLocallyUniformlyOn_weierstrassE1_div ha R
  have hdiff : ∀ᶠ (F : Finset ι) in atTop,
      DifferentiableOn ℂ (fun w : ℂ => ∏ n ∈ F, Cvs.Zeta.weierstrassE1 (w / a n))
        (Metric.ball (0 : ℂ) R) := by
    refine Eventually.of_forall (fun F w _ => ?_)
    exact (DifferentiableAt.fun_finsetProd fun i _ =>
      (Cvs.Zeta.differentiable_weierstrassE1_div i) w).differentiableWithinAt
  have hgz : (fun w : ℂ => ∏' n, Cvs.Zeta.weierstrassE1 (w / a n)) z ≠ 0 :=
    Cvs.Zeta.tprod_weierstrassE1_div_ne_zero ha hz
  have htend := Complex.logDeriv_tendsto Metric.isOpen_ball hzs hlu hdiff hgz
  have hfin : ∀ F : Finset ι,
      logDeriv (fun w : ℂ => ∏ n ∈ F, Cvs.Zeta.weierstrassE1 (w / a n)) z
        = ∑ n ∈ F, (1 / (z - a n) + 1 / a n) := by
    intro F
    have hfun : (fun w : ℂ => ∏ n ∈ F, Cvs.Zeta.weierstrassE1 (w / a n))
        = ∏ n ∈ F, (fun w : ℂ => Cvs.Zeta.weierstrassE1 (w / a n)) := by
      funext w; simp [Finset.prod_apply]
    rw [hfun, logDeriv_prod (fun i _ => factor_ne_zero h0 hz i)
      (fun i _ => (Cvs.Zeta.differentiable_weierstrassE1_div i) z)]
    exact Finset.sum_congr rfl
      (fun n _ => Cvs.ZeroFree.logDeriv_weierstrassE1_div (h0 n) (hz n))
  simp only [hfin] at htend
  exact htend

end Cvs.ZeroFree
