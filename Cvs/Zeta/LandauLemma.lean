import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Cvs.Zeta.ArgumentPrinciple
import Cvs.Zeta.Hadamard
import Cvs.Zeta.LandauCancel

/-!
# Landau's lemma

`Cvs.Zeta.LandauCancel` proves the analytic core: for `g` analytic, zero-free and bounded by
`M` on a disc, `‖g'/g‖` is `O(log M)` on a quarter of it.
-/

open Complex Set Metric Finset

namespace Cvs.Zeta

/-- The **normalised** product of linear factors, `∏ (1 - z/ρ)^{m ρ}`. -/
noncomputable def normProd (S : Finset ℂ) (m : ℂ → ℕ) (z : ℂ) : ℂ :=
  ∏ ρ ∈ S, (1 - z / ρ) ^ m ρ

theorem normProd_eq_const_mul_finiteFactor {S : Finset ℂ} {m : ℂ → ℕ}
    (hS : ∀ ρ ∈ S, ρ ≠ 0) (z : ℂ) :
    normProd S m z = (∏ ρ ∈ S, (-(ρ⁻¹)) ^ m ρ) * finiteFactor S m z := by
  rw [normProd, finiteFactor, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun ρ hρ => ?_
  have hρ0 : ρ ≠ 0 := hS ρ hρ
  rw [← mul_pow]
  congr 1
  field_simp
  ring

theorem const_ne_zero_of_forall_ne_zero {S : Finset ℂ} {m : ℂ → ℕ}
    (hS : ∀ ρ ∈ S, ρ ≠ 0) : (∏ ρ ∈ S, (-(ρ⁻¹)) ^ m ρ) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun ρ hρ => ?_
  exact pow_ne_zero _ (neg_ne_zero.mpr (inv_ne_zero (hS ρ hρ)))

theorem differentiable_normProd (S : Finset ℂ) (m : ℂ → ℕ) (hS : ∀ ρ ∈ S, ρ ≠ 0) :
    Differentiable ℂ (normProd S m) := by
  intro z
  rw [show normProd S m = fun w =>
      (∏ ρ ∈ S, (-(ρ⁻¹)) ^ m ρ) * finiteFactor S m w from
    funext (normProd_eq_const_mul_finiteFactor hS)]
  exact (differentiable_finiteFactor S m).const_mul _ z

theorem normProd_ne_zero_of_notMem {S : Finset ℂ} {m : ℂ → ℕ} {z : ℂ}
    (hS : ∀ ρ ∈ S, ρ ≠ 0) (hz : z ∉ S) : normProd S m z ≠ 0 := by
  rw [normProd_eq_const_mul_finiteFactor hS]
  exact mul_ne_zero (const_ne_zero_of_forall_ne_zero hS) (finiteFactor_ne_zero hz)

/-- The logarithmic derivative of the normalised product is the same partial fraction as
for the monic one — the constant between them drops out, which is the point of the bridge. -/
theorem logDeriv_normProd {S : Finset ℂ} {m : ℂ → ℕ} (hS : ∀ ρ ∈ S, ρ ≠ 0) {z : ℂ}
    (hz : z ∉ S) :
    logDeriv (normProd S m) z = ∑ ρ ∈ S, (m ρ : ℂ) / (z - ρ) := by
  have hfun : normProd S m
      = fun w => (∏ ρ ∈ S, (-(ρ⁻¹)) ^ m ρ) * finiteFactor S m w :=
    funext (normProd_eq_const_mul_finiteFactor hS)
  rw [hfun, logDeriv_const_mul _ _ (const_ne_zero_of_forall_ne_zero hS)]
  exact logDeriv_finiteFactor hz

/-- **Landau's lemma.** -/
theorem norm_logDeriv_sub_sum_le {f g : ℂ → ℂ} {S : Finset ℂ} {m : ℂ → ℕ} {r M : ℝ}
    (hr : 0 < r)
    (hfg : ∀ z, f z = g z * normProd S m z)
    (hS : ∀ ρ ∈ S, ρ ≠ 0)
    (hgd : DifferentiableOn ℂ g (ball 0 r))
    (hg0 : ∀ z ∈ ball 0 r, g z ≠ 0)
    (hMg : ∀ z ∈ ball 0 r, ‖g z‖ ≤ M)
    {z : ℂ} (hz : ‖z‖ ≤ r / 4) (hzS : z ∉ S) :
    ‖logDeriv f z - ∑ ρ ∈ S, (m ρ : ℂ) / (z - ρ)‖
      ≤ 8 * (Real.log M - Real.log ‖g 0‖ + 1) / r := by
  have hzball : z ∈ ball (0 : ℂ) r := by rw [mem_ball_zero_iff]; linarith
  have hgz : g z ≠ 0 := hg0 z hzball
  have hnz : normProd S m z ≠ 0 := normProd_ne_zero_of_notMem hS hzS
  have hgd' : DifferentiableAt ℂ g z := hgd.differentiableAt (isOpen_ball.mem_nhds hzball)
  have hnd : DifferentiableAt ℂ (normProd S m) z := differentiable_normProd S m hS z
  have hfun : f = g * normProd S m := funext hfg
  rw [hfun, logDeriv_mul z hgz hnz hgd' hnd, logDeriv_normProd hS hzS,
    add_sub_cancel_right, logDeriv_apply]
  exact norm_logDeriv_le_of_bounded hr hgd hg0 hMg hz

end Cvs.Zeta
