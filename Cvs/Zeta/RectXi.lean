import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Cvs.Zeta.Hadamard
import Cvs.Zeta.InnerFactor
import Cvs.Zeta.LandauLemma
import Cvs.Zeta.RectArgument
import Cvs.Zeta.RectWeighted
import Cvs.Zeta.RectWinding
import Cvs.Zeta.RiemannXi

/-!
# The zero sum for `ξ` on a rectangle

`Cvs.Zeta.RectWeighted.rect_argument_principle_weighted` had no consumer.
-/

open Complex

namespace Cvs.Zeta

/-- Repeating each zero according to its multiplicity, as a `Finset.sigma`. -/
theorem prod_sigma_sub (S : Finset ℂ) (m : ℂ → ℕ) (u : ℂ) :
    (∏ n ∈ S.sigma fun ρ => Finset.range (m ρ), (u - n.1)) = ∏ ρ ∈ S, (u - ρ) ^ m ρ := by
  rw [Finset.prod_sigma]
  exact Finset.prod_congr rfl fun ρ _ => by simp

theorem sum_sigma_apply (S : Finset ℂ) (m : ℂ → ℕ) (φ : ℂ → ℂ) :
    (∑ n ∈ S.sigma fun ρ => Finset.range (m ρ), φ n.1) = ∑ ρ ∈ S, (m ρ : ℂ) * φ ρ := by
  rw [Finset.sum_sigma]
  exact Finset.sum_congr rfl fun ρ _ => by simp [nsmul_eq_mul]

/-- **The weighted argument principle with multiplicities.** -/
theorem rect_argument_principle_mult {f g φ : ℂ → ℂ} {z w : ℂ} {S : Finset ℂ} {m : ℂ → ℕ}
    {U : Set ℂ}
    (hin : ∀ ρ ∈ S, z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im)
    (hUo : IsOpen U) (hU : closedRect z w ⊆ U)
    (hfg : ∀ u, f u = (∏ ρ ∈ S, (u - ρ) ^ m ρ) * g u)
    (hgd : DifferentiableOn ℂ g U) (hgne : ∀ u ∈ U, g u ≠ 0)
    (hφ : DifferentiableOn ℂ φ U) :
    rectBoundaryIntegral (fun u => deriv f u / f u * φ u) z w
      = 2 * (Real.pi : ℂ) * I * ∑ ρ ∈ S, (m ρ : ℂ) * φ ρ := by
  classical
  have h := rect_argument_principle_weighted
    (F := S.sigma fun ρ => Finset.range (m ρ)) (b := fun n => n.1)
    (f := f) (g := g) (φ := φ) (U := U)
    (fun n hn => hin n.1 (Finset.mem_sigma.mp hn).1)
    hUo hU (fun u => by rw [hfg u, prod_sigma_sub]) hgd hgne hφ
  rw [h, sum_sigma_apply]

/-! ### The zero sum for `ξ` at finite height -/

/-- **The argument principle at `f = ξ`.** -/
theorem rect_argument_principle_riemannXi {z w : ℂ} {U : Set ℂ} {φ : ℂ → ℂ} (r : ℝ)
    (hUo : IsOpen U) (hU : closedRect z w ⊆ U) (hUr : U ⊆ Metric.closedBall (0 : ℂ) r)
    (hzU : ∀ u ∈ U, riemannXi u = 0 →
      z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im)
    (hφ : DifferentiableOn ℂ φ U) :
    ∃ (S : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ ∈ S, riemannXi ρ = 0) ∧
      (∀ ρ ∈ S, z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im) ∧
      (∀ u ∈ U, riemannXi u = 0 → u ∈ S) ∧
      (∀ u : ℂ, (m u : ℤ) = MeromorphicOn.divisor riemannXi Set.univ u) ∧
      rectBoundaryIntegral (fun u => logDeriv riemannXi u * φ u) z w
        = 2 * (Real.pi : ℂ) * I * ∑ ρ ∈ S, (m ρ : ℂ) * φ ρ := by
  classical
  obtain ⟨T, m, g, hT0, hTr, hgana, hfac, hgne, -, hTzero, hTmult⟩ :=
    exists_inner_factorization analyticOnNhd_riemannXi analyticOrderAt_riemannXi_ne_top
      riemannXi_zero_ne_zero r
  -- points of `U` sit in the disc, so `g` cannot vanish there
  have hUnorm : ∀ u ∈ U, ‖u‖ ≤ r := by
    intro u hu
    have := hUr hu
    simpa [Metric.mem_closedBall, dist_zero_right] using this
  -- every zero of `ξ` in `U` is a member of `T`
  have hmemT : ∀ u ∈ U, riemannXi u = 0 → u ∈ T := by
    intro u hu h0
    by_contra hc
    have hg : g u ≠ 0 := hgne u (hUnorm u hu)
    have hn : normProd T m u ≠ 0 := normProd_ne_zero_of_notMem hT0 hc
    have hxi : riemannXi u ≠ 0 := by rw [hfac u]; exact mul_ne_zero hg hn
    exact hxi h0
  set S : Finset ℂ := T.filter
    (fun ρ => z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im) with hSdef
  have hSsub : S ⊆ T := Finset.filter_subset _ _
  have hSin : ∀ ρ ∈ S, z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im :=
    fun ρ hρ => (Finset.mem_filter.mp hρ).2
  have hcap : ∀ u ∈ U, riemannXi u = 0 → u ∈ S :=
    fun u hu h0 => Finset.mem_filter.mpr ⟨hmemT u hu h0, hzU u hu h0⟩
  -- the outside zeros never meet `U`
  have hout : ∀ u ∈ U, u ∉ T \ S := by
    intro u hu hc
    obtain ⟨huT, huS⟩ := Finset.mem_sdiff.mp hc
    exact huS (hcap u hu (hTzero u huT))
  refine ⟨S, m, fun ρ hρ => hTzero ρ (hSsub hρ), hSin, hcap, hTmult, ?_⟩
  -- the rectangle-adapted factorisation
  set C : ℂ := ∏ ρ ∈ S, (-(ρ⁻¹)) ^ m ρ with hCdef
  set G : ℂ → ℂ := fun u => C * (g u * normProd (T \ S) m u) with hGdef
  have hT0' : ∀ ρ ∈ T \ S, ρ ≠ 0 := fun ρ hρ => hT0 ρ (Finset.mem_sdiff.mp hρ).1
  have hS0 : ∀ ρ ∈ S, ρ ≠ 0 := fun ρ hρ => hT0 ρ (hSsub hρ)
  have hsplit : ∀ u : ℂ, riemannXi u = (∏ ρ ∈ S, (u - ρ) ^ m ρ) * G u := by
    intro u
    have hprod : normProd (T \ S) m u * normProd S m u = normProd T m u := by
      rw [normProd, normProd, normProd, Finset.prod_sdiff hSsub]
    rw [hfac u, hGdef, ← hprod, normProd_eq_const_mul_finiteFactor hS0, finiteFactor, hCdef]
    ring
  have hgdiff : Differentiable ℂ g := fun x => (hgana x (Set.mem_univ x)).differentiableAt
  have hGd : DifferentiableOn ℂ G U :=
    ((differentiable_const C).mul
      (hgdiff.mul (differentiable_normProd (T \ S) m hT0'))).differentiableOn
  have hGne : ∀ u ∈ U, G u ≠ 0 := by
    intro u hu
    refine mul_ne_zero ?_ (mul_ne_zero (hgne u (hUnorm u hu)) ?_)
    · exact const_ne_zero_of_forall_ne_zero hS0
    · exact normProd_ne_zero_of_notMem hT0' (hout u hu)
  have := rect_argument_principle_mult (f := riemannXi) (g := G) (φ := φ) (U := U)
    hSin hUo hU hsplit hGd hGne hφ
  simpa [logDeriv_apply] using this

end Cvs.Zeta
