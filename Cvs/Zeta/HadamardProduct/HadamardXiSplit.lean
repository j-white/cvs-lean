import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Cvs.Zeta.ArgumentPrinciple
import Cvs.Zeta.Hadamard
import Cvs.Zeta.HadamardProduct.CanonicalProductLogDeriv
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.Weierstrass

/-!
# Hadamard for `ξ`, in the criterion's shape

`Cvs.Zeta.exists_logDeriv_riemannXi` gives
-/

noncomputable section

open Complex Finset Cvs.Zeta

namespace Cvs.ZeroFree

/-- Each index of the canonical product names a zero: the fibre `Fin (divisor u).toNat` is
inhabited only where the order is positive. -/
theorem riemannXi_zeroSeq (n : zeroIndex riemannXi) : riemannXi (zeroSeq riemannXi n) = 0 := by
  by_contra hc
  have hord : analyticOrderAt riemannXi ((n.1 : ℂ)) = 0 := by
    rw [analyticOrderAt_eq_zero]
    exact Or.inr hc
  have hd : ((MeromorphicOn.divisor riemannXi Set.univ ((n.1 : ℂ)) : ℤ)) = 0 := by
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply analyticOnNhd_riemannXi (Set.mem_univ _),
      hord]
    simp
  have hpos : 0 < ((MeromorphicOn.divisor riemannXi Set.univ ((n.1 : ℂ)) : ℤ)).toNat :=
    lt_of_le_of_lt (Nat.zero_le _) n.2.isLt
  rw [hd] at hpos
  simp at hpos

/-- Nor is `z` a small zero, when `ξ(z) ≠ 0`. -/
theorem notMem_smallZeros {z : ℂ} (hz : riemannXi z ≠ 0) :
    z ∉ finite_xiSmallZeros.toFinset := by
  intro hmem
  rw [Set.Finite.mem_toFinset] at hmem
  have hord : analyticOrderAt riemannXi z = 0 := by
    rw [analyticOrderAt_eq_zero]; exact Or.inr hz
  refine hmem.2 ?_
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply analyticOnNhd_riemannXi (Set.mem_univ z), hord]
  simp

/-- **Hadamard for `ξ`, product and logarithmic derivative together.**
`Cvs.Zeta.exists_logDeriv_riemannXi` quantifies its `h` away, so the `h` it hands back cannot
be tied to the one in `hadamard_riemannXi`. -/
theorem exists_hadamard_riemannXi_split :
    ∃ h : ℂ → ℂ, Differentiable ℂ h
      ∧ (∀ z : ℂ, riemannXi z
          = finiteFactor finite_xiSmallZeros.toFinset
              (fun u => ((MeromorphicOn.divisor riemannXi Set.univ u : ℤ)).toNat) z
            * (∏' n : zeroIndex riemannXi, weierstrassE1 (z / zeroSeq riemannXi n))
            * Complex.exp (h z))
      ∧ (∀ z : ℂ, riemannXi z ≠ 0 →
          logDeriv riemannXi z
            = (∑ u ∈ finite_xiSmallZeros.toFinset,
                  (((((MeromorphicOn.divisor riemannXi Set.univ u : ℤ)).toNat : ℕ) : ℂ))
                    / (z - u))
              + ((∑' n : zeroIndex riemannXi,
                    (1 / (z - zeroSeq riemannXi n) + 1 / zeroSeq riemannXi n))
                  + deriv h z)) := by
  classical
  obtain ⟨h, hhdiff, hfac⟩ := hadamard_riemannXi
  refine ⟨h, hhdiff, hfac, fun z hz => ?_⟩
  have hzS : z ∉ finite_xiSmallZeros.toFinset := notMem_smallZeros hz
  have hzn : ∀ n, z ≠ zeroSeq riemannXi n := by
    intro n hc
    exact hz (by rw [hc]; exact riemannXi_zeroSeq n)
  have hFne : finiteFactor finite_xiSmallZeros.toFinset
      (fun u => ((MeromorphicOn.divisor riemannXi Set.univ u : ℤ)).toNat) z ≠ 0 := by
    rw [finiteFactor, Finset.prod_ne_zero_iff]
    intro u hu
    refine pow_ne_zero _ (sub_ne_zero_of_ne ?_)
    intro hc
    exact hzS (hc ▸ hu)
  have hPne : (∏' n : zeroIndex riemannXi, weierstrassE1 (z / zeroSeq riemannXi n)) ≠ 0 :=
    tprod_weierstrassE1_div_ne_zero summable_inv_norm_sq_riemannXi hzn
  have hFd : DifferentiableAt ℂ (finiteFactor finite_xiSmallZeros.toFinset
      (fun u => ((MeromorphicOn.divisor riemannXi Set.univ u : ℤ)).toNat)) z :=
    differentiable_finiteFactor _ _ z
  have hPd : DifferentiableAt ℂ
      (fun w : ℂ => ∏' n : zeroIndex riemannXi, weierstrassE1 (w / zeroSeq riemannXi n)) z :=
    differentiable_tprod_riemannXi z
  have hEne : Complex.exp (h z) ≠ 0 := Complex.exp_ne_zero _
  have hEd : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (h w)) z :=
    (Complex.differentiable_exp.comp hhdiff) z
  have hlogexp : logDeriv (fun w : ℂ => Complex.exp (h w)) z = deriv h z := by
    rw [logDeriv_apply]
    have hd : HasDerivAt (fun w : ℂ => Complex.exp (h w))
        (Complex.exp (h z) * deriv h z) z := ((hhdiff z).hasDerivAt).cexp
    rw [hd.deriv]
    field_simp
  have hsum := (Cvs.ZeroFree.hasSum_logDeriv_tprod summable_inv_norm_sq_riemannXi
    (fun n => zeroSeq_ne_zero n) hzn).tsum_eq
  have hcongr : logDeriv riemannXi z
      = logDeriv (fun w : ℂ =>
          (finiteFactor finite_xiSmallZeros.toFinset
              (fun u => ((MeromorphicOn.divisor riemannXi Set.univ u : ℤ)).toNat) w
            * (∏' n : zeroIndex riemannXi, weierstrassE1 (w / zeroSeq riemannXi n)))
          * Complex.exp (h w)) z := by
    exact congrArg (fun f : ℂ → ℂ => logDeriv f z) (funext hfac)
  -- the two splits, as typed `have`s: `logDeriv_mul` will not unify higher-order as a
  -- rewrite argument
  have hsplit1 : logDeriv (fun w : ℂ =>
        (finiteFactor finite_xiSmallZeros.toFinset
            (fun u => ((MeromorphicOn.divisor riemannXi Set.univ u : ℤ)).toNat) w
          * (∏' n : zeroIndex riemannXi, weierstrassE1 (w / zeroSeq riemannXi n)))
        * Complex.exp (h w)) z
      = logDeriv (fun w : ℂ =>
            finiteFactor finite_xiSmallZeros.toFinset
              (fun u => ((MeromorphicOn.divisor riemannXi Set.univ u : ℤ)).toNat) w
            * (∏' n : zeroIndex riemannXi, weierstrassE1 (w / zeroSeq riemannXi n))) z
        + logDeriv (fun w : ℂ => Complex.exp (h w)) z :=
    logDeriv_mul z (mul_ne_zero hFne hPne) hEne (hFd.mul hPd) hEd
  have hsplit2 : logDeriv (fun w : ℂ =>
        finiteFactor finite_xiSmallZeros.toFinset
          (fun u => ((MeromorphicOn.divisor riemannXi Set.univ u : ℤ)).toNat) w
        * (∏' n : zeroIndex riemannXi, weierstrassE1 (w / zeroSeq riemannXi n))) z
      = logDeriv (finiteFactor finite_xiSmallZeros.toFinset
            (fun u => ((MeromorphicOn.divisor riemannXi Set.univ u : ℤ)).toNat)) z
        + logDeriv (fun w : ℂ =>
            ∏' n : zeroIndex riemannXi, weierstrassE1 (w / zeroSeq riemannXi n)) z :=
    logDeriv_mul z hFne hPne hFd hPd
  rw [hcongr, hsplit1, hsplit2, logDeriv_finiteFactor hzS, hsum, hlogexp]
  ring

end Cvs.ZeroFree
