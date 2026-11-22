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
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Cvs.Zeta.Hadamard
import Cvs.Zeta.RiemannXi

/-!
# The zeros of `ξ` are countable
-/

noncomputable section

open Complex Cvs.Zeta

namespace Cvs.ZeroFree

/-- Each index of the canonical product names a point where the divisor is nonzero. -/
theorem divisor_zeroSeq_ne_zero (n : zeroIndex riemannXi) :
    ((MeromorphicOn.divisor riemannXi Set.univ (zeroSeq riemannXi n) : ℤ)) ≠ 0 := by
  intro hc
  have hpos : 0 < ((MeromorphicOn.divisor riemannXi Set.univ ((n.1 : ℂ)) : ℤ)).toNat :=
    lt_of_le_of_lt (Nat.zero_le _) n.2.isLt
  rw [show ((n.1 : ℂ)) = zeroSeq riemannXi n from rfl, hc] at hpos
  simp at hpos

/-- **The zeros of `ξ` are countable.**  A countable union of the finite sets rung 4 already
produces. -/
theorem countable_range_zeroSeq : (Set.range (zeroSeq riemannXi)).Countable := by
  have hsub : Set.range (zeroSeq riemannXi)
      ⊆ ⋃ k : ℕ, {u : ℂ | ‖u‖ ≤ (k : ℝ)
          ∧ ((MeromorphicOn.divisor riemannXi Set.univ u : ℤ)) ≠ 0} := by
    rintro u ⟨n, rfl⟩
    obtain ⟨k, hk⟩ := exists_nat_ge ‖zeroSeq riemannXi n‖
    exact Set.mem_iUnion.mpr ⟨k, hk, divisor_zeroSeq_ne_zero n⟩
  refine Set.Countable.mono hsub ?_
  exact Set.countable_iUnion fun k =>
    (finite_setOf_divisor_ne_zero analyticOnNhd_riemannXi (k : ℝ)).countable

end Cvs.ZeroFree
