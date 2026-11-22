import Mathlib
import Cvs.Zeta.AllZerosOnLine
import Cvs.Zeta.GaussKernel.RiemannHypothesisTarget
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement

/-!
# The induction on zeros is RH, not a route to it

A natural proposal, given that this development has the zeros as actual objects: enumerate
them and induct.
-/

namespace Cvs.Criterion

open Cvs.Zeta.GaussKernel.AdmissibleKernel Cvs.GaussKernel

/-- Under RH every nontrivial zero has zero deviation. -/
theorem del_eq_zero_of_riemannHypothesis (h : riemannHypothesis)
    (rho : nonTrivialZeroSet) : del rho = 0 := by
  obtain ⟨hz, h0, h1⟩ := rho.2
  have hre : ((rho : ℂ)).re = 1 / 2 := by
    refine h (rho : ℂ) hz (fun hn => ?_) (fun he => ?_)
    · obtain ⟨n, hn'⟩ := hn
      rw [hn'] at h0
      simp at h0
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    · rw [he] at h1; norm_num at h1
  rw [del, hre]; ring

end Cvs.Criterion
