import Mathlib
import Cvs.Zeta.GaussKernel.ArchimedeanCutoffBound

/-!
# The Riemann–Siegel phase, without a branch of `log Γ`
-/

open intervalIntegral

namespace Cvs.ZeroCounting

/-- **The Riemann–Siegel phase**, normalised by `θ(0) = 0`. -/
noncomputable def theta (t : ℝ) : ℝ := ∫ u in (0 : ℝ)..t, Cvs.Zeta.GaussKernel.ArchimedeanCutoffBound.archScore u

end Cvs.ZeroCounting
