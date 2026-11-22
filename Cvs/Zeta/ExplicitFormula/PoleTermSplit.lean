import Mathlib
import Cvs.Zeta.CriticalParam
import Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly

/-!
# The pole term splits into an entire part and an explicit pole
-/

namespace Cvs.Detection

open Complex
open scoped Topology

/-- The difference quotient of an entire function is entire. -/
theorem differentiable_dslope {G : ℂ → ℂ} (hG : Differentiable ℂ G) (a : ℂ) :
    Differentiable ℂ (dslope G a) := by
  rw [← differentiableOn_univ]
  rw [Complex.differentiableOn_dslope (by simp : (Set.univ : Set ℂ) ∈ 𝓝 a)]
  exact hG.differentiableOn

/-- **The split.**  Away from `z = 1` the second pole term is an entire part plus
an explicit simple pole. -/
theorem poleTwo_decomp (h : ℂ → ℂ) {z : ℂ} (hz : z ≠ 1) :
    Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly.poleTwo h z
      = dslope (Cvs.Zeta.ofCritical h) 1 z + Cvs.Zeta.ofCritical h 1 / (z - 1) := by
  rw [Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly.poleTwo, dslope_of_ne _ hz, slope_def_field]
  have hsub : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  field_simp
  ring

/-- The entire summand, named. -/
noncomputable def poleTwoEntire (h : ℂ → ℂ) (z : ℂ) : ℂ :=
  dslope (Cvs.Zeta.ofCritical h) 1 z

theorem differentiable_poleTwoEntire {h : ℂ → ℂ} (hd : Differentiable ℂ h) :
    Differentiable ℂ (poleTwoEntire h) :=
  differentiable_dslope (Cvs.Zeta.differentiable_ofCritical hd) 1

end Cvs.Detection
