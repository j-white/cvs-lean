import Mathlib
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LipschitzLevyIntegrable
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.WeilFormAeClass
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.WeilPositivityStatement

/-!
# Lipschitz window tests, and the tent basis

A continuous, globally Lipschitz function supported in `[0, L]` has an integrable Lévy
term, so its window class lies in the form domain; the tents `max (1 − |xn/L − i|) 0` at
the interior nodes of an `n`-fold subdivision are such functions.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Real Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.LipschitzTentBasis

/-! ### A Lipschitz test lies in the form domain -/

/-- **Lipschitz window tests lie in the form domain.**  The deficit's quadratic vanishing
absorbs the density's singularity at the origin. -/
theorem lipschitz_mem_formDomain {L K : ℝ} (hL : 0 ≤ L) {F : ℝ → ℝ}
    (hFc : Continuous F) (hlip : ∀ s t : ℝ, |F s - F t| ≤ K * |s - t|)
    (hsupp : ∀ x, x ∉ Icc (0:ℝ) L → F x = 0)
    (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)
    (hφ : Cvs.WeilForm.WindowRepresentative.rep φ =ᵐ[volume] F) :
    φ ∈ Cvs.WeilForm.FormDomain.formDomain hL := by
  have hsq : Integrable fun s => (F s) ^ 2 := by
    refine Continuous.integrable_of_hasCompactSupport (by continuity) ?_
    exact HasCompactSupport.intro (isCompact_Icc (a := (0:ℝ)) (b := L))
      (fun x hx => by rw [hsupp x hx]; ring)
  have hcross : ∀ v : ℝ, Integrable fun s => F s * F (s + v) := by
    intro v
    refine Continuous.integrable_of_hasCompactSupport
      (hFc.mul (hFc.comp (continuous_id.add continuous_const))) ?_
    exact HasCompactSupport.intro (isCompact_Icc (a := (0:ℝ)) (b := L))
      (fun x hx => by simp [hsupp x hx])
  have hmain := Cvs.WeilForm.Archimedean.LipschitzLevyIntegrable.integrableOn_levy_of_lipschitz hL hFc hlip hsupp hsq hcross
  show IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep φ)) (Ioi 0) volume
  have heq : Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep φ)
      = fun u => Cvs.WeilForm.Archimedean.LevyDensity.densityU u
        * (selfConvolution F 0 - selfConvolution F (u / 2)) := by
    funext u
    unfold Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy
    rw [Cvs.WeilForm.WeilFormAeClass.selfConvolution_congr_ae hφ 0,
      Cvs.WeilForm.WeilFormAeClass.selfConvolution_congr_ae hφ (u / 2)]
  rw [heq]
  exact hmain

/-! ### The tents of an `n`-fold subdivision -/

/-! ### Finite tent combinations -/

/-! ### From form bounds on the form domain to form bounds on the window -/

end Cvs.WeilForm.LipschitzTentBasis
