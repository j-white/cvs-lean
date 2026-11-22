import Mathlib
import Cvs.L2a.ArchChannelFloorAbove
import Cvs.L2a.LeakageTailThreeChannels
import Cvs.Upstream.PlancherelL1L2SpectralDensity
import Cvs.WeilForm.Archimedean.ArchEnergySpectral
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# L2a's Part 1 on the project's own Weil form

For a tail `f` in the log variable, `SelfConvolutionFunctional`'s `weilForm P R f` is the pole `2(∫f e^{s/2})(∫f e^{−s/2})`, the archimedean
Lévy channel, and the truncated prime side. By Cvs.WeilForm.Archimedean.ArchEnergySpectral and Cvs.Upstream.PlancherelL1L2SpectralDensity the archimedean channel is `∫ archSymbol · ρ`,
`ρ = specDensity f`, `∫ρ = ∫f²`, so Cvs.L2a.LeakageTailThreeChannels applies: the form is at least `(ℓ − (ℓ − a₀)ε − p − q) ∫f²`, and eventually
positive along a family of scales.
-/

namespace Cvs.L2a.PartOneWeilForm

open MeasureTheory Real Filter
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.L2a.ArchChannelFloorAbove (floorK)
open Cvs.WeilForm.SelfConvolutionCosine (specDensity)

/-- **The archimedean channel of `weilForm` is `∫ archSymbol · specDensity`.** -/
theorem arch_eq {f : ℝ → ℝ} (h2 : MemLp f 2 volume) (h1 : Integrable f volume)
    (hsq : Integrable (fun s => f s ^ 2) volume)
    (hsh : ∀ u : ℝ, Integrable (fun s => f s * f (s + u)) volume)
    (hlevy : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Set.Ioi 0) volume)
    (hspec : Integrable (fun t => specDensity f t * (archSymbol t - archSymbol 0)) volume)
    (hρ : Integrable (specDensity f) volume) :
    archSymbol 0 * Cvs.Zeta.Explicit.Weil.selfConvolution f 0
        + ∫ u in Set.Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u
            * (Cvs.Zeta.Explicit.Weil.selfConvolution f 0 - Cvs.Zeta.Explicit.Weil.selfConvolution f (u / 2))
      = ∫ t, archSymbol t * specDensity f t := by
  have hL := Cvs.WeilForm.Archimedean.ArchEnergySpectral.integral_levy_eq h2 h1 hsq hsh hlevy hspec
  have hP := Cvs.Upstream.PlancherelL1L2SpectralDensity.integral_specDensity_eq_selfConvolution h1 h2
  have e : (∫ u in Set.Ioi (0:ℝ), Cvs.WeilForm.Archimedean.LevyDensity.densityU u
      * (Cvs.Zeta.Explicit.Weil.selfConvolution f 0 - Cvs.Zeta.Explicit.Weil.selfConvolution f (u / 2)))
      = ∫ u in Set.Ioi (0:ℝ), Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f u := rfl
  rw [e, hL, ← hP]
  have hsplit : ∫ t, archSymbol t * specDensity f t
      = (∫ t, specDensity f t * (archSymbol t - archSymbol 0)) + ∫ t, archSymbol 0 * specDensity f t := by
    calc ∫ t, archSymbol t * specDensity f t
        = ∫ t, (specDensity f t * (archSymbol t - archSymbol 0) + archSymbol 0 * specDensity f t) := by
          congr 1; funext t; ring
      _ = _ := integral_add hspec (hρ.const_mul (archSymbol 0))
  rw [hsplit, integral_const_mul]; ring

/-- **L2a Part 1 on `weilForm`.** With `N = ∫ f²`, low mass `≤ εN`, prime side `≤ pN`, pole `≥ −qN`:
`(floorK x K − (floorK x K − a₀)ε − p − q) N ≤ weilForm P R f`. -/
theorem weilForm_ge {f : ℝ → ℝ} (P R : ℕ) (h2 : MemLp f 2 volume) (h1 : Integrable f volume)
    (hsq : Integrable (fun s => f s ^ 2) volume)
    (hsh : ∀ u : ℝ, Integrable (fun s => f s * f (s + u)) volume)
    (hlevy : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Set.Ioi 0) volume)
    (hspec : Integrable (fun t => specDensity f t * (archSymbol t - archSymbol 0)) volume)
    (hρ : Integrable (specDensity f) volume)
    (hA : Integrable (fun t => archSymbol t * specDensity f t) volume)
    {x : ℝ} (hx : 0 < x) {K : ℕ} (hK : 1 ≤ K) (hfl : archSymbol 0 ≤ floorK x K) {ε p q : ℝ}
    (hlow : (∫ t in {t : ℝ | |t| < 2 * π * x}, specDensity f t) ≤ ε * ∫ s, f s ^ 2)
    (hPr : Cvs.Zeta.Explicit.Weil.primePowerSideTruncated P R (Cvs.Zeta.Explicit.Weil.selfConvolution f)
      ≤ p * ∫ s, f s ^ 2)
    (hpole : -(q * ∫ s, f s ^ 2) ≤ 2 * (∫ s, f s * exp (s / 2)) * (∫ s, f s * exp (-(s / 2)))) :
    (floorK x K - (floorK x K - archSymbol 0) * ε - p - q) * (∫ s, f s ^ 2)
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R f := by
  have hN : ∫ t, specDensity f t = ∫ s, f s ^ 2 := Cvs.Upstream.PlancherelL1L2SpectralDensity.integral_specDensity h1 h2
  rw [← hN] at hlow hPr hpole ⊢
  have h := Cvs.L2a.LeakageTailThreeChannels.tail_form_ge (specDensity f) (fun t => Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg f t)
    hρ hA hx hK hfl hlow hPr hpole
  rw [Cvs.WeilForm.SelfConvolutionFunctional.weilForm_eq, arch_eq h2 h1 hsq hsh hlevy hspec hρ]
  linarith

end Cvs.L2a.PartOneWeilForm
