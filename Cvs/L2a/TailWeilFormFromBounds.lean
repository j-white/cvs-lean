import Mathlib
import Cvs.L2a.ArchChannelFloorAbove
import Cvs.L2a.PartOneWeilForm
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.TailPrimeSideMultiplicative
import Cvs.Prolate.Mellin.FirstModeMellinEdge
import Cvs.Prolate.Mellin.MellinKernelSturmLiouville
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyIntegrandSpectral
import Cvs.WeilForm.Archimedean.LevyTonelli
import Cvs.WeilForm.EffectiveSymbolThreeFacts
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
# The Weil form of a tail on `[1, ∞)`, from its Mellin, prime and pole bounds

For `f = logScale F` in `L¹ ∩ L²` with the Lévy condition: if `|∫F y_t|, |∫F ỹ_t| ≤ B` for `|t| < 2πx`, the prime
side `2Σ log p ∫F(θ)F(p^rθ) ≤ p N` and `−qN ≤ 2(∫F)(∫F/θ)`, `N = ∫F²`, then
`(floorK x K − (floorK x K − a₀)·4xB²/N − p − q) N ≤ W(f)`.
-/

namespace Cvs.L2a.TailWeilFormFromBounds

open MeasureTheory Real Set Cvs.L2a.TailLogScaleTest
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.L2a.ArchChannelFloorAbove (floorK)
open Cvs.WeilForm.SelfConvolutionCosine (specDensity)

/-- `F y_t` is integrable on `(1, ∞)` when `F` is. -/
theorem integrableOn_mul_ky {F : ℝ → ℝ} (hF : IntegrableOn F (Ioi 1)) (t : ℝ) :
    IntegrableOn (fun θ => F θ * Cvs.Prolate.Mellin.MellinKernelSturmLiouville.ky t θ) (Ioi 1) := by
  have hm : AEStronglyMeasurable (Cvs.Prolate.Mellin.MellinKernelSturmLiouville.ky t) (volume.restrict (Ioi 1)) := by
    have : Measurable (Cvs.Prolate.Mellin.MellinKernelSturmLiouville.ky t) := by unfold Cvs.Prolate.Mellin.MellinKernelSturmLiouville.ky; fun_prop
    exact this.aestronglyMeasurable
  have := hF.bdd_mul (c := 1) hm (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with θ hθ
    have := Cvs.Prolate.Mellin.FirstModeMellinEdge.abs_ky_le (ξ := t) (by linarith [mem_Ioi.mp hθ] : (0 : ℝ) < θ)
    rw [Real.norm_eq_abs]
    exact this.trans (div_le_one_of_le₀ (Real.one_le_sqrt.mpr (le_of_lt hθ)) (sqrt_nonneg _)))
  simpa [IntegrableOn, mul_comm] using this

theorem integrableOn_mul_kys {F : ℝ → ℝ} (hF : IntegrableOn F (Ioi 1)) (t : ℝ) :
    IntegrableOn (fun θ => F θ * Cvs.Prolate.Mellin.MellinKernelSturmLiouville.kys t θ) (Ioi 1) := by
  have hm : AEStronglyMeasurable (Cvs.Prolate.Mellin.MellinKernelSturmLiouville.kys t) (volume.restrict (Ioi 1)) := by
    have : Measurable (Cvs.Prolate.Mellin.MellinKernelSturmLiouville.kys t) := by unfold Cvs.Prolate.Mellin.MellinKernelSturmLiouville.kys; fun_prop
    exact this.aestronglyMeasurable
  have := hF.bdd_mul (c := 1) hm (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with θ hθ
    have := Cvs.Prolate.Mellin.FirstModeMellinEdge.abs_kys_le (ξ := t) (by linarith [mem_Ioi.mp hθ] : (0 : ℝ) < θ)
    rw [Real.norm_eq_abs]
    exact this.trans (div_le_one_of_le₀ (Real.one_le_sqrt.mpr (le_of_lt hθ)) (sqrt_nonneg _)))
  simpa [IntegrableOn, mul_comm] using this

/-- **The Weil form of a tail**, from its Mellin bound below `2πx`, its prime bound and its pole bound. -/
theorem weilForm_tail_ge {F : ℝ → ℝ} (P R : ℕ) (hF : ∀ θ ≤ 1, F θ = 0) (hFi : IntegrableOn F (Ioi 1))
    (h2 : MemLp (logScale F) 2 volume) (h1 : Integrable (logScale F) volume)
    (hsq : Integrable (fun s => logScale F s ^ 2) volume)
    (hsh : ∀ u : ℝ, Integrable (fun s => logScale F s * logScale F (s + u)) volume)
    (hlevy : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (logScale F)) (Ioi 0) volume)
    {x : ℝ} (hx : 0 < x) {K : ℕ} (hK : 1 ≤ K) (hfl : archSymbol 0 ≤ floorK x K) {B p q : ℝ}
    (hN : 0 < ∫ θ in Ioi 1, F θ ^ 2)
    (hB : ∀ t : ℝ, |t| < 2 * π * x → |∫ θ in Ioi 1, F θ * Cvs.Prolate.Mellin.MellinKernelSturmLiouville.ky t θ| ≤ B
      ∧ |∫ θ in Ioi 1, F θ * Cvs.Prolate.Mellin.MellinKernelSturmLiouville.kys t θ| ≤ B)
    (hPr : ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
        2 * Real.log p * (∫ θ in Ioi 1, F θ * F ((p : ℝ) ^ r * θ)) ≤ p * ∫ θ in Ioi 1, F θ ^ 2)
    (hpole : -(q * ∫ θ in Ioi 1, F θ ^ 2) ≤ 2 * (∫ θ in Ioi 1, F θ) * (∫ θ in Ioi 1, F θ / θ)) :
    (floorK x K - (floorK x K - archSymbol 0) * (4 * x * B ^ 2 / ∫ θ in Ioi 1, F θ ^ 2) - p - q)
        * (∫ θ in Ioi 1, F θ ^ 2)
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (logScale F) := by
  set N := ∫ θ in Ioi 1, F θ ^ 2 with hNdef
  have hNf : ∫ s, logScale F s ^ 2 = N := integral_sq F hF
  have hρ := Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity h2 h1
  have hspec := Cvs.WeilForm.Archimedean.LevyTonelli.integrable_specDensity_mul_arch h2 h1 hlevy
  have hA := Cvs.WeilForm.EffectiveSymbolThreeFacts.integrable_arch_mul h2 h1 hlevy
  -- the low mass
  have hset : {t : ℝ | |t| < 2 * π * x} = Ioo (-(2 * π * x)) (2 * π * x) := by
    ext t; simp [abs_lt]
  have hpt : ∀ t ∈ Ioo (-(2 * π * x)) (2 * π * x), specDensity (logScale F) t ≤ B ^ 2 / π := by
    intro t ht
    have ht' : |t| < 2 * π * x := abs_lt.mpr ⟨ht.1, ht.2⟩
    rw [specDensity_eq F hF t (integrableOn_mul_ky hFi t) (integrableOn_mul_kys hFi t)]
    obtain ⟨ha, hb⟩ := hB t ht'
    have ha2 := sq_le_sq' (abs_le.mp ha).1 (abs_le.mp ha).2
    have hb2 := sq_le_sq' (abs_le.mp hb).1 (abs_le.mp hb).2
    rw [div_le_div_iff₀ (by positivity) pi_pos]
    nlinarith [pi_pos]
  have hlow : (∫ t in {t : ℝ | |t| < 2 * π * x}, specDensity (logScale F) t)
      ≤ 4 * x * B ^ 2 / N * ∫ s, logScale F s ^ 2 := by
    rw [hset, hNf, div_mul_cancel₀ _ hN.ne']
    calc (∫ t in Ioo (-(2 * π * x)) (2 * π * x), specDensity (logScale F) t)
        ≤ ∫ t in Ioo (-(2 * π * x)) (2 * π * x), B ^ 2 / π :=
          setIntegral_mono_on hρ.integrableOn (integrableOn_const (by simp [Real.volume_Ioo]))
            measurableSet_Ioo hpt
      _ = 4 * x * B ^ 2 := by
          rw [setIntegral_const, Real.volume_real_Ioo_of_le (by nlinarith [pi_pos]), smul_eq_mul]
          field_simp; ring
  have hPr' : Cvs.Zeta.Explicit.Weil.primePowerSideTruncated P R
      (Cvs.Zeta.Explicit.Weil.selfConvolution (logScale F)) ≤ p * ∫ s, logScale F s ^ 2 := by
    rw [Cvs.L2a.TailPrimeSideMultiplicative.primeSide_eq F hF, hNf]; exact hPr
  have hpole' : -(q * ∫ s, logScale F s ^ 2)
      ≤ 2 * (∫ s, logScale F s * exp (s / 2)) * (∫ s, logScale F s * exp (-(s / 2))) := by
    rw [hNf, integral_mul_exp F hF, integral_mul_exp_neg F hF]; exact hpole
  have key := Cvs.L2a.PartOneWeilForm.weilForm_ge P R h2 h1 hsq hsh hlevy hspec hρ hA hx hK hfl hlow hPr' hpole'
  rwa [hNf] at key

end Cvs.L2a.TailWeilFormFromBounds
