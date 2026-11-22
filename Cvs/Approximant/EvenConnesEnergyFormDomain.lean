import Mathlib
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.FullTailPolarisation
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowFormTailLimit
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.BilinearCrossRepresentatives
import Cvs.WeilForm.CentredWindowTranslate
import Cvs.WeilForm.CompressedPhysicalPrimeForm
import Cvs.WeilForm.EffectiveSymbolThreeFacts
import Cvs.WeilForm.EvenFormMobiusPreimage
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.LevyDomainSpectral
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.TailBoundOnWindow
import Cvs.WeilForm.ThetaFormWindowIdentification
import Cvs.WeilForm.ThetaPairingBilinear
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.WeilForm.TruncatedFormPolarised
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowRepresentative
import Cvs.Xi.EImageWindowPoisson
import Cvs.Xi.PhysicalReciprocalReflection
import Cvs.Xi.ReciprocalWindowPhysicalL2
import Cvs.Zeta.PrimePowerSideTruncated

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The full even Connes energy on the closed form domain

Exact support and the actual logarithmic form-domain hypotheses suffice for the
angular Weil bridge.  Those hypotheses follow from the constructed Connes class,
so the full arch, pole, and arithmetic double-commutator identity is an identity
of the closed quadratic form, without a new regularity or decay premise.
-/

noncomputable section

open Real Set MeasureTheory Filter
open scoped InnerProductSpace

namespace Cvs.Approximant.EvenConnesEnergyFormDomain
open Cvs.ZeroCounting

open Cvs.WeilForm.ThetaSpaceParseval (weilθ poleP poleM dil)
open Cvs.L2a.TailLogScaleTest (logScale)

/-- The angular bridge requires the logarithmic form domain, not a tame physical representative. -/
theorem weilθ_eq_crossW_of_log_domain {F G : ℝ → ℝ} {α β : ℝ}
    (hα : 0 < α) (hF : ∀ θ ∉ Icc α β, F θ = 0)
    (hG : ∀ θ ∉ Icc α β, G θ = 0)
    (hf1 : Integrable (logScale F)) (hf2 : MemLp (logScale F) 2 volume)
    (hfl : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (logScale F)) (Ioi 0) volume)
    (hg1 : Integrable (logScale G)) (hg2 : MemLp (logScale G) 2 volume)
    (hgl : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (logScale G)) (Ioi 0) volume)
    {P R : ℕ} (hP : β / α ≤ P) (hR : log (β / α) ≤ R * log 2) :
    weilθ F G = Cvs.WeilForm.SymmetricBilinearForm.crossW P R (logScale F) (logScale G) := by
  unfold weilθ Cvs.WeilForm.SymmetricBilinearForm.crossW Cvs.WeilForm.TruncatedFormPolarised.poleF Cvs.WeilForm.TruncatedFormPolarised.poleG
  rw [Cvs.WeilForm.ThetaFormWindowIdentification.poleP_eq_integral hF, Cvs.WeilForm.ThetaFormWindowIdentification.poleP_eq_integral hG,
    ← Cvs.WeilForm.ThetaFormWindowIdentification.integral_logScale_mul_exp F, ← Cvs.WeilForm.ThetaFormWindowIdentification.integral_logScale_mul_exp G,
    ← Cvs.WeilForm.ThetaFormWindowIdentification.integral_logScale_mul_exp_neg F, ← Cvs.WeilForm.ThetaFormWindowIdentification.integral_logScale_mul_exp_neg G,
    Cvs.L2a.WindowFormTailLimit.integral_arch_crossSpec_eq hf2 hf1 hfl hg2 hg1 hgl,
    Cvs.WeilForm.ThetaPairingBilinear.tsum_dil_eq hα hF hG hP hR]
  ring

/-- The actual even angular Connes representative has exact physical support. -/
theorem connesAngularEven_support (x : ℝ) :
    ∀ θ ∉ Icc (1 / x) 1, Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x θ = 0 :=
  fun _ hθ => Cvs.Xi.PhysicalReciprocalReflection.evenPhysical_of_notMem hθ _

/-- The closed-domain representative is the shifted logarithmic actual angular profile. -/
theorem rep_even_connesClass_ae_logScale {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    Cvs.WeilForm.WindowRepresentative.rep (Cvs.WeilForm.EvenOddSplitForm.evenPart (log_natCast_nonneg x) (Cvs.Approximant.CosineColumnTailPairing.connesClass hx)
      : Cvs.WeilForm.WeilFormOnWindowL2.window (log x)) =ᵐ[volume]
        fun s => logScale (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) (s - log x) :=
  (Cvs.WeilForm.WindowRepresentative.ae_eq_rep _).symm.trans (Cvs.Xi.PhysicalReciprocalReflection.coe_even_connesClass_ae_logScale hx)

/-- All logarithmic integrability hypotheses come from actual closed form-domain membership. -/
theorem connesAngularEven_log_domain {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    Integrable (logScale (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x)) ∧
      MemLp (logScale (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x)) 2 volume ∧
      IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (logScale (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x))) (Ioi 0) volume := by
  let φ := Cvs.WeilForm.EvenOddSplitForm.evenPart (log_natCast_nonneg x) (Cvs.Approximant.CosineColumnTailPairing.connesClass hx)
  have hrep := rep_even_connesClass_ae_logScale hx
  have hi := (Cvs.WeilForm.LevyDomainSpectral.integrable_rep (log_natCast_nonneg x)
    (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (log x))).congr hrep
  have h2 := (memLp_congr_ae hrep).mp (Cvs.WeilForm.WindowRepresentative.memLp_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (log x)))
  have hl := Cvs.WeilForm.FormDomain.hdom_of_mem φ
  rw [Cvs.Approximant.SpineSubspace.levy_congr_ae hrep] at hl
  simp only [sub_eq_add_neg, Cvs.WeilForm.TailBoundOnWindow.levy_translate] at hl
  refine ⟨?_, ?_, hl⟩
  · simpa only [add_sub_cancel_right] using hi.comp_add_right (log (x : ℝ))
  · simpa only [add_sub_cancel_right] using Cvs.WeilForm.CentredWindowTranslate.memLp_translate (log (x : ℝ)) h2

/-- The actual spectral arch channel is genuinely integrable on the full line. -/
theorem integrable_arch_connesAngularEven {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    Integrable (fun t => Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t * Cvs.L2a.FullTailPolarisation.crossSpec
      (logScale (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x)) (logScale (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x)) t) := by
  obtain ⟨hf1, hf2, hfl⟩ := connesAngularEven_log_domain hx
  simpa only [Cvs.WeilForm.ThetaFormWindowIdentification.crossSpec_self] using Cvs.WeilForm.EffectiveSymbolThreeFacts.integrable_arch_mul hf2 hf1 hfl

/-- The actual physical profile is integrable, so its positive pole is a genuine integral. -/
theorem integrable_connesAngularEven {x : ℝ} (hx : 0 < x) :
    Integrable (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) := by
  apply Cvs.WeilForm.CentredWindowTranslate.integrable_of_support zero_le_one (Cvs.Xi.PhysicalReciprocalReflection.memLp_connesAngularEven hx)
  intro θ hθ
  apply connesAngularEven_support x θ
  intro hm
  apply hθ
  exact ⟨(one_div_pos.mpr hx).trans_le hm.1, hm.2⟩

/-- The actual reciprocal pole is also a genuine integral. -/
theorem integrable_connesAngularEven_div {x : ℝ} (hx : 0 < x) :
    Integrable (fun θ => Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x θ / θ) := by
  have hi := (integrable_connesAngularEven hx).integrableOn (s := Icc (1 / x) 1)
  have hc : ContinuousOn (fun θ : ℝ => θ⁻¹) (Icc (1 / x) 1) :=
    continuousOn_inv₀.mono fun θ hθ => ((one_div_pos.mpr hx).trans_le hθ.1).ne'
  have hp := hi.continuousOn_mul hc isCompact_Icc
  have hp' : IntegrableOn (fun θ => Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x θ / θ)
      (Icc (1 / x) 1) volume := by
    simpa only [div_eq_mul_inv, mul_comm] using hp
  exact hp'.integrable_of_forall_notMem_eq_zero fun θ hθ => by
    rw [connesAngularEven_support x θ hθ, zero_div]

/-- The actual angular prime channel has finite support at the complete cutoff. -/
theorem prime_connesAngularEven_zero_of_large {x n : ℕ}
    (hx : 80 ≤ 2 * π * x) (hn : x < n) :
    (ArithmeticFunction.vonMangoldt n : ℝ) *
      (dil (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) n
        + dil (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) n) = 0 := by
  have hd : (1 : ℝ) / (1 / x) < n := by
    rw [one_div_one_div]
    exact_mod_cast hn
  simp only [Cvs.L2a.WindowFormTailLimit.dil_eq_zero_of_support (one_div_pos.mpr (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx))
    (connesAngularEven_support x) (connesAngularEven_support x) hd, add_zero, mul_zero]

/-- The actual infinite prime channel is a finite sum, with no convergence premise. -/
theorem prime_connesAngularEven_eq_sum {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
      (dil (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) n
        + dil (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) n))
      = ∑ n ∈ Finset.range (x + 1), (ArithmeticFunction.vonMangoldt n : ℝ) *
        (dil (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) n
          + dil (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) n) := by
  apply tsum_eq_sum
  intro n hn
  apply prime_connesAngularEven_zero_of_large hx
  simp only [Finset.mem_range, not_lt] at hn
  omega

/-- Finite support proves actual prime-channel summability. -/
theorem summable_prime_connesAngularEven {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) *
      (dil (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) n
        + dil (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) n)) := by
  apply summable_of_ne_finset_zero (s := Finset.range (x + 1))
  intro n hn
  apply prime_connesAngularEven_zero_of_large hx
  simp only [Finset.mem_range, not_lt] at hn
  omega

/-- The actual even closed quadratic form equals its full angular Weil pairing. -/
theorem Q_even_connesClass_eq_weilθ {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    Cvs.WeilForm.InfimumAttainedSphere.Q (log_natCast_nonneg x) x (Nat.clog 2 x)
      (Cvs.WeilForm.EvenOddSplitForm.evenPart (log_natCast_nonneg x) (Cvs.Approximant.CosineColumnTailPairing.connesClass hx))
        = weilθ (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) := by
  have hx0 := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have hx2 : 2 ≤ x := by exact_mod_cast Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx
  obtain ⟨_, _, hR⟩ := Cvs.Approximant.SpineSubspace.sizes x hx2
  obtain ⟨hf1, hf2, hfl⟩ := connesAngularEven_log_domain hx
  rw [← Cvs.WeilForm.SymmetricBilinearForm.QWbil_self, Cvs.WeilForm.BilinearCrossRepresentatives.QWbil_apply,
    Cvs.WeilForm.BilinearCrossRepresentatives.crossW_congr x (Nat.clog 2 x)
      (rep_even_connesClass_ae_logScale hx) (rep_even_connesClass_ae_logScale hx),
    Cvs.WeilForm.BilinearCrossRepresentatives.crossW_translate]
  symm
  apply weilθ_eq_crossW_of_log_domain (one_div_pos.mpr hx0)
    (connesAngularEven_support x) (connesAngularEven_support x)
    hf1 hf2 hfl hf1 hf2 hfl
  · rw [one_div_one_div]
  · simpa only [one_div_one_div] using hR

/-- The full closed-domain even Connes energy retains arch and both poles, with its exact arithmetic double commutator. -/
theorem Q_even_connesClass_eq_double {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    Cvs.WeilForm.InfimumAttainedSphere.Q (log_natCast_nonneg x) x (Nat.clog 2 x)
      (Cvs.WeilForm.EvenOddSplitForm.evenPart (log_natCast_nonneg x) (Cvs.Approximant.CosineColumnTailPairing.connesClass hx))
        = 2 * poleP (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) * poleM (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x)
          + (∫ t, Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t * Cvs.L2a.FullTailPolarisation.crossSpec
              (logScale (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x)) (logScale (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x)) t)
          - ⟪Cvs.WeilForm.CompressedPhysicalPrimeForm.doubleLogCommutator (one_div_pos.mpr (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx))
              (Cvs.WeilForm.EvenFormMobiusPreimage.connesPreimage (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx)),
              Cvs.WeilForm.EvenFormMobiusPreimage.connesPreimage (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx)⟫_ℝ := by
  rw [Q_even_connesClass_eq_weilθ]
  exact Cvs.WeilForm.EvenFormMobiusPreimage.weilθ_connesAngularEven_self_eq_double (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx)

end Cvs.Approximant.EvenConnesEnergyFormDomain
