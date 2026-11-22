import Mathlib
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.EvenConnesEnergyFormDomain
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.L2a.FullTailPolarisation
import Cvs.L2a.PlaneCorrelationL2
import Cvs.L2a.TailLogScaleTest
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyChannelSumSquares
import Cvs.WeilForm.CompressedPhysicalPrimeForm
import Cvs.WeilForm.EvenFormMobiusPreimage
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.PhysicalCubicCorrectionColumn
import Cvs.WeilForm.SeparatedArchDilationPairing
import Cvs.WeilForm.ThetaFormWindowIdentification
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.Xi.EImageWindowPoisson
import Cvs.Xi.PhysicalReciprocalReflection
import Cvs.Xi.ReciprocalWindowPhysicalL2
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The even Connes energy in output coordinates

Reciprocal symmetry makes the pole channel a positive rank-one square.
The complete finite prime channel is its scalar norm budget minus a
positive sum of actual dilation differences.  All channels of the actual
Connes specialization are genuine integrals on its closed form domain.
-/

noncomputable section

open Real Set MeasureTheory Filter
open scoped InnerProductSpace

namespace Cvs.Approximant.EvenConnesEnergyOutput
open Cvs.ZeroCounting

open Cvs.WeilForm.ThetaSpaceParseval (poleP poleM dil weilθ)
open Cvs.L2a.TailLogScaleTest (logScale)

/-- The complete finite Mangoldt norm weight, including its vanishing zero and one terms. -/
def primeWeight (x : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (x + 1), (ArithmeticFunction.vonMangoldt n : ℝ) / √(n : ℝ)

/-- The actual finite dilation Dirichlet defect in logarithmic coordinates. -/
def dilationDefect (x : ℕ) (F : ℝ → ℝ) : ℝ :=
  ∑ n ∈ Finset.range (x + 1), (ArithmeticFunction.vonMangoldt n : ℝ) / √(n : ℝ) *
    ∫ s, (logScale F s - logScale F (s + log (n : ℝ))) ^ 2

/-- Reciprocal-even physical outputs have only one pole functional. -/
theorem poleP_eq_sqrt_mul_poleM {a : ℝ} (ha : 0 < a) {F : ℝ → ℝ}
    (hF : ∀ θ ∉ Icc a 1, F θ = 0) (hJ : Cvs.Xi.PhysicalReciprocalReflection.reciprocal a F = F) :
    poleP F = √a * poleM F := by
  let χ : ℝ → ℝ := (Icc a 1).indicator (fun _ => 1)
  have h := Cvs.Xi.PhysicalReciprocalReflection.integral_reciprocal_mul ha F χ
  have hl : (fun θ => Cvs.Xi.PhysicalReciprocalReflection.reciprocal a F θ * χ θ) = F := by
    funext θ
    rw [hJ]
    by_cases hθ : θ ∈ Icc a 1
    · simp only [χ, indicator_of_mem hθ, mul_one]
    · simp only [χ, indicator_of_notMem hθ, hF θ hθ, zero_mul]
  have hr : (fun θ => F θ * Cvs.Xi.PhysicalReciprocalReflection.reciprocal a χ θ) =
      fun θ => √a * (F θ / θ) := by
    funext θ
    by_cases hθ : θ ∈ Icc a 1
    · rw [Cvs.Xi.PhysicalReciprocalReflection.reciprocal_apply ha hθ]
      simp only [χ, indicator_of_mem (Cvs.Xi.PhysicalReciprocalReflection.recip_mem_Icc ha hθ), mul_one]
      ring
    · simp only [Cvs.Xi.PhysicalReciprocalReflection.reciprocal_of_notMem hθ, hF θ hθ, zero_div, mul_zero]
  rw [hl, hr, integral_const_mul] at h
  have hpos : ∫ θ in Ioi (0 : ℝ), F θ = ∫ θ, F θ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro θ hθ
    simp only [mem_Ioi, not_lt] at hθ
    exact hF θ (fun hm => ha.not_ge (hm.1.trans hθ))
  have hdiv : ∫ θ in Ioi (0 : ℝ), F θ / θ = ∫ θ, F θ / θ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro θ hθ
    simp only [mem_Ioi, not_lt] at hθ
    rw [hF θ (fun hm => ha.not_ge (hm.1.trans hθ)), zero_div]
  rw [Cvs.WeilForm.ThetaFormWindowIdentification.poleP_eq_integral hF, hpos, poleM, hdiv]
  exact h

/-- The reciprocal-even pole channel is a positive square. -/
theorem pole_channel_eq_square {a : ℝ} (ha : 0 < a) {F : ℝ → ℝ}
    (hF : ∀ θ ∉ Icc a 1, F θ = 0) (hJ : Cvs.Xi.PhysicalReciprocalReflection.reciprocal a F = F) :
    2 * poleP F * poleM F = (2 / √a) * poleP F ^ 2 := by
  have h := poleP_eq_sqrt_mul_poleM ha hF hJ
  have hs : √a ≠ 0 := (sqrt_pos.mpr ha).ne'
  rw [h]
  field_simp

/-- Every logarithmic dilation difference is genuinely square integrable. -/
theorem integrable_dilation_difference {F : ℝ → ℝ}
    (hF : MemLp (logScale F) 2 volume) (n : ℕ) :
    Integrable (fun s => (logScale F s - logScale F (s + log (n : ℝ))) ^ 2) := by
  exact (hF.sub (hF.comp_measurePreserving
    (measurePreserving_add_right volume (log (n : ℝ))))).integrable_sq

/-- The finite Mangoldt norm budget is nonnegative. -/
theorem primeWeight_nonneg (x : ℕ) : 0 ≤ primeWeight x := by
  unfold primeWeight
  exact Finset.sum_nonneg fun n _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (sqrt_nonneg _)

/-- The finite actual dilation defect is nonnegative. -/
theorem dilationDefect_nonneg (x : ℕ) (F : ℝ → ℝ) : 0 ≤ dilationDefect x F := by
  unfold dilationDefect
  exact Finset.sum_nonneg fun n _ => mul_nonneg
    (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (sqrt_nonneg _))
    (integral_nonneg fun _ => sq_nonneg _)

/-- Every finite angular prime self-pairing is its norm weight minus the actual dilation defect. -/
theorem finite_prime_eq_budget_sub {F : ℝ → ℝ}
    (hF : MemLp (logScale F) 2 volume) (x : ℕ) :
    (∑ n ∈ Finset.range (x + 1), (ArithmeticFunction.vonMangoldt n : ℝ) *
      (dil F F n + dil F F n))
      = 2 * primeWeight x * Cvs.Zeta.Explicit.Weil.selfConvolution (logScale F) 0
        - dilationDefect x F := by
  calc
    _ = ∑ n ∈ Finset.range (x + 1),
        (2 * ((ArithmeticFunction.vonMangoldt n : ℝ) / √(n : ℝ)) *
          Cvs.Zeta.Explicit.Weil.selfConvolution (logScale F) 0
        - ((ArithmeticFunction.vonMangoldt n : ℝ) / √(n : ℝ)) *
          ∫ s, (logScale F s - logScale F (s + log (n : ℝ))) ^ 2) := by
      apply Finset.sum_congr rfl
      intro n _
      by_cases hn : n = 0
      · subst n
        simp
      have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      have hs : √(n : ℝ) ≠ 0 := (sqrt_pos.mpr hn0).ne'
      have hd := Cvs.WeilForm.Archimedean.LevyChannelSumSquares.selfConvolution_zero_sub hF (log (n : ℝ))
      have hc := Cvs.WeilForm.ThetaFormWindowIdentification.selfConvolution_logScale_log F hn0
      have hdi : dil F F n =
          Cvs.Zeta.Explicit.Weil.selfConvolution (logScale F) (log (n : ℝ)) / √(n : ℝ) := by
        apply (eq_div_iff hs).mpr
        simpa only [dil, mul_comm] using hc.symm
      have hz : Cvs.Zeta.Explicit.Weil.selfConvolution (logScale F) 0 =
          Cvs.Zeta.Explicit.Weil.selfConvolution (logScale F) (log (n : ℝ))
            + (1 / 2) * ∫ s, (logScale F s - logScale F (s + log (n : ℝ))) ^ 2 := by
        linarith
      rw [hdi, hz]
      ring
    _ = _ := by
      unfold primeWeight dilationDefect
      rw [Finset.sum_sub_distrib]
      congr 1
      rw [← Finset.sum_mul, ← Finset.mul_sum]

/-- Positive-support logarithmic energy equals the genuine physical L² norm. -/
theorem selfConvolution_logScale_zero_eq_norm {F : ℝ → ℝ}
    (hF : MemLp F 2 volume) (hs : ∀ θ ≤ 0, F θ = 0) :
    Cvs.Zeta.Explicit.Weil.selfConvolution (logScale F) 0 = ‖hF.toLp F‖ ^ 2 := by
  rw [Cvs.Zeta.Explicit.Weil.selfConvolution]
  simp only [add_zero, ← sq]
  rw [Cvs.WeilForm.PhysicalCubicCorrectionColumn.integral_logScale_sq hs, Cvs.L2a.PlaneCorrelationL2.norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [hF.coeFn_toLp] with θ hθ
  rw [hθ]

/-- The actual Connes output has a positive rank-one pole channel. -/
theorem connes_pole_channel_eq_square {x : ℝ} (hx : 0 < x) :
    2 * poleP (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) * poleM (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x)
      = (2 / √(1 / x)) * poleP (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) ^ 2 := by
  apply pole_channel_eq_square (one_div_pos.mpr hx) (Cvs.Approximant.EvenConnesEnergyFormDomain.connesAngularEven_support x)
  exact Cvs.Xi.PhysicalReciprocalReflection.reciprocal_evenPhysical (one_div_pos.mpr hx) _

/-- Each summand of the actual Connes dilation defect is a genuine finite integral. -/
theorem integrable_connes_dilation_difference {x : ℕ} (hx : 80 ≤ 2 * π * x) (n : ℕ) :
    Integrable (fun s => (logScale (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) s -
      logScale (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) (s + log (n : ℝ))) ^ 2) :=
  integrable_dilation_difference (Cvs.Approximant.EvenConnesEnergyFormDomain.connesAngularEven_log_domain hx).2.1 n

/-- The complete actual Connes prime energy has no inverse norm in its budget-minus-defect identity. -/
theorem prime_connesAngularEven_eq_budget_sub {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
      (dil (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) n
        + dil (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) n))
      = 2 * primeWeight x *
        ‖(Cvs.Xi.PhysicalReciprocalReflection.memLp_connesAngularEven (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx)).toLp
          (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x)‖ ^ 2
        - dilationDefect x (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) := by
  rw [Cvs.Approximant.EvenConnesEnergyFormDomain.prime_connesAngularEven_eq_sum hx,
    finite_prime_eq_budget_sub (Cvs.Approximant.EvenConnesEnergyFormDomain.connesAngularEven_log_domain hx).2.1]
  rw [selfConvolution_logScale_zero_eq_norm
    (Cvs.Xi.PhysicalReciprocalReflection.memLp_connesAngularEven (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx))]
  intro θ hθ
  exact Cvs.Approximant.EvenConnesEnergyFormDomain.connesAngularEven_support x θ
    (fun hm => (one_div_pos.mpr (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx)).not_ge (hm.1.trans hθ))

/-- The full actual closed Connes energy consists of arch, a pole square and positive dilation defect,
less its finite scalar norm weight, all measured directly at the output. -/
theorem Q_even_connesClass_eq_output_defect {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    Cvs.WeilForm.InfimumAttainedSphere.Q (log_natCast_nonneg x) x (Nat.clog 2 x)
      (Cvs.WeilForm.EvenOddSplitForm.evenPart (log_natCast_nonneg x) (Cvs.Approximant.CosineColumnTailPairing.connesClass hx))
      = (∫ t, Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t * Cvs.L2a.FullTailPolarisation.crossSpec
          (logScale (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x)) (logScale (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x)) t)
        + (2 / √(1 / (x : ℝ))) * poleP (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) ^ 2
        + dilationDefect x (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x)
        - 2 * primeWeight x *
          ‖(Cvs.Xi.PhysicalReciprocalReflection.memLp_connesAngularEven (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx)).toLp
            (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x)‖ ^ 2 := by
  rw [Cvs.Approximant.EvenConnesEnergyFormDomain.Q_even_connesClass_eq_weilθ]
  unfold weilθ
  rw [prime_connesAngularEven_eq_budget_sub hx]
  have hp := connes_pole_channel_eq_square (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx)
  nlinarith

/-- The actual arithmetic double commutator at the Möbius preimage is exactly
the output prime budget minus its positive dilation defect. -/
theorem double_connesPreimage_eq_output_defect {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    ⟪Cvs.WeilForm.CompressedPhysicalPrimeForm.doubleLogCommutator (one_div_pos.mpr (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx))
        (Cvs.WeilForm.EvenFormMobiusPreimage.connesPreimage (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx)),
      Cvs.WeilForm.EvenFormMobiusPreimage.connesPreimage (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx)⟫_ℝ
      = 2 * primeWeight x *
        ‖(Cvs.Xi.PhysicalReciprocalReflection.memLp_connesAngularEven (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx)).toLp
          (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x)‖ ^ 2
        - dilationDefect x (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) := by
  have hd := Cvs.Approximant.EvenConnesEnergyFormDomain.Q_even_connesClass_eq_double hx
  have hq := Q_even_connesClass_eq_output_defect hx
  have hp := connes_pole_channel_eq_square (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx)
  linarith

end Cvs.Approximant.EvenConnesEnergyOutput
