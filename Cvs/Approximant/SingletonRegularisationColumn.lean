import Mathlib
import Cvs.Approximant.ConnesErrorColumn
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.EvenConnesEnergyOutput
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineNearQuarticHermite
import Cvs.Approximant.SpineRegularisationDefect
import Cvs.Finite.SymmetricModeSet
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BetaProfilePoissonTail
import Cvs.L2a.FullTailArchChannel
import Cvs.L2a.FullTailBilinearChannels
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailPolarisation
import Cvs.L2a.FullTailPoleChannel
import Cvs.L2a.FullTailWeilFormLimit
import Cvs.L2a.PlaneCorrelationL2
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.RungWindowCouplingTail
import Cvs.L2a.SpanPlungeBound
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowChainInputsProlate
import Cvs.L2a.WindowFormTailLimit
import Cvs.Prolate.AngularBesselInequality
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.EvenRungDavisKahan
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.ForbiddenZoneClosedForm
import Cvs.Prolate.ForbiddenZoneGrowth
import Cvs.Prolate.HermiteTrialResiduals
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.RungFamilyRangePartners
import Cvs.Prolate.SlepianEvenOrdering
import Cvs.Route.JointGapFromResidual
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyTonelli
import Cvs.WeilForm.CubicTailSeparatedKernel
import Cvs.WeilForm.PhysicalCubicCorrectionColumn
import Cvs.WeilForm.PoleTermDilationMean
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SeparatedArchDilationPairing
import Cvs.WeilForm.ThetaSpaceParseval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
 developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The singleton regularization column has a quadratic defect budget

The stable beta tail has a complete arithmetic column bound at every cosine
order. The actual regularization coefficient retains the squared rung ratio.
-/

noncomputable section
set_option maxHeartbeats 1600000
open Real Set MeasureTheory Filter Matrix

namespace Cvs.Approximant.SingletonRegularisationColumn
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet (Idx mode negI)
open Cvs.WeilForm.ThetaSpaceParseval (dil poleP poleM weilθ)
open Cvs.L2a.TailLogScaleTest (logScale)

/-- The fixed tail used by the spine regularization. -/
def betaTail : ℝ → ℝ := Cvs.L2a.FullTailConvergence.fullTail Cvs.L2a.BetaProfilePoissonTail.Psi

/-- The elementary Mangoldt partial-sum constant. -/
def mangoldtConstant : ℝ := log 4+4

/-- The reciprocal fourth-power beta-tail majorant. -/
def betaConstant : ℝ := Cvs.L2a.BetaProfilePoissonTail.KPsi/1440

/-- The complete prime density budget of the stable beta tail. -/
def betaPrimeConstant : ℝ := (4/3)*mangoldtConstant*betaConstant

private def layer (r u : ℝ) : ℝ := if r≤u then 1/u^5 else 0

private theorem integrable_layer (r : ℝ) :
    IntegrableOn (layer r) (Ioi (1 : ℝ)) volume := by
  apply (Cvs.L2a.BetaProfilePoissonTail.integrableOn_Ioi_inv_pow (n := 5) one_pos (by norm_num)).mono'
  · exact ((measurable_const.div (measurable_id.pow_const (5 : ℕ))).ite
      (measurableSet_le measurable_const measurable_id) measurable_const).aestronglyMeasurable
  · apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro u hu
    change 1<u at hu
    unfold layer
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    · simp only [norm_zero]
      positivity

private theorem integral_layer (r : ℝ) :
    (∫ u in Ioi (1 : ℝ), layer r u)=1/(4*(max 1 r)^4) := by
  by_cases hr : r≤1
  · have he : (∫ u in Ioi (1 : ℝ), layer r u)=∫ u in Ioi (1 : ℝ), 1/u^5 := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      exact ite_eq_left (hr.trans (le_of_lt hu))
    rw [he, Cvs.L2a.BetaProfilePoissonTail.integral_Ioi_inv_pow one_pos (by norm_num : 2≤5), max_eq_left hr]
    norm_num
  · have hr1 : 1<r := lt_of_not_ge hr
    have he : (∫ u in Ioi (1 : ℝ), layer r u)=∫ u in Ioi r, layer r u := by
      apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet
        (Ioi_subset_Ioi hr1.le)
      filter_upwards [volume.ae_ne r] with u hur hu
      unfold layer
      apply ite_eq_right
      intro hru
      simp only [Set.mem_sdiff, mem_Ioi, not_lt] at hu
      exact hur (le_antisymm hu.2 hru)
    rw [he]
    have he' : (∫ u in Ioi r, layer r u)=∫ u in Ioi r, 1/u^5 := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      exact ite_eq_left (le_of_lt hu)
    rw [he', Cvs.L2a.BetaProfilePoissonTail.integral_Ioi_inv_pow (zero_lt_one.trans hr1) (by norm_num : 2≤5),
      max_eq_right hr1.le]
    norm_num

/-- Every finite Mangoldt reciprocal-power sum has the same reciprocal-step budget. -/
theorem finite_mangoldt_soft_le {θ : ℝ} (hθ : 0<θ) (S : Finset ℕ) :
    (∑ n ∈ S, (ArithmeticFunction.vonMangoldt n : ℝ)/(max 1 ((n : ℝ)*θ))^4)
      ≤ (4/3)*mangoldtConstant/θ := by
  have he : (∑ n ∈ S, (ArithmeticFunction.vonMangoldt n : ℝ)/(max 1 ((n : ℝ)*θ))^4)=
      4*∫ u in Ioi (1 : ℝ), ∑ n ∈ S, (ArithmeticFunction.vonMangoldt n : ℝ)*layer ((n : ℝ)*θ) u := by
    rw [integral_finsetSum S (fun n _ => (integrable_layer ((n : ℝ)*θ)).const_mul _)]
    simp_rw [integral_const_mul, integral_layer]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  have hi : IntegrableOn (fun u : ℝ => mangoldtConstant/θ*(1/u^4)) (Ioi (1 : ℝ)) volume :=
    (Cvs.L2a.BetaProfilePoissonTail.integrableOn_Ioi_inv_pow (n := 4) one_pos (by norm_num)).const_mul _
  have hleft : IntegrableOn
      (fun u => ∑ n ∈ S, (ArithmeticFunction.vonMangoldt n : ℝ)*layer ((n : ℝ)*θ) u)
      (Ioi (1 : ℝ)) volume :=
    integrable_finsetSum S fun n _ => (integrable_layer ((n : ℝ)*θ)).const_mul _
  have hb : ∀ u∈Ioi (1 : ℝ),
      (∑ n ∈ S, (ArithmeticFunction.vonMangoldt n : ℝ)*layer ((n : ℝ)*θ) u)
        ≤ mangoldtConstant/θ*(1/u^4) := by
    intro u hu
    have hu0 : 0<u := zero_lt_one.trans hu
    have hmass : (∑ n ∈ S.filter (fun n : ℕ => (n : ℝ)*θ≤u), (ArithmeticFunction.vonMangoldt n : ℝ))
        ≤ mangoldtConstant*(u/θ) := by
      calc
        _ ≤ ∑ n ∈ Finset.Icc 0 ⌊u/θ⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn
            simp only [Finset.mem_filter] at hn
            exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_floor ((le_div_iff₀ hθ).mpr hn.2)⟩
          · intro n _ _; exact ArithmeticFunction.vonMangoldt_nonneg
        _ = Chebyshev.psi (u/θ) := (Chebyshev.psi_eq_sum_Icc _).symm
        _ ≤ _ := Chebyshev.psi_le_const_mul_self (div_nonneg hu0.le hθ.le)
    have he' : (∑ n ∈ S, (ArithmeticFunction.vonMangoldt n : ℝ)*layer ((n : ℝ)*θ) u)=
        (∑ n ∈ S.filter (fun n : ℕ => (n : ℝ)*θ≤u), (ArithmeticFunction.vonMangoldt n : ℝ))*(1/u^5) := by
      rw [Finset.sum_mul, Finset.sum_filter]
      unfold layer
      exact Finset.sum_congr rfl fun n _ => by split_ifs <;> simp
    rw [he']
    calc
      _ ≤ (mangoldtConstant*(u/θ))*(1/u^5) :=
        mul_le_mul_of_nonneg_right hmass (by positivity)
      _ = _ := by field_simp
  rw [he]
  have hb' := integral_mono_ae hleft hi (ae_restrict_of_forall_mem measurableSet_Ioi hb)
  calc
    _ ≤ 4*∫ u in Ioi (1 : ℝ), mangoldtConstant/θ*(1/u^4) :=
      mul_le_mul_of_nonneg_left hb' (by norm_num)
    _ = _ := by
      rw [integral_const_mul, Cvs.L2a.BetaProfilePoissonTail.integral_Ioi_inv_pow one_pos (by norm_num : 2≤4)]
      norm_num
      ring

/-- The stable beta tail is bounded by a reciprocal fourth power, with its support retained. -/
theorem abs_betaTail_le_soft (r : ℝ) : |betaTail r|≤betaConstant/(max 1 r)^4 := by
  have hC : 0≤betaConstant := div_nonneg Cvs.L2a.BetaProfilePoissonTail.KPsi_nonneg (by norm_num)
  by_cases hr : 1<r
  · unfold betaTail betaConstant
    have h := Cvs.L2a.BetaProfilePoissonTail.abs_fullTail_Psi_le hr
    rw [max_eq_right hr.le]
    exact h.trans_eq (by ring)
  · rw [betaTail, Cvs.L2a.FullTailWeilFormLimit.fullTail_of_le_one _ (le_of_not_gt hr), abs_zero]
    exact div_nonneg hC (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)

/-- Actual beta-tail Mangoldt samples are absolutely summable at every positive physical point. -/
theorem summable_beta_prime {θ : ℝ} (hθ : 0<θ) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ)*betaTail ((n : ℝ)*θ)) := by
  have hnorm : Summable (fun n : ℕ => |(ArithmeticFunction.vonMangoldt n : ℝ)*betaTail ((n : ℝ)*θ)|) := by
    apply summable_of_sum_le (fun _ => abs_nonneg _)
    intro S
    calc
      _ ≤ betaConstant*∑ n∈S, (ArithmeticFunction.vonMangoldt n : ℝ)/(max 1 ((n : ℝ)*θ))^4 := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro n _
        rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        have h := mul_le_mul_of_nonneg_left (abs_betaTail_le_soft ((n : ℝ)*θ))
          (ArithmeticFunction.vonMangoldt_nonneg (n := n))
        exact h.trans_eq (by ring)
      _ ≤ betaConstant*((4/3)*mangoldtConstant/θ) :=
        mul_le_mul_of_nonneg_left (finite_mangoldt_soft_le hθ S)
          (div_nonneg Cvs.L2a.BetaProfilePoissonTail.KPsi_nonneg (by norm_num))
  exact hnorm.of_norm

/-- The complete actual prime density of the stable beta tail has the reciprocal-point budget. -/
theorem beta_prime_sum_abs_le {θ : ℝ} (hθ : 0<θ) :
    (∑' n : ℕ, |(ArithmeticFunction.vonMangoldt n : ℝ)*betaTail ((n : ℝ)*θ)|)
      ≤ betaPrimeConstant/θ := by
  apply tsum_le_of_sum_le (fun _ => abs_nonneg _)
  intro S
  calc
    _ ≤ betaConstant*∑ n∈S, (ArithmeticFunction.vonMangoldt n : ℝ)/(max 1 ((n : ℝ)*θ))^4 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n _
      rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      have h := mul_le_mul_of_nonneg_left (abs_betaTail_le_soft ((n : ℝ)*θ))
        (ArithmeticFunction.vonMangoldt_nonneg (n := n))
      exact h.trans_eq (by ring)
    _ ≤ betaConstant*((4/3)*mangoldtConstant/θ) :=
      mul_le_mul_of_nonneg_left (finite_mangoldt_soft_le hθ S)
        (div_nonneg Cvs.L2a.BetaProfilePoissonTail.KPsi_nonneg (by norm_num))
    _ = _ := by unfold betaPrimeConstant; ring

private theorem betaPrimeConstant_nonneg : 0≤betaPrimeConstant := by
  unfold betaPrimeConstant mangoldtConstant betaConstant
  have hk := Cvs.L2a.BetaProfilePoissonTail.KPsi_nonneg
  positivity

/-- The beta tail belongs to physical L² on the whole line. -/
theorem memLp_betaTail : MemLp betaTail 2 volume :=
  Cvs.WeilForm.PhysicalCubicCorrectionColumn.memLp_fullTail Cvs.L2a.BetaProfilePoissonTail.hasDerivAt_beta_on Cvs.L2a.BetaProfilePoissonTail.hasDerivAt_beta1_on
    Cvs.L2a.BetaProfilePoissonTail.continuousOn_beta2 (by positivity)

private theorem norm_toLp_sq {F : ℝ → ℝ} (hF : MemLp F 2 volume) :
    ‖hF.toLp F‖^2=∫ θ, F θ^2 := by
  rw [Cvs.L2a.PlaneCorrelationL2.norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [hF.coeFn_toLp] with θ hθ
  rw [hθ]

/-- The actual beta-tail physical norm has the project's fixed rational budget. -/
theorem norm_betaTail_le : ‖memLp_betaTail.toLp betaTail‖≤√(133/1000 : ℝ) := by
  have he : (∫ θ, betaTail θ^2)=∫ θ in Ioi (1 : ℝ), betaTail θ^2 := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro θ hθ
    rw [betaTail, Cvs.L2a.FullTailWeilFormLimit.fullTail_of_le_one _ (by simpa only [mem_Ioi, not_lt] using hθ)]
    ring
  have h : (∫ θ in Ioi (1 : ℝ), betaTail θ^2)≤133/1000 := Cvs.L2a.BetaProfilePoissonTail.integral_fullTail_Psi_sq_le_rat
  rw [← he, ← norm_toLp_sq memLp_betaTail] at h
  exact (Real.le_sqrt (norm_nonneg _) (by norm_num)).mpr h

/-- The actual beta-tail pole is the explicit convergent physical integral. -/
theorem poleP_betaTail : poleP betaTail=49/48-log (2*π)/2 := by
  have hi : IntegrableOn betaTail (Ioi (1 : ℝ)) volume :=
    (Cvs.L2a.BetaProfilePoissonTail.integrableOn_of_le_inv_pow (F := betaTail) (K := Cvs.L2a.BetaProfilePoissonTail.KPsi/1440) (n := 4)
      Cvs.L2a.BetaProfilePoissonTail.measurable_fullTail_Psi.aestronglyMeasurable (by norm_num)
      (fun θ hθ => by rw [div_div]; exact Cvs.L2a.BetaProfilePoissonTail.abs_fullTail_Psi_le hθ)).1
  have hi0 : IntegrableOn betaTail (Ioi (0 : ℝ)) volume :=
    (hi.integrable_of_forall_notMem_eq_zero (fun θ hθ =>
      Cvs.L2a.FullTailWeilFormLimit.fullTail_of_le_one _ (by simpa only [mem_Ioi, not_lt] using hθ))).restrict
  apply Cvs.WeilForm.ThetaSpaceParseval.poleP_eq_of_tendsto
  have h := intervalIntegral_tendsto_integral_Ioi 0 hi0 (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop)
  have he : (∫ θ in Ioi (0 : ℝ), betaTail θ)=∫ θ in Ioi (1 : ℝ), betaTail θ := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (Ioi_subset_Ioi zero_le_one)
    intro θ hθ
    exact Cvs.L2a.FullTailWeilFormLimit.fullTail_of_le_one _ (by simpa only [Set.mem_sdiff, mem_Ioi, not_lt] using hθ.2)
  rw [he] at h
  change Tendsto (fun Y => ∫ θ in 0..Y, betaTail θ) atTop
    (nhds (∫ θ in Ioi (1 : ℝ), Cvs.L2a.FullTailConvergence.fullTail Cvs.L2a.BetaProfilePoissonTail.Psi θ)) at h
  rw [Cvs.L2a.BetaProfilePoissonTail.integral_fullTail_Psi] at h
  exact h

/-- Reciprocal physical L¹ of a window test has its exact L² interval budget. -/
theorem integral_abs_div_le {a : ℝ} (ha : 0<a) (ha1 : a≤1) {v : ℝ → ℝ}
    (hv : Cvs.L2a.WindowFormTailLimit.Tame v a 1) :
    (∫ θ in Ioi (0 : ℝ), |v θ/θ|)≤
      ‖(Cvs.WeilForm.PhysicalCubicCorrectionColumn.memLp_of_tame hv).toLp v‖*√(1/a-1) := by
  have hV := Cvs.WeilForm.PhysicalCubicCorrectionColumn.memLp_of_tame hv
  have he : (∫ θ in Ioi (0 : ℝ), |v θ/θ|)=∫ θ in Icc a 1, |v θ| *(1/θ) := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (show Icc a 1⊆Ioi (0 : ℝ) from fun θ hθ => ha.trans_le hθ.1) ?_]
    · apply setIntegral_congr_fun measurableSet_Icc
      intro θ hθ
      change |v θ/θ|=|v θ| *(1/θ)
      rw [abs_div, abs_of_pos (ha.trans_le hθ.1)]
      ring
    · intro θ hθ
      rw [hv.supp θ hθ.2, zero_div, abs_zero]
  have hi1 : IntegrableOn (fun θ => |v θ|^2) (Icc a 1) volume := hV.norm.integrable_sq.restrict
  have hi2 : IntegrableOn (fun θ : ℝ => (1/θ)^2) (Icc a 1) volume := by
    exact (((continuousOn_const.div₀ continuousOn_id
      (fun θ (hθ : θ ∈ Icc a 1) => (ha.trans_le hθ.1).ne')).pow 2).integrableOn_Icc)
  have hip : IntegrableOn (fun θ => |v θ| *(1/θ)) (Icc a 1) volume := by
    apply hv.div.abs.restrict.congr
    apply ae_restrict_of_forall_mem measurableSet_Icc
    intro θ hθ
    change |v θ/θ|=|v θ| *(1/θ)
    rw [abs_div, abs_of_pos (ha.trans_le hθ.1)]
    ring
  have hm1 : MemLp (fun θ => |v θ|) 2 (volume.restrict (Icc a 1)) := by
    simpa only [Real.norm_eq_abs] using hV.norm.restrict (Icc a 1)
  have hm2 : MemLp (fun θ : ℝ => 1/θ) 2 (volume.restrict (Icc a 1)) :=
    (memLp_two_iff_integrable_sq (measurable_const.div measurable_id).aestronglyMeasurable).mpr hi2
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict (Icc a 1)) Real.HolderConjugate.two_two
    (Eventually.of_forall (fun θ => abs_nonneg (v θ)))
    (ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
      one_div_nonneg.mpr (ha.trans_le hθ.1).le))
    (by simpa only [ENNReal.ofReal_ofNat] using hm1)
    (by simpa only [ENNReal.ofReal_ofNat] using hm2)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hcs
  have hnonneg : 0≤∫ θ in Icc a 1, |v θ| *(1/θ) :=
    setIntegral_nonneg measurableSet_Icc fun θ hθ => mul_nonneg (abs_nonneg _)
      (one_div_nonneg.mpr (ha.trans_le hθ.1).le)
  have hsquare : (∫ θ in Icc a 1, |v θ|^2)=‖hV.toLp v‖^2 := by
    simp_rw [sq_abs]
    rw [norm_toLp_sq hV]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro θ hθ
    rw [hv.supp θ hθ]
    ring
  have hinv : (∫ θ in Icc a 1, (1/θ)^2)=1/a-1 := by
    simp_rw [_root_.one_div_pow]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha1,
      Cvs.L2a.BetaProfilePoissonTail.integral_inv_sq_interval ha ha1]
    norm_num
  rw [hsquare, hinv, sqrt_sq (norm_nonneg _)] at hcs
  rw [he]
  exact hcs

private theorem integrable_prime_beta {a : ℝ} {v : ℝ → ℝ}
    (hv : Cvs.L2a.WindowFormTailLimit.Tame v a 1) (n : ℕ) :
    IntegrableOn (fun θ => (ArithmeticFunction.vonMangoldt n : ℝ)*v θ*betaTail ((n : ℝ)*θ))
      (Ioi (0 : ℝ)) volume := by
  refine ((hv.div.abs.const_mul betaPrimeConstant).restrict (s := Ioi (0 : ℝ))).mono'
    (((measurable_const.mul hv.meas).mul
      (Cvs.L2a.BetaProfilePoissonTail.measurable_fullTail_Psi.comp (measurable_const.mul measurable_id))).aestronglyMeasurable) ?_
  apply ae_restrict_of_forall_mem measurableSet_Ioi
  intro θ hθ
  change 0<θ at hθ
  have hpoint : |(ArithmeticFunction.vonMangoldt n : ℝ)*betaTail ((n : ℝ)*θ)|≤betaPrimeConstant/θ :=
    ((summable_beta_prime hθ).abs.le_tsum n (fun _ _ => abs_nonneg _)).trans
      (beta_prime_sum_abs_le hθ)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have he : (ArithmeticFunction.vonMangoldt n : ℝ)*|v θ| *|betaTail ((n : ℝ)*θ)|=
      |v θ| *|(ArithmeticFunction.vonMangoldt n : ℝ)*betaTail ((n : ℝ)*θ)| := by
    rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    ring
  rw [he]
  have h := mul_le_mul_of_nonneg_left hpoint (abs_nonneg (v θ))
  simpa only [abs_div, abs_of_pos hθ] using h.trans_eq (by ring)

/-- The complete stable-beta prime pairing is absolutely convergent and has its physical budget. -/
theorem prime_beta_budget {a : ℝ} (ha : 0<a) (ha1 : a≤1) {v : ℝ → ℝ}
    (hv : Cvs.L2a.WindowFormTailLimit.Tame v a 1) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ)*dil v betaTail n) ∧
      |∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ)*dil v betaTail n|
        ≤betaPrimeConstant*‖(Cvs.WeilForm.PhysicalCubicCorrectionColumn.memLp_of_tame hv).toLp v‖*√(1/a-1) := by
  have hfinite (S : Finset ℕ) :
      (∑ n∈S, |(ArithmeticFunction.vonMangoldt n : ℝ)*dil v betaTail n|)
        ≤ betaPrimeConstant*(∫ θ in Ioi (0 : ℝ), |v θ/θ|) := by
    calc
      _ ≤ ∑ n∈S, ∫ θ in Ioi (0 : ℝ),
          |(ArithmeticFunction.vonMangoldt n : ℝ)*v θ*betaTail ((n : ℝ)*θ)| := by
        apply Finset.sum_le_sum
        intro n _
        rw [dil, ← integral_const_mul]
        simpa only [mul_assoc] using (abs_integral_le_integral_abs
          (f := fun θ => (ArithmeticFunction.vonMangoldt n : ℝ)*(v θ*betaTail ((n : ℝ)*θ)))
          (μ := volume.restrict (Ioi (0 : ℝ))))
      _ = ∫ θ in Ioi (0 : ℝ), ∑ n∈S,
          |(ArithmeticFunction.vonMangoldt n : ℝ)*v θ*betaTail ((n : ℝ)*θ)| := by
        rw [integral_finsetSum S (fun n _ => (integrable_prime_beta hv n).abs)]
      _ ≤ ∫ θ in Ioi (0 : ℝ), betaPrimeConstant*|v θ/θ| := by
        apply integral_mono_ae
          (integrable_finsetSum S (fun n _ => (integrable_prime_beta hv n).abs))
          ((hv.div.abs.const_mul betaPrimeConstant).restrict (s := Ioi (0 : ℝ)))
        apply ae_restrict_of_forall_mem measurableSet_Ioi
        intro θ hθ
        change 0<θ at hθ
        have hb : (∑ n∈S, |(ArithmeticFunction.vonMangoldt n : ℝ)*betaTail ((n : ℝ)*θ)|)
            ≤betaPrimeConstant/θ :=
          ((summable_beta_prime hθ).abs.sum_le_tsum S (fun _ _ => abs_nonneg _)).trans
            (beta_prime_sum_abs_le hθ)
        have he : (∑ n∈S, |(ArithmeticFunction.vonMangoldt n : ℝ)*v θ*betaTail ((n : ℝ)*θ)|)=
            |v θ| *(∑ n∈S, |(ArithmeticFunction.vonMangoldt n : ℝ)*betaTail ((n : ℝ)*θ)|) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n _
          simp only [abs_mul]
          ring
        change (∑ n∈S, |(ArithmeticFunction.vonMangoldt n : ℝ)*v θ*betaTail ((n : ℝ)*θ)|)≤betaPrimeConstant*|v θ/θ|
        rw [he]
        have h := mul_le_mul_of_nonneg_left hb (abs_nonneg (v θ))
        simpa only [abs_div, abs_of_pos hθ] using h.trans_eq (by ring)
      _ = _ := integral_const_mul _ _
  have hsabs : Summable (fun n : ℕ => |(ArithmeticFunction.vonMangoldt n : ℝ)*dil v betaTail n|) :=
    summable_of_sum_le (fun _ => abs_nonneg _) hfinite
  have hnorm : Summable (fun n : ℕ => ‖(ArithmeticFunction.vonMangoldt n : ℝ)*dil v betaTail n‖) := by
    simpa only [Real.norm_eq_abs] using hsabs
  refine ⟨hnorm.of_norm, ?_⟩
  calc
    _ ≤ ∑' n : ℕ, |(ArithmeticFunction.vonMangoldt n : ℝ)*dil v betaTail n| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
    _ ≤ betaPrimeConstant*(∫ θ in Ioi (0 : ℝ), |v θ/θ|) :=
      tsum_le_of_sum_le (fun _ => abs_nonneg _) hfinite
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (integral_abs_div_le ha ha1 hv)
        betaPrimeConstant_nonneg

/-- The explicit full beta-column growth budget in the physical window. -/
def betaBudget (x : ℝ) : ℝ :=
  (betaPrimeConstant+|49/48-log (2*π)/2|)*√(x-1)+(π/2)*√(133/1000 : ℝ)

/-- The actual beta-tail Weil functional is bounded on every physical window test. -/
theorem abs_weil_beta_le {x : ℝ} (hx : 1≤x) {v : ℝ → ℝ}
    (hv : Cvs.L2a.WindowFormTailLimit.Tame v (1/x) 1) :
    |-weilθ betaTail v|≤betaBudget x*‖(Cvs.WeilForm.PhysicalCubicCorrectionColumn.memLp_of_tame hv).toLp v‖ := by
  have hx0 : 0<x := zero_lt_one.trans_le hx
  have ha : 0<1/x := one_div_pos.mpr hx0
  have ha1 : 1/x≤1 := (div_le_one hx0).mpr hx
  have hdecomp := Cvs.WeilForm.SeparatedArchDilationPairing.neg_weil_fullTail_eq_cubic Cvs.L2a.BetaProfilePoissonTail.hasDerivAt_beta_on
    Cvs.L2a.BetaProfilePoissonTail.hasDerivAt_beta1_on Cvs.L2a.BetaProfilePoissonTail.continuousOn_beta2 (by positivity : 0<2*π) hv le_rfl
  change -weilθ betaTail v=_ at hdecomp
  rw [hdecomp]
  have hp := (prime_beta_budget ha ha1 hv).2
  rw [one_div_one_div] at hp
  have hm : |poleP betaTail*poleM v|≤
      |49/48-log (2*π)/2| *‖(Cvs.WeilForm.PhysicalCubicCorrectionColumn.memLp_of_tame hv).toLp v‖*√(x-1) := by
    rw [poleP_betaTail, abs_mul]
    have hb : |poleM v|≤(∫ θ in Ioi (0 : ℝ), |v θ/θ|) := abs_integral_le_integral_abs
    have hc := hb.trans (integral_abs_div_le ha ha1 hv)
    rw [one_div_one_div] at hc
    exact (mul_le_mul_of_nonneg_left hc (abs_nonneg _)).trans_eq (by ring)
  have hc := Cvs.WeilForm.CubicTailSeparatedKernel.abs_integral_cubic_le Cvs.L2a.BetaProfilePoissonTail.measurable_fullTail_Psi hv.meas
    memLp_betaTail (Cvs.WeilForm.PhysicalCubicCorrectionColumn.memLp_of_tame hv)
    (fun η hη => Cvs.L2a.FullTailWeilFormLimit.fullTail_of_le_one _ hη)
    (fun θ hθ => hv.supp θ (fun h => hθ.not_ge h.2))
  have hc' : |∫ r in Ioi (1 : ℝ), Cvs.WeilForm.PoleTermDilationMean.dilR v betaTail r/(r*(r^2-1))|≤
      (π/2)*√(133/1000 : ℝ)*‖(Cvs.WeilForm.PhysicalCubicCorrectionColumn.memLp_of_tame hv).toLp v‖ :=
    hc.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left norm_betaTail_le (by positivity)) (norm_nonneg _))
  exact ((abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add hp hm)) hc')).trans_eq
    (by unfold betaBudget; ring)

/-- The stable beta functional on actual signed cosine tests. -/
def betaPairing (x N : ℕ) (f : Idx N → ℝ) : ℝ :=
  -weilθ betaTail (Cvs.Approximant.CosineColumnTailPairing.modeTest x N f)

/-- The complete beta correction column uses the actual signed coordinate tests. -/
def betaColumn (x N : ℕ) (i : Idx N) : ℝ :=
  betaPairing x N (Cvs.Approximant.CosineColumnTailPairing.cosineRow N i)

theorem betaColumn_even (x N : ℕ) (i : Idx N) :
    betaColumn x N (negI N i)=betaColumn x N i := by
  rw [betaColumn, Cvs.Approximant.ConnesErrorColumn.cosineRow_neg]
  rfl

private theorem beta_cubic_rows {x : ℕ} (hx0 : (0 : ℝ)<x) (N : ℕ)
    (f : Idx N → ℝ) (hf : ∀ i, f (negI N i)=f i) :
    (∫ p, Cvs.WeilForm.CubicTailSeparatedKernel.kernelPair betaTail (Cvs.Approximant.CosineColumnTailPairing.modeTest x N f) p
      ∂Cvs.WeilForm.CubicTailSeparatedKernel.leftVolume.prod Cvs.WeilForm.CubicTailSeparatedKernel.rightVolume)=
    ∑ i, f i*(∫ p, Cvs.WeilForm.CubicTailSeparatedKernel.kernelPair betaTail
      (Cvs.Approximant.CosineColumnTailPairing.modeTest x N (Cvs.Approximant.CosineColumnTailPairing.cosineRow N i)) p
        ∂Cvs.WeilForm.CubicTailSeparatedKernel.leftVolume.prod Cvs.WeilForm.CubicTailSeparatedKernel.rightVolume) := by
  have hi (i : Idx N) : Integrable
      (Cvs.WeilForm.CubicTailSeparatedKernel.kernelPair betaTail (Cvs.Approximant.CosineColumnTailPairing.modeTest x N (Cvs.Approximant.CosineColumnTailPairing.cosineRow N i)))
      (Cvs.WeilForm.CubicTailSeparatedKernel.leftVolume.prod Cvs.WeilForm.CubicTailSeparatedKernel.rightVolume) :=
    Cvs.WeilForm.CubicTailSeparatedKernel.integrable_kernelPair Cvs.L2a.BetaProfilePoissonTail.measurable_fullTail_Psi
    (Cvs.Approximant.CosineColumnTailPairing.tame_modeTest hx0 N (Cvs.Approximant.CosineColumnTailPairing.cosineRow N i)).meas
    memLp_betaTail (Cvs.WeilForm.PhysicalCubicCorrectionColumn.memLp_modeTest hx0 N _)
  calc
    _ = ∫ p, ∑ i, f i*Cvs.WeilForm.CubicTailSeparatedKernel.kernelPair betaTail
        (Cvs.Approximant.CosineColumnTailPairing.modeTest x N (Cvs.Approximant.CosineColumnTailPairing.cosineRow N i)) p
          ∂Cvs.WeilForm.CubicTailSeparatedKernel.leftVolume.prod Cvs.WeilForm.CubicTailSeparatedKernel.rightVolume := by
      apply integral_congr_ae
      filter_upwards [] with p
      simp only [Cvs.WeilForm.CubicTailSeparatedKernel.kernelPair, Cvs.WeilForm.PhysicalCubicCorrectionColumn.modeTest_eq_sum_rows x N f hf,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, mul_assoc]
    _ = _ := by
      rw [integral_finsetSum Finset.univ (fun i _ => (hi i).const_mul (f i))]
      simp only [integral_const_mul]

/-- The entire beta column represents the actual functional on all even tests. -/
theorem betaPairing_eq_dot {x : ℕ} (hx : 80≤2*π*x) (N : ℕ)
    (f : Idx N → ℝ) (hf : ∀ i, f (negI N i)=f i) :
    betaPairing x N f=betaColumn x N ⬝ᵥ f := by
  have hx0 := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have ht := Cvs.Approximant.CosineColumnTailPairing.tame_modeTest hx0 N f
  have htr (i : Idx N) := Cvs.Approximant.CosineColumnTailPairing.tame_modeTest hx0 N (Cvs.Approximant.CosineColumnTailPairing.cosineRow N i)
  have ha : 0<1/(x : ℝ) := one_div_pos.mpr hx0
  have ha1 : 1/(x : ℝ)≤1 := (div_le_one hx0).mpr (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx).le
  have hdecomp (g : Idx N → ℝ) : betaPairing x N g=
      (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ)*dil (Cvs.Approximant.CosineColumnTailPairing.modeTest x N g) betaTail n)
      - poleP betaTail*poleM (Cvs.Approximant.CosineColumnTailPairing.modeTest x N g)
      + ∫ p, Cvs.WeilForm.CubicTailSeparatedKernel.kernelPair betaTail (Cvs.Approximant.CosineColumnTailPairing.modeTest x N g) p
          ∂Cvs.WeilForm.CubicTailSeparatedKernel.leftVolume.prod Cvs.WeilForm.CubicTailSeparatedKernel.rightVolume := by
    have hd := Cvs.WeilForm.SeparatedArchDilationPairing.neg_weil_fullTail_eq_cubic
      Cvs.L2a.BetaProfilePoissonTail.hasDerivAt_beta_on Cvs.L2a.BetaProfilePoissonTail.hasDerivAt_beta1_on Cvs.L2a.BetaProfilePoissonTail.continuousOn_beta2
      (by positivity : 0<2*π) (Cvs.Approximant.CosineColumnTailPairing.tame_modeTest hx0 N g) le_rfl
    change betaPairing x N g=
      (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ)*dil (Cvs.Approximant.CosineColumnTailPairing.modeTest x N g) betaTail n)
      -poleP betaTail*poleM (Cvs.Approximant.CosineColumnTailPairing.modeTest x N g)
      +(∫ r in Ioi (1 : ℝ), Cvs.WeilForm.PoleTermDilationMean.dilR (Cvs.Approximant.CosineColumnTailPairing.modeTest x N g) betaTail r/(r*(r^2-1))) at hd
    rw [hd]
    have hk := Cvs.WeilForm.CubicTailSeparatedKernel.integral_cubic_eq_kernelPair Cvs.L2a.BetaProfilePoissonTail.measurable_fullTail_Psi
      (Cvs.Approximant.CosineColumnTailPairing.tame_modeTest hx0 N g).meas memLp_betaTail (Cvs.WeilForm.PhysicalCubicCorrectionColumn.memLp_modeTest hx0 N g)
      (fun _ h => Cvs.L2a.FullTailWeilFormLimit.fullTail_of_le_one _ h)
      (fun θ hθ => (Cvs.Approximant.CosineColumnTailPairing.tame_modeTest hx0 N g).supp θ (fun h => hθ.not_ge h.2))
    change (∫ r in Ioi (1 : ℝ), Cvs.WeilForm.PoleTermDilationMean.dilR (Cvs.Approximant.CosineColumnTailPairing.modeTest x N g) betaTail r/(r*(r^2-1)))=_ at hk
    rw [hk]
    rfl
  have hp : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ)*dil (Cvs.Approximant.CosineColumnTailPairing.modeTest x N f) betaTail n)=
      ∑ i, f i*(∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ)*
        dil (Cvs.Approximant.CosineColumnTailPairing.modeTest x N (Cvs.Approximant.CosineColumnTailPairing.cosineRow N i)) betaTail n) := by
    have he (n : ℕ) : (ArithmeticFunction.vonMangoldt n : ℝ)*dil (Cvs.Approximant.CosineColumnTailPairing.modeTest x N f) betaTail n=
        ∑ i, f i*((ArithmeticFunction.vonMangoldt n : ℝ)*
          dil (Cvs.Approximant.CosineColumnTailPairing.modeTest x N (Cvs.Approximant.CosineColumnTailPairing.cosineRow N i)) betaTail n) := by
      unfold dil
      rw [← integral_const_mul]
      calc
        _ = ∫ θ in Ioi (0 : ℝ), ∑ i, f i*((ArithmeticFunction.vonMangoldt n : ℝ)*
            Cvs.Approximant.CosineColumnTailPairing.modeTest x N (Cvs.Approximant.CosineColumnTailPairing.cosineRow N i) θ*betaTail ((n : ℝ)*θ)) := by
          apply integral_congr_ae
          filter_upwards [] with θ
          simp only [Cvs.WeilForm.PhysicalCubicCorrectionColumn.modeTest_eq_sum_rows x N f hf, Finset.sum_apply,
            Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by
          rw [integral_finsetSum Finset.univ
            (fun i _ => (integrable_prime_beta (htr i) n).const_mul (f i))]
          apply Finset.sum_congr rfl
          intro i _
          rw [integral_const_mul]
          congr 1
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards [] with θ
          ring
    simp_rw [he]
    rw [Summable.tsum_finsetSum (fun i _ => ((prime_beta_budget ha ha1 (htr i)).1).mul_left (f i))]
    simp_rw [tsum_mul_left]
  have hm : poleM (Cvs.Approximant.CosineColumnTailPairing.modeTest x N f)=
      ∑ i, f i*poleM (Cvs.Approximant.CosineColumnTailPairing.modeTest x N (Cvs.Approximant.CosineColumnTailPairing.cosineRow N i)) := by
    unfold poleM
    calc
      _ = ∫ θ in Ioi (0 : ℝ), ∑ i, f i*(Cvs.Approximant.CosineColumnTailPairing.modeTest x N (Cvs.Approximant.CosineColumnTailPairing.cosineRow N i) θ/θ) := by
        apply integral_congr_ae
        filter_upwards [] with θ
        simp only [Cvs.WeilForm.PhysicalCubicCorrectionColumn.modeTest_eq_sum_rows x N f hf, Finset.sum_apply,
          Pi.smul_apply, smul_eq_mul, Finset.sum_div, mul_div_assoc]
      _ = _ := by
        rw [integral_finsetSum Finset.univ (fun i _ => ((htr i).div.restrict).const_mul (f i))]
        simp only [integral_const_mul]
  rw [hdecomp, hp, hm, beta_cubic_rows hx0 N f hf]
  unfold betaColumn dotProduct
  simp_rw [hdecomp]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The complete stable correction column has a cutoff-independent physical budget. -/
theorem betaColumn_sq_le {x : ℕ} (hx : 80≤2*π*x) (N : ℕ) :
    ∑ i, betaColumn x N i^2≤log x*betaBudget x^2 := by
  have hx1 := Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx
  have h := Cvs.WeilForm.PhysicalCubicCorrectionColumn.column_sq_le_of_unit_pairing (negI N) (betaColumn x N)
    (betaColumn_even x N) (betaBudget x*√(log x)) ?_
  · simpa only [mul_pow, sq_sqrt (log_pos hx1).le, mul_comm] using h
  intro f hf hunit
  rw [← betaPairing_eq_dot hx N f hf]
  have hb := abs_weil_beta_le hx1.le (Cvs.Approximant.CosineColumnTailPairing.tame_modeTest (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N f)
  change |betaPairing x N f|≤_ at hb
  have hn := Cvs.WeilForm.PhysicalCubicCorrectionColumn.norm_modeTest_toLp hx1 N f hf
  change ‖(Cvs.WeilForm.PhysicalCubicCorrectionColumn.memLp_of_tame (Cvs.Approximant.CosineColumnTailPairing.tame_modeTest (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N f)).toLp
    (Cvs.Approximant.CosineColumnTailPairing.modeTest x N f)‖=_ at hn
  rw [hn, show f ⬝ᵥ f=1 by simpa only [dotProduct, sq] using hunit, mul_one] at hb
  exact hb

/-- Orthogonal centering retains the whole stable correction budget. -/
theorem centered_betaColumn_sq_le {x : ℕ} (hx : 80≤2*π*x) (N : ℕ) (α : Idx N → ℝ) :
    ∑ i, Cvs.Approximant.ConnesErrorColumn.center (betaColumn x N) α i^2≤log x*betaBudget x^2 := by
  have h := Cvs.Approximant.ConnesErrorColumn.center_sq_le (betaColumn x N) α
  have h' : (∑ i, Cvs.Approximant.ConnesErrorColumn.center (betaColumn x N) α i^2)≤∑ i, betaColumn x N i^2 := by
    simpa only [dotProduct, sq] using h
  exact h'.trans (betaColumn_sq_le hx N)

/-- The actual singleton regularization scalar. -/
def polarParameter (x : ℕ) : ℝ :=
  (2*π/(2*π*x))*Cvs.Approximant.DeepIndexSpineSpan.spineG (2*π*x) (S := {1}) (fun _ => 1) 0

/-- The actual singleton centre retains its exact angular eigenvalue ratio. -/
theorem singleton_center_eq {c : ℝ} (hc : 0<c)
    (h2 : ∃ χ, Cvs.Prolate.EvenRungsByIndex.IsLevelIdx c 2 χ) :
    Cvs.Approximant.DeepIndexSpineSpan.spineG c (S := {1}) (fun _ => 1) 0=
      Cvs.Prolate.EvenRungsByIndex.rung c 2 0*(1-Cvs.Prolate.EvenRungsByIndex.muR c 2/Cvs.Prolate.EvenRungsByIndex.muR c 0) := by
  have h0 := Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero c
  have hi0 := Cvs.Prolate.AngularBesselInequality.integral_eq_mu_mul (Cvs.Prolate.EvenRungsByIndex.psi_rung h0)
  have hi2 := Cvs.Prolate.AngularBesselInequality.integral_eq_mu_mul (Cvs.Prolate.EvenRungsByIndex.psi_rung h2)
  have hg0 : Cvs.Prolate.EvenRungsByIndex.rung c 0 0≠0 := by
    intro h
    have hn := Cvs.Prolate.EvenRungsByIndex.integral_rung_zero_ne hc
    rw [hi0, h, mul_zero] at hn
    exact hn rfl
  have hm0 := Cvs.Prolate.EvenRungsByIndex.muR_pos_of_even hc h0 (show Even 0 from ⟨0,rfl⟩)
  rw [Cvs.Approximant.SpineNearQuarticHermite.spineG_one]
  unfold Cvs.Approximant.DeepIndexSpineSpan.alpha
  rw [hi0, hi2]
  field_simp

/-- Angular Bessel bounds the actual singleton centre before weakening its eigenvalue ratio. -/
theorem connes_polar_parameter_sq_le_ratio {x : ℕ} (hx : 80≤2*π*x) :
    polarParameter x^2≤(4/(x : ℝ))*(1-Cvs.Prolate.EvenRungsByIndex.muR (2*π*x) 2/Cvs.Prolate.EvenRungsByIndex.muR (2*π*x) 0)^2 := by
  have hc : 0<2*π*(x : ℝ) := by linarith
  have h2 := Cvs.Prolate.RungFamilyRangePartners.exists_main hx ⟨1,Finset.mem_range.mpr
    (Cvs.Approximant.CosineColumnTailPairing.singleton_lt_of_scale hx 1 (Finset.mem_singleton.mpr rfl))⟩
  have h2' : ∃ χ, Cvs.Prolate.EvenRungsByIndex.IsLevelIdx (2*π*x) 2 χ := by simpa using h2
  have hs := Cvs.Prolate.EvenRungsByIndex.rung_spec h2'
  have hb := Cvs.Prolate.AngularBesselInequality.sum_lam_mul_sq_le ({()} : Finset Unit) hc
    (fun _ => hs.1) (fun _ => hs.2.1) (fun _ => hs.2.2.2.1)
    (fun _ _ _ _ _ => Subsingleton.elim _ _)
    (fun _ _ => hs.2.2.2.2.2) (fun _ _ => Cvs.Prolate.EvenRungsByIndex.psi_rung h2')
  simp only [Finset.sum_singleton] at hb
  change Cvs.Prolate.EvenRungsByIndex.lamR (2*π*x) 2*Cvs.Prolate.EvenRungsByIndex.rung (2*π*x) 2 0^2≤(2*π*x)/π at hb
  have hl := Cvs.L2a.WindowChainInputsProlate.half_le_lamR hx
    (Cvs.Approximant.CosineColumnTailPairing.singleton_lt_of_scale hx 1 (Finset.mem_singleton.mpr rfl))
  norm_num at hl
  have hr : Cvs.Prolate.EvenRungsByIndex.rung (2*π*x) 2 0^2≤2*(2*π*x)/π := by
    have hm := mul_le_mul_of_nonneg_right hl (sq_nonneg (Cvs.Prolate.EvenRungsByIndex.rung (2*π*x) 2 0))
    calc
      _ = 2*((1/2)*Cvs.Prolate.EvenRungsByIndex.rung (2*π*x) 2 0^2) := by ring
      _ ≤ 2*((2*π*x)/π) := mul_le_mul_of_nonneg_left (hm.trans hb) (by norm_num)
      _ = _ := by ring
  have he : polarParameter x^2=
      (2*π/(2*π*x))^2*Cvs.Prolate.EvenRungsByIndex.rung (2*π*x) 2 0^2*
        (1-Cvs.Prolate.EvenRungsByIndex.muR (2*π*x) 2/Cvs.Prolate.EvenRungsByIndex.muR (2*π*x) 0)^2 := by
    unfold polarParameter
    rw [singleton_center_eq hc h2']
    ring
  rw [he]
  calc
    _≤(2*π/(2*π*x))^2*(2*(2*π*x)/π)*
        (1-Cvs.Prolate.EvenRungsByIndex.muR (2*π*x) 2/Cvs.Prolate.EvenRungsByIndex.muR (2*π*x) 0)^2 := by
      gcongr
    _=_ := by
      field_simp
      ring

/-- The actual singleton concentration defect has an unconditional exponential majorant. -/
theorem singleton_defect_exponential_le {c : ℝ} (hc : 80 ≤ c) :
    1 - Cvs.Prolate.EvenRungsByIndex.lamR c 2 ≤
      (71 / 10) * (Real.exp 3 / 2) * (π * (c - 9) / 4 + 2)
        * Real.exp (-(π * (c - 9) / 2)) := by
  have hc0 : 0 < c := by linarith
  have hc31 : 31 ≤ c := by linarith
  have hcm : 0 ≤ c - 9 := by linarith
  have hk := Cvs.Prolate.EvenRungDavisKahan.exists_isLevelIdx_of_le_three hc31 (show (2 : ℕ) ≤ 3 by norm_num)
  have hχ0 := Cvs.Prolate.SlepianEvenOrdering.nonneg_of_mem_evenSpec c (Cvs.Prolate.EvenRungsByIndex.lev_spec hk).1
  have hχ9 : Cvs.Prolate.EvenRungsByIndex.lev c 2 ≤ 9 * c := by
    have h := Cvs.Prolate.EvenRungDavisKahan.sq_lev_two_sub_le hc31
    rw [Cvs.Prolate.EvenRungDavisKahan.mu_two, Cvs.Prolate.HermiteTrialResiduals.kap2_values.2.2] at h
    nlinarith
  have hD : c ^ 2 < 4 * (c ^ 2 - Cvs.Prolate.EvenRungsByIndex.lev c 2) := by nlinarith
  obtain ⟨hg, hg₁, hg₂c, hang, heven, -⟩ := Cvs.Prolate.EvenRungsByIndex.rung_spec hk
  have hP := Cvs.L2a.SpanPlungeBound.plunge_large hg hg₁ hg₂c hang hc hχ0 hD heven
    (Cvs.Prolate.EvenRungsByIndex.rung_ne_zero hk) (Cvs.Prolate.EvenRungsByIndex.psi_rung hk)
  have hlam : c / (2 * π) * Cvs.Prolate.EvenRungsByIndex.muR c 2 ^ 2 = Cvs.Prolate.EvenRungsByIndex.lamR c 2 := by
    rw [Cvs.Prolate.EvenRungsByIndex.lamR, mul_pow, sq_sqrt (by positivity)]
    ring
  rw [hlam] at hP
  have hZ : π * (c - 9) / 4 ≤ π * (c ^ 2 - Cvs.Prolate.EvenRungsByIndex.lev c 2) / (4 * c) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  have hanti := Cvs.Prolate.ForbiddenZoneClosedForm.exp_neg_two_PhiC_anti (Z := π * (c - 9) / 4)
    (by positivity) hZ
  have hsmall := Cvs.Prolate.ForbiddenZoneClosedForm.exp_neg_two_PhiC_le (Z := π * (c - 9) / 4) (by positivity)
  calc
    1 - Cvs.Prolate.EvenRungsByIndex.lamR c 2 ≤ Cvs.L2a.SpanPlungeBound.Cbig * Real.exp
      (-(2 * Cvs.Prolate.ForbiddenZoneGrowth.PhiC (π * (c ^ 2 - Cvs.Prolate.EvenRungsByIndex.lev c 2) / (4 * c)))) := hP
    _ ≤ Cvs.L2a.SpanPlungeBound.Cbig * Real.exp (-(2 * Cvs.Prolate.ForbiddenZoneGrowth.PhiC (π * (c - 9) / 4))) :=
      mul_le_mul_of_nonneg_left hanti Cvs.L2a.SpanPlungeBound.Cbig_pos.le
    _ ≤ (71 / 10) * (Real.exp 3 / 2 * (π * (c - 9) / 4 + 2)
      * Real.exp (-(2 * (π * (c - 9) / 4)))) :=
      mul_le_mul Cvs.L2a.SpanPlungeBound.Cbig_le hsmall (Real.exp_pos _).le (by norm_num)
    _ = _ := by
      rw [show -(2 * (π * (c - 9) / 4)) = -(π * (c - 9) / 2) by ring]
      ring

/-- The Connes scale specialization of the singleton exponential concentration bound. -/
theorem connes_defect_exponential_le {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    1 - Cvs.Prolate.EvenRungsByIndex.lamR (2 * π * x) 2 ≤
      (71 / 10) * (Real.exp 3 / 2) * (π * (2 * π * x - 9) / 4 + 2)
        * Real.exp (-(π * (2 * π * x - 9) / 2)) :=
  singleton_defect_exponential_le hx

/-- The full signed correction column of the actual regularization scalar. -/
def regularizationColumn (x N : ℕ) : Idx N → ℝ :=
  polarParameter x • betaColumn x N

/-- The complete correction budget retains the exact singleton angular ratio, uniformly in order. -/
theorem regularizationColumn_sq_le_ratio {x : ℕ} (hx : 80≤2*π*x) (N : ℕ) :
    ∑ i, regularizationColumn x N i^2≤
      (4*log x/(x : ℝ))*(1-Cvs.Prolate.EvenRungsByIndex.muR (2*π*x) 2/Cvs.Prolate.EvenRungsByIndex.muR (2*π*x) 0)^2*betaBudget x^2 := by
  unfold regularizationColumn
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  calc
    _≤polarParameter x^2*(log x*betaBudget x^2) :=
      mul_le_mul_of_nonneg_left (betaColumn_sq_le hx N) (sq_nonneg _)
    _≤((4/(x : ℝ))*(1-Cvs.Prolate.EvenRungsByIndex.muR (2*π*x) 2/Cvs.Prolate.EvenRungsByIndex.muR (2*π*x) 0)^2)*
        (log x*betaBudget x^2) :=
      mul_le_mul_of_nonneg_right (connes_polar_parameter_sq_le_ratio hx)
        (mul_nonneg (log_natCast_nonneg x) (sq_nonneg _))
    _=_ := by ring

/-- Centering does not enlarge the complete actual regularization correction. -/
theorem centered_regularizationColumn_sq_le_ratio {x : ℕ} (hx : 80≤2*π*x)
    (N : ℕ) (α : Idx N → ℝ) :
    ∑ i, Cvs.Approximant.ConnesErrorColumn.center (regularizationColumn x N) α i^2≤
      (4*log x/(x : ℝ))*(1-Cvs.Prolate.EvenRungsByIndex.muR (2*π*x) 2/Cvs.Prolate.EvenRungsByIndex.muR (2*π*x) 0)^2*betaBudget x^2 := by
  have h : (∑ i, Cvs.Approximant.ConnesErrorColumn.center (regularizationColumn x N) α i^2)≤
      ∑ i, regularizationColumn x N i^2 := by
    simpa only [dotProduct, sq] using Cvs.Approximant.ConnesErrorColumn.center_sq_le (regularizationColumn x N) α
  exact h.trans (regularizationColumn_sq_le_ratio hx N)

/-- The concentration defect's explicit exponential budget. -/
def defectBudget (c : ℝ) : ℝ :=
  (71/10)*(exp 3/2)*(π*(c-9)/4+2)*exp (-(π*(c-9)/2))

/-- The complete correction has an unconditional exponential concentration budget. -/
theorem regularizationColumn_sq_le_exponential {x : ℕ} (hx : 80≤2*π*x) (N : ℕ) :
    ∑ i, regularizationColumn x N i^2≤
      (4*log x/(x : ℝ))*defectBudget (2*π*x)^2*betaBudget x^2 := by
  have hp : polarParameter x^2≤8*π/(2*π*x)*(1-Cvs.Prolate.EvenRungsByIndex.lamR (2*π*x) 2)^2 := by
    simpa only [polarParameter, mul_pow] using Cvs.Approximant.SpineRegularisationDefect.connes_polar_parameter_sq_le hx
  have he := connes_defect_exponential_le hx
  change 1-Cvs.Prolate.EvenRungsByIndex.lamR (2*π*x) 2≤defectBudget (2*π*x) at he
  have hn : 0≤1-Cvs.Prolate.EvenRungsByIndex.lamR (2*π*x) 2 := by
    have h2 : ∃ χ, Cvs.Prolate.EvenRungsByIndex.IsLevelIdx (2*π*x) 2 χ := by
      simpa using Cvs.Prolate.RungFamilyRangePartners.exists_main hx ⟨1,Finset.mem_range.mpr
        (Cvs.Approximant.CosineColumnTailPairing.singleton_lt_of_scale hx 1 (Finset.mem_singleton.mpr rfl))⟩
    exact sub_nonneg.mpr (Cvs.Prolate.EvenRungsByIndex.lamR_lt_one (by linarith) h2 (by norm_num)).le
  have he2 := pow_le_pow_left₀ hn he 2
  have hbudget : polarParameter x^2≤(4/(x : ℝ))*defectBudget (2*π*x)^2 := by
    calc
      _≤8*π/(2*π*x)*(1-Cvs.Prolate.EvenRungsByIndex.lamR (2*π*x) 2)^2 := hp
      _≤8*π/(2*π*x)*defectBudget (2*π*x)^2 :=
        mul_le_mul_of_nonneg_left he2 (by positivity)
      _=_ := by field_simp; ring
  unfold regularizationColumn
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  calc
    _≤polarParameter x^2*(log x*betaBudget x^2) :=
      mul_le_mul_of_nonneg_left (betaColumn_sq_le hx N) (sq_nonneg _)
    _≤((4/(x : ℝ))*defectBudget (2*π*x)^2)*(log x*betaBudget x^2) :=
      mul_le_mul_of_nonneg_right hbudget (mul_nonneg (log_natCast_nonneg x) (sq_nonneg _))
    _=_ := by ring

/-- The fixed constant controlling stable beta-column growth with scale. -/
def betaGrowthConstant : ℝ :=
  betaPrimeConstant+|49/48-log (2*π)/2|+(π/2)*√(133/1000 : ℝ)

/-- The stable beta budget grows at most as the square root of the physical scale. -/
theorem betaBudget_le_sqrt_scale {x : ℝ} (hx : 1≤x) :
    betaBudget x≤betaGrowthConstant*√x := by
  have hx0 : 0≤x := zero_le_one.trans hx
  have hr : √(x-1)≤√x := sqrt_le_sqrt (by linarith)
  have hr1 : 1≤√x := by simpa using sqrt_le_sqrt hx
  unfold betaBudget betaGrowthConstant
  have hA := add_nonneg betaPrimeConstant_nonneg (abs_nonneg (49/48-log (2*π)/2))
  have hB : 0≤(π/2)*√(133/1000 : ℝ) := by positivity
  have h1 := mul_le_mul_of_nonneg_left hr hA
  have h2 := mul_le_mul_of_nonneg_left hr1 hB
  nlinarith

/-- Explicit scale growth cancels the inverse-scale regularization factor. -/
theorem regularizationColumn_sq_le_exponential_growth {x : ℕ} (hx : 80≤2*π*x) (N : ℕ) :
    ∑ i, regularizationColumn x N i^2≤
      4*log x*defectBudget (2*π*x)^2*betaGrowthConstant^2 := by
  have hx0 := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have hx1 := (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx).le
  have hbp := betaPrimeConstant_nonneg
  have hb := pow_le_pow_left₀ (show 0≤betaBudget (x : ℝ) by unfold betaBudget; positivity)
    (betaBudget_le_sqrt_scale hx1) 2
  rw [mul_pow, sq_sqrt hx0.le] at hb
  calc
    _≤(4*log x/(x : ℝ))*defectBudget (2*π*x)^2*betaBudget x^2 :=
      regularizationColumn_sq_le_exponential hx N
    _≤(4*log x/(x : ℝ))*defectBudget (2*π*x)^2*(betaGrowthConstant^2*x) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _=_ := by field_simp

def rawTail (x : ℕ) : ℝ → ℝ :=
  Cvs.L2a.FullTailConvergence.fullTail (Cvs.L2a.AngularProlateTailPositive.psi (2*π*x)
    (Cvs.Approximant.DeepIndexSpineSpan.spineG (2*π*x) (S := {1}) fun _ => 1))
theorem fullTail_regProfile_eq {c : ℝ} (hc : 2*π≤c) {G G₁ G₂ : ℝ → ℝ}
    (hg : ∀ s∈uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s∈uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s)
    (hg₂c : ContinuousOn G₂ (uIcc (-1) 1)) :
    Cvs.L2a.FullTailConvergence.fullTail (Cvs.L2a.AngularProlateTailPositive.psi c (Cvs.L2a.WindowFormTailLimit.regProfile c G)) = fun θ =>
      Cvs.L2a.FullTailConvergence.fullTail (Cvs.L2a.AngularProlateTailPositive.psi c G) θ-(2*π/c*G 0)*betaTail θ := by
  have hGc : ContinuousOn G (uIcc (-1) 1) :=
    fun s hs => (hg s hs).continuousAt.continuousWithinAt
  unfold Cvs.L2a.WindowFormTailLimit.regProfile
  rw [Cvs.L2a.FullTailPolarisation.psi_add_smul hGc (by
    have h : Continuous (Cvs.L2a.FullTailBilinearChannels.betaA c) := by
      unfold Cvs.L2a.FullTailBilinearChannels.betaA
      exact continuous_const.mul (Cvs.L2a.BetaProfilePoissonTail.contDiff_beta.continuous.comp
        (continuous_id.div_const _))
    exact h.continuousOn),
    Cvs.L2a.FullTailPolarisation.fullTail_psi_add_smul hg hg₁ hg₂c
      (fun s _ => Cvs.L2a.FullTailBilinearChannels.hasDerivAt_betaA c s)
      (fun s _ => Cvs.L2a.FullTailBilinearChannels.hasDerivAt_betaA1 c s)
      (Cvs.L2a.FullTailBilinearChannels.continuous_betaA2 c).continuousOn (by linarith [pi_pos]),
    Cvs.L2a.FullTailBilinearChannels.psi_betaA hc]
  funext θ
  simp only [betaTail]
  ring

theorem connesTail_eq_raw_sub_beta {x : ℕ} (hx : 80≤2*π*x) :
    Cvs.Approximant.CosineColumnTailPairing.connesTail x = fun θ => rawTail x θ-polarParameter x*betaTail θ := by
  obtain ⟨G₁,G₂,hg,hg₁,hg₂c,_,_⟩ :=
    Cvs.Approximant.SpineCouplingTailPairing.spine_profile_data hx (Cvs.Approximant.CosineColumnTailPairing.singleton_lt_of_scale hx) (fun _ => 1)
  exact fullTail_regProfile_eq (by
    have hx1 := Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx
    nlinarith [pi_pos]) hg hg₁ hg₂c

theorem rawTail_eq_connes_add_beta {x : ℕ} (hx : 80≤2*π*x) :
    rawTail x = fun θ => Cvs.Approximant.CosineColumnTailPairing.connesTail x θ+polarParameter x*betaTail θ := by
  rw [connesTail_eq_raw_sub_beta hx]
  funext θ
  ring

theorem adm_fullTail_of_prime {g g₁ g₂ : ℝ → ℝ} {c : ℝ}
    (hg : ∀ s∈uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s∈uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1)) (hc : 0<c)
    {v : ℝ → ℝ} {a : ℝ} (hv : Cvs.L2a.WindowFormTailLimit.Tame v a 1)
    (hp : Summable fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ)*
      dil v (Cvs.L2a.FullTailConvergence.fullTail (Cvs.L2a.AngularProlateTailPositive.psi c g)) n) :
    Cvs.L2a.WindowFormTailLimit.Adm (Cvs.L2a.FullTailConvergence.fullTail (Cvs.L2a.AngularProlateTailPositive.psi c g)) v := by
  let F := Cvs.L2a.FullTailConvergence.fullTail (Cvs.L2a.AngularProlateTailPositive.psi c g)
  have hm : Measurable F := Cvs.L2a.FullTailConvergence.measurable_fullTail hg hg₁ hg₂c hc
  have hzero : ∀ θ≤1, F θ=0 := fun _ hθ => Cvs.L2a.FullTailWeilFormLimit.fullTail_of_le_one _ hθ
  obtain ⟨hF2,hF1⟩ := Cvs.L2a.FullTailConvergence.memLp_logScale_fullTail hg hg₁ hg₂c hc
  obtain ⟨M,hM⟩ := hv.bdd
  refine {
    pole := ⟨_,Cvs.L2a.WindowFormTailLimit.tendsto_integral_fullTail hg hg₁ hg₂c hc⟩
    div := ?_
    log := hF1
    arch := ?_
    left := ?_
    right := ?_
    prime := ?_ }
  · have hi := Cvs.L2a.FullTailPolarisation.integrableOn_div_of_le hm
      (fun θ hθ => Cvs.L2a.FullTailConvergence.abs_fullTail_le hg hg₁ hg₂c hc hθ)
    apply (integrableOn_iff_integrable_of_support_subset (μ := volume.restrict (Ioi (0 : ℝ)))
      (s := Ioi (1 : ℝ)) ?_).1
    · simpa only [IntegrableOn, Measure.restrict_restrict measurableSet_Ioi,
        inter_eq_left.mpr (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤1))] using hi
    · intro θ hθ
      by_contra h
      apply hθ
      change F θ / θ=0
      rw [hzero θ (not_lt.mp h), zero_div]
  · have harch := Cvs.WeilForm.Archimedean.LevyTonelli.integrable_specDensity_mul_arch hF2 hF1
      (Cvs.L2a.FullTailArchChannel.integrableOn_levy_fullTail hg hg₁ hg₂c hc)
    exact Cvs.L2a.WindowFormTailLimit.integrable_arch_crossSpec hF1 hF2 harch hv.log.1 hv.log.2 hv.arch
  · intro n hn
    have he : (fun θ => F θ*v ((n : ℝ)*θ))=fun _ => (0 : ℝ) := by
      funext θ
      by_cases hθ : θ≤1
      · rw [hzero θ hθ, zero_mul]
      · have hn1 : (1 : ℝ)≤n := by exact_mod_cast hn
        have hprod : 1<(n : ℝ)*θ := by nlinarith
        rw [hv.supp _ (fun h => by linarith [h.2]), mul_zero]
    rw [he]
    exact integrableOn_zero
  · intro n _
    exact (Cvs.L2a.WindowFormTailLimit.integrable_mul_of_support hv.meas hM hv.supp
      (hm.comp (measurable_const.mul measurable_id))
      (fun θ => Cvs.L2a.WindowFormTailLimit.abs_fullTail_le_BG hg hg₁ hg₂c hc _)).integrableOn
  · refine hp.congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [Cvs.L2a.RungWindowCouplingTail.dil_fullTail_left_eq_zero _ (le_refl 1) hv.supp hn, zero_add]

theorem adm_betaTail {v : ℝ → ℝ} {a : ℝ} (hv : Cvs.L2a.WindowFormTailLimit.Tame v a 1)
    (hb : Summable fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ)*dil v betaTail n) :
    Cvs.L2a.WindowFormTailLimit.Adm betaTail v :=
  adm_fullTail_of_prime Cvs.L2a.BetaProfilePoissonTail.hasDerivAt_beta_on Cvs.L2a.BetaProfilePoissonTail.hasDerivAt_beta1_on
    Cvs.L2a.BetaProfilePoissonTail.continuousOn_beta2 (by positivity) hv hb

theorem adm_connesTail {x : ℕ} (hx : 80≤2*π*x)
    {v : ℝ → ℝ} {a : ℝ} (hv : Cvs.L2a.WindowFormTailLimit.Tame v a 1) :
    Cvs.L2a.WindowFormTailLimit.Adm (Cvs.Approximant.CosineColumnTailPairing.connesTail x) v := by
  obtain ⟨G₁,G₂,hg,hg₁,hg₂c,heven,hGi⟩ :=
    Cvs.Approximant.SpineCouplingTailPairing.spine_profile_data hx (Cvs.Approximant.CosineColumnTailPairing.singleton_lt_of_scale hx) (fun _ => 1)
  obtain ⟨H₁,H₂,hH,hH₁,hH₂c⟩ := Cvs.WeilForm.SeparatedArchDilationPairing.regProfile_derivative_data hg hg₁ hg₂c
  have hc0 : 0<2*π*(x : ℝ) := by linarith
  have hc : 2*π≤2*π*(x : ℝ) := by
    have hx1 := Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx
    nlinarith [pi_pos]
  have hH0 : Cvs.L2a.WindowFormTailLimit.regProfile (2*π*x)
      (Cvs.Approximant.DeepIndexSpineSpan.spineG (2*π*x) (S := {1}) fun _ => 1) 0=0 := by
    rw [Cvs.L2a.WindowFormTailLimit.regProfile_eq hc0]
    simp [Cvs.L2a.BetaProfilePoissonTail.beta_zero]
  have hHeven : ∀ s∈Icc (-1 : ℝ) 1,
      Cvs.L2a.WindowFormTailLimit.regProfile (2*π*x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2*π*x) (S := {1}) fun _ => 1) (-s)=
      Cvs.L2a.WindowFormTailLimit.regProfile (2*π*x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2*π*x) (S := {1}) fun _ => 1) s := by
    intro s hs
    simp only [Cvs.L2a.WindowFormTailLimit.regProfile, heven s hs, Cvs.L2a.WindowFormTailLimit.betaA_neg]
  have hHi : ∫ s in (-1 : ℝ)..1,
      Cvs.L2a.WindowFormTailLimit.regProfile (2*π*x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2*π*x) (S := {1}) fun _ => 1) s=0 := by
    have hGc : ContinuousOn (Cvs.Approximant.DeepIndexSpineSpan.spineG (2*π*x) (S := {1}) fun _ => 1)
        (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
    unfold Cvs.L2a.WindowFormTailLimit.regProfile
    have hb : Continuous (Cvs.L2a.FullTailBilinearChannels.betaA (2*π*x)) := by
      unfold Cvs.L2a.FullTailBilinearChannels.betaA
      exact continuous_const.mul (Cvs.L2a.BetaProfilePoissonTail.contDiff_beta.continuous.comp
        (continuous_id.div_const _))
    rw [intervalIntegral.integral_add hGc.intervalIntegrable
      ((hb.const_mul _).intervalIntegrable _ _)]
    rw [intervalIntegral.integral_const_mul, hGi, Cvs.L2a.WindowFormTailLimit.integral_betaA hc]
    ring
  have hA := (Cvs.L2a.WindowFormTailLimit.adm_of_tame (Cvs.L2a.WindowFormTailLimit.tame_posTail_psi hH hH₁ hH₂c hc0
      (le_refl (1 : ℝ))) hv).add
    (Cvs.L2a.WindowFormTailLimit.adm_tailRem hH hH₁ hH₂c hHeven hc0 hH0 hHi (le_refl (1 : ℝ)) hv)
  rw [Cvs.L2a.RungWindowCouplingTail.posTail_add_tailRem] at hA
  exact hA

theorem adm_rawTail {x : ℕ} (hx : 80≤2*π*x)
    {v : ℝ → ℝ} {a : ℝ} (hv : Cvs.L2a.WindowFormTailLimit.Tame v a 1)
    (hb : Summable fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ)*dil v betaTail n) :
    Cvs.L2a.WindowFormTailLimit.Adm (rawTail x) v := by
  rw [rawTail_eq_connes_add_beta hx]
  exact (adm_connesTail hx hv).add ((adm_betaTail hv hb).smul (polarParameter x))

theorem summable_prime_rawTail {x : ℕ} (hx : 80≤2*π*x)
    {v : ℝ → ℝ} {a : ℝ} (hv : Cvs.L2a.WindowFormTailLimit.Tame v a 1)
    (hb : Summable fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ)*dil v betaTail n) :
    Summable fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ)*dil v (rawTail x) n := by
  refine (adm_rawTail hx hv hb).prime.congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [rawTail, Cvs.L2a.RungWindowCouplingTail.dil_fullTail_left_eq_zero _ (le_refl 1) hv.supp hn, zero_add]

theorem weilθ_smul_of_adm {F v : ℝ → ℝ} (hF : Cvs.L2a.WindowFormTailLimit.Adm F v) (d : ℝ) :
    weilθ (fun θ => d*F θ) v=d*weilθ F v := by
  obtain ⟨p,hp⟩ := hF.pole
  have hp' := (hp.const_mul d).congr fun Y =>
    (intervalIntegral.integral_const_mul d _).symm
  have hP : poleP (fun θ => d*F θ)=d*poleP F := by
    rw [Cvs.WeilForm.ThetaSpaceParseval.poleP_eq_of_tendsto hp', Cvs.WeilForm.ThetaSpaceParseval.poleP_eq_of_tendsto hp]
  have hM : poleM (fun θ => d*F θ)=d*poleM F := by
    unfold poleM
    simp_rw [mul_div_assoc]
    exact integral_const_mul _ _
  unfold weilθ
  rw [hP,hM,Cvs.L2a.WindowFormTailLimit.logScale_smul]
  simp_rw [Cvs.L2a.WindowFormTailLimit.crossSpec_smul_left hF.log, Cvs.L2a.WindowFormTailLimit.dil_smul_left, Cvs.L2a.WindowFormTailLimit.dil_smul_right]
  have harch : (∫ t, Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t*(d*Cvs.L2a.FullTailPolarisation.crossSpec (logScale F) (logScale v) t))=
      d*(∫ t, Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t*Cvs.L2a.FullTailPolarisation.crossSpec (logScale F) (logScale v) t) := by
    rw [← integral_const_mul]
    congr 1
    funext t
    ring
  rw [harch]
  have hs : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ)*
      (d*dil F v n+d*dil v F n))=d*(∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ)*
      (dil F v n+dil v F n)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    ring
  rw [hs]
  ring

theorem weilθ_connesTail_eq_raw_sub_beta {x : ℕ} (hx : 80≤2*π*x)
    {v : ℝ → ℝ} {a : ℝ} (hv : Cvs.L2a.WindowFormTailLimit.Tame v a 1)
    (hb : Summable fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ)*dil v betaTail n) :
    -weilθ (Cvs.Approximant.CosineColumnTailPairing.connesTail x) v=
      -weilθ (rawTail x) v-polarParameter x*(-weilθ betaTail v) := by
  have he := Cvs.L2a.WindowFormTailLimit.weilθ_add (adm_connesTail hx hv)
    ((adm_betaTail hv hb).smul (polarParameter x))
  rw [← rawTail_eq_connes_add_beta hx, weilθ_smul_of_adm (adm_betaTail hv hb)] at he
  linarith

/-- Actual beta summability is supplied by the complete beta prime budget. -/
theorem adm_betaTail_actual {v : ℝ → ℝ} {a : ℝ} (hv : Cvs.L2a.WindowFormTailLimit.Tame v a 1)
    (ha1 : a≤1) : Cvs.L2a.WindowFormTailLimit.Adm betaTail v :=
  adm_betaTail hv (prime_beta_budget hv.pos ha1 hv).1

theorem adm_rawTail_actual {x : ℕ} (hx : 80≤2*π*x)
    {v : ℝ → ℝ} {a : ℝ} (hv : Cvs.L2a.WindowFormTailLimit.Tame v a 1) (ha1 : a≤1) :
    Cvs.L2a.WindowFormTailLimit.Adm (rawTail x) v :=
  adm_rawTail hx hv (prime_beta_budget hv.pos ha1 hv).1

theorem summable_prime_rawTail_actual {x : ℕ} (hx : 80≤2*π*x)
    {v : ℝ → ℝ} {a : ℝ} (hv : Cvs.L2a.WindowFormTailLimit.Tame v a 1) (ha1 : a≤1) :
    Summable fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ)*dil v (rawTail x) n :=
  summable_prime_rawTail hx hv (prime_beta_budget hv.pos ha1 hv).1

/-- Complete regularization of the actual signed-cosine tail pairing. -/
theorem connesTail_pairing_eq_raw_sub_beta {x : ℕ} (hx : 80≤2*π*x)
    (N : ℕ) (f : Cvs.Finite.SymmetricModeSet.Idx N → ℝ) :
    -weilθ (Cvs.Approximant.CosineColumnTailPairing.connesTail x) (Cvs.Approximant.CosineColumnTailPairing.modeTest x N f)=
      -weilθ (rawTail x) (Cvs.Approximant.CosineColumnTailPairing.modeTest x N f)-
        polarParameter x*betaPairing x N f := by
  have hx1 := Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx
  exact weilθ_connesTail_eq_raw_sub_beta hx
    (Cvs.Approximant.CosineColumnTailPairing.tame_modeTest (by linarith) N f)
    (prime_beta_budget (by positivity)
      ((div_le_one (by linarith : (0:ℝ)<x)).mpr (le_of_lt hx1))
      (Cvs.Approximant.CosineColumnTailPairing.tame_modeTest (by linarith) N f)).1

/-- The raw singleton tail paired with every actual signed cosine coordinate. -/
def rawTailColumn (x N : ℕ) (i : Cvs.Finite.SymmetricModeSet.Idx N) : ℝ :=
  -weilθ (rawTail x) (Cvs.Approximant.CosineColumnTailPairing.modeTest x N (Cvs.Approximant.CosineColumnTailPairing.cosineRow N i))

/-- The actual tail column includes the complete beta correction with its exact sign. -/
theorem tailColumn_eq_raw_sub_regularization {x : ℕ} (hx : 80≤2*π*x) (N : ℕ) :
    Cvs.Approximant.ConnesErrorColumn.tailColumn x N=rawTailColumn x N-regularizationColumn x N := by
  funext i
  exact connesTail_pairing_eq_raw_sub_beta hx N (Cvs.Approximant.CosineColumnTailPairing.cosineRow N i)

/-- The actual arithmetic matrix column retains both regularization and form-truncation errors. -/
theorem connesColumn_eq_raw_sub_regularization_sub_error {x : ℕ}
    (hx : 80≤2*π*x) (N : ℕ) :
    Cvs.Approximant.CosineColumnTailPairing.connesColumn hx N=
      rawTailColumn x N-regularizationColumn x N-Cvs.Approximant.ConnesErrorColumn.errorColumn hx N := by
  rw [Cvs.Approximant.ConnesErrorColumn.connesColumn_eq_tail_sub_error hx N, tailColumn_eq_raw_sub_regularization hx N]

/-- The complete difference between the actual raw and regularized tail columns has its exponential budget. -/
theorem actual_tail_column_difference_sq_le {x : ℕ} (hx : 80≤2*π*x) (N : ℕ) :
    ∑ i, (rawTailColumn x N i-Cvs.Approximant.ConnesErrorColumn.tailColumn x N i)^2≤
      4*log x*defectBudget (2*π*x)^2*betaGrowthConstant^2 := by
  rw [tailColumn_eq_raw_sub_regularization hx N]
  simpa only [Pi.sub_apply, sub_sub_cancel] using
    regularizationColumn_sq_le_exponential_growth hx N

/-- The actual coefficient-perpendicular correction has the same complete, order-independent budget. -/
theorem actual_centered_tail_column_difference_sq_le {x : ℕ}
    (hx : 80≤2*π*x) (N : ℕ) :
    let α := Cvs.Approximant.ConnesVectorRealScale.connesCoef x N
    ∑ i, (Cvs.Approximant.ConnesErrorColumn.center (rawTailColumn x N) α i-
      Cvs.Approximant.ConnesErrorColumn.center (Cvs.Approximant.ConnesErrorColumn.tailColumn x N) α i)^2≤
        4*log x*defectBudget (2*π*x)^2*betaGrowthConstant^2 := by
  dsimp only
  rw [tailColumn_eq_raw_sub_regularization hx N, Cvs.Approximant.ConnesErrorColumn.center_sub]
  have h : (∑ i, Cvs.Approximant.ConnesErrorColumn.center (regularizationColumn x N) (Cvs.Approximant.ConnesVectorRealScale.connesCoef x N) i^2)≤
      ∑ i, regularizationColumn x N i^2 := by
    simpa only [dotProduct, sq] using
      Cvs.Approximant.ConnesErrorColumn.center_sq_le (regularizationColumn x N) (Cvs.Approximant.ConnesVectorRealScale.connesCoef x N)
  simpa only [Pi.sub_apply, sub_sub_cancel] using
    h.trans (regularizationColumn_sq_le_exponential_growth hx N)

private theorem dot_sub_sq {ι : Type*} [Fintype ι] (R C : ι → ℝ) :
    (R-C) ⬝ᵥ (R-C)=R ⬝ᵥ R+C ⬝ᵥ C-2*(R ⬝ᵥ C) := by
  simp only [sub_dotProduct, dotProduct_sub, dotProduct_comm C R]
  ring

/-- The actual centered residual retains the signed covariance of raw tail, truncation and regularization. -/
theorem connes_residual_eq_raw_regularization_covariance {x : ℕ}
    (hx : 80≤2*π*x) (N : ℕ)
    (hs : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N≠0) :
    let α := Cvs.Approximant.ConnesVectorRealScale.connesCoef x N
    let v := Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x
    let R := Cvs.Approximant.ConnesErrorColumn.center (rawTailColumn x N) α-Cvs.Approximant.ConnesErrorColumn.centeredErrorColumn hx N
    let C := Cvs.Approximant.ConnesErrorColumn.center (regularizationColumn x N) α
    log x^2*(α ⬝ᵥ α)*Cvs.Route.JointGapFromResidual.residualSq x (Nat.clog 2 x) (log x) N v=
      R ⬝ᵥ R+C ⬝ᵥ C-2*(R ⬝ᵥ C) := by
  dsimp only
  rw [Cvs.Approximant.ConnesErrorColumn.connes_residual_eq_tail_error hx N hs,
    tailColumn_eq_raw_sub_regularization hx N, Cvs.Approximant.ConnesErrorColumn.center_sub]
  have he : Cvs.Approximant.ConnesErrorColumn.center (rawTailColumn x N) (Cvs.Approximant.ConnesVectorRealScale.connesCoef x N)-
      Cvs.Approximant.ConnesErrorColumn.center (regularizationColumn x N) (Cvs.Approximant.ConnesVectorRealScale.connesCoef x N)-
        Cvs.Approximant.ConnesErrorColumn.centeredErrorColumn hx N=
      (Cvs.Approximant.ConnesErrorColumn.center (rawTailColumn x N) (Cvs.Approximant.ConnesVectorRealScale.connesCoef x N)-
        Cvs.Approximant.ConnesErrorColumn.centeredErrorColumn hx N)-
          Cvs.Approximant.ConnesErrorColumn.center (regularizationColumn x N) (Cvs.Approximant.ConnesVectorRealScale.connesCoef x N) := by
    funext i
    simp only [Pi.sub_apply]
    ring
  rw [he]
  exact dot_sub_sq _ _

end Cvs.Approximant.SingletonRegularisationColumn
