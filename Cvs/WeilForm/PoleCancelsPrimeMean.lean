import Mathlib
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.EvenConnesEnergyFormDomain
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailPolarisation
import Cvs.L2a.TailLogScaleTest
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.CentredWindowTranslate
import Cvs.WeilForm.CubicTailSeparatedKernel
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.PoleTermDilationMean
import Cvs.WeilForm.ThetaFormWindowIdentification
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.Xi.EImageMellin
import Cvs.Xi.EImageWindowPoisson
import Cvs.Xi.EWindowReciprocalContraction
import Cvs.Xi.PhysicalReciprocalReflection

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The pole cancels the continuous prime mean

For actual supported L² profiles, subtracting the continuous dilation mean
from the pole leaves the positive Gram kernel `1/max(θ,η)`.
-/

noncomputable section

open Real Set MeasureTheory Filter

namespace Cvs.WeilForm.PoleCancelsPrimeMean
open Cvs.ZeroCounting

open Cvs.WeilForm.ThetaSpaceParseval (poleP poleM dil weilθ)
open Cvs.WeilForm.PoleTermDilationMean (dilR)

/-- The actual continuous analogue of the two prime orientations. -/
def continuousMean (F : ℝ → ℝ) : ℝ := 2 * ∫ r in Ioi (1 : ℝ), dilR F F r

/-- The surviving physical positive kernel. -/
def greenPair (F : ℝ → ℝ) (p : ℝ × ℝ) : ℝ := F p.1 * F p.2 / max p.1 p.2

/-- The associated positive output energy. -/
def greenEnergy (F : ℝ → ℝ) : ℝ := ∫ p, greenPair F p ∂volume.prod volume

/-- The actual signed prime discrepancy against continuous dilation. -/
def primeDiscrepancy (F : ℝ → ℝ) : ℝ :=
  (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (dil F F n + dil F F n))
    - continuousMean F

private theorem integrable_of_supported {a : ℝ} (ha : 0<a) {F : ℝ → ℝ}
    (hF : MemLp F 2 volume) (hs : ∀ θ ∉ Icc a 1, F θ=0) : Integrable F volume := by
  apply Cvs.WeilForm.CentredWindowTranslate.integrable_of_support zero_le_one hF
  intro θ hθ
  exact hs θ (fun hm => hθ ⟨ha.trans_le hm.1, hm.2⟩)

private theorem supported_lower {a θ : ℝ} {F : ℝ → ℝ}
    (hs : ∀ θ ∉ Icc a 1, F θ=0) (hθ : F θ≠0) : a≤θ := by
  by_contra h
  exact hθ (hs θ (fun hm => h hm.1))

private theorem supported_zero_nonpos {a : ℝ} (ha : 0<a) {F : ℝ → ℝ}
    (hs : ∀ θ ∉ Icc a 1, F θ=0) {θ : ℝ} (hθ : θ≤0) : F θ=0 :=
  hs θ (fun hm => ha.not_ge (hm.1.trans hθ))

/-- The physical Gram feature before integration in the auxiliary variable. -/
def gramFeature (F : ℝ → ℝ) (u θ : ℝ) : ℝ := (Iio u).indicator F θ / u

/-- The actual three-variable Gram product. -/
def gramPair (F : ℝ → ℝ) (q : (ℝ × ℝ) × ℝ) : ℝ :=
  gramFeature F q.2 q.1.1 * gramFeature F q.2 q.1.2

private theorem measurable_gramPair {F : ℝ → ℝ} (hm : Measurable F) : Measurable (gramPair F) := by
  unfold gramPair gramFeature
  apply Measurable.mul
  · apply Measurable.div _ measurable_snd
    apply Measurable.ite (measurableSet_lt (measurable_fst.comp measurable_fst) measurable_snd)
    · exact hm.comp (measurable_fst.comp measurable_fst)
    · exact measurable_const
  · apply Measurable.div _ measurable_snd
    apply Measurable.ite (measurableSet_lt (measurable_snd.comp measurable_fst) measurable_snd)
    · exact hm.comp (measurable_snd.comp measurable_fst)
    · exact measurable_const

/-- Genuine absolute triple integrability precedes the Gram/Fubini passage. -/
theorem integrable_gramPair {a : ℝ} (ha : 0<a) {F : ℝ → ℝ}
    (hm : Measurable F) (hi : Integrable F volume) :
    Integrable (gramPair F) ((volume.prod volume).prod (volume.restrict (Ioi a))) := by
  have hmaj := (hi.norm.mul_prod hi.norm).mul_prod (Cvs.L2a.FullTailConvergence.integrableOn_one_div_sq ha)
  refine hmaj.mono' (measurable_gramPair hm).aestronglyMeasurable ?_
  have hae : ∀ᵐ (q : (ℝ × ℝ) × ℝ) ∂((volume.prod volume).prod (volume.restrict (Ioi a))), a < q.2 :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const measurable_snd)).2
      (ae_of_all _ fun _ => ae_restrict_mem measurableSet_Ioi)
  filter_upwards [hae] with q hq
  change a<q.2 at hq
  have hu : 0<q.2 := ha.trans hq
  unfold gramPair gramFeature
  by_cases hθ : q.1.1∈Iio q.2 <;> by_cases hη : q.1.2∈Iio q.2
  · simp only [indicator_of_mem hθ, indicator_of_mem hη, norm_mul, norm_div,
      Real.norm_eq_abs, abs_of_pos hu]
    have he : |F q.1.1| / q.2 * (|F q.1.2| / q.2) =
      (|F q.1.1| * |F q.1.2|) * (1/q.2^2) := by ring
    exact he.le
  all_goals simp [hθ, hη]
  all_goals positivity

/-- Integrating each actual Gram feature product gives exactly `1/max`. -/
theorem integral_gramPair_fiber {a : ℝ} (ha : 0<a) {F : ℝ → ℝ}
    (hs : ∀ θ ∉ Icc a 1, F θ=0) (p : ℝ × ℝ) :
    (∫ u in Ioi a, gramPair F (p,u)) = greenPair F p := by
  by_cases hθ : F p.1=0
  · simp only [gramPair, gramFeature, greenPair]
    have he : ∀ u, (Iio u).indicator F p.1=0 := fun u => by
      by_cases h : p.1∈Iio u <;> simp [h, hθ]
    simp only [he, hθ, zero_div, zero_mul, integral_zero]
  by_cases hη : F p.2=0
  · simp only [gramPair, gramFeature, greenPair]
    have he : ∀ u, (Iio u).indicator F p.2=0 := fun u => by
      by_cases h : p.2∈Iio u <;> simp [h, hη]
    simp only [he, hη, zero_div, mul_zero, integral_zero]
  have hl : a ≤ max p.1 p.2 := (supported_lower hs hθ).trans (le_max_left _ _)
  have hp : 0 < max p.1 p.2 := ha.trans_le hl
  have he : (fun u => gramPair F (p,u)) = (Ioi (max p.1 p.2)).indicator
      (fun u => (F p.1*F p.2)*(1/u^2)) := by
    funext u
    unfold gramPair gramFeature
    by_cases h : max p.1 p.2<u
    · rw [indicator_of_mem (show u ∈ Ioi (max p.1 p.2) from h), indicator_of_mem (show p.1∈Iio u from (le_max_left _ _).trans_lt h),
        indicator_of_mem (show p.2∈Iio u from (le_max_right _ _).trans_lt h)]
      ring
    · rw [indicator_of_notMem (show u ∉ Ioi (max p.1 p.2) from h)]
      by_cases h1 : p.1<u
      · have h2 : ¬p.2<u := fun h2 => h (max_lt h1 h2)
        simp only [indicator_of_notMem (show p.2 ∉ Iio u from h2), zero_div, mul_zero]
      · simp only [indicator_of_notMem (show p.1 ∉ Iio u from h1), zero_div, zero_mul]
  rw [he, integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
  have hi : Ioi (max p.1 p.2) ∩ Ioi a = Ioi (max p.1 p.2) :=
    inter_eq_left.mpr (fun u hu => hl.trans_lt hu)
  rw [hi, integral_const_mul, Cvs.L2a.FullTailConvergence.integral_one_div_sq hp]
  unfold greenPair
  ring

/-- The positive physical kernel is genuinely jointly integrable. -/
theorem integrable_greenPair {a : ℝ} (ha : 0<a) {F : ℝ → ℝ}
    (hm : Measurable F) (hF : MemLp F 2 volume) (hs : ∀ θ ∉ Icc a 1, F θ=0) :
    Integrable (greenPair F) (volume.prod volume) := by
  have hi := integrable_of_supported ha hF hs
  exact (integrable_gramPair ha hm hi).integral_prod_left.congr
    (ae_of_all _ fun p => integral_gramPair_fiber ha hs p)

/-- The exact output energy is an actual integral of squares of its cumulative profile. -/
theorem greenEnergy_eq_gram {a : ℝ} (ha : 0<a) {F : ℝ → ℝ}
    (hm : Measurable F) (hF : MemLp F 2 volume) (hs : ∀ θ ∉ Icc a 1, F θ=0) :
    greenEnergy F = ∫ u in Ioi a, (∫ θ, gramFeature F u θ)^2 := by
  have hi := integrable_gramPair ha hm (integrable_of_supported ha hF hs)
  unfold greenEnergy
  calc
    _ = ∫ p, (∫ u in Ioi a, gramPair F (p,u)) ∂volume.prod volume := by
      apply integral_congr_ae
      exact ae_of_all _ fun p => (integral_gramPair_fiber ha hs p).symm
    _ = ∫ u in Ioi a, ∫ p, gramPair F (p,u) ∂volume.prod volume :=
      integral_integral_swap (show Integrable
        (Function.uncurry (fun p u => gramPair F (p,u))) _ from hi)
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u _
      change (∫ p, gramFeature F u p.1*gramFeature F u p.2 ∂volume.prod volume) = _
      rw [integral_prod_mul]
      ring

/-- Positivity comes from the actual Gram identity, not a prime-sign premise. -/
theorem greenEnergy_nonneg {a : ℝ} (ha : 0<a) {F : ℝ → ℝ}
    (hm : Measurable F) (hF : MemLp F 2 volume) (hs : ∀ θ ∉ Icc a 1, F θ=0) :
    0≤greenEnergy F := by
  rw [greenEnergy_eq_gram ha hm hF hs]
  exact integral_nonneg fun _ => sq_nonneg _

/-- The upper physical triangle whose integral is the one-sided continuous mean. -/
def meanTriangle (F : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  if p.1<p.2 then F p.1*F p.2/p.1 else 0

private theorem measurable_meanTriangle {F : ℝ → ℝ} (hm : Measurable F) :
    Measurable (meanTriangle F) := by
  unfold meanTriangle
  apply Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
  · exact ((hm.comp measurable_fst).mul (hm.comp measurable_snd)).div measurable_fst
  · exact measurable_const

/-- The upper-triangle mean pairing is genuinely absolutely integrable. -/
theorem integrable_meanTriangle {a : ℝ} (ha : 0<a) {F : ℝ → ℝ}
    (hm : Measurable F) (hF : MemLp F 2 volume) (hs : ∀ θ ∉ Icc a 1, F θ=0) :
    Integrable (meanTriangle F) (volume.prod volume) := by
  have hi := integrable_of_supported ha hF hs
  refine ((hi.norm.mul_prod hi.norm).const_mul (1/a)).mono'
    (measurable_meanTriangle hm).aestronglyMeasurable (ae_of_all _ fun p => ?_)
  unfold meanTriangle
  by_cases h : p.1<p.2
  · rw [if_pos h]
    by_cases hθ : F p.1=0
    · simp [hθ]
    have haθ := supported_lower hs hθ
    have hθ0 : 0<p.1 := ha.trans_le haθ
    simp only [norm_div, norm_mul, Real.norm_eq_abs, abs_of_pos hθ0]
    calc
      _ ≤ |F p.1| * |F p.2|/a := div_le_div_of_nonneg_left (by positivity) ha haθ
      _ = _ := by ring
  · rw [if_neg h, norm_zero]
    positivity

/-- The original mean integrand in dilation coordinates. -/
def meanDilationPair (F : ℝ → ℝ) (p : ℝ × ℝ) : ℝ := F p.2*F (p.1*p.2)

private theorem integral_norm_mean_fiber {θ : ℝ} (hθ : 0<θ) (F : ℝ → ℝ) :
    (∫ r in Ioi (1 : ℝ), ‖meanDilationPair F (r,θ)‖)
      = |F θ|/θ * ∫ η in Ioi θ, |F η| := by
  have he : (∫ r in Ioi (1 : ℝ), ‖meanDilationPair F (r,θ)‖) =
      ∫ r in Ioi (1 : ℝ), |F θ| * |F (θ*r)| := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r _
    simp only [meanDilationPair, Real.norm_eq_abs, abs_mul, mul_comm r θ]
  rw [he, integral_const_mul, integral_comp_mul_left_Ioi (fun η => |F η|) 1 hθ]
  simp only [smul_eq_mul, mul_one]
  ring

/-- Genuine product integrability of continuous physical dilation on compact L² support. -/
theorem integrable_meanDilationPair {a : ℝ} (ha : 0<a) {F : ℝ → ℝ}
    (hm : Measurable F) (hF : MemLp F 2 volume) (hs : ∀ θ ∉ Icc a 1, F θ=0) :
    Integrable (meanDilationPair F)
      ((volume.restrict (Ioi (1 : ℝ))).prod Cvs.WeilForm.CubicTailSeparatedKernel.positiveVolume) := by
  have hi := integrable_of_supported ha hF hs
  have hmp : Measurable (meanDilationPair F) :=
    (hm.comp measurable_snd).mul (hm.comp (measurable_fst.mul measurable_snd))
  apply (integrable_prod_iff' hmp.aestronglyMeasurable).mpr
  constructor
  · apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro θ hθ
    have hc := (integrableOn_Ioi_comp_mul_left_iff F 1 hθ).mpr hi.restrict
    refine IntegrableOn.congr_fun (hc.const_mul (F θ)) (fun r _ => ?_) measurableSet_Ioi
    simp only [meanDilationPair, mul_comm r θ]
  · have hmeas : AEStronglyMeasurable
        (fun θ => ∫ r in Ioi (1 : ℝ), ‖meanDilationPair F (r,θ)‖) Cvs.WeilForm.CubicTailSeparatedKernel.positiveVolume :=
      (hmp.comp measurable_swap).norm.aestronglyMeasurable.integral_prod_right'
    refine ((hi.norm.const_mul ((∫ η, |F η|)/a)).restrict).mono' hmeas ?_
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro θ hθ
    change 0 < θ at hθ
    rw [integral_norm_mean_fiber hθ F]
    simp only [Real.norm_eq_abs]
    have hnn : 0≤∫ η, |F η| := integral_nonneg fun _ => abs_nonneg _
    have hcut : (∫ η in Ioi θ, |F η|) ≤ ∫ η, |F η| :=
      integral_mono_measure Measure.restrict_le_self (ae_of_all _ fun _ => abs_nonneg _) hi.abs
    by_cases hzero : F θ=0
    · simp [hzero]
    have haθ := supported_lower hs hzero
    rw [abs_of_nonneg (mul_nonneg (div_nonneg (abs_nonneg _) hθ.le)
      (integral_nonneg fun _ => abs_nonneg _))]
    calc
      _ ≤ |F θ|/θ * ∫ η, |F η| := mul_le_mul_of_nonneg_left hcut (by positivity)
      _ ≤ |F θ|/a * ∫ η, |F η| :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (abs_nonneg _) ha haθ) hnn
      _ = _ := by ring

/-- The signed continuous mean fibre is the exact physical upper triangle. -/
theorem integral_mean_fiber {θ : ℝ} (hθ : 0<θ) (F : ℝ → ℝ) :
    (∫ r in Ioi (1 : ℝ), meanDilationPair F (r,θ)) = ∫ η, meanTriangle F (θ,η) := by
  have he : (∫ r in Ioi (1 : ℝ), meanDilationPair F (r,θ)) =
      ∫ r in Ioi (1 : ℝ), F θ*F (θ*r) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r _
    simp only [meanDilationPair, mul_comm r θ]
  rw [he, integral_const_mul, integral_comp_mul_left_Ioi F 1 hθ]
  simp only [smul_eq_mul, mul_one]
  have htri : (fun η => meanTriangle F (θ,η)) =
      (Ioi θ).indicator (fun η => (F θ/θ)*F η) := by
    funext η
    simp only [meanTriangle, indicator, mem_Ioi]
    split_ifs <;> ring
  rw [htri, integral_indicator measurableSet_Ioi, integral_const_mul]
  ring

/-- The actual continuous dilation mean equals twice the genuine upper-triangle integral. -/
theorem continuousMean_eq_triangle {a : ℝ} (ha : 0<a) {F : ℝ → ℝ}
    (hm : Measurable F) (hF : MemLp F 2 volume) (hs : ∀ θ ∉ Icc a 1, F θ=0) :
    continuousMean F = 2 * ∫ p, meanTriangle F p ∂volume.prod volume := by
  unfold continuousMean dilR
  congr 1
  have hi := integrable_meanDilationPair ha hm hF hs
  have hi' : Integrable (Function.uncurry (fun r θ => meanDilationPair F (r,θ)))
      ((volume.restrict (Ioi (1 : ℝ))).prod Cvs.WeilForm.CubicTailSeparatedKernel.positiveVolume) := hi
  change (∫ r in Ioi (1 : ℝ), ∫ θ in Ioi (0 : ℝ), meanDilationPair F (r,θ)) = _
  rw [integral_integral_swap hi', integral_prod _ (integrable_meanTriangle ha hm hF hs)]
  have hz : ∀ θ, θ∉Ioi (0 : ℝ) → (∫ η, meanTriangle F (θ,η))=0 := by
    intro θ hθ
    have ht : θ≤0 := by simpa only [mem_Ioi, not_lt] using hθ
    apply integral_eq_zero_of_ae
    filter_upwards [] with η
    simp only [meanTriangle, supported_zero_nonpos ha hs ht, zero_mul, zero_div, ite_self, Pi.zero_apply]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  exact setIntegral_congr_fun measurableSet_Ioi (fun θ hθ => integral_mean_fiber hθ F)

/-- The physical reciprocal pole integrand is genuinely integrable. -/
theorem integrable_div_supported {a : ℝ} (ha : 0<a) {F : ℝ → ℝ}
    (hm : Measurable F) (hF : MemLp F 2 volume) (hs : ∀ θ ∉ Icc a 1, F θ=0) :
    Integrable (fun θ => F θ/θ) volume := by
  have hi := integrable_of_supported ha hF hs
  refine (hi.norm.const_mul (1/a)).mono' (hm.div measurable_id).aestronglyMeasurable
    (ae_of_all _ fun θ => ?_)
  by_cases h : F θ=0
  · simp [h]
  have ht : 0<θ := ha.trans_le (supported_lower hs h)
  simp only [norm_div, Real.norm_eq_abs, abs_of_pos ht]
  calc
    _ ≤ |F θ|/a := div_le_div_of_nonneg_left (abs_nonneg _) ha (supported_lower hs h)
    _ = _ := by ring

/-- The symmetrized physical pole kernel. -/
def polePair (F : ℝ → ℝ) (p : ℝ × ℝ) : ℝ := F p.1*F p.2/p.1 + F p.1*F p.2/p.2

private theorem integrable_polePair {a : ℝ} (ha : 0<a) {F : ℝ → ℝ}
    (hm : Measurable F) (hF : MemLp F 2 volume) (hs : ∀ θ ∉ Icc a 1, F θ=0) :
    Integrable (polePair F) (volume.prod volume) := by
  have hi := integrable_of_supported ha hF hs
  have hd := integrable_div_supported ha hm hF hs
  refine ((hd.mul_prod hi).add (hi.mul_prod hd)).congr (ae_of_all _ fun p => ?_)
  simp only [Pi.add_apply]
  unfold polePair
  ring

/-- The full pole is exactly the integrated symmetrized kernel, with both orientations. -/
theorem integral_polePair {a : ℝ} (ha : 0<a) {F : ℝ → ℝ}
    (hm : Measurable F) (hF : MemLp F 2 volume) (hs : ∀ θ ∉ Icc a 1, F θ=0) :
    (∫ p, polePair F p ∂volume.prod volume) = 2*poleP F*poleM F := by
  have hi := integrable_of_supported ha hF hs
  have hd := integrable_div_supported ha hm hF hs
  have hp : (∫ θ, F θ) = poleP F := by
    rw [Cvs.WeilForm.ThetaFormWindowIdentification.poleP_eq_integral hs]
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro θ hθ
    exact supported_zero_nonpos ha hs (by simpa only [mem_Ioi, not_lt] using hθ)
  have hm' : (∫ θ, F θ/θ) = poleM F := by
    unfold poleM
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro θ hθ
    rw [supported_zero_nonpos ha hs (by simpa only [mem_Ioi, not_lt] using hθ), zero_div]
  have he : polePair F = (fun p : ℝ × ℝ => (F p.1/p.1)*F p.2) +
      (fun p : ℝ × ℝ => F p.1*(F p.2/p.2)) := by
    funext p
    unfold polePair
    simp only [Pi.add_apply]
    ring
  rw [he]
  simp only [Pi.add_apply]
  rw [integral_add (hd.mul_prod hi) (hi.mul_prod hd),
    integral_prod_mul (fun θ => F θ/θ) F,
    integral_prod_mul F (fun θ => F θ/θ), hp, hm']
  ring

/-- The pole minus the two continuous triangles is exactly the surviving Green kernel. -/
theorem polePair_sub_triangles_ae (F : ℝ → ℝ) :
    (fun p : ℝ × ℝ => polePair F p-meanTriangle F p-meanTriangle F p.swap)
      =ᵐ[volume.prod volume] greenPair F := by
  have hdiag : ∀ᵐ p : ℝ × ℝ ∂volume.prod volume, p.1≠p.2 :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun measurable_fst measurable_snd).compl).2
      (ae_of_all _ fun θ => (volume.ae_ne θ).mono fun η hη => Ne.symm hη)
  filter_upwards [hdiag] with p hp
  rcases lt_or_gt_of_ne hp with h | h
  · simp only [polePair, meanTriangle, greenPair, if_pos h, if_neg (not_lt.mpr h.le),
      max_eq_right h.le, Prod.swap]
    ring
  · simp only [polePair, meanTriangle, greenPair, if_neg (not_lt.mpr h.le), if_pos h,
      max_eq_left h.le, Prod.swap]
    ring

/-- Exact aggregate pole/continuous-mean cancellation for actual supported physical L² profiles. -/
theorem pole_sub_continuousMean_eq_green {a : ℝ} (ha : 0<a) {F : ℝ → ℝ}
    (hm : Measurable F) (hF : MemLp F 2 volume) (hs : ∀ θ ∉ Icc a 1, F θ=0) :
    2*poleP F*poleM F-continuousMean F = greenEnergy F := by
  have hp := integrable_polePair ha hm hF hs
  have ht := integrable_meanTriangle ha hm hF hs
  unfold greenEnergy
  rw [← integral_congr_ae (polePair_sub_triangles_ae F)]
  have hs1 : (∫ p, polePair F p-meanTriangle F p-meanTriangle F p.swap ∂volume.prod volume) =
      (∫ p, polePair F p-meanTriangle F p ∂volume.prod volume) -
        ∫ p, meanTriangle F p.swap ∂volume.prod volume := by
    simpa only [Pi.sub_apply, Function.comp_apply] using integral_sub (hp.sub ht) ht.swap
  rw [hs1, integral_sub hp ht, integral_polePair ha hm hF hs,
    integral_prod_swap (meanTriangle F)]
  rw [continuousMean_eq_triangle ha hm hF hs]
  ring

/-- The actual aggregate pole channel dominates the continuous mean, regardless of signs of F. -/
theorem continuousMean_le_pole {a : ℝ} (ha : 0<a) {F : ℝ → ℝ}
    (hm : Measurable F) (hF : MemLp F 2 volume) (hs : ∀ θ ∉ Icc a 1, F θ=0) :
    continuousMean F≤2*poleP F*poleM F := by
  have h := greenEnergy_nonneg ha hm hF hs
  rw [← pole_sub_continuousMean_eq_green ha hm hF hs] at h
  linarith

/-- The angular Weil expression retains the signed aggregate cancellation. -/
theorem weilθ_eq_arch_green_sub_discrepancy {a : ℝ} (ha : 0<a) {F : ℝ → ℝ}
    (hm : Measurable F) (hF : MemLp F 2 volume) (hs : ∀ θ ∉ Icc a 1, F θ=0) :
    weilθ F F = (∫ t, Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t*Cvs.L2a.FullTailPolarisation.crossSpec (Cvs.L2a.TailLogScaleTest.logScale F) (Cvs.L2a.TailLogScaleTest.logScale F) t)
      + greenEnergy F-primeDiscrepancy F := by
  have h := pole_sub_continuousMean_eq_green ha hm hF hs
  unfold weilθ primeDiscrepancy
  linarith

/-- The angular expression has a lower bound leaving the signed arithmetic discrepancy. -/
theorem weilθ_ge_arch_sub_discrepancy {a : ℝ} (ha : 0<a) {F : ℝ → ℝ}
    (hm : Measurable F) (hF : MemLp F 2 volume) (hs : ∀ θ ∉ Icc a 1, F θ=0) :
    (∫ t, Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t*Cvs.L2a.FullTailPolarisation.crossSpec (Cvs.L2a.TailLogScaleTest.logScale F) (Cvs.L2a.TailLogScaleTest.logScale F) t)
      - primeDiscrepancy F≤weilθ F F := by
  rw [weilθ_eq_arch_green_sub_discrepancy ha hm hF hs]
  linarith [greenEnergy_nonneg ha hm hF hs]

/-- The exact Connes representative is measurable, including its reciprocal average. -/
theorem measurable_connesAngularEven {x : ℝ} (hx : 0 < x) :
    Measurable (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) := by
  let G := Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (S := {1}) fun _ => 1
  have hGc : ContinuousOn G (Icc 0 1) :=
    (Cvs.Approximant.ConnesVectorRealScale.continuousOn_spineG _ _).mono (Icc_subset_Icc (by norm_num) le_rfl)
  have hm : Measurable (Cvs.Xi.EImageWindowPoisson.window (1 / x) G) :=
    (Cvs.Xi.EImageMellin.measurable_eimage_of_continuousOn (one_div_pos.mpr hx) hGc).indicator
      measurableSet_Icc
  have hr : Measurable (Cvs.Xi.PhysicalReciprocalReflection.reciprocal (1 / x) (Cvs.Xi.EImageWindowPoisson.window (1 / x) G)) := by
    unfold Cvs.Xi.PhysicalReciprocalReflection.reciprocal Cvs.Xi.EWindowReciprocalContraction.branch
    exact (((measurable_const.div measurable_id).mul
      (hm.comp (measurable_const.div measurable_id))).indicator measurableSet_Icc).div_const _
  unfold Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven Cvs.Xi.PhysicalReciprocalReflection.evenPhysical Cvs.Xi.PhysicalReciprocalReflection.cut
  exact ((hm.indicator measurableSet_Icc).add hr).div_const _

/-- For the actual Connes profile the discrepancy is a finite signed sum. -/
theorem primeDiscrepancy_connesAngularEven_eq_sum {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    primeDiscrepancy (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) =
      (∑ n ∈ Finset.range (x+1), (ArithmeticFunction.vonMangoldt n : ℝ) *
        (dil (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) n +
          dil (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) n)) -
        continuousMean (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) := by
  unfold primeDiscrepancy
  rw [Cvs.Approximant.EvenConnesEnergyFormDomain.prime_connesAngularEven_eq_sum hx]

/-- The proved closed Connes form has the exact pole/mean Green-kernel decomposition. -/
theorem Q_even_connesClass_eq_arch_green_sub_discrepancy {x : ℕ}
    (hx : 80 ≤ 2 * π * x) :
    Cvs.WeilForm.InfimumAttainedSphere.Q (log_natCast_nonneg x) x (Nat.clog 2 x)
      (Cvs.WeilForm.EvenOddSplitForm.evenPart (log_natCast_nonneg x) (Cvs.Approximant.CosineColumnTailPairing.connesClass hx)) =
      (∫ t, Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t * Cvs.L2a.FullTailPolarisation.crossSpec
        (Cvs.L2a.TailLogScaleTest.logScale (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x))
        (Cvs.L2a.TailLogScaleTest.logScale (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x)) t) +
      greenEnergy (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) -
        primeDiscrepancy (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) := by
  rw [Cvs.Approximant.EvenConnesEnergyFormDomain.Q_even_connesClass_eq_weilθ hx]
  have hx0 := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  exact weilθ_eq_arch_green_sub_discrepancy (one_div_pos.mpr hx0)
    (measurable_connesAngularEven hx0) (Cvs.Xi.PhysicalReciprocalReflection.memLp_connesAngularEven hx0)
    (Cvs.Approximant.EvenConnesEnergyFormDomain.connesAngularEven_support x)

/-- An unconditional lower bound on the actual closed Connes form retains the signed discrepancy. -/
theorem Q_even_connesClass_ge_arch_sub_discrepancy {x : ℕ}
    (hx : 80 ≤ 2 * π * x) :
    (∫ t, Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t * Cvs.L2a.FullTailPolarisation.crossSpec
      (Cvs.L2a.TailLogScaleTest.logScale (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x))
      (Cvs.L2a.TailLogScaleTest.logScale (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x)) t) -
      primeDiscrepancy (Cvs.Xi.PhysicalReciprocalReflection.connesAngularEven x) ≤
    Cvs.WeilForm.InfimumAttainedSphere.Q (log_natCast_nonneg x) x (Nat.clog 2 x)
      (Cvs.WeilForm.EvenOddSplitForm.evenPart (log_natCast_nonneg x) (Cvs.Approximant.CosineColumnTailPairing.connesClass hx)) := by
  rw [Cvs.Approximant.EvenConnesEnergyFormDomain.Q_even_connesClass_eq_weilθ hx]
  have hx0 := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  exact weilθ_ge_arch_sub_discrepancy (one_div_pos.mpr hx0)
    (measurable_connesAngularEven hx0) (Cvs.Xi.PhysicalReciprocalReflection.memLp_connesAngularEven hx0)
    (Cvs.Approximant.EvenConnesEnergyFormDomain.connesAngularEven_support x)

end Cvs.WeilForm.PoleCancelsPrimeMean
