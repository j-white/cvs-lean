import Mathlib
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.Finite.DiscreteTwoGap
import Cvs.Finite.ModeSumFormDomain
import Cvs.Finite.ModeSumPairValues
import Cvs.Finite.PairFormDividedDifference
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.CouplingRegularisedProfile
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowFormTailLimit
import Cvs.Route.GroundRouteJointGap
import Cvs.Route.JointGapFromResidual
import Cvs.Upstream.SymmetricMatrixBottom
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.BilinearCrossRepresentatives
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.ThetaPairingBilinear
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowReflectionSymmetry
import Cvs.WeilForm.WindowRepresentative
import Cvs.Xi.EImageWindowPoisson

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A finite cosine column as a tail pairing plus its form truncation error

Cosine sums have tame inverse log-scale tests, so the spine tail identity applies to every
finite cosine column and preserves the omitted-series pairing explicitly.
-/

noncomputable section

open Real Set MeasureTheory Matrix
open scoped InnerProductSpace

namespace Cvs.Approximant.CosineColumnTailPairing
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet (Idx mode negI)

/-- A window test pulled back through log scaling. -/
def pullTest (L : ℝ) (g : ℝ → ℝ) : ℝ → ℝ :=
  (Icc (Real.exp (-L)) 1).indicator (fun θ => Real.exp (-Real.log θ / 2) * g (Real.log θ + L))

/-- A continuously differentiable log-window test is tame on its positive compact window. -/
theorem tame_pullTest {L : ℝ} (hL : 0 ≤ L) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) :
    Cvs.L2a.WindowFormTailLimit.Tame (pullTest L g) (Real.exp (-L)) 1 := by
  let a := Real.exp (-L)
  let w : ℝ → ℝ := fun θ => Real.exp (-Real.log θ / 2) * g (Real.log θ + L)
  have ha : 0 < a := Real.exp_pos _
  have ha1 : a ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hw : ContDiffOn ℝ 1 w (Ioi 0) := by
    intro θ hθ
    have hc : ContDiffAt ℝ 1 Real.log θ := Real.contDiffAt_log.mpr (ne_of_gt hθ)
    exact ((((hc.neg.div_const 2).exp).mul
      (hg.contDiffAt.comp θ (hc.add contDiffAt_const))).contDiffWithinAt)
  have hsub : Icc a 1 ⊆ Ioi (0 : ℝ) := fun _ h => ha.trans_le h.1
  have hwc := hw.continuousOn.mono hsub
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hwc
  have hM0 : 0 ≤ M := by
    exact (norm_nonneg _).trans (hM 1 ⟨ha1, le_rfl⟩)
  refine ⟨ha, ?_, ?_, ⟨M, ?_⟩, ?_⟩
  · intro θ hθ
    exact indicator_of_notMem hθ _
  · exact ((Real.measurable_log.neg.div_const 2).exp.mul
      (hg.continuous.measurable.comp (Real.measurable_log.add_const L))).indicator measurableSet_Icc
  · intro θ
    by_cases hθ : θ ∈ Icc a 1
    · simpa only [pullTest, a, indicator_of_mem hθ, Real.norm_eq_abs] using hM θ hθ
    · simpa only [pullTest, a, indicator_of_notMem hθ, abs_zero] using hM0
  · apply Cvs.L2a.WindowFormTailLimit.dec_of_pieces (Finset.univ : Finset Unit) (fun _ => a) (fun _ => 1)
      (fun _ => w) (fun _ => deriv w)
    · intro _ _; exact ha
    · intro _ _; exact hwc
    · intro _ _ θ hθ
      exact ((hw.differentiableOn (by norm_num)) θ (ha.trans hθ.1)).differentiableAt
        (Ioi_mem_nhds (ha.trans hθ.1)) |>.hasDerivAt
    · intro _ _
      exact ((hw.continuousOn_deriv_of_isOpen isOpen_Ioi (le_refl 1)).mono hsub).intervalIntegrable_of_Icc ha1
    · filter_upwards [(countable_singleton (1 : ℝ)).ae_notMem volume] with θ hθ1
      simp only [Finset.univ_unique, Finset.sum_singleton]
      change (Icc a 1).indicator w θ = (Ico a 1).indicator w θ
      by_cases hθ : θ ∈ Icc a 1
      · rw [indicator_of_mem hθ,
          indicator_of_mem (show θ ∈ Ico a 1 from ⟨hθ.1,
            lt_of_le_of_ne hθ.2 (by simpa using hθ1)⟩)]
      · rw [indicator_of_notMem hθ, indicator_of_notMem (fun h : θ ∈ Ico a 1 => hθ ⟨h.1, h.2.le⟩)]

/-- The uncut cosine sum associated with the signed mode coefficients. -/
def cosineSum (L : ℝ) (N : ℕ) (f : Idx N → ℝ) (s : ℝ) : ℝ :=
  ∑ i, f i * Real.cos (Cvs.Finite.TruncationZeroFreeOffAxes.omega L (mode N) i * s)

/-- A finite cosine sum is continuously differentiable on the line. -/
theorem contDiff_cosineSum (L : ℝ) (N : ℕ) (f : Idx N → ℝ) :
    ContDiff ℝ 1 (cosineSum L N f) := by
  unfold cosineSum
  fun_prop

/-- Log scaling of the pulled test is the original function cut to the closed log window. -/
theorem logScale_pullTest (L : ℝ) (g : ℝ → ℝ) (s : ℝ) :
    Cvs.L2a.TailLogScaleTest.logScale (pullTest L g) (s - L) = (Icc (0 : ℝ) L).indicator g s := by
  have hm : Real.exp (s - L) ∈ Icc (Real.exp (-L)) 1 ↔ s ∈ Icc (0 : ℝ) L := by
    simp only [mem_Icc, Real.exp_le_exp, Real.exp_le_one_iff]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  unfold Cvs.L2a.TailLogScaleTest.logScale pullTest
  by_cases hs : s ∈ Icc (0 : ℝ) L
  · rw [indicator_of_mem (hm.mpr hs), indicator_of_mem hs, Real.log_exp, sub_add_cancel]
    have he : Real.exp (-(s - L) / 2) * Real.exp ((s - L) / 2) = 1 := by
      rw [← Real.exp_add, show -(s - L) / 2 + (s - L) / 2 = 0 by ring, Real.exp_zero]
    calc Real.exp (-(s - L) / 2) * g s * Real.exp ((s - L) / 2)
        = (Real.exp (-(s - L) / 2) * Real.exp ((s - L) / 2)) * g s := by ring
      _ = g s := by rw [he, one_mul]
  · rw [indicator_of_notMem (mt hm.mp hs), indicator_of_notMem hs, zero_mul]

/-- The theta-space test corresponding to a finite cosine sum at scale `x`. -/
def modeTest (x : ℕ) (N : ℕ) (f : Idx N → ℝ) : ℝ → ℝ :=
  pullTest (Real.log x) (cosineSum (Real.log x) N f)

/-- Every finite theta-space cosine test is tame on `[1/x,1]`. -/
theorem tame_modeTest {x : ℕ} (hx0 : (0 : ℝ) < x) (N : ℕ) (f : Idx N → ℝ) :
    Cvs.L2a.WindowFormTailLimit.Tame (modeTest x N f) (1 / x) 1 := by
  have h := tame_pullTest (Real.log_natCast_nonneg x) (contDiff_cosineSum (Real.log x) N f)
  simpa only [modeTest, Real.exp_neg, Real.exp_log hx0, one_div] using h

/-- The translated log-scaled theta test agrees almost everywhere with the cut cosine sum. -/
theorem fv_modeTest_ae {x : ℕ} (N : ℕ) (f : Idx N → ℝ) :
    Cvs.Approximant.SpineCouplingTailPairing.fv x (modeTest x N f) =ᵐ[volume] Cvs.Finite.TruncationZeroFreeOffAxes.modeSum (Real.log x) (mode N) f := by
  filter_upwards [(countable_singleton (0 : ℝ)).ae_notMem volume] with s hs0
  rw [Cvs.Approximant.SpineCouplingTailPairing.fv, modeTest, logScale_pullTest]
  unfold Cvs.Finite.TruncationZeroFreeOffAxes.modeSum
  by_cases hs : s ∈ Ioc (0 : ℝ) (Real.log x)
  · rw [ite_eq_left hs, indicator_of_mem (show s ∈ Icc (0 : ℝ) (Real.log x) from ⟨hs.1.le, hs.2⟩)]
    rfl
  · rw [ite_eq_right hs, indicator_of_notMem (fun h : s ∈ Icc (0 : ℝ) (Real.log x) => hs ⟨lt_of_le_of_ne h.1
      (by simpa [eq_comm] using hs0), h.2⟩)]

/-- A finite cosine sum as a class in the continuous form domain. -/
def modeClass {x : ℕ} (hx0 : (0 : ℝ) < x) (N : ℕ) (f : Idx N → ℝ) :
    Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x) :=
  Cvs.Approximant.SpineCouplingTailPairing.wv hx0 (tame_modeTest hx0 N f)

/-- The cosine class represents its cut cosine sum almost everywhere. -/
theorem coe_modeClass_ae {x : ℕ} (hx0 : (0 : ℝ) < x) (N : ℕ) (f : Idx N → ℝ) :
    (((modeClass hx0 N f : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x))
      : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) : Lp ℝ 2 volume)
        =ᵐ[volume] Cvs.Finite.TruncationZeroFreeOffAxes.modeSum (Real.log x) (mode N) f :=
  (Cvs.Approximant.SpineCouplingTailPairing.coe_wv_ae hx0 (tame_modeTest hx0 N f)).trans (fv_modeTest_ae N f)

/-- The coefficient-to-form-domain map is linear. -/
def modeMap {x : ℕ} (hx0 : (0 : ℝ) < x) (N : ℕ) :
    (Idx N → ℝ) →ₗ[ℝ] Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x) where
  toFun := modeClass hx0 N
  map_add' f g := by
    apply Subtype.ext; apply Subtype.ext; apply Lp.ext
    rw [Submodule.coe_add, Submodule.coe_add]
    filter_upwards [coe_modeClass_ae hx0 N (f + g), coe_modeClass_ae hx0 N f,
      coe_modeClass_ae hx0 N g,
      Lp.coeFn_add (E := ℝ) (p := 2) (μ := volume) _ _] with s h1 h2 h3 h4
    rw [h4, Pi.add_apply, h1, h2, h3, Cvs.Finite.DiscreteTwoGap.modeSum_add]
  map_smul' t f := by
    apply Subtype.ext; apply Subtype.ext; apply Lp.ext
    rw [RingHom.id_apply, Submodule.coe_smul, Submodule.coe_smul]
    filter_upwards [coe_modeClass_ae hx0 N (t • f), coe_modeClass_ae hx0 N f,
      Lp.coeFn_smul (E := ℝ) (p := 2) (μ := volume) t
        (((modeClass hx0 N f : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x))
          : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) : Lp ℝ 2 volume)] with s h1 h2 h4
    rw [h4, Pi.smul_apply, h1, h2, Cvs.Finite.ModeSumFormDomain.modeSum_smul, smul_eq_mul]

/-- Every finite cosine class is reflection-even, independently of its signed coefficients. -/
theorem reflD_modeMap {x : ℕ} (hx0 : (0 : ℝ) < x) (N : ℕ) (f : Idx N → ℝ) :
    Cvs.WeilForm.WindowReflectionSymmetry.reflD (Real.log_natCast_nonneg x) (modeMap hx0 N f) = modeMap hx0 N f := by
  apply Subtype.ext; apply Subtype.ext; apply Lp.ext
  let v : Lp ℝ 2 (volume : Measure ℝ) := (modeClass hx0 N f).val.val
  change ((Cvs.WeilForm.WindowReflectionSymmetry.refl (Real.log x) v : Lp ℝ 2 (volume : Measure ℝ)) : ℝ → ℝ)
    =ᵐ[volume] (v : ℝ → ℝ)
  have hc : (v : ℝ → ℝ) =ᵐ[volume] Cvs.Finite.TruncationZeroFreeOffAxes.modeSum (Real.log x) (mode N) f :=
    coe_modeClass_ae hx0 N f
  have hr : (v : ℝ → ℝ) ∘ (fun s => Real.log x - s)
      =ᵐ[volume] Cvs.Finite.TruncationZeroFreeOffAxes.modeSum (Real.log x) (mode N) f ∘ (fun s => Real.log x - s) :=
    (Measure.measurePreserving_sub_left (volume : Measure ℝ) (Real.log x)).quasiMeasurePreserving.ae_eq_comp hc
  have hm := Cvs.Finite.ModeSumFormDomain.reflect_ae_of_window (f := Cvs.Finite.TruncationZeroFreeOffAxes.modeSum (Real.log x) (mode N) f) 1
    (fun s hs => Cvs.Finite.ModeSumPairValues.modeSum_eq_zero_of_notMem (Real.log x) (mode N) f hs)
    (fun s hs => by rw [Cvs.Finite.ModeSumFormDomain.modeSum_reflect (Real.log x) (mode N) f hs, one_mul])
  have hm' : (fun s => Cvs.Finite.TruncationZeroFreeOffAxes.modeSum (Real.log x) (mode N) f (Real.log x - s))
      =ᵐ[volume] Cvs.Finite.TruncationZeroFreeOffAxes.modeSum (Real.log x) (mode N) f := by
    simpa only [one_mul] using hm
  exact ((Cvs.WeilForm.WindowReflectionSymmetry.refl_ae (Real.log x) v).trans hr).trans (hm'.trans hc.symm)

/-- Reflection invariance of the Weil quadratic form polarizes without a positivity assumption. -/
theorem QWbil_reflD {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) (u v : Cvs.WeilForm.FormDomain.formDomain hL) :
    Cvs.WeilForm.SymmetricBilinearForm.QWbil hL P R (Cvs.WeilForm.WindowReflectionSymmetry.reflD hL u) (Cvs.WeilForm.WindowReflectionSymmetry.reflD hL v)
      = Cvs.WeilForm.SymmetricBilinearForm.QWbil hL P R u v := by
  have h := Cvs.WeilForm.WindowReflectionSymmetry.weilQW_reflD hL P R (u + v)
  change Cvs.WeilForm.InfimumAttainedSphere.Q hL P R (Cvs.WeilForm.WindowReflectionSymmetry.reflD hL (u + v)) = Cvs.WeilForm.InfimumAttainedSphere.Q hL P R (u + v) at h
  rw [Cvs.WeilForm.EvenOddSplitForm.reflD_add, ← Cvs.WeilForm.SymmetricBilinearForm.QWbil_self, ← Cvs.WeilForm.SymmetricBilinearForm.QWbil_self] at h
  simp only [map_add, LinearMap.add_apply] at h
  simp only [Cvs.WeilForm.SymmetricBilinearForm.QWbil_self] at h
  have hu := Cvs.WeilForm.WindowReflectionSymmetry.weilQW_reflD hL P R u
  have hv := Cvs.WeilForm.WindowReflectionSymmetry.weilQW_reflD hL P R v
  change Cvs.WeilForm.InfimumAttainedSphere.Q hL P R (Cvs.WeilForm.WindowReflectionSymmetry.reflD hL u) = Cvs.WeilForm.InfimumAttainedSphere.Q hL P R u at hu
  change Cvs.WeilForm.InfimumAttainedSphere.Q hL P R (Cvs.WeilForm.WindowReflectionSymmetry.reflD hL v) = Cvs.WeilForm.InfimumAttainedSphere.Q hL P R v at hv
  rw [hu, hv,
    (Cvs.WeilForm.SymmetricBilinearForm.QWbil_isSymm hL P R).eq (Cvs.WeilForm.WindowReflectionSymmetry.reflD hL v) (Cvs.WeilForm.WindowReflectionSymmetry.reflD hL u),
    (Cvs.WeilForm.SymmetricBilinearForm.QWbil_isSymm hL P R).eq v u] at h
  linarith

/-- Against a finite cosine test the form sees exactly the reflection-even part of a class. -/
theorem QWbil_modeMap_eq_evenPart {x : ℕ} (hx0 : (0 : ℝ) < x) (P R N : ℕ)
    (k : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x)) (f : Idx N → ℝ) :
    Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) P R k (modeMap hx0 N f)
      = Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) P R
        (Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) k) (modeMap hx0 N f) := by
  have h := QWbil_reflD (Real.log_natCast_nonneg x) P R k (modeMap hx0 N f)
  rw [reflD_modeMap] at h
  unfold Cvs.WeilForm.EvenOddSplitForm.evenPart
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, map_add, LinearMap.add_apply]
  rw [h]
  ring

/-- The continuous quadratic form of the cosine class is its exact finite matrix form. -/
theorem Q_modeMap {x : ℕ} (hx0 : (0 : ℝ) < x) (hx1 : (1 : ℝ) < x) (P R N : ℕ)
    (f : Idx N → ℝ) (hfe : ∀ i, f (negI N i) = f i) :
    Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) P R (modeMap hx0 N f)
      = Real.log x * (f ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R (Real.log x) (mode N) *ᵥ f)) := by
  have hQ : Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) P R (modeMap hx0 N f)
      = Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum (Real.log x) (mode N) f) :=
    Cvs.WeilForm.WeilFormOnWindowL2.weilQ_eq (coe_modeClass_ae hx0 N f)
  rw [hQ]
  exact Cvs.Finite.PairFormDividedDifference.weilForm_modeSum_eq_ddMatrix (Real.log_pos hx1) P R (Cvs.Finite.SymmetricModeSet.mode_injective N)
    (Cvs.Finite.SymmetricModeSet.negI_involutive N) (Cvs.Finite.SymmetricModeSet.mode_negI N) hfe

/-- Polarization transfers every even finite cosine column to the continuous form exactly. -/
theorem QWbil_modeMap {x : ℕ} (hx0 : (0 : ℝ) < x) (hx1 : (1 : ℝ) < x) (P R N : ℕ)
    (f g : Idx N → ℝ) (hfe : ∀ i, f (negI N i) = f i) (hge : ∀ i, g (negI N i) = g i) :
    Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) P R (modeMap hx0 N f) (modeMap hx0 N g)
      = Real.log x * (f ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R (Real.log x) (mode N) *ᵥ g)) := by
  have hfg : ∀ i, (f + g) (negI N i) = (f + g) i := by
    intro i; simp only [Pi.add_apply, hfe, hge]
  have h := Cvs.WeilForm.SymmetricBilinearForm.QWbil_self (Real.log_natCast_nonneg x) P R (modeMap hx0 N (f + g))
  rw [Q_modeMap hx0 hx1 P R N (f + g) hfg, map_add] at h
  simp only [map_add, LinearMap.add_apply] at h
  rw [Cvs.WeilForm.SymmetricBilinearForm.QWbil_self, Cvs.WeilForm.SymmetricBilinearForm.QWbil_self,
    (Cvs.WeilForm.SymmetricBilinearForm.QWbil_isSymm (Real.log_natCast_nonneg x) P R).eq (modeMap hx0 N g) (modeMap hx0 N f)] at h
  have hf := Q_modeMap hx0 hx1 P R N f hfe
  have hg := Q_modeMap hx0 hx1 P R N g hge
  have hc := Cvs.Upstream.SymmetricMatrixBottom.dotProduct_mulVec_comm
    (Cvs.Finite.TruncationQuadraticForm.M_symm (Real.log_pos hx1) P R (Cvs.Finite.SymmetricModeSet.mode_injective N)) g f
  rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, hc] at h
  linarith

/-- The Connes spine scale is strictly larger than one. -/
theorem one_lt_of_scale {x : ℕ} (hx : 80 ≤ 2 * π * x) : (1 : ℝ) < x := by
  by_contra h
  have hle : (x : ℝ) ≤ 1 := le_of_not_gt h
  have hx0 : 0 ≤ (x : ℝ) := Nat.cast_nonneg x
  nlinarith [Real.pi_lt_four, Real.pi_pos]

/-- The singleton Connes profile is among the admissible spine profiles. -/
theorem singleton_lt_of_scale {x : ℕ} (hx : 80 ≤ 2 * π * x) : ∀ j ∈ ({1} : Finset ℕ), j < x := by
  intro j hj
  have hj1 : j = 1 := Finset.mem_singleton.mp hj
  subst j
  exact_mod_cast one_lt_of_scale hx

/-- The untruncated Connes test as its continuous form-domain class. -/
def connesClass {x : ℕ} (hx : 80 ≤ 2 * π * x) : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x) :=
  Cvs.Approximant.SpineSubspace.ofFun (Real.log_natCast_nonneg x)
    (Cvs.Approximant.SpineSubspace.kG_memLp hx (singleton_lt_of_scale hx) (fun _ => 1))
    (Cvs.Approximant.SpineSubspace.kG_ae_supp hx (singleton_lt_of_scale hx) (fun _ => 1))
    (Cvs.Approximant.SpineSubspace.kG_levy hx (singleton_lt_of_scale hx) (fun _ => 1))

/-- The Connes class represents the untruncated Connes test almost everywhere. -/
theorem coe_connesClass_ae {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    (((connesClass hx : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x))
      : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) : Lp ℝ 2 volume) =ᵐ[volume] Cvs.Approximant.ConnesVectorRealScale.connesK x := by
  rw [Cvs.Approximant.ConnesVectorRealScale.connesK_natCast]
  exact Cvs.Approximant.SpineSubspace.coe_ofFun_ae (Real.log_natCast_nonneg x) _ _ _

/-- The regularized tail of Connes' singleton spine profile. -/
def connesTail (x : ℕ) : ℝ → ℝ :=
  Cvs.L2a.FullTailConvergence.fullTail (Cvs.L2a.AngularProlateTailPositive.psi (2 * π * x)
    (Cvs.L2a.WindowFormTailLimit.regProfile (2 * π * x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (S := {1}) fun _ => 1)))

/-- Every continuous cosine column of the untruncated Connes test is its negative tail pairing. -/
theorem QWbil_connesClass_modeMap {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ) (f : Idx N → ℝ) :
    Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x)
      (connesClass hx) (modeMap (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N f)
        = -Cvs.WeilForm.ThetaSpaceParseval.weilθ (connesTail x) (modeTest x N f) := by
  have hx0 := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have hx2 : 2 ≤ x := by exact_mod_cast one_lt_of_scale hx
  rw [Cvs.WeilForm.BilinearCrossRepresentatives.QWbil_apply]
  change Cvs.WeilForm.SymmetricBilinearForm.crossW x (Nat.clog 2 x) (Cvs.WeilForm.WindowRepresentative.rep (connesClass hx : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
    (Cvs.WeilForm.WindowRepresentative.rep (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 (tame_modeTest hx0 N f) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))) = _
  rw [Cvs.WeilForm.BilinearCrossRepresentatives.crossW_congr x (Nat.clog 2 x)
    ((Cvs.WeilForm.WindowRepresentative.ae_eq_rep _).symm.trans (coe_connesClass_ae hx))
    ((Cvs.WeilForm.WindowRepresentative.ae_eq_rep _).symm.trans (Cvs.Approximant.SpineCouplingTailPairing.coe_wv_ae hx0 (tame_modeTest hx0 N f)))]
  rw [Cvs.Approximant.ConnesVectorRealScale.connesK_natCast]
  change Cvs.WeilForm.SymmetricBilinearForm.crossW x (Nat.clog 2 x)
    (fun s => Cvs.L2a.TailLogScaleTest.logScale (Cvs.Xi.EImageWindowPoisson.window (2 * π / (2 * π * x))
      (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (S := {1}) fun _ => 1)) (s - Real.log x))
    (fun s => Cvs.L2a.TailLogScaleTest.logScale (modeTest x N f) (s - Real.log x)) = _
  rw [Cvs.WeilForm.BilinearCrossRepresentatives.crossW_translate]
  have hα : 2 * π / (2 * π * x) = 1 / x := by field_simp
  have hF := Cvs.Approximant.SpineSubspace.tame_spine hx (singleton_lt_of_scale hx) (fun _ => 1)
  rw [hα] at hF
  obtain ⟨_, _, hR⟩ := Cvs.Approximant.SpineSubspace.sizes x hx2
  have hP : (1 : ℝ) / (1 / x) ≤ x := by rw [one_div_one_div]
  have hR' : Real.log (1 / (1 / x)) ≤ (Nat.clog 2 x : ℝ) * Real.log 2 := by rwa [one_div_one_div]
  rw [hα, ← Cvs.WeilForm.ThetaPairingBilinear.weilθ_eq_crossW hF (tame_modeTest hx0 N f) hP hR']
  obtain ⟨G₁, G₂, hg, hg₁, hg₂c, heven, hGi⟩ :=
    Cvs.Approximant.SpineCouplingTailPairing.spine_profile_data hx (singleton_lt_of_scale hx) (fun _ => 1)
  have hc : 2 * π ≤ 2 * π * x := by nlinarith [Real.pi_pos, one_lt_of_scale hx]
  have h := Cvs.L2a.CouplingRegularisedProfile.coupling_eq_neg_tail_reg hc hg hg₁ hg₂c heven hGi (tame_modeTest hx0 N f)
  rw [hα] at h
  exact h

/-- The omitted Connes cosine series as a class in the continuous form domain. -/
def connesTruncError {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ) :
    Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x) :=
  connesClass hx - modeMap (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N (Cvs.Approximant.ConnesVectorRealScale.connesCoef x N)

/-- Left subtraction for `QWbil`, stated with the subtraction the form domain elaborates to. -/
private theorem QWbil_sub_left {L : ℝ} (hL : 0 ≤ L) (P R : ℕ)
    (a b c : Cvs.WeilForm.FormDomain.formDomain hL) :
    Cvs.WeilForm.SymmetricBilinearForm.QWbil hL P R (a - b) c
      = Cvs.WeilForm.SymmetricBilinearForm.QWbil hL P R a c
        - Cvs.WeilForm.SymmetricBilinearForm.QWbil hL P R b c :=
  LinearMap.map_sub₂ _ a b c

/-- The actual omitted-series pairing contains no contribution from Connes' reflection-odd part. -/
theorem QWbil_connesTruncError_eq_evenPart {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ)
    (f : Idx N → ℝ) :
    Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x)
      (connesTruncError hx N) (modeMap (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N f)
      = Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x)
        (Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (connesClass hx)
          - modeMap (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N (Cvs.Approximant.ConnesVectorRealScale.connesCoef x N))
        (modeMap (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N f) := by
  unfold connesTruncError
  rw [QWbil_sub_left, QWbil_sub_left]
  rw [QWbil_modeMap_eq_evenPart (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) x (Nat.clog 2 x) N (connesClass hx) f]

/-- The finite Connes column is exactly its tail pairing plus the omitted-series form pairing. -/
theorem connes_column_eq_tail_truncation {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ)
    (f : Idx N → ℝ) (hfe : ∀ i, f (negI N i) = f i) :
    Real.log x * (Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ
      (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x) (mode N) *ᵥ f))
      = -Cvs.WeilForm.ThetaSpaceParseval.weilθ (connesTail x) (modeTest x N f)
        - Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x)
          (connesTruncError hx N) (modeMap (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N f) := by
  have h := QWbil_connesClass_modeMap hx N f
  have he : Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x)
      (connesTruncError hx N) (modeMap (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N f)
      = Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x)
          (connesClass hx) (modeMap (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N f)
        - Real.log x * (Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ
            (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x) (mode N) *ᵥ f)) := by
    unfold connesTruncError
    rw [QWbil_sub_left, QWbil_modeMap (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx)
      (one_lt_of_scale hx) x (Nat.clog 2 x) N _ f (Cvs.Approximant.ConnesVectorRealScale.connesCoef_even x N) hfe]
  linarith

/-- The even coordinate vector testing a signed cosine row. -/
def cosineRow (N : ℕ) (i : Idx N) : Idx N → ℝ :=
  Cvs.Finite.TruncationQuadraticForm.evenPart (negI N) (Pi.single i 1)

/-- A cosine row coefficient vector is even. -/
theorem cosineRow_even (N : ℕ) (i j : Idx N) :
    cosineRow N i (negI N j) = cosineRow N i j :=
  Cvs.Finite.TruncationQuadraticForm.evenPart_even (Cvs.Finite.SymmetricModeSet.negI_involutive N) (Pi.single i 1) j

/-- The Connes matrix column written through its tail and form truncation pairings. -/
def connesColumn {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ) (i : Idx N) : ℝ :=
  -Cvs.WeilForm.ThetaSpaceParseval.weilθ (connesTail x) (modeTest x N (cosineRow N i))
    - Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x)
      (connesTruncError hx N) (modeMap (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N (cosineRow N i))

/-- Each finite arithmetic row is exactly the tail-plus-truncation column divided by the log-window scale. -/
theorem connesColumn_eq_mulVec {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ) (i : Idx N) :
    connesColumn hx N i = Real.log x *
      (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x) (mode N) *ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N) i := by
  have h := connes_column_eq_tail_truncation hx N (cosineRow N i) (cosineRow_even N i)
  have hL : 0 < Real.log x := Real.log_pos (one_lt_of_scale hx)
  have hM := Cvs.Route.GroundRouteJointGap.mulVec_even (Cvs.Finite.SymmetricModeSet.negI_involutive N)
    (Cvs.Finite.TruncationQuadraticForm.M_neg_neg hL x (Nat.clog 2 x) (Cvs.Finite.SymmetricModeSet.mode_injective N) (Cvs.Finite.SymmetricModeSet.mode_negI N))
    (Cvs.Approximant.ConnesVectorRealScale.connesCoef_even x N)
  have he : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ
      (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x) (mode N) *ᵥ cosineRow N i)
      = (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x) (mode N) *ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N) i := by
    rw [Cvs.Upstream.SymmetricMatrixBottom.dotProduct_mulVec_comm
      (Cvs.Finite.TruncationQuadraticForm.M_symm hL x (Nat.clog 2 x) (Cvs.Finite.SymmetricModeSet.mode_injective N))]
    unfold cosineRow
    rw [Cvs.Route.GroundRouteJointGap.evenPart_dotProduct (Cvs.Finite.SymmetricModeSet.negI_involutive N) (Pi.single i 1) hM,
      single_dotProduct, one_mul]
  rw [he] at h
  exact h.symm

/-- The normalized Connes residual is the exact squared centered tail-plus-truncation column. -/
theorem connes_residual_eq_column {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ)
    (hs : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) :
    let α := Cvs.Approximant.ConnesVectorRealScale.connesCoef x N
    let v := Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x
    let q := v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x) (mode N) *ᵥ v)
    Real.log x ^ 2 * (α ⬝ᵥ α) * Cvs.Route.JointGapFromResidual.residualSq x (Nat.clog 2 x) (Real.log x) N v
      = ∑ i, (connesColumn hx N i - Real.log x * q * α i) ^ 2 := by
  dsimp only
  let α := Cvs.Approximant.ConnesVectorRealScale.connesCoef x N
  let v := Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x
  let M := Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x) (mode N)
  let q := v ⬝ᵥ (M *ᵥ v)
  let t := (Real.sqrt (α ⬝ᵥ α))⁻¹
  have hv : v = t • α := by
    simp only [v, Cvs.Approximant.ConnesVectorRealScale.connesVec, ite_eq_right hs]
    rfl
  have ht : t ^ 2 * (α ⬝ᵥ α) = 1 := by
    have hα : 0 ≤ α ⬝ᵥ α := Finset.sum_nonneg fun i _ => mul_self_nonneg _
    dsimp only [t]
    rw [inv_pow, Real.sq_sqrt hα, inv_mul_cancel₀ hs]
  have hr : M *ᵥ v - q • v = t • (M *ᵥ α - q • α) := by
    rw [hv, Matrix.mulVec_smul]
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have he : Cvs.Route.JointGapFromResidual.residualSq x (Nat.clog 2 x) (Real.log x) N v
      = t ^ 2 * ((M *ᵥ α - q • α) ⬝ᵥ (M *ᵥ α - q • α)) := by
    change (M *ᵥ v - q • v) ⬝ᵥ (M *ᵥ v - q • v) = _
    rw [hr, Cvs.Finite.DiscreteTwoGap.dot_smul_self]
  calc Real.log x ^ 2 * (α ⬝ᵥ α) * Cvs.Route.JointGapFromResidual.residualSq x (Nat.clog 2 x) (Real.log x) N v
      = Real.log x ^ 2 * ((M *ᵥ α - q • α) ⬝ᵥ (M *ᵥ α - q • α)) := by
        rw [he]
        calc Real.log x ^ 2 * (α ⬝ᵥ α) *
            (t ^ 2 * ((M *ᵥ α - q • α) ⬝ᵥ (M *ᵥ α - q • α)))
            = Real.log x ^ 2 * (t ^ 2 * (α ⬝ᵥ α)) *
              ((M *ᵥ α - q • α) ⬝ᵥ (M *ᵥ α - q • α)) := by ring
          _ = _ := by rw [ht, mul_one]
    _ = ∑ i, (connesColumn hx N i - Real.log x * q * α i) ^ 2 := by
      rw [dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [connesColumn_eq_mulVec]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      change Real.log x ^ 2 * (((M *ᵥ α) i - q * α i) * ((M *ᵥ α) i - q * α i))
        = (Real.log x * (M *ᵥ α) i - Real.log x * q * α i) ^ 2
      ring

end Cvs.Approximant.CosineColumnTailPairing
