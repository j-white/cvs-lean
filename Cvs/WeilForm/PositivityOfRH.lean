import Mathlib
import Cvs.Finite.OddSectorZeroSide
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.ConcreteTestIdentification
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.Mollify.ComposedApproximant
import Cvs.WeilForm.Mollify.ContinuousApproximation
import Cvs.WeilForm.Mollify.MollifySmooth
import Cvs.WeilForm.Mollify.WindowNormalisation
import Cvs.WeilForm.OddCapTransfer
import Cvs.WeilForm.PrimeSideExplicitIndex
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.WeilFormNullSets
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowConstraintSet
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.ExplicitFormula.CompactTestAdmissibility
import Cvs.Zeta.ExplicitFormula.CompactTestModulusSquared
import Cvs.Zeta.ExplicitFormula.HannWindowShifts
import Cvs.Zeta.ExplicitFormula.QuadraticDecayZeroSide
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.RiemannHypothesisTarget
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZeroInductionIsRH
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.WeilPositivityStatement
import Cvs.Zeta.ZeroSideMoments

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# RH makes the window Weil form nonnegative on the whole form domain

At any complete `(P, R)` the window Weil form of an admissible test is the zero side of its squared
transform (Cvs.Zeta.ExplicitFormula.QuadraticDecayZeroSide, Cvs.WeilForm.PrimeSideExplicitIndex). Under RH that zero side is nonnegative, and `ContinuousApproximation`'s `C²` approximants
carry `0 ≤ Q` to every class of the form domain.
-/

noncomputable section

open MeasureTheory Real Set

namespace Cvs.WeilForm.PositivityOfRH
open Cvs.ZeroCounting

/-- **The zero side is the window Weil form at any complete `(P, R)`**: `e^L ≤ P`, `L ≤ R log 2`,
for a continuous test vanishing at `0` and `L` whose transform is admissible. -/
theorem kernelZeroSide_eq_weilForm_of_complete {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hfc : Continuous f) (h0 : f 0 = 0) (hLz : f L = 0)
    {C0 C2 : ℝ} (hC0 : 0 ≤ C0) (hC2 : 0 ≤ C2)
    (hplain : ∀ ξ : ℂ, |ξ.im| ≤ 3 / 2 →
      ‖Cvs.Detection.windowTransform L (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖ ≤ C0)
    (hquad : ∀ ξ : ℂ, ξ ≠ 0 → |ξ.im| ≤ 3 / 2 →
      ‖Cvs.Detection.windowTransform L (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ‖ ≤ C2 / ‖ξ‖ ^ 2)
    (lam a : ℝ) {P R : ℕ} (hP : Real.exp L ≤ P) (hR : L ≤ R * Real.log 2) :
    kernelZeroSide (Cvs.Detection.sqTransform L (Cvs.WeilForm.SelfConvolutionTransform.cf f)) lam a
      = Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Set.indicator (Set.Ioc (0:ℝ) L) f) := by
  rw [Cvs.Zeta.ExplicitFormula.QuadraticDecayZeroSide.weilForm_eq_kernelZeroSide₂ hL hfc h0 hLz hC0 hC2 hplain hquad lam a,
    Cvs.WeilForm.PrimeSideExplicitIndex.weilForm_eq_range hL.le (Cvs.WeilForm.ConcreteTestIdentification.le_ceil_exp L) (Cvs.WeilForm.ConcreteTestIdentification.le_ceil_log L) f,
    Cvs.WeilForm.PrimeSideExplicitIndex.weilForm_eq_range hL.le hP hR f]

/-- Under RH the zero side of a squared window transform is nonnegative. -/
theorem kernelZeroSide_nonneg_of_RH (hRH : RiemannHypothesis) (L : ℝ) (f : ℝ → ℝ) (lam a : ℝ) :
    0 ≤ kernelZeroSide (Cvs.Detection.sqTransform L (Cvs.WeilForm.SelfConvolutionTransform.cf f)) lam a := by
  have h := Cvs.Zeta.GaussKernel.AdmissibleKernel.riemannHypothesis_iff.mpr hRH
  unfold kernelZeroSide
  refine tsum_nonneg fun rho => ?_
  have hre : (rho : ℂ).re = 1 / 2 := by
    have := Cvs.Criterion.del_eq_zero_of_riemannHypothesis h rho
    unfold Cvs.GaussKernel.del at this
    linarith
  rw [zPoint_of_re_eq_half hre]
  rw [show Cvs.WeilForm.SelfConvolutionTransform.cf f = fun s => ((f s : ℝ) : ℂ) from rfl, Cvs.Detection.sqTransform_real]
  simp only [Complex.ofReal_re]
  positivity

/-- Under RH the window form at any complete `(P, R)`, `e^L ≤ P` and `L ≤ R log 2`, is nonnegative
on `C²` functions supported in `(0, L]`. -/
theorem weilForm_nonneg_of_contDiff_of_RH (hRH : RiemannHypothesis) {L : ℝ} (hL : 0 < L)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hsupp : ∀ s ∉ Set.Ioc (0:ℝ) L, f s = 0)
    {P R : ℕ} (hP : Real.exp L ≤ P) (hR : L ≤ R * Real.log 2) :
    0 ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R f := by
  have hc := hf.continuous
  have h0 : f 0 = 0 := hsupp 0 (by simp)
  have hLz : f L = 0 := by
    have hlim : Filter.Tendsto f (nhdsWithin L (Ioi L)) (nhds (f L)) :=
      hc.continuousAt.continuousWithinAt.tendsto
    have hev : f =ᶠ[nhdsWithin L (Ioi L)] fun _ => 0 :=
      Filter.eventually_of_mem self_mem_nhdsWithin fun s hs => hsupp s fun h => by
        exact absurd h.2 (not_le.2 hs)
    exact tendsto_nhds_unique (hlim.congr' hev) tendsto_const_nhds
  have hind : Set.indicator (Set.Ioc (0:ℝ) L) f = f := by
    funext s; by_cases hs : s ∈ Set.Ioc (0:ℝ) L
    · simp [hs]
    · simp [hs, hsupp s hs]
  have hcs : HasCompactSupport f :=
    HasCompactSupport.intro isCompact_Icc fun s hs => hsupp s fun h => hs (Ioc_subset_Icc_self h)
  have hf2 : ContDiff ℝ (1 + 1) f := by norm_num; exact hf
  have hd := contDiff_succ_iff_deriv.mp hf2
  have hf1 : ContDiff ℝ (0 + 1) (deriv f) := by simpa using hd.2.2
  have hd' := contDiff_succ_iff_deriv.mp hf1
  obtain ⟨M0, hM0⟩ := hc.bounded_above_of_compact_support hcs
  obtain ⟨M2, hM2⟩ := hd'.2.2.continuous.bounded_above_of_compact_support hcs.deriv.deriv
  obtain ⟨C0, C2, hC0, hC2, hplain, hquad⟩ := Cvs.Finite.OddSectorZeroSide.admissible_of_C2 hL
    (fun s => (hd.1 s).hasDerivAt) (fun s => (hd'.1 s).hasDerivAt) hc hd.2.2.continuous
    hd'.2.2.continuous h0 hLz (M0 := M0) (M2 := M2) (fun s => by simpa using hM0 s)
    (fun s => by simpa using hM2 s)
  have hk := kernelZeroSide_eq_weilForm_of_complete hL hc h0 hLz hC0 hC2 hplain hquad 0 0 hP hR
  rw [hind] at hk
  rw [← hk]
  exact kernelZeroSide_nonneg_of_RH hRH L f 0 0

/-- **RH makes the window form nonnegative on the whole form domain**, at any complete
`(P, R)`: `e^L ≤ P` and `L ≤ R log 2`. -/
theorem Q_nonneg_of_RH (hRH : RiemannHypothesis) {L : ℝ} (hL : 0 < L) {P R : ℕ}
    (hP : Real.exp L ≤ P) (hR : L ≤ R * Real.log 2) (φ : Cvs.WeilForm.FormDomain.formDomain hL.le) :
    0 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R φ := by
  by_cases hφ : φ = 0
  · rw [hφ, Cvs.WeilForm.SymmetricBilinearForm.Q_zero]
  set h := Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) with hh
  have hE : 0 < ∫ s, h s ^ 2 := by
    rw [hh, ← Cvs.WeilForm.OddCapTransfer.sq_norm_eq_integral_rep]
    exact pow_pos (norm_pos_iff.mpr fun h0 => hφ (Subtype.ext h0)) 2
  have hmem := Cvs.WeilForm.Mollify.WindowNormalisation.mem_windowSet_normalised (Cvs.WeilForm.WindowRepresentative.memLp_rep _) (Cvs.WeilForm.WindowRepresentative.rep_supp _) φ.2 hE
  obtain ⟨g, hg, hgm, -, hgform⟩ := Cvs.WeilForm.WeilFormNullSets.exists_measurable_rep P R hmem
  obtain ⟨Ξ, hΞ, -, -, hlim, hshape⟩ := Cvs.WeilForm.Mollify.ContinuousApproximation.exists_windowApprox hL P R hg hgm
  have hnn : ∀ n, 0 ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Ξ n) := by
    intro n
    obtain ⟨c, m, hcm⟩ := hshape n
    have hcd : ContDiff ℝ 2 (Ξ n) := by
      rw [hcm]
      exact contDiff_const.mul
        (Cvs.WeilForm.Mollify.MollifySmooth.contDiff_conv (Cvs.WeilForm.Mollify.ComposedApproximant.memLp_shifted hg.1 L m) (Cvs.WeilForm.Mollify.ComposedApproximant.shift_pos hL m))
    exact weilForm_nonneg_of_contDiff_of_RH hRH hL hcd (hΞ n).2.1 hP hR
  have hg0 : 0 ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R g := ge_of_tendsto' hlim hnn
  rw [hgform, Cvs.WeilForm.Mollify.WindowNormalisation.weilForm_normalised P R hE, ← (Cvs.WeilForm.WindowRepresentative.weilQW_rep P R _).1] at hg0
  exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr hE)).mp hg0

end Cvs.WeilForm.PositivityOfRH
