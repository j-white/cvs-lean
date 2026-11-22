import Mathlib
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.LevyDomainSpectral
import Cvs.WeilForm.PoleAndPrimeContinuousWindow
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.WeilFormAeClass
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-!
# The parallelogram law for the Weil form on its domain

    `weilQW (φ + ψ) + weilQW (φ − ψ) = 2 weilQW φ + 2 weilQW ψ`

because every term of the form is quadratic in the representative.
-/

noncomputable section

open MeasureTheory Set Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.ParallelogramLaw

/-- The self-convolution is insensitive to null sets. -/
theorem selfConvolution_congr_ae {f g : ℝ → ℝ} (h : f =ᵐ[volume] g) (u : ℝ) :
    selfConvolution f u = selfConvolution g u := by
  unfold selfConvolution
  refine integral_congr_ae ?_
  have h' := (measurePreserving_add_right volume u).quasiMeasurePreserving.ae_eq_comp h
  filter_upwards [h, h'] with s hs1 hs2
  rw [hs1]
  exact congrArg _ hs2

/-- Two window representatives multiply to an integrable function, with a shift. -/
theorem integrable_cross {L : ℝ} (φ ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L) (u : ℝ) :
    Integrable fun s => Cvs.WeilForm.WindowRepresentative.rep φ s * Cvs.WeilForm.WindowRepresentative.rep ψ (s + u) :=
  (Cvs.WeilForm.WindowRepresentative.memLp_rep φ).integrable_mul
    ((Cvs.WeilForm.WindowRepresentative.memLp_rep ψ).comp_measurePreserving
      (measurePreserving_add_right volume u))

/-- **The self-convolution obeys the parallelogram law.** -/
theorem selfConvolution_add_sub {L : ℝ} (φ ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L) (u : ℝ) :
    selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ + Cvs.WeilForm.WindowRepresentative.rep ψ) u
        + selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ - Cvs.WeilForm.WindowRepresentative.rep ψ) u
      = 2 * selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ) u
        + 2 * selfConvolution (Cvs.WeilForm.WindowRepresentative.rep ψ) u := by
  unfold selfConvolution
  have hff := integrable_cross φ φ u
  have hfh := integrable_cross φ ψ u
  have hhf := integrable_cross ψ φ u
  have hhh := integrable_cross ψ ψ u
  have h1 : Integrable fun s => (Cvs.WeilForm.WindowRepresentative.rep φ + Cvs.WeilForm.WindowRepresentative.rep ψ) s
      * (Cvs.WeilForm.WindowRepresentative.rep φ + Cvs.WeilForm.WindowRepresentative.rep ψ) (s + u) := by
    refine (((hff.add hfh).add hhf).add hhh).congr (Filter.Eventually.of_forall fun s => ?_)
    simp only [Pi.add_apply]; ring
  have h2 : Integrable fun s => (Cvs.WeilForm.WindowRepresentative.rep φ - Cvs.WeilForm.WindowRepresentative.rep ψ) s
      * (Cvs.WeilForm.WindowRepresentative.rep φ - Cvs.WeilForm.WindowRepresentative.rep ψ) (s + u) := by
    refine (((hff.sub hfh).sub hhf).add hhh).congr (Filter.Eventually.of_forall fun s => ?_)
    simp only [Pi.add_apply, Pi.sub_apply]; ring
  rw [← integral_add h1 h2, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hff.const_mul 2) (hhh.const_mul 2)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only [Pi.add_apply, Pi.sub_apply]; ring

/-- The pole functionals are linear. -/
theorem integral_add_mul_exp {L : ℝ} (hL : 0 ≤ L) (φ ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L)
    {w : ℝ → ℝ} (hw : Continuous w) {M : ℝ} (hM : ∀ s ∈ Icc (0:ℝ) L, |w s| ≤ M) :
    (∫ s, (Cvs.WeilForm.WindowRepresentative.rep φ + Cvs.WeilForm.WindowRepresentative.rep ψ) s * w s)
        = (∫ s, Cvs.WeilForm.WindowRepresentative.rep φ s * w s) + ∫ s, Cvs.WeilForm.WindowRepresentative.rep ψ s * w s ∧
    (∫ s, (Cvs.WeilForm.WindowRepresentative.rep φ - Cvs.WeilForm.WindowRepresentative.rep ψ) s * w s)
        = (∫ s, Cvs.WeilForm.WindowRepresentative.rep φ s * w s) - ∫ s, Cvs.WeilForm.WindowRepresentative.rep ψ s * w s := by
  have h1 := Cvs.WeilForm.PoleAndPrimeContinuousWindow.integrable_rep_mul hL φ hw hM
  have h2 := Cvs.WeilForm.PoleAndPrimeContinuousWindow.integrable_rep_mul hL ψ hw hM
  constructor
  · rw [← integral_add h1 h2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [Pi.add_apply]; ring
  · rw [← integral_sub h1 h2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [Pi.sub_apply]; ring

/-- The prime sum obeys the parallelogram law, termwise. -/
theorem primeSide_add_sub {L : ℝ} (P R : ℕ) (φ ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    primePowerSideTruncated P R (selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ + Cvs.WeilForm.WindowRepresentative.rep ψ))
        + primePowerSideTruncated P R (selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ - Cvs.WeilForm.WindowRepresentative.rep ψ))
      = 2 * primePowerSideTruncated P R (selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ))
        + 2 * primePowerSideTruncated P R (selfConvolution (Cvs.WeilForm.WindowRepresentative.rep ψ)) := by
  unfold primePowerSideTruncated
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => ?_
  have h1 := selfConvolution_add_sub φ ψ ((r : ℝ) * Real.log p)
  have h2 := selfConvolution_add_sub φ ψ (-((r : ℝ) * Real.log p))
  linear_combination (primePowerWeight p r) * h1 + (primePowerWeight p r) * h2

/-- The Lévy integrand obeys the parallelogram law, pointwise. -/
theorem levy_add_sub {L : ℝ} (φ ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L) (u : ℝ) :
    Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep φ + Cvs.WeilForm.WindowRepresentative.rep ψ) u
        + Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep φ - Cvs.WeilForm.WindowRepresentative.rep ψ) u
      = 2 * Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep φ) u
        + 2 * Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep ψ) u := by
  unfold Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy
  have h0 := selfConvolution_add_sub φ ψ 0
  have hu := selfConvolution_add_sub φ ψ (u / 2)
  linear_combination (Cvs.WeilForm.Archimedean.LevyDensity.densityU u) * h0 - (Cvs.WeilForm.Archimedean.LevyDensity.densityU u) * hu

/-- The Lévy integrand of a sum or difference of domain classes, as a pointwise function. -/
theorem levy_rep_add {L : ℝ} (φ ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep (φ + ψ))
      = Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep φ + Cvs.WeilForm.WindowRepresentative.rep ψ) := by
  funext u; unfold Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy
  rw [selfConvolution_congr_ae (Cvs.WeilForm.LevyDomainSpectral.rep_add_ae φ ψ),
    selfConvolution_congr_ae (Cvs.WeilForm.LevyDomainSpectral.rep_add_ae φ ψ)]

theorem levy_rep_sub {L : ℝ} (φ ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep (φ - ψ))
      = Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep φ - Cvs.WeilForm.WindowRepresentative.rep ψ) := by
  funext u; unfold Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy
  rw [selfConvolution_congr_ae (Cvs.WeilForm.PoleAndPrimeContinuousWindow.rep_sub_ae φ ψ),
    selfConvolution_congr_ae (Cvs.WeilForm.PoleAndPrimeContinuousWindow.rep_sub_ae φ ψ)]

/-- **The parallelogram law**, on the form domain. -/
theorem weilQW_parallelogram {L : ℝ} (hL : 0 ≤ L) (P R : ℕ)
    (φ ψ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Cvs.WeilForm.WindowRepresentative.weilQW P R ((φ + ψ : Cvs.WeilForm.FormDomain.formDomain hL) :
        Cvs.WeilForm.WeilFormOnWindowL2.window L)
      + Cvs.WeilForm.WindowRepresentative.weilQW P R ((φ - ψ : Cvs.WeilForm.FormDomain.formDomain hL) :
        Cvs.WeilForm.WeilFormOnWindowL2.window L)
      = 2 * Cvs.WeilForm.WindowRepresentative.weilQW P R (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)
        + 2 * Cvs.WeilForm.WindowRepresentative.weilQW P R (ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L) := by
  -- the four forms, on pointwise representatives
  have e1 : Cvs.WeilForm.WindowRepresentative.weilQW P R ((φ + ψ : Cvs.WeilForm.FormDomain.formDomain hL) :
      Cvs.WeilForm.WeilFormOnWindowL2.window L) = Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R
        (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)
          + Cvs.WeilForm.WindowRepresentative.rep (ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) := by
    rw [(Cvs.WeilForm.WindowRepresentative.weilQW_rep P R _).1, Submodule.coe_add,
      Cvs.WeilForm.WeilFormAeClass.weilForm_congr_ae P R (Cvs.WeilForm.LevyDomainSpectral.rep_add_ae _ _)]
  have e2 : Cvs.WeilForm.WindowRepresentative.weilQW P R ((φ - ψ : Cvs.WeilForm.FormDomain.formDomain hL) :
      Cvs.WeilForm.WeilFormOnWindowL2.window L) = Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R
        (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)
          - Cvs.WeilForm.WindowRepresentative.rep (ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) := by
    rw [(Cvs.WeilForm.WindowRepresentative.weilQW_rep P R _).1, Submodule.coe_sub,
      Cvs.WeilForm.WeilFormAeClass.weilForm_congr_ae P R (Cvs.WeilForm.PoleAndPrimeContinuousWindow.rep_sub_ae _ _)]
  have e3 := (Cvs.WeilForm.WindowRepresentative.weilQW_rep P R (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)).1
  have e4 := (Cvs.WeilForm.WindowRepresentative.weilQW_rep P R (ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L)).1
  rw [e1, e2, e3, e4, Cvs.WeilForm.SelfConvolutionFunctional.weilForm_eq, Cvs.WeilForm.SelfConvolutionFunctional.weilForm_eq,
    Cvs.WeilForm.SelfConvolutionFunctional.weilForm_eq, Cvs.WeilForm.SelfConvolutionFunctional.weilForm_eq]
  -- the pole functionals
  obtain ⟨hA1, hA2⟩ := integral_add_mul_exp hL (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) ψ
    (w := fun s => Real.exp (s / 2)) (by fun_prop) Cvs.WeilForm.PoleAndPrimeContinuousWindow.abs_exp_half_le
  obtain ⟨hB1, hB2⟩ := integral_add_mul_exp hL (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) ψ
    (w := fun s => Real.exp (-(s / 2))) (by fun_prop) Cvs.WeilForm.PoleAndPrimeContinuousWindow.abs_exp_neg_half_le
  -- the Lévy integrals
  have hL1 : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy
      (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)
        + Cvs.WeilForm.WindowRepresentative.rep (ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L))) (Ioi 0) volume := by
    rw [← levy_rep_add]; exact Cvs.WeilForm.FormDomain.hdom_of_mem (φ + ψ)
  have hL2 : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy
      (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)
        - Cvs.WeilForm.WindowRepresentative.rep (ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L))) (Ioi 0) volume := by
    rw [← levy_rep_sub]; exact Cvs.WeilForm.FormDomain.hdom_of_mem (φ - ψ)
  have hL3 := Cvs.WeilForm.FormDomain.hdom_of_mem φ
  have hL4 := Cvs.WeilForm.FormDomain.hdom_of_mem ψ
  have hLevy := congrArg (fun F : ℝ → ℝ => ∫ u in Ioi (0:ℝ), F u)
    (show Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)
          + Cvs.WeilForm.WindowRepresentative.rep (ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L))
        + Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)
          - Cvs.WeilForm.WindowRepresentative.rep (ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L))
        = 2 * Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L))
          + 2 * Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep (ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L))
      from funext fun u => by
        simpa [Pi.add_apply, Pi.mul_apply] using
          levy_add_sub (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) (ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L) u)
  simp only [Pi.add_apply, Pi.mul_apply, Pi.ofNat_apply] at hLevy
  rw [integral_add hL1 hL2, integral_add (hL3.const_mul 2) (hL4.const_mul 2),
    integral_const_mul, integral_const_mul] at hLevy
  unfold Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy at hLevy
  have hg0 := selfConvolution_add_sub (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) ψ 0
  have hPi := primeSide_add_sub P R (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) ψ
  rw [hA1, hA2, hB1, hB2]
  linear_combination hLevy + (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) * hg0 - hPi

end Cvs.WeilForm.ParallelogramLaw
