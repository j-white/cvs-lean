import Mathlib
import Cvs.StepA.StepAPredicate
import Cvs.WeilForm.Archimedean.ArchFormIntegrable
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyTonelli
import Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin
import Cvs.WeilForm.LevyDomainSpectral
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowFormNormFloor
import Cvs.WeilForm.WindowRepresentative

/-!
# The form domain, and step (a) stated on it

    `formDomain hL = {φ ∈ window L | the Lévy integrand of φ is integrable}`

is a subspace of the window, the floor bound holds on it, and the terminal statement of
step (a) is `StepA` for the Weil form on this subspace.
-/

noncomputable section

open MeasureTheory Real FourierTransform Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.FormDomain

/-- The spectral mass `∫⁻ specDensity · (archSymbol − archSymbol 0)`, as an extended real. -/
def spectralMass (f : ℝ → ℝ) : ENNReal :=
  ∫⁻ t, ENNReal.ofReal (Cvs.WeilForm.SelfConvolutionCosine.specDensity f t *
    (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0))

/-- The archimedean excess is nonnegative. -/
theorem excess_nonneg (t : ℝ) :
    0 ≤ Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 :=
  sub_nonneg.mpr (Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.archSymbol_min_at_zero t)

/-- The spectral integrand is measurable. -/
theorem measurable_integrand {f : ℝ → ℝ} (hf : Integrable f) :
    Measurable fun t => ENNReal.ofReal (Cvs.WeilForm.SelfConvolutionCosine.specDensity f t *
      (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)) :=
  ((Cvs.WeilForm.Archimedean.LevyTonelli.continuous_specDensity hf).mul
    (Cvs.WeilForm.Archimedean.ArchFormIntegrable.continuous_archSymbol.sub continuous_const)).measurable.ennreal_ofReal

/-- **Spectral mass is insensitive to null sets.** -/
theorem spectralMass_congr_ae {f g : ℝ → ℝ} (h : f =ᵐ[volume] g) :
    spectralMass f = spectralMass g := by
  unfold spectralMass
  rw [Cvs.WeilForm.LevyDomainSpectral.specDensity_congr_ae h]

/-- **Spectral mass of a sum.** -/
theorem spectralMass_add_le {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) :
    spectralMass (f + g) ≤ ENNReal.ofReal 2 * spectralMass f + ENNReal.ofReal 2 * spectralMass g := by
  unfold spectralMass
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_add_left' ((measurable_integrand hf).const_mul _).aemeasurable]
  refine lintegral_mono fun t => ?_
  have ha := excess_nonneg t
  have h1 := Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg f t
  have h2 := Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg g t
  have hle := Cvs.WeilForm.LevyDomainSpectral.specDensity_add_le hf hg t
  calc ENNReal.ofReal (Cvs.WeilForm.SelfConvolutionCosine.specDensity (f + g) t *
        (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0))
      ≤ ENNReal.ofReal (2 * (Cvs.WeilForm.SelfConvolutionCosine.specDensity f t *
          (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0))
        + 2 * (Cvs.WeilForm.SelfConvolutionCosine.specDensity g t *
          (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0))) := by
        apply ENNReal.ofReal_le_ofReal
        nlinarith [mul_le_mul_of_nonneg_right hle ha]
    _ = _ := by
        rw [ENNReal.ofReal_add (mul_nonneg (by norm_num) (mul_nonneg h1 ha))
          (mul_nonneg (by norm_num) (mul_nonneg h2 ha))]
        simp only [ENNReal.ofReal_mul (show (0:ℝ) ≤ 2 by norm_num)]

/-- **Spectral mass of a scalar multiple.** -/
theorem spectralMass_smul (c : ℝ) (f : ℝ → ℝ) :
    spectralMass (fun x => c * f x) = ENNReal.ofReal (c ^ 2) * spectralMass f := by
  unfold spectralMass
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun t => ?_
  rw [Cvs.WeilForm.LevyDomainSpectral.specDensity_smul, mul_assoc,
    ENNReal.ofReal_mul (by positivity)]

/-- **The zero function has no spectral mass.** -/
theorem spectralMass_zero : spectralMass (0 : ℝ → ℝ) = 0 := by
  have hF : (𝓕 (0 : ℝ → ℂ)) = 0 := by
    have h := VectorFourier.fourierIntegral_const_smul 𝐞 volume (innerₗ ℝ) (0 : ℝ → ℂ) (0 : ℂ)
    rw [zero_smul, zero_smul] at h
    exact h
  have hsd : ∀ t, Cvs.WeilForm.SelfConvolutionCosine.specDensity (0 : ℝ → ℝ) t = 0 := by
    intro t
    unfold Cvs.WeilForm.SelfConvolutionCosine.specDensity
    have hcf : Cvs.WeilForm.SelfConvolutionTransform.cf (0 : ℝ → ℝ) = 0 := by
      funext x; simp [Cvs.WeilForm.SelfConvolutionTransform.cf]
    rw [hcf, hF]; simp
  unfold spectralMass
  simp [hsd]

/-- **Membership in the domain, spectrally.** -/
theorem levyDom_iff_spectralMass {L : ℝ} (hL : 0 ≤ L) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep φ)) (Set.Ioi 0)
        (volume : Measure ℝ)
      ↔ spectralMass (Cvs.WeilForm.WindowRepresentative.rep φ) < ⊤ :=
  Cvs.WeilForm.LevyDomainSpectral.levyDom_iff (Cvs.WeilForm.WindowRepresentative.memLp_rep φ)
    (Cvs.WeilForm.LevyDomainSpectral.integrable_rep hL φ) (Cvs.WeilForm.WindowRepresentative.integrable_sq_rep φ)
    (Cvs.WeilForm.WindowRepresentative.integrable_cross_rep φ)

/-- **The form domain**: the classes in the window whose Lévy integrand is integrable. -/
def formDomain {L : ℝ} (hL : 0 ≤ L) : Submodule ℝ (Cvs.WeilForm.WeilFormOnWindowL2.window L) where
  carrier := {φ | IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep φ))
    (Set.Ioi 0) (volume : Measure ℝ)}
  add_mem' := by
    intro φ ψ hφ hψ
    have hφ' := (levyDom_iff_spectralMass hL φ).mp hφ
    have hψ' := (levyDom_iff_spectralMass hL ψ).mp hψ
    refine (levyDom_iff_spectralMass hL (φ + ψ)).mpr ?_
    rw [spectralMass_congr_ae (Cvs.WeilForm.LevyDomainSpectral.rep_add_ae φ ψ)]
    refine lt_of_le_of_lt (spectralMass_add_le (Cvs.WeilForm.LevyDomainSpectral.integrable_rep hL φ)
      (Cvs.WeilForm.LevyDomainSpectral.integrable_rep hL ψ)) ?_
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hφ',
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hψ'⟩
  zero_mem' := by
    refine (levyDom_iff_spectralMass hL 0).mpr ?_
    have h0 : Cvs.WeilForm.WindowRepresentative.rep (0 : Cvs.WeilForm.WeilFormOnWindowL2.window L) =ᵐ[volume] 0 := by
      have h : Cvs.WeilForm.WindowRepresentative.fn (0 : Cvs.WeilForm.WeilFormOnWindowL2.window L) =ᵐ[volume] 0 := by
        unfold Cvs.WeilForm.WindowRepresentative.fn
        rw [Submodule.coe_zero]
        exact Lp.coeFn_zero ℝ 2 volume
      filter_upwards [h] with x hx
      simp [Cvs.WeilForm.WindowRepresentative.rep, Set.indicator_apply, hx]
    rw [spectralMass_congr_ae h0, spectralMass_zero]
    exact ENNReal.zero_lt_top
  smul_mem' := by
    intro c φ hφ
    have hφ' := (levyDom_iff_spectralMass hL φ).mp hφ
    refine (levyDom_iff_spectralMass hL (c • φ)).mpr ?_
    rw [spectralMass_congr_ae (Cvs.WeilForm.LevyDomainSpectral.rep_smul_ae c φ), spectralMass_smul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hφ'

/-- **Membership is the Lévy hypothesis** every bound in the project consumes. -/
theorem hdom_of_mem {L : ℝ} {hL : 0 ≤ L} (φ : formDomain hL) :
    IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)))
      (Set.Ioi 0) (volume : Measure ℝ) := φ.2

/-- **The floor bound, on the form domain.** -/
theorem weilQW_ge_floor {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) (φ : formDomain hL) :
    Cvs.WeilForm.WindowFormNormFloor.floorConst L P R * ‖φ‖ ^ 2
      ≤ Cvs.WeilForm.WindowRepresentative.weilQW P R (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :=
  Cvs.WeilForm.WindowFormNormFloor.weilQW_ge_floor hL P R (Cvs.WeilForm.WindowRepresentative.ae_eq_rep _)
    (Cvs.WeilForm.WindowRepresentative.memLp_rep _) (Cvs.WeilForm.WindowRepresentative.rep_supp _) (hdom_of_mem φ)

/-- **Step (a) on the form domain.**  The seven hypotheses of `StepA`, each stated for the
Weil form on the subspace where it is the Weil form. -/
theorem stepA_weil {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) {lam mu : ℝ}
    {Refl : formDomain hL → formDomain hL} {eta : formDomain hL}
    (hbot : ∀ v : formDomain hL,
      lam * ‖v‖ ^ 2 ≤ Cvs.WeilForm.WindowRepresentative.weilQW P R (v : Cvs.WeilForm.WeilFormOnWindowL2.window L))
    (hatt : Cvs.WeilForm.WindowRepresentative.weilQW P R (eta : Cvs.WeilForm.WeilFormOnWindowL2.window L)
      = lam * ‖eta‖ ^ 2)
    (hne : eta ≠ 0)
    (hsimple : ∀ v : formDomain hL,
      Cvs.WeilForm.WindowRepresentative.weilQW P R (v : Cvs.WeilForm.WeilFormOnWindowL2.window L) = lam * ‖v‖ ^ 2
        → ∃ c : ℝ, v = c • eta)
    (hgap : lam < mu)
    (hperp : ∀ v : formDomain hL, (inner ℝ eta v : ℝ) = 0 →
      mu * ‖v‖ ^ 2 ≤ Cvs.WeilForm.WindowRepresentative.weilQW P R (v : Cvs.WeilForm.WeilFormOnWindowL2.window L))
    (heven : Refl eta = eta) :
    Cvs.StepA.StepAPredicate.StepA
      (fun v : formDomain hL => Cvs.WeilForm.WindowRepresentative.weilQW P R (v : Cvs.WeilForm.WeilFormOnWindowL2.window L))
      Refl lam eta :=
  Cvs.StepA.StepAPredicate.stepA_of hbot hatt hne hsimple hgap hperp heven

end Cvs.WeilForm.FormDomain
