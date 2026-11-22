import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Fourier.LpSpace

/-!
# The `L²` Fourier transform is the Fourier integral on `L¹ ∩ L²`

    `Integrable f`, `MemLp f 2`   ⟹   `𝓕 (toLp f) =ᵐ 𝓕 f`

through tempered distributions: both sides define the same distribution, and a distribution
determines a locally integrable function almost everywhere.
-/

noncomputable section

open MeasureTheory FourierTransform SchwartzMap
open scoped ContDiff

namespace Cvs.Upstream.L2FourierIntegralL1L2

/-- **The Fourier integral of an integrable function pairs by flipping.**  Against a Schwartz
test function, `∫ g • 𝓕 f = ∫ (𝓕 g) • f`. -/
theorem integral_smul_fourier_eq {f : ℝ → ℂ} (hf : Integrable f) (g : 𝓢(ℝ, ℂ)) :
    ∫ x, g x • (𝓕 f) x = ∫ x, (𝓕 g) x • f x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (e := 𝐞) (μ := volume)
    (ν := volume) (L := innerₗ ℝ) (f := f) (g := (g : ℝ → ℂ)) Real.continuous_fourierChar
    (by fun_prop) hf g.integrable
  have hflip : (innerₗ ℝ).flip = innerₗ ℝ := by
    ext; simp
  rw [hflip] at h
  have e1 : 𝓕 f = VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) f := rfl
  have e2 : ((𝓕 g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) g := by
    rw [fourier_coe]; rfl
  rw [e1, e2]
  calc ∫ x, g x • VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) f x
        = ∫ x, VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) f x • (g : ℝ → ℂ) x := by
        simp only [smul_eq_mul, mul_comm]
    _ = ∫ x, f x • VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) g x := h
    _ = ∫ x, VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) g x • f x := by
        simp only [smul_eq_mul, mul_comm]

/-- **The `L²` transform is the Fourier integral on `L¹ ∩ L²`.**  The `L²` transform and the
Fourier integral define the same tempered distribution, so they agree almost everywhere. -/
theorem fourier_toLp_ae_eq {f : ℝ → ℂ} (hf : Integrable f)
    (hf2 : MemLp f 2 (volume : Measure ℝ)) :
    ((𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] 𝓕 f := by
  have hu : LocallyIntegrable ((𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      volume := (Lp.memLp _).locallyIntegrable one_le_two
  have hv : LocallyIntegrable (𝓕 f) volume :=
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop)
      hf).locallyIntegrable
  refine ae_eq_of_integral_contDiff_smul_eq hu hv fun g hg hgc => ?_
  -- the real test function, complexified, is a Schwartz function
  have hgc' : HasCompactSupport (fun x => (g x : ℂ)) := hgc.comp_left Complex.ofReal_zero
  have hgs : ContDiff ℝ ∞ (fun x => (g x : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
  set G : 𝓢(ℝ, ℂ) := hgc'.toSchwartzMap hgs with hG
  have hGx : ∀ x, G x = (g x : ℂ) := fun x => rfl
  -- the distributional identity, evaluated at `G`
  have key := congrArg (fun T : TemperedDistribution ℝ ℂ => T G)
    (Lp.fourier_toTemperedDistribution_eq (hf2.toLp f))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at key
  -- the left side is the pairing with `f` itself, then flipped
  have hleft : ∫ x, (𝓕 G) x • ((hf2.toLp f : Lp ℂ 2 volume) : ℝ → ℂ) x
      = ∫ x, G x • (𝓕 f) x := by
    rw [integral_smul_fourier_eq hf G]
    refine integral_congr_ae ?_
    filter_upwards [hf2.coeFn_toLp] with x hx
    rw [hx]
  rw [hleft] at key
  -- `key : ∫ G • 𝓕 f = ∫ G • 𝓕 (toLp f)`; strip the complexification
  have hsmul : ∀ (x : ℝ) (z : ℂ), g x • z = G x • z := fun x z => by
    rw [hGx, Complex.real_smul, smul_eq_mul]
  simp only [hsmul]
  exact key.symm

end Cvs.Upstream.L2FourierIntegralL1L2
