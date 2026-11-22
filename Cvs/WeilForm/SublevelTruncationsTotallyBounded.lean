import Mathlib
import Cvs.Upstream.BoundedKernelIntegralOperator
import Cvs.Upstream.ComplexificationIsometryL2
import Cvs.Upstream.FrequencyTruncationL2
import Cvs.Upstream.LipschitzFamilyTotallyBoundedL2
import Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.LevyDomainSpectral
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowFourierBoundedLipschitz
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.WeilPositivityStatement

/-!
# The truncations of a sublevel set of the form are totally bounded

    `{cut T (emb φ) | ‖φ‖ ≤ 1, weilQW φ ≤ c}` is totally bounded in `L²`

because the transforms of window classes of norm at most one are bounded by `√L` and
`2πL√L`-Lipschitz, so Arzelà–Ascoli applies to them below frequency `T`.
-/

noncomputable section

open MeasureTheory FourierTransform Real Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.SublevelTruncationsTotallyBounded

/-- **The `L¹` norm of a window representative**, by Cauchy–Schwarz on the window. -/
theorem integral_abs_rep_le {L : ℝ} (hL : 0 ≤ L) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    ∫ x, |Cvs.WeilForm.WindowRepresentative.rep φ x| ≤ Real.sqrt L * ‖φ‖ := by
  have hint := Cvs.WeilForm.LevyDomainSpectral.integrable_rep hL φ
  have hsupp := Cvs.WeilForm.WindowRepresentative.rep_supp φ
  have h1 : ∫ x, |Cvs.WeilForm.WindowRepresentative.rep φ x|
      = ∫ x in (0:ℝ)..L, |Cvs.WeilForm.WindowRepresentative.rep φ x| := by
    rw [intervalIntegral.integral_of_le hL, setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx; simp [hsupp x hx]
  have h2 : ∫ x, (Cvs.WeilForm.WindowRepresentative.rep φ x) ^ 2
      = ∫ x in (0:ℝ)..L, (Cvs.WeilForm.WindowRepresentative.rep φ x) ^ 2 := by
    rw [intervalIntegral.integral_of_le hL, setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx; simp [hsupp x hx]
  have hcs := Cvs.Upstream.BoundedKernelIntegralOperator.sq_integral_abs_le hL hint.abs.intervalIntegrable
    (Cvs.WeilForm.WindowRepresentative.integrable_sq_rep φ).intervalIntegrable
  have hn : ∫ x in (0:ℝ)..L, (Cvs.WeilForm.WindowRepresentative.rep φ x) ^ 2 = ‖φ‖ ^ 2 := by
    rw [← h2, ← (Cvs.WeilForm.WindowRepresentative.weilQW_rep 0 0 φ).2]
    unfold Cvs.Zeta.Explicit.Weil.selfConvolution
    simp [pow_two]
  have hA : 0 ≤ ∫ x in (0:ℝ)..L, |Cvs.WeilForm.WindowRepresentative.rep φ x| :=
    intervalIntegral.integral_nonneg hL fun x _ => abs_nonneg _
  rw [h1]
  calc ∫ x in (0:ℝ)..L, |Cvs.WeilForm.WindowRepresentative.rep φ x|
      = Real.sqrt ((∫ x in (0:ℝ)..L, |Cvs.WeilForm.WindowRepresentative.rep φ x|) ^ 2) :=
        (Real.sqrt_sq hA).symm
    _ ≤ Real.sqrt (L * ‖φ‖ ^ 2) := Real.sqrt_le_sqrt (by rw [← hn]; exact hcs)
    _ = Real.sqrt L * ‖φ‖ := by rw [Real.sqrt_mul hL, Real.sqrt_sq (norm_nonneg _)]

/-- The transforms of the sublevel set. -/
def fam {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) (c : ℝ) : Set (ℝ → ℂ) :=
  {g | ∃ φ : Cvs.WeilForm.FormDomain.formDomain hL, ‖φ‖ ≤ 1 ∧
    Cvs.WeilForm.WindowRepresentative.weilQW P R (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) ≤ c ∧
    g = 𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)))}

/-- The complexified representative vanishes off `[0, L]`. -/
theorem cf_rep_supp {L : ℝ} (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    ∀ x, x ∉ Set.Icc (0:ℝ) L →
      Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.WeilForm.WindowRepresentative.rep φ) x = 0 := by
  intro x hx
  simp [Cvs.WeilForm.SelfConvolutionTransform.cf,
    Cvs.WeilForm.WindowRepresentative.rep_supp φ x (fun h => hx (Set.Ioc_subset_Icc_self h))]

/-- The `L¹` norm of the complexified representative. -/
theorem integral_norm_cf_rep_le {L : ℝ} (hL : 0 ≤ L) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    ∫ x, ‖Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.WeilForm.WindowRepresentative.rep φ) x‖ ≤ Real.sqrt L * ‖φ‖ := by
  have : (fun x => ‖Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.WeilForm.WindowRepresentative.rep φ) x‖)
      = fun x => |Cvs.WeilForm.WindowRepresentative.rep φ x| := by
    funext x; simp [Cvs.WeilForm.SelfConvolutionTransform.cf, Complex.norm_real]
  rw [this]
  exact integral_abs_rep_le hL φ

/-- **The family is uniformly bounded by `√L`.** -/
theorem fam_bdd {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) (c : ℝ) :
    ∀ g ∈ fam hL P R c, ∀ ξ, ‖g ξ‖ ≤ ((⟨Real.sqrt L, Real.sqrt_nonneg _⟩ : NNReal) : ℝ) := by
  rintro g ⟨φ, hn, _, rfl⟩ ξ
  refine (Cvs.WeilForm.WindowFourierBoundedLipschitz.norm_fourier_le _ ξ).trans ?_
  refine (integral_norm_cf_rep_le hL _).trans ?_
  show Real.sqrt L * ‖(φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)‖ ≤ Real.sqrt L
  have : ‖(φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)‖ = ‖φ‖ := rfl
  rw [this]
  exact mul_le_of_le_one_right (Real.sqrt_nonneg _) hn

/-- **The family is uniformly Lipschitz with constant `2πL√L`.** -/
theorem fam_lip {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) (c : ℝ) :
    ∀ g ∈ fam hL P R c, LipschitzWith
      ⟨2 * π * L * Real.sqrt L, mul_nonneg (mul_nonneg (by positivity) hL) (Real.sqrt_nonneg _)⟩ g := by
  rintro g ⟨φ, hn, _, rfl⟩
  refine LipschitzWith.of_dist_le_mul fun ξ η => ?_
  rw [dist_eq_norm, Real.dist_eq]
  show ‖_ - _‖ ≤ 2 * π * L * Real.sqrt L * |ξ - η|
  refine (Cvs.WeilForm.WindowFourierBoundedLipschitz.norm_fourier_sub_le
    ((Cvs.WeilForm.LevyDomainSpectral.integrable_rep hL _).ofReal) (cf_rep_supp _) ξ η).trans ?_
  have h1 := integral_norm_cf_rep_le hL (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)
  have h2 : ‖(φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)‖ = ‖φ‖ := rfl
  rw [h2] at h1
  have h3 : ∫ x, ‖Cvs.WeilForm.SelfConvolutionTransform.cf
      (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) x‖ ≤ Real.sqrt L :=
    h1.trans (mul_le_of_le_one_right (Real.sqrt_nonneg _) hn)
  have hpos : 0 ≤ 2 * π * L := mul_nonneg (by positivity) hL
  calc 2 * π * L * (∫ x, ‖Cvs.WeilForm.SelfConvolutionTransform.cf
        (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) x‖) * |ξ - η|
      ≤ 2 * π * L * Real.sqrt L * |ξ - η| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hpos) (abs_nonneg _)

/-- **The truncations of the sublevel set are totally bounded.** -/
theorem totallyBounded_cut {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) (c : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    TotallyBounded ((fun φ : Cvs.WeilForm.FormDomain.formDomain hL =>
        Cvs.Upstream.FrequencyTruncationL2.cut T (Cvs.Upstream.ComplexificationIsometryL2.emb
          ((φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)))) ''
      {φ | ‖φ‖ ≤ 1 ∧ Cvs.WeilForm.WindowRepresentative.weilQW P R (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) ≤ c}) := by
  have hB : MeasurableSet (Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.tailSet T)ᶜ :=
    (Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.measurableSet_tailSet T).compl
  have hBsub : (Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.tailSet T)ᶜ ⊆ Set.Icc (-T) T := by
    intro t ht
    have : |t| < T := lt_of_not_ge ht
    exact abs_le.mp this.le
  have hab : -T ≤ T := by linarith
  have hTB := Cvs.Upstream.LipschitzFamilyTotallyBoundedL2.totallyBounded_of_lipschitz hab (fam hL P R c)
    (fam_bdd hL P R c) (fam_lip hL P R c) hB hBsub
  have himg := hTB.image (Lp.fourierTransformₗᵢ ℝ ℂ).symm.isometry.uniformContinuous
  refine himg.subset ?_
  rintro _ ⟨φ, ⟨hn, hQ⟩, rfl⟩
  have h2 := Cvs.Upstream.ComplexificationIsometryL2.fourier_emb_window hL (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)
  show Cvs.Upstream.FrequencyTruncationL2.cut T (Cvs.Upstream.ComplexificationIsometryL2.emb
    ((φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))) ∈ _
  generalize hψ : ((φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)) = ψ
  rw [hψ] at h2
  have hcut : Cvs.Upstream.FrequencyTruncationL2.cut T (Cvs.Upstream.ComplexificationIsometryL2.emb ψ)
      = (Lp.fourierTransformₗᵢ ℝ ℂ).symm
          (((Lp.memLp (𝓕 (Cvs.Upstream.ComplexificationIsometryL2.emb ψ) : Lp ℂ 2 (volume : Measure ℝ))).indicator
            hB.nullMeasurableSet).toLp _) := rfl
  have h1 : ((((Lp.memLp (𝓕 (Cvs.Upstream.ComplexificationIsometryL2.emb ψ) : Lp ℂ 2 (volume : Measure ℝ))).indicator
        hB.nullMeasurableSet).toLp _ : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] (Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.tailSet T)ᶜ.indicator
        ((𝓕 (Cvs.Upstream.ComplexificationIsometryL2.emb ψ) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) :=
    MemLp.coeFn_toLp _
  have hmem : ((((Lp.memLp (𝓕 (Cvs.Upstream.ComplexificationIsometryL2.emb ψ) : Lp ℂ 2 (volume : Measure ℝ))).indicator
        hB.nullMeasurableSet).toLp _ : Lp ℂ 2 (volume : Measure ℝ)))
      ∈ {u : Lp ℂ 2 (volume : Measure ℝ) | ∃ g ∈ fam hL P R c,
          (u : ℝ → ℂ) =ᵐ[volume] (Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.tailSet T)ᶜ.indicator g} := by
    refine ⟨_, ⟨φ, hn, hQ, rfl⟩, ?_⟩
    filter_upwards [h1, h2] with x h1 h2
    rw [h1]
    by_cases hx : x ∈ (Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.tailSet T)ᶜ
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, h2]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
  rw [hcut]
  exact ⟨_, hmem, rfl⟩

end Cvs.WeilForm.SublevelTruncationsTotallyBounded
