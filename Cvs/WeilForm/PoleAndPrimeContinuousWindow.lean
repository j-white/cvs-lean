import Mathlib
import Cvs.WeilForm.LevyDomainSpectral
import Cvs.WeilForm.SelfConvolutionClassLipschitz
import Cvs.WeilForm.SublevelTruncationsTotallyBounded
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-!
# The pole functionals and the prime-power sum are continuous on the window

    `∫ rep φ · e^{±s/2}` and `primePowerSideTruncated P R (selfConvolution (rep φ))`
        converge along `L²` convergence in the window

the first by `∫|rep φ − rep ψ| ≤ √L ‖φ − ψ‖`, the second termwise from the self-convolution.
-/

noncomputable section

open MeasureTheory Filter Topology Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.PoleAndPrimeContinuousWindow

/-- **Representatives subtract**, almost everywhere. -/
theorem rep_sub_ae {L : ℝ} (φ ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    Cvs.WeilForm.WindowRepresentative.rep (φ - ψ)
      =ᵐ[volume] Cvs.WeilForm.WindowRepresentative.rep φ - Cvs.WeilForm.WindowRepresentative.rep ψ := by
  have h : Cvs.WeilForm.WindowRepresentative.fn (φ - ψ)
      =ᵐ[volume] Cvs.WeilForm.WindowRepresentative.fn φ - Cvs.WeilForm.WindowRepresentative.fn ψ := by
    unfold Cvs.WeilForm.WindowRepresentative.fn
    rw [Submodule.coe_sub]
    exact Lp.coeFn_sub _ _
  filter_upwards [h] with x hx
  simp only [Cvs.WeilForm.WindowRepresentative.rep, Set.indicator_apply, Pi.sub_apply]
  split_ifs <;> simp [hx]

/-- The `L¹` distance of representatives is controlled by the `L²` distance. -/
theorem integral_abs_rep_sub_le {L : ℝ} (hL : 0 ≤ L) (φ ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    ∫ x, |Cvs.WeilForm.WindowRepresentative.rep φ x - Cvs.WeilForm.WindowRepresentative.rep ψ x|
      ≤ Real.sqrt L * ‖(φ : Lp ℝ 2 (volume : Measure ℝ)) - ψ‖ := by
  have h := Cvs.WeilForm.SublevelTruncationsTotallyBounded.integral_abs_rep_le hL (φ - ψ)
  have heq : ∫ x, |Cvs.WeilForm.WindowRepresentative.rep φ x - Cvs.WeilForm.WindowRepresentative.rep ψ x|
      = ∫ x, |Cvs.WeilForm.WindowRepresentative.rep (φ - ψ) x| := by
    refine integral_congr_ae ?_
    filter_upwards [rep_sub_ae φ ψ] with x hx
    rw [hx, Pi.sub_apply]
  rw [heq]
  exact h

/-- A weighted representative is integrable, for a weight bounded on the window. -/
theorem integrable_rep_mul {L : ℝ} (hL : 0 ≤ L) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)
    {w : ℝ → ℝ} (hw : Continuous w) {M : ℝ} (hM : ∀ s ∈ Set.Icc (0:ℝ) L, |w s| ≤ M) :
    Integrable (fun s => Cvs.WeilForm.WindowRepresentative.rep φ s * w s) := by
  have hint := Cvs.WeilForm.LevyDomainSpectral.integrable_rep hL φ
  refine Integrable.mono' (hint.norm.const_mul M) (hint.aestronglyMeasurable.mul
    hw.aestronglyMeasurable) (Filter.Eventually.of_forall fun s => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  by_cases hs : s ∈ Set.Icc (0:ℝ) L
  · have := hM s hs
    have := abs_nonneg (Cvs.WeilForm.WindowRepresentative.rep φ s)
    nlinarith
  · rw [Cvs.WeilForm.WindowRepresentative.rep_supp φ s (fun h => hs (Set.Ioc_subset_Icc_self h))]
    simp

/-- **A weighted integral of the representative is Lipschitz in the class.** -/
theorem abs_integral_rep_mul_sub_le {L : ℝ} (hL : 0 ≤ L) (φ ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L)
    {w : ℝ → ℝ} (hw : Continuous w) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ s ∈ Set.Icc (0:ℝ) L, |w s| ≤ M) :
    |(∫ s, Cvs.WeilForm.WindowRepresentative.rep φ s * w s) - ∫ s, Cvs.WeilForm.WindowRepresentative.rep ψ s * w s|
      ≤ M * (Real.sqrt L * ‖(φ : Lp ℝ 2 (volume : Measure ℝ)) - ψ‖) := by
  rw [← integral_sub (integrable_rep_mul hL φ hw hM) (integrable_rep_mul hL ψ hw hM)]
  have hd : Integrable (fun s => Cvs.WeilForm.WindowRepresentative.rep φ s - Cvs.WeilForm.WindowRepresentative.rep ψ s) :=
    (Cvs.WeilForm.LevyDomainSpectral.integrable_rep hL φ).sub (Cvs.WeilForm.LevyDomainSpectral.integrable_rep hL ψ)
  have hpt : ∀ s, ‖Cvs.WeilForm.WindowRepresentative.rep φ s * w s - Cvs.WeilForm.WindowRepresentative.rep ψ s * w s‖
      ≤ M * |Cvs.WeilForm.WindowRepresentative.rep φ s - Cvs.WeilForm.WindowRepresentative.rep ψ s| := by
    intro s
    rw [← sub_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_comm]
    by_cases hs : s ∈ Set.Icc (0:ℝ) L
    · exact mul_le_mul_of_nonneg_right (hM s hs) (abs_nonneg _)
    · rw [Cvs.WeilForm.WindowRepresentative.rep_supp φ s (fun h => hs (Set.Ioc_subset_Icc_self h)),
        Cvs.WeilForm.WindowRepresentative.rep_supp ψ s (fun h => hs (Set.Ioc_subset_Icc_self h))]
      simp
  calc ‖∫ s, (Cvs.WeilForm.WindowRepresentative.rep φ s * w s - Cvs.WeilForm.WindowRepresentative.rep ψ s * w s)‖
      ≤ ∫ s, M * |Cvs.WeilForm.WindowRepresentative.rep φ s - Cvs.WeilForm.WindowRepresentative.rep ψ s| :=
        norm_integral_le_of_norm_le (hd.abs.const_mul M) (Filter.Eventually.of_forall hpt)
    _ = M * ∫ s, |Cvs.WeilForm.WindowRepresentative.rep φ s - Cvs.WeilForm.WindowRepresentative.rep ψ s| :=
        integral_const_mul _ _
    _ ≤ M * (Real.sqrt L * ‖(φ : Lp ℝ 2 (volume : Measure ℝ)) - ψ‖) :=
        mul_le_mul_of_nonneg_left (integral_abs_rep_sub_le hL φ ψ) hM0

/-- **Weighted integrals converge along `L²` convergence in the window.** -/
theorem tendsto_integral_rep_mul {L : ℝ} (hL : 0 ≤ L) {x : ℕ → Cvs.WeilForm.WeilFormOnWindowL2.window L}
    {y : Cvs.WeilForm.WeilFormOnWindowL2.window L}
    (hx : Tendsto (fun k => ((x k : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)))
      atTop (𝓝 (y : Lp ℝ 2 (volume : Measure ℝ))))
    {w : ℝ → ℝ} (hw : Continuous w) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ s ∈ Set.Icc (0:ℝ) L, |w s| ≤ M) :
    Tendsto (fun k => ∫ s, Cvs.WeilForm.WindowRepresentative.rep (x k) s * w s) atTop
      (𝓝 (∫ s, Cvs.WeilForm.WindowRepresentative.rep y s * w s)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h1 := tendsto_iff_norm_sub_tendsto_zero.mp hx
  have h2 : Tendsto (fun k => M * (Real.sqrt L * ‖((x k : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
      Lp ℝ 2 (volume : Measure ℝ)) - (y : Lp ℝ 2 (volume : Measure ℝ))‖)) atTop (𝓝 0) := by
    have := (h1.const_mul (Real.sqrt L)).const_mul M
    simpa using this
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) h2
  rw [Real.norm_eq_abs]
  exact abs_integral_rep_mul_sub_le hL (x k) y hw hM0 hM

/-- **The exponential weights are bounded on the window.** -/
theorem abs_exp_half_le {L : ℝ} :
    ∀ s ∈ Set.Icc (0:ℝ) L, |Real.exp (s / 2)| ≤ Real.exp (L / 2) := by
  intro s hs
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (by linarith [hs.2])

theorem abs_exp_neg_half_le {L : ℝ} :
    ∀ s ∈ Set.Icc (0:ℝ) L, |Real.exp (-(s / 2))| ≤ 1 := by
  intro s hs
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (by linarith [hs.1])

/-- **The prime-power sum converges along `L²` convergence in the window.** -/
theorem tendsto_primeSide {L : ℝ} (P R : ℕ) {x : ℕ → Cvs.WeilForm.WeilFormOnWindowL2.window L}
    {y : Cvs.WeilForm.WeilFormOnWindowL2.window L}
    (hx : Tendsto (fun k => ((x k : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)))
      atTop (𝓝 (y : Lp ℝ 2 (volume : Measure ℝ)))) :
    Tendsto (fun k => primePowerSideTruncated P R (selfConvolution (Cvs.WeilForm.WindowRepresentative.rep (x k))))
      atTop (𝓝 (primePowerSideTruncated P R (selfConvolution (Cvs.WeilForm.WindowRepresentative.rep y)))) := by
  unfold primePowerSideTruncated
  refine tendsto_finsetSum _ fun p _ => tendsto_finsetSum _ fun r _ => ?_
  exact ((Cvs.WeilForm.SelfConvolutionClassLipschitz.tendsto_selfConvolution hx _).add
    (Cvs.WeilForm.SelfConvolutionClassLipschitz.tendsto_selfConvolution hx _)).const_mul _

end Cvs.WeilForm.PoleAndPrimeContinuousWindow
