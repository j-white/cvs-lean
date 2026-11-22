import Mathlib
import Cvs.WeilForm.Archimedean.ArchEnergySpectral
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.PoleAndPrimeContinuousWindow
import Cvs.WeilForm.SelfConvolutionClassLipschitz
import Cvs.WeilForm.SelfConvolutionContinuous
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.TruncatedArchDomain
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-!
# The Weil form is lower semicontinuous, and the form domain closes under bounded limits

    `x k ∈ formDomain`, `weilQW (x k) ≤ c`, `x k → y` in `L²`   ⟹   `y ∈ formDomain`, `weilQW y ≤ c`

by Fatou on the nonnegative Lévy integrand, the other terms of the form being continuous.
-/

noncomputable section

open MeasureTheory Filter Topology Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.FormLscDomainClosed

/-- The Weil form without its Lévy integral: pole term, `archSymbol 0 · g(0)`, minus the primes. -/
def par {L : ℝ} (P R : ℕ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : ℝ :=
  2 * (∫ s, Cvs.WeilForm.WindowRepresentative.rep φ s * Real.exp (s / 2))
      * (∫ s, Cvs.WeilForm.WindowRepresentative.rep φ s * Real.exp (-(s / 2)))
    + Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ) 0
    - primePowerSideTruncated P R (selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ))

/-- **The form is `par` plus the Lévy integral.** -/
theorem weilQW_eq_par_add {L : ℝ} (P R : ℕ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    Cvs.WeilForm.WindowRepresentative.weilQW P R φ
      = par P R φ + ∫ u in Set.Ioi (0:ℝ), Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep φ) u := by
  rw [(Cvs.WeilForm.WindowRepresentative.weilQW_rep P R φ).1, Cvs.WeilForm.SelfConvolutionFunctional.weilForm_eq]
  unfold par Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy
  ring

/-- **`par` is continuous along `L²` convergence in the window.** -/
theorem tendsto_par {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) {x : ℕ → Cvs.WeilForm.WeilFormOnWindowL2.window L}
    {y : Cvs.WeilForm.WeilFormOnWindowL2.window L}
    (hx : Tendsto (fun k => ((x k : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)))
      atTop (𝓝 (y : Lp ℝ 2 (volume : Measure ℝ)))) :
    Tendsto (fun k => par P R (x k)) atTop (𝓝 (par P R y)) := by
  have hA := Cvs.WeilForm.PoleAndPrimeContinuousWindow.tendsto_integral_rep_mul hL hx (w := fun s => Real.exp (s / 2))
    (by fun_prop) (Real.exp_pos _).le Cvs.WeilForm.PoleAndPrimeContinuousWindow.abs_exp_half_le
  have hB := Cvs.WeilForm.PoleAndPrimeContinuousWindow.tendsto_integral_rep_mul hL hx (w := fun s => Real.exp (-(s / 2)))
    (by fun_prop) zero_le_one Cvs.WeilForm.PoleAndPrimeContinuousWindow.abs_exp_neg_half_le
  have hg := Cvs.WeilForm.SelfConvolutionClassLipschitz.tendsto_selfConvolution hx 0
  have hp := Cvs.WeilForm.PoleAndPrimeContinuousWindow.tendsto_primeSide P R hx
  unfold par
  exact (((hA.const_mul 2).mul hB).add (hg.const_mul _)).sub hp

/-- **The Lévy integrand converges pointwise.** -/
theorem tendsto_levy {L : ℝ} {x : ℕ → Cvs.WeilForm.WeilFormOnWindowL2.window L}
    {y : Cvs.WeilForm.WeilFormOnWindowL2.window L}
    (hx : Tendsto (fun k => ((x k : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)))
      atTop (𝓝 (y : Lp ℝ 2 (volume : Measure ℝ)))) (u : ℝ) :
    Tendsto (fun k => Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep (x k)) u) atTop
      (𝓝 (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep y) u)) := by
  unfold Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy
  exact tendsto_const_nhds.mul ((Cvs.WeilForm.SelfConvolutionClassLipschitz.tendsto_selfConvolution hx 0).sub
    (Cvs.WeilForm.SelfConvolutionClassLipschitz.tendsto_selfConvolution hx (u / 2)))

/-- The Lévy integrand of a window class is nonnegative on `(0, ∞)`, almost everywhere. -/
theorem levy_nonneg_ae {L : ℝ} (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    0 ≤ᵐ[volume.restrict (Set.Ioi (0:ℝ))] Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep φ) := by
  refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
  exact Filter.Eventually.of_forall fun u hu =>
    Cvs.WeilForm.Archimedean.ArchEnergySpectral.levy_nonneg (Cvs.WeilForm.WindowRepresentative.integrable_sq_rep φ)
      (Cvs.WeilForm.WindowRepresentative.integrable_cross_rep φ) hu

/-- The Lévy integrand of a window class is measurable on `(0, ∞)`. -/
theorem aemeasurable_levy {L : ℝ} (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    AEMeasurable (fun u => ENNReal.ofReal (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep φ) u))
      (volume.restrict (Set.Ioi (0:ℝ))) :=
  (Cvs.WeilForm.TruncatedArchDomain.aestronglyMeasurable_levy
    (Cvs.WeilForm.SelfConvolutionContinuous.continuous_selfConvolution
      (Cvs.WeilForm.WindowRepresentative.memLp_rep φ)).aestronglyMeasurable).aemeasurable.ennreal_ofReal

/-- **Lower semicontinuity, and the limit is in the domain.** -/
theorem lsc {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) {c : ℝ} (x : ℕ → Cvs.WeilForm.FormDomain.formDomain hL)
    (hQ : ∀ k, Cvs.WeilForm.WindowRepresentative.weilQW P R ((x k : Cvs.WeilForm.FormDomain.formDomain hL) :
      Cvs.WeilForm.WeilFormOnWindowL2.window L) ≤ c)
    {y : Cvs.WeilForm.WeilFormOnWindowL2.window L}
    (hx : Tendsto (fun k => (((x k : Cvs.WeilForm.FormDomain.formDomain hL) :
      Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)))
      atTop (𝓝 (y : Lp ℝ 2 (volume : Measure ℝ)))) :
    y ∈ Cvs.WeilForm.FormDomain.formDomain hL ∧ Cvs.WeilForm.WindowRepresentative.weilQW P R y ≤ c := by
  set xw : ℕ → Cvs.WeilForm.WeilFormOnWindowL2.window L := fun k => (x k : Cvs.WeilForm.WeilFormOnWindowL2.window L)
    with hxw
  have hxw' : Tendsto (fun k => ((xw k : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)))
      atTop (𝓝 (y : Lp ℝ 2 (volume : Measure ℝ))) := hx
  -- along the sequence, the Lévy integral is at most `c − par`
  have hk : ∀ k, ∫ u in Set.Ioi (0:ℝ), Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep (xw k)) u
      ≤ c - par P R (xw k) := fun k => by
    have := hQ k
    rw [weilQW_eq_par_add] at this
    linarith
  have hpar := tendsto_par hL P R hxw'
  -- and that bound is nonnegative in the limit
  have hknn : ∀ k, 0 ≤ c - par P R (xw k) := fun k =>
    le_trans (setIntegral_nonneg measurableSet_Ioi fun u hu =>
      Cvs.WeilForm.Archimedean.ArchEnergySpectral.levy_nonneg (Cvs.WeilForm.WindowRepresentative.integrable_sq_rep _)
        (Cvs.WeilForm.WindowRepresentative.integrable_cross_rep _) hu) (hk k)
  have hnn : 0 ≤ c - par P R y :=
    ge_of_tendsto' (tendsto_const_nhds.sub hpar) hknn
  -- Fatou
  have hfatou : ∫⁻ u in Set.Ioi (0:ℝ), ENNReal.ofReal (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy
      (Cvs.WeilForm.WindowRepresentative.rep y) u) ≤ ENNReal.ofReal (c - par P R y) := by
    have h1 : ∫⁻ u in Set.Ioi (0:ℝ), ENNReal.ofReal (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy
        (Cvs.WeilForm.WindowRepresentative.rep y) u)
        = ∫⁻ u in Set.Ioi (0:ℝ), liminf (fun k => ENNReal.ofReal (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy
          (Cvs.WeilForm.WindowRepresentative.rep (xw k)) u)) atTop := by
      refine lintegral_congr fun u => ?_
      exact (((ENNReal.continuous_ofReal.tendsto _).comp (tendsto_levy hxw' u)).liminf_eq).symm
    have h2 := lintegral_liminf_le' (μ := volume.restrict (Set.Ioi (0:ℝ)))
      (f := fun k u => ENNReal.ofReal (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep (xw k)) u))
      (u := atTop) fun k => aemeasurable_levy (xw k)
    have h3 : ∀ k, ∫⁻ u in Set.Ioi (0:ℝ), ENNReal.ofReal (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy
        (Cvs.WeilForm.WindowRepresentative.rep (xw k)) u) ≤ ENNReal.ofReal (c - par P R (xw k)) := fun k => by
      rw [← ofReal_integral_eq_lintegral_ofReal (x k).2 (levy_nonneg_ae (xw k))]
      exact ENNReal.ofReal_le_ofReal (hk k)
    have h4 : liminf (fun k => ∫⁻ u in Set.Ioi (0:ℝ), ENNReal.ofReal (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy
        (Cvs.WeilForm.WindowRepresentative.rep (xw k)) u)) atTop
        ≤ liminf (fun k => ENNReal.ofReal (c - par P R (xw k))) atTop :=
      liminf_le_liminf (Filter.Eventually.of_forall h3)
    have h5 : liminf (fun k => ENNReal.ofReal (c - par P R (xw k))) atTop
        = ENNReal.ofReal (c - par P R y) :=
      ((ENNReal.continuous_ofReal.tendsto _).comp (tendsto_const_nhds.sub hpar)).liminf_eq
    rw [h1]
    exact h2.trans (h4.trans h5.le)
  -- the limit is in the domain
  have hmem : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep y))
      (Set.Ioi (0:ℝ)) (volume : Measure ℝ) :=
    ⟨Cvs.WeilForm.TruncatedArchDomain.aestronglyMeasurable_levy
      (Cvs.WeilForm.SelfConvolutionContinuous.continuous_selfConvolution
        (Cvs.WeilForm.WindowRepresentative.memLp_rep y)).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (levy_nonneg_ae y)).mpr
        (hfatou.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hmem, ?_⟩
  -- and the form does not rise
  have hint : ∫ u in Set.Ioi (0:ℝ), Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (Cvs.WeilForm.WindowRepresentative.rep y) u
      ≤ c - par P R y := by
    have h := hfatou
    rw [← ofReal_integral_eq_lintegral_ofReal hmem (levy_nonneg_ae y)] at h
    exact (ENNReal.ofReal_le_ofReal_iff hnn).mp h
  rw [weilQW_eq_par_add]
  linarith

end Cvs.WeilForm.FormLscDomainClosed
