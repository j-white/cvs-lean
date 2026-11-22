import Mathlib
import Cvs.StepA.DerivativeFormPrimeSide
import Cvs.Upstream.ContinuousCompactDenseWindow
import Cvs.WeilForm.Archimedean.TruncatedSymbolConstant
import Cvs.WeilForm.ChannelKernelBoundedOperator
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.OddCapTransfer
import Cvs.WeilForm.PoleAndPrimeContinuousWindow
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SimplicityCriterionWindow
import Cvs.WeilForm.TruncatedEffectiveSymbol
import Cvs.WeilForm.TruncatedFormKernelOperator
import Cvs.WeilForm.TruncatedFormL2Below
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowReflectionSymmetry
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-!
# The truncated window form of a derivative, on the prime side

`weilFormTrunc N P R f = −¼·pole(g) + ∫ truncEffSymbol N P R t · t²·specDensity g t` for `f = g'`
inside the window, needing only `f ∈ L¹ ∩ L²`.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace Cvs.StepA.TruncatedDerivativeFormPrime

variable {L : ℝ} {g f : ℝ → ℝ}

/-- **The truncated form of a derivative.** -/
theorem weilFormTrunc_deriv (N P R : ℕ) (hL : 0 ≤ L)
    (hgs : ∀ s, s ∉ Ioo (0:ℝ) L → g s = 0) (hfs : ∀ s, s ∉ Ioo (0:ℝ) L → f s = 0)
    (hg : ContinuousOn g (Icc 0 L))
    (hg' : ∀ x ∈ Ioo (0:ℝ) L, HasDerivWithinAt g (f x) (Ioi x) x)
    (hf : IntervalIntegrable f volume 0 L)
    (hf2 : MemLp f 2 (volume : Measure ℝ)) (hfint : Integrable f (volume : Measure ℝ)) :
    Cvs.WeilForm.TruncatedFormL2Below.weilFormTrunc N P R f
      = -(1/4) * (2 * (∫ x : ℝ, g x * Real.exp (x / 2))
            * (∫ x : ℝ, g x * Real.exp (-(x / 2))))
        + ∫ t : ℝ, Cvs.WeilForm.TruncatedEffectiveSymbol.truncEffSymbol N P R t
            * (t ^ 2 * Cvs.WeilForm.SelfConvolutionCosine.specDensity g t) := by
  rw [Cvs.WeilForm.TruncatedEffectiveSymbol.weilFormTrunc_effective N P R hf2 hfint,
    Cvs.StepA.DerivativeFormPrimeSide.pole_deriv hL hgs hfs hg hg' hf]
  congr 1
  congr 1; funext t
  rw [Cvs.StepA.DerivativeFormPrimeSide.specDensity_deriv hL hgs hfs hg hg' hf]

/-- **The truncated form of a window class represented by a derivative.** -/
theorem weilQWTrunc_deriv (N P R : ℕ) (hL : 0 ≤ L)
    (hgs : ∀ s, s ∉ Ioo (0:ℝ) L → g s = 0) (hfs : ∀ s, s ∉ Ioo (0:ℝ) L → f s = 0)
    (hg : ContinuousOn g (Icc 0 L))
    (hg' : ∀ x ∈ Ioo (0:ℝ) L, HasDerivWithinAt g (f x) (Ioi x) x)
    (hf : IntervalIntegrable f volume 0 L)
    (hf2 : MemLp f 2 (volume : Measure ℝ)) (hfint : Integrable f (volume : Measure ℝ))
    (v : Cvs.WeilForm.WeilFormOnWindowL2.window L) (hv : Cvs.WeilForm.WindowRepresentative.rep v =ᵐ[volume] f) :
    Cvs.WeilForm.SimplicityCriterionWindow.weilQWTrunc N P R v
      = -(1/4) * (2 * (∫ x : ℝ, g x * Real.exp (x / 2))
            * (∫ x : ℝ, g x * Real.exp (-(x / 2))))
        + ∫ t : ℝ, Cvs.WeilForm.TruncatedEffectiveSymbol.truncEffSymbol N P R t
            * (t ^ 2 * Cvs.WeilForm.SelfConvolutionCosine.specDensity g t) := by
  rw [← weilFormTrunc_deriv N P R hL hgs hfs hg hg' hf hf2 hfint]
  exact Cvs.WeilForm.TruncatedFormL2Below.weilQTrunc_eq ((Cvs.WeilForm.WindowRepresentative.ae_eq_rep v).trans hv)

/-! ### Sequential continuity of the truncated form -/

/-- **The truncated form is sequentially continuous on the window.** -/
theorem tendsto_weilQWTrunc (hL : 0 ≤ L) (N P R : ℕ) {x : ℕ → Cvs.WeilForm.WeilFormOnWindowL2.window L}
    {y : Cvs.WeilForm.WeilFormOnWindowL2.window L}
    (hx : Tendsto (fun k => ((x k : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)))
      atTop (𝓝 (y : Lp ℝ 2 (volume : Measure ℝ)))) :
    Tendsto (fun k => Cvs.WeilForm.SimplicityCriterionWindow.weilQWTrunc N P R (x k)) atTop
      (𝓝 (Cvs.WeilForm.SimplicityCriterionWindow.weilQWTrunc N P R y)) := by
  have hx' : Tendsto x atTop (𝓝 y) := tendsto_subtype_rng.mpr hx
  simp_rw [Cvs.WeilForm.TruncatedFormKernelOperator.weilQWTrunc_eq_inner hL N P R]
  refine Tendsto.sub (Tendsto.sub ?_ ?_) (Cvs.WeilForm.PoleAndPrimeContinuousWindow.tendsto_primeSide P R hx)
  · exact ((continuous_norm.pow 2).tendsto y |>.comp hx').const_mul _
  · have hc : Continuous fun φ : Cvs.WeilForm.WeilFormOnWindowL2.window L =>
        (inner ℝ (Cvs.WeilForm.ChannelKernelBoundedOperator.kernelCLM N L hL φ) φ : ℝ) :=
      (Cvs.WeilForm.ChannelKernelBoundedOperator.kernelCLM N L hL).continuous.inner continuous_id
    exact (hc.tendsto y).comp hx'

/-! ### The primitive from the left end of the window -/

/-- The primitive from `0`. -/
def prim0 (f : ℝ → ℝ) (s : ℝ) : ℝ := ∫ x in (0:ℝ)..s, f x

/-- **The primitive has derivative `f` everywhere**, for continuous `f`. -/
theorem hasDerivAt_prim0 {f : ℝ → ℝ} (hf : Continuous f) (s : ℝ) :
    HasDerivAt (prim0 f) (f s) s :=
  intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt

/-- **The primitive is continuous.** -/
theorem continuous_prim0 {f : ℝ → ℝ} (hf : Continuous f) : Continuous (prim0 f) :=
  continuous_iff_continuousAt.mpr fun s => (hasDerivAt_prim0 hf s).continuousAt

/-- **An odd function integrates to zero over the window.** -/
theorem integral_window_eq_zero {f : ℝ → ℝ} (hf : Continuous f)
    (hodd : ∀ s, f (L - s) = -f s) : ∫ x in (0:ℝ)..L, f x = 0 := by
  have h1 : ∫ x in (0:ℝ)..L, f (L - x) = ∫ x in (0:ℝ)..L, f x := by
    rw [intervalIntegral.integral_comp_sub_left (fun x => f x) L]; simp
  have h2 : ∫ x in (0:ℝ)..L, f (L - x) = -∫ x in (0:ℝ)..L, f x := by
    simp_rw [hodd]; rw [intervalIntegral.integral_neg]
  linarith

/-- **The primitive of an odd function vanishes off the open window.** -/
theorem prim0_eq_zero {f : ℝ → ℝ} (hf : Continuous f) (hL : 0 ≤ L)
    (hfs : ∀ s, s ∉ Ioo (0:ℝ) L → f s = 0) (hodd : ∀ s, f (L - s) = -f s)
    {s : ℝ} (hs : s ∉ Ioo (0:ℝ) L) : prim0 f s = 0 := by
  unfold prim0
  by_cases h0 : s ≤ 0
  · rw [intervalIntegral.integral_symm]
    have : ∫ x in s..(0:ℝ), f x = ∫ x in s..(0:ℝ), (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le h0] at hx
      exact hfs x (fun hx' => by linarith [hx.2, hx'.1])
    rw [this]; simp
  · have hsL : L ≤ s := by
      by_contra h; push Not at h; exact hs ⟨by linarith, h⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable 0 L)
      (hf.intervalIntegrable L s), integral_window_eq_zero hf hodd]
    have : ∫ x in L..s, f x = ∫ x in L..s, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hsL] at hx
      exact hfs x (fun hx' => by linarith [hx.1, hx'.2])
    rw [this]; simp

/-! ### Working backwards: the odd gap on the prime side, truncated -/

/-- **The odd gap at level `lam` for the truncated form, on the prime side**, stated on continuous
odd functions supported in the window through their even primitives. -/
def OddGapDerivTrunc (N P R : ℕ) (L lam : ℝ) : Prop :=
  ∀ f : ℝ → ℝ, Continuous f → (∀ s, s ∉ Ioo (0:ℝ) L → f s = 0) → (∀ s, f (L - s) = -f s) →
    lam * ∫ x : ℝ, f x ^ 2
      ≤ -(1/4) * (2 * (∫ x : ℝ, prim0 f x * Real.exp (x / 2))
            * (∫ x : ℝ, prim0 f x * Real.exp (-(x / 2))))
        + ∫ t : ℝ, Cvs.WeilForm.TruncatedEffectiveSymbol.truncEffSymbol N P R t
            * (t ^ 2 * Cvs.WeilForm.SelfConvolutionCosine.specDensity (prim0 f) t)

/-- **The odd gap on continuous odd functions, from the prime-side statement.** -/
theorem weilQWTrunc_ge_of_oddGapDerivTrunc {N P R : ℕ} {lam : ℝ}
    (h : OddGapDerivTrunc N P R L lam) (hL : 0 ≤ L) {f : ℝ → ℝ} (hf : Continuous f)
    (hfs : ∀ s, s ∉ Ioo (0:ℝ) L → f s = 0) (hodd : ∀ s, f (L - s) = -f s)
    (v : Cvs.WeilForm.WeilFormOnWindowL2.window L) (hv : Cvs.WeilForm.WindowRepresentative.rep v =ᵐ[volume] f) :
    lam * ‖v‖ ^ 2 ≤ Cvs.WeilForm.SimplicityCriterionWindow.weilQWTrunc N P R v := by
  have hcs : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (fun s hs => by
        by_contra hs'
        exact hs (hfs s (fun h' => hs' ⟨h'.1.le, h'.2.le⟩)))
  have hf2 : MemLp f 2 (volume : Measure ℝ) := hf.memLp_of_hasCompactSupport hcs
  have hfint : Integrable f (volume : Measure ℝ) := hf.integrable_of_hasCompactSupport hcs
  have hnorm : ‖v‖ ^ 2 = ∫ x : ℝ, f x ^ 2 := by
    rw [Cvs.WeilForm.OddCapTransfer.sq_norm_eq_integral_rep]
    exact integral_congr_ae (hv.fun_comp fun y : ℝ => y ^ 2)
  rw [weilQWTrunc_deriv N P R hL (fun s hs => prim0_eq_zero hf hL hfs hodd hs) hfs
    (continuous_prim0 hf).continuousOn
    (fun x _ => (hasDerivAt_prim0 hf x).hasDerivWithinAt) (hf.intervalIntegrable _ _) hf2 hfint
    v hv, hnorm]
  exact h f hf hfs hodd

/-- **The odd gap on the form domain, from the prime-side statement at a higher level.** -/
theorem hoddT_of_oddGapDerivTrunc (hL : 0 < L) (N P R : ℕ) {lam lam' : ℝ} (hll : lam < lam')
    (h : OddGapDerivTrunc N P R L lam') :
    ∀ o : Cvs.WeilForm.FormDomain.formDomain hL.le,
      Cvs.WeilForm.WindowReflectionSymmetry.reflD hL.le o = -o → o ≠ 0 →
      lam * ‖o‖ ^ 2 < Cvs.WeilForm.SimplicityCriterionWindow.weilQWTrunc N P R (o : Cvs.WeilForm.WeilFormOnWindowL2.window L) := by
  intro o hro hne
  set ow : Cvs.WeilForm.WeilFormOnWindowL2.window L := (o : Cvs.WeilForm.WeilFormOnWindowL2.window L) with how
  have hrw : Cvs.WeilForm.WindowReflectionSymmetry.reflW ow = -ow := congrArg Subtype.val hro
  -- the representative is odd almost everywhere
  have hodd_ae : (fun s => Cvs.WeilForm.WindowRepresentative.rep ow (L - s))
      =ᵐ[volume] fun s => -Cvs.WeilForm.WindowRepresentative.rep ow s := by
    have h1 := Cvs.WeilForm.WindowReflectionSymmetry.rep_reflW_ae ow
    have h2 : Cvs.WeilForm.WindowRepresentative.rep (Cvs.WeilForm.WindowReflectionSymmetry.reflW ow)
        =ᵐ[volume] fun s => -Cvs.WeilForm.WindowRepresentative.rep ow s := by
      rw [hrw]
      have := Cvs.WeilForm.WindowRepresentative.ae_eq_rep (-ow)
      have hneg := Lp.coeFn_neg (ow : Lp ℝ 2 (volume : Measure ℝ))
      have h3 := Cvs.WeilForm.WindowRepresentative.ae_eq_rep ow
      filter_upwards [this, hneg, h3] with s hs1 hs2 hs3
      rw [← hs1]
      show ((-ow : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)) s = _
      rw [Submodule.coe_neg, hs2]
      show -(Cvs.WeilForm.WindowRepresentative.fn ow s) = _
      rw [hs3]
    exact h1.symm.trans h2
  -- the approximating odd continuous functions
  have happrox : ∀ k : ℕ, ∃ φ : Cvs.WeilForm.WeilFormOnWindowL2.window L,
      lam' * ‖φ‖ ^ 2 ≤ Cvs.WeilForm.SimplicityCriterionWindow.weilQWTrunc N P R φ ∧
      ‖φ - ow‖ ≤ 1 / ((k : ℝ) + 1) := by
    intro k
    have hε : (0:ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    obtain ⟨g, hgc, hgcs, hgs, hg⟩ :=
      Cvs.Upstream.ContinuousCompactDenseWindow.approx_by_continuous_supported hL ow hε
    set f := Cvs.WeilForm.OddCapTransfer.oddify L g with hfdef
    have hfc : Continuous f := by
      show Continuous (fun s => (g s - g (L - s)) / 2)
      fun_prop
    have hfs : ∀ s, s ∉ Ioo (0:ℝ) L → f s = 0 := fun s hs =>
      Cvs.WeilForm.OddCapTransfer.oddify_vanish L hgs hs
    have hfodd : ∀ s, f (L - s) = -f s := fun s => Cvs.WeilForm.OddCapTransfer.oddify_odd L g s
    have hfcs : HasCompactSupport f :=
      HasCompactSupport.of_support_subset_isCompact isCompact_Icc
        (fun s hs => by
          by_contra hs'
          exact hs (hfs s (fun h' => hs' ⟨h'.1.le, h'.2.le⟩)))
    obtain ⟨φ, hφ⟩ := Cvs.WeilForm.OddCapTransfer.window_of_continuous hfc hfcs
      (fun s hs => hfs s (fun h' => hs ⟨h'.1, h'.2.le⟩))
    refine ⟨φ, weilQWTrunc_ge_of_oddGapDerivTrunc h hL.le hfc hfs hfodd φ hφ, ?_⟩
    -- the distance: `oddify` contracts, and fixes the odd representative
    have hdiff : (fun s => Cvs.WeilForm.WindowRepresentative.rep ow s - f s)
        =ᵐ[volume] Cvs.WeilForm.OddCapTransfer.oddify L (fun s => Cvs.WeilForm.WindowRepresentative.rep ow s - g s) := by
      filter_upwards [hodd_ae] with s hs
      simp only [hfdef, Cvs.WeilForm.OddCapTransfer.oddify, hs]
      ring
    have hmeas : AEStronglyMeasurable (fun s => Cvs.WeilForm.WindowRepresentative.rep ow s - g s)
        (volume : Measure ℝ) :=
      (Cvs.WeilForm.WindowRepresentative.memLp_rep ow).aestronglyMeasurable.sub hgc.aestronglyMeasurable
    have hbound : eLpNorm (fun s => Cvs.WeilForm.WindowRepresentative.rep ow s - f s) 2 (volume : Measure ℝ)
        ≤ ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
      rw [eLpNorm_congr_ae hdiff]
      exact (Cvs.WeilForm.OddCapTransfer.eLpNorm_oddify_le _ hmeas L).trans hg
    rw [Submodule.coe_norm, Submodule.coe_sub, Lp.norm_def]
    have hae : ⇑((φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))
          - ⇑((ow : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))
        =ᵐ[volume] -(fun s => Cvs.WeilForm.WindowRepresentative.rep ow s - f s) := by
      filter_upwards [Cvs.WeilForm.WindowRepresentative.ae_eq_rep φ, Cvs.WeilForm.WindowRepresentative.ae_eq_rep ow, hφ]
        with s h1 h2 h3
      show Cvs.WeilForm.WindowRepresentative.fn φ s - Cvs.WeilForm.WindowRepresentative.fn ow s
        = -(Cvs.WeilForm.WindowRepresentative.rep ow s - f s)
      rw [h1, h2, h3]; ring
    rw [eLpNorm_congr_ae (Lp.coeFn_sub _ _), eLpNorm_congr_ae hae, eLpNorm_neg]
    exact ENNReal.toReal_le_of_le_ofReal hε.le hbound
  choose φ hφ using happrox
  -- pass to the limit
  have hconv : Tendsto (fun k => ((φ k : Cvs.WeilForm.WeilFormOnWindowL2.window L)
      : Lp ℝ 2 (volume : Measure ℝ))) atTop (𝓝 (ow : Lp ℝ 2 (volume : Measure ℝ))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    rw [← Submodule.coe_sub, ← Submodule.coe_norm]
    exact (hφ k).2
  have hconv' : Tendsto (fun k => φ k) atTop (𝓝 ow) := tendsto_subtype_rng.mpr hconv
  have hlimQ := tendsto_weilQWTrunc hL.le N P R hconv
  have hlimN : Tendsto (fun k => lam' * ‖φ k‖ ^ 2) atTop (𝓝 (lam' * ‖ow‖ ^ 2)) :=
    (((continuous_norm.pow 2).tendsto ow).comp hconv').const_mul _
  have hle : lam' * ‖ow‖ ^ 2 ≤ Cvs.WeilForm.SimplicityCriterionWindow.weilQWTrunc N P R ow :=
    le_of_tendsto_of_tendsto hlimN hlimQ (Eventually.of_forall fun k => (hφ k).1)
  have hpos : 0 < ‖ow‖ ^ 2 := by
    have : ow ≠ 0 := fun h0 => hne (Subtype.ext h0)
    have : 0 < ‖ow‖ := norm_pos_iff.mpr this
    positivity
  have : lam * ‖ow‖ ^ 2 < lam' * ‖ow‖ ^ 2 := by nlinarith
  calc lam * ‖o‖ ^ 2 = lam * ‖ow‖ ^ 2 := rfl
    _ < lam' * ‖ow‖ ^ 2 := this
    _ ≤ _ := hle

end Cvs.StepA.TruncatedDerivativeFormPrime
