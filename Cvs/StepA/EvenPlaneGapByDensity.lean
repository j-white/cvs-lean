import Mathlib
import Cvs.StepA.DerivativeFormPrimeSide
import Cvs.StepA.StepAFromTwoGaps
import Cvs.StepA.TruncatedDerivativeFormPrime
import Cvs.Upstream.ContinuousCompactDenseWindow
import Cvs.WeilForm.EvenSectorSecondValue
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.LevyDomainSpectral
import Cvs.WeilForm.OddCapTransfer
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SimplicityCriterionWindow
import Cvs.WeilForm.TruncatedEffectiveSymbol
import Cvs.WeilForm.TruncatedFormL2Below
import Cvs.WeilForm.TruncatedFormPolarised
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowReflectionSymmetry
import Cvs.WeilForm.WindowRepresentative

/-!
# The even plane gap reached by density, on the prime side

Even continuous functions orthogonal to a continuous even trial are dense among the even window
classes orthogonal to it, the truncated form is continuous, and so a prime-side bound on those
functions gives the complement bound that `Cvs.WeilForm.EvenSectorSecondValue` turns into the plane gap.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace Cvs.StepA.EvenPlaneGapByDensity

variable {L : ℝ}

/-- The even part about the midpoint. -/
def evenify (L : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := fun s => (f s + f (L - s)) / 2

theorem evenify_even (L : ℝ) (f : ℝ → ℝ) (s : ℝ) : evenify L f (L - s) = evenify L f s := by
  simp only [evenify, sub_sub_cancel]; ring

theorem evenify_vanish (L : ℝ) {f : ℝ → ℝ} (hf : ∀ s, s ∉ Ioo (0:ℝ) L → f s = 0)
    {s : ℝ} (hs : s ∉ Ioo (0:ℝ) L) : evenify L f s = 0 := by
  have : L - s ∉ Ioo (0:ℝ) L := fun h => hs ⟨by linarith [h.2], by linarith [h.1]⟩
  simp [evenify, hf s hs, hf _ this]

/-- **Evenification is a contraction in `L²`.** -/
theorem eLpNorm_evenify_le (d : ℝ → ℝ) (hd : AEStronglyMeasurable d (volume : Measure ℝ)) (L : ℝ) :
    eLpNorm (evenify L d) 2 (volume : Measure ℝ) ≤ eLpNorm d 2 (volume : Measure ℝ) := by
  set r : ℝ → ℝ := fun s => d (L - s) with hr
  have hrmeas : AEStronglyMeasurable r (volume : Measure ℝ) :=
    hd.comp_measurePreserving ((volume : Measure ℝ).measurePreserving_sub_left L)
  have hfun : evenify L d = (2⁻¹ : ℝ) • (d + r) := by
    funext s; simp only [evenify, Pi.smul_apply, Pi.add_apply, smul_eq_mul, hr]; ring
  rw [hfun, eLpNorm_const_smul]
  have hsub : eLpNorm (d + r) 2 (volume : Measure ℝ)
      ≤ eLpNorm d 2 (volume : Measure ℝ) + eLpNorm r 2 (volume : Measure ℝ) :=
    eLpNorm_add_le (by norm_num)
  have hreq : eLpNorm r 2 (volume : Measure ℝ) = eLpNorm d 2 (volume : Measure ℝ) :=
    Cvs.WeilForm.OddCapTransfer.eLpNorm_reflect d hd L
  rw [hreq] at hsub
  have hsub2 : eLpNorm (d + r) 2 (volume : Measure ℝ) ≤ 2 * eLpNorm d 2 (volume : Measure ℝ) := by
    rw [two_mul]; exact hsub
  have h2e : ‖(2⁻¹ : ℝ)‖ₑ = ENNReal.ofReal 2⁻¹ := by
    rw [Real.eNorm_eq_ofReal_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2⁻¹)]
  have hone : ENNReal.ofReal 2⁻¹ * (2 : ENNReal) = 1 := by
    rw [(by norm_num : (2 : ENNReal) = ENNReal.ofReal 2),
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2⁻¹)]
    norm_num
  calc ‖(2⁻¹ : ℝ)‖ₑ * eLpNorm (d + r) 2 (volume : Measure ℝ)
      ≤ ‖(2⁻¹ : ℝ)‖ₑ * (2 * eLpNorm d 2 (volume : Measure ℝ)) := mul_le_mul' le_rfl hsub2
    _ = eLpNorm d 2 (volume : Measure ℝ) := by rw [h2e, ← mul_assoc, hone, one_mul]

/-- **The truncated form of a class represented by a continuous function supported in the
window.** -/
theorem weilQWTrunc_eq_of_continuous (N P R : ℕ) {g : ℝ → ℝ} (hgc : Continuous g)
    (hgs : ∀ s, s ∉ Ioo (0:ℝ) L → g s = 0) (v : Cvs.WeilForm.WeilFormOnWindowL2.window L)
    (hv : Cvs.WeilForm.WindowRepresentative.rep v =ᵐ[volume] g) :
    Cvs.WeilForm.SimplicityCriterionWindow.weilQWTrunc N P R v
      = 2 * (∫ x : ℝ, g x * Real.exp (x / 2)) * (∫ x : ℝ, g x * Real.exp (-(x / 2)))
        + ∫ t : ℝ, Cvs.WeilForm.TruncatedEffectiveSymbol.truncEffSymbol N P R t
            * Cvs.WeilForm.SelfConvolutionCosine.specDensity g t := by
  have hcs : HasCompactSupport g :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (fun s hs => by
        by_contra hs'
        exact hs (hgs s (fun h' => hs' ⟨h'.1.le, h'.2.le⟩)))
  rw [← Cvs.WeilForm.TruncatedEffectiveSymbol.weilFormTrunc_effective N P R (hgc.memLp_of_hasCompactSupport hcs)
    (hgc.integrable_of_hasCompactSupport hcs)]
  exact Cvs.WeilForm.TruncatedFormL2Below.weilQTrunc_eq ((Cvs.WeilForm.WindowRepresentative.ae_eq_rep v).trans hv)

/-- **The even complement gap on the prime side**, on continuous even functions supported in the
window and orthogonal to `ζf`. -/
def EvenPerpGapTrunc (N P R : ℕ) (L : ℝ) (ζf : ℝ → ℝ) (mu2 : ℝ) : Prop :=
  ∀ g : ℝ → ℝ, Continuous g → (∀ s, s ∉ Ioo (0:ℝ) L → g s = 0) → (∀ s, g (L - s) = g s) →
    (∫ x : ℝ, g x * ζf x) = 0 →
    mu2 * ∫ x : ℝ, g x ^ 2
      ≤ 2 * (∫ x : ℝ, g x * Real.exp (x / 2)) * (∫ x : ℝ, g x * Real.exp (-(x / 2)))
        + ∫ t : ℝ, Cvs.WeilForm.TruncatedEffectiveSymbol.truncEffSymbol N P R t
            * Cvs.WeilForm.SelfConvolutionCosine.specDensity g t

/-- **Removing the component along `ζ` does not increase the distance to a class orthogonal to
`ζ`.** -/
theorem norm_sub_proj_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u ζ : E) (hζ : ζ ≠ 0) :
    ‖u - ((inner ℝ u ζ : ℝ) / ‖ζ‖ ^ 2) • ζ‖ ≤ ‖u‖ := by
  have hζpos : 0 < ‖ζ‖ ^ 2 := by
    have : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ
    positivity
  have hsq : ‖u - ((inner ℝ u ζ : ℝ) / ‖ζ‖ ^ 2) • ζ‖ ^ 2 = ‖u‖ ^ 2 - (inner ℝ u ζ : ℝ) ^ 2 / ‖ζ‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      div_pow]
    field_simp
    ring
  have h1 : ‖u - ((inner ℝ u ζ : ℝ) / ‖ζ‖ ^ 2) • ζ‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    rw [hsq]
    have : 0 ≤ (inner ℝ u ζ : ℝ) ^ 2 / ‖ζ‖ ^ 2 := by positivity
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1

/-- **The complement bound on even window classes, from the prime-side statement.** -/
theorem hbd_of_evenPerpGapTrunc (hL : 0 < L) (N P R : ℕ) {mu2 : ℝ}
    (ζ : Cvs.WeilForm.WeilFormOnWindowL2.window L) {ζf : ℝ → ℝ}
    (hζ : Cvs.WeilForm.WindowRepresentative.rep ζ =ᵐ[volume] ζf) (hζc : Continuous ζf)
    (hζs : ∀ s, s ∉ Ioo (0:ℝ) L → ζf s = 0) (hζe : ∀ s, ζf (L - s) = ζf s) (hζne : ζ ≠ 0)
    (h : EvenPerpGapTrunc N P R L ζf mu2) :
    ∀ χ : Cvs.WeilForm.WeilFormOnWindowL2.window L, Cvs.WeilForm.WindowReflectionSymmetry.reflW χ = χ →
      (inner ℝ ζ χ : ℝ) = 0 →
      mu2 * ‖χ‖ ^ 2 ≤ Cvs.WeilForm.SimplicityCriterionWindow.weilQWTrunc N P R χ := by
  intro χ hrw hperp
  -- the representative is even almost everywhere
  have heven_ae : (fun s => Cvs.WeilForm.WindowRepresentative.rep χ (L - s))
      =ᵐ[volume] Cvs.WeilForm.WindowRepresentative.rep χ := by
    have h1 := Cvs.WeilForm.WindowReflectionSymmetry.rep_reflW_ae χ
    rw [hrw] at h1
    exact h1.symm
  -- inner products against `ζ` are integrals against `ζf`
  have hinner : ∀ (ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L) (g : ℝ → ℝ),
      Cvs.WeilForm.WindowRepresentative.rep ψ =ᵐ[volume] g → (∀ s, s ∉ Ioo (0:ℝ) L → g s = 0) →
      (inner ℝ ζ ψ : ℝ) = ∫ x : ℝ, g x * ζf x := by
    intro ψ g hg hgs
    rw [Cvs.WeilForm.TruncatedFormPolarised.inner_eq_integral hL.le,
      Cvs.StepA.DerivativeFormPrimeSide.integral_eq_interval hL.le (φ := fun x => g x * ζf x)
        (fun s hs => by rw [hgs s hs, zero_mul])]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hζ, hg] with s h1 h2 _
    rw [h1, h2, mul_comm]
  -- the approximants
  have happrox : ∀ k : ℕ, ∃ ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L,
      mu2 * ‖ψ‖ ^ 2 ≤ Cvs.WeilForm.SimplicityCriterionWindow.weilQWTrunc N P R ψ ∧
      ‖ψ - χ‖ ≤ 1 / ((k : ℝ) + 1) := by
    intro k
    have hε : (0:ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    obtain ⟨g, hgc, _, hgs, hg⟩ :=
      Cvs.Upstream.ContinuousCompactDenseWindow.approx_by_continuous_supported hL χ hε
    set e := evenify L g with hedef
    have hec : Continuous e := by
      show Continuous (fun s => (g s + g (L - s)) / 2)
      fun_prop
    have hes : ∀ s, s ∉ Ioo (0:ℝ) L → e s = 0 := fun s hs => evenify_vanish L hgs hs
    have hee : ∀ s, e (L - s) = e s := fun s => evenify_even L g s
    have hecs : HasCompactSupport e :=
      HasCompactSupport.of_support_subset_isCompact isCompact_Icc
        (fun s hs => by
          by_contra hs'
          exact hs (hes s (fun h' => hs' ⟨h'.1.le, h'.2.le⟩)))
    obtain ⟨ε₀, hε₀⟩ := Cvs.WeilForm.OddCapTransfer.window_of_continuous hec hecs
      (fun s hs => hes s (fun h' => hs ⟨h'.1, h'.2.le⟩))
    -- the class of the even approximant is within `ε` of `χ`
    have hdist : ‖ε₀ - χ‖ ≤ 1 / ((k : ℝ) + 1) := by
      have hdiff : (fun s => Cvs.WeilForm.WindowRepresentative.rep χ s - e s)
          =ᵐ[volume] evenify L (fun s => Cvs.WeilForm.WindowRepresentative.rep χ s - g s) := by
        filter_upwards [heven_ae] with s hs
        simp only [hedef, evenify, hs]
        ring
      have hmeas : AEStronglyMeasurable (fun s => Cvs.WeilForm.WindowRepresentative.rep χ s - g s)
          (volume : Measure ℝ) :=
        (Cvs.WeilForm.WindowRepresentative.memLp_rep χ).aestronglyMeasurable.sub hgc.aestronglyMeasurable
      have hbound : eLpNorm (fun s => Cvs.WeilForm.WindowRepresentative.rep χ s - e s) 2 (volume : Measure ℝ)
          ≤ ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
        rw [eLpNorm_congr_ae hdiff]
        exact (eLpNorm_evenify_le _ hmeas L).trans hg
      rw [← Submodule.norm_coe, Submodule.coe_sub, Lp.norm_def]
      have hae : ⇑((ε₀ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))
            - ⇑((χ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))
          =ᵐ[volume] -(fun s => Cvs.WeilForm.WindowRepresentative.rep χ s - e s) := by
        filter_upwards [Cvs.WeilForm.WindowRepresentative.ae_eq_rep ε₀, Cvs.WeilForm.WindowRepresentative.ae_eq_rep χ,
          hε₀] with s h1 h2 h3
        show Cvs.WeilForm.WindowRepresentative.fn ε₀ s - Cvs.WeilForm.WindowRepresentative.fn χ s
          = -(Cvs.WeilForm.WindowRepresentative.rep χ s - e s)
        rw [h1, h2, h3]; ring
      rw [eLpNorm_congr_ae (Lp.coeFn_sub _ _), eLpNorm_congr_ae hae, eLpNorm_neg]
      exact ENNReal.toReal_le_of_le_ofReal hε.le hbound
    -- project off `ζ`
    set c : ℝ := (inner ℝ ε₀ ζ : ℝ) / ‖ζ‖ ^ 2 with hc
    refine ⟨ε₀ - c • ζ, ?_, ?_⟩
    · -- the prime-side bound applies to the representative `e − c·ζf`
      have hrep : Cvs.WeilForm.WindowRepresentative.rep (ε₀ - c • ζ) =ᵐ[volume] fun s => e s - c * ζf s := by
        have h1 := Cvs.WeilForm.LevyDomainSpectral.rep_add_ae ε₀ (-(c • ζ))
        have h2 := Cvs.WeilForm.LevyDomainSpectral.rep_smul_ae (-c) ζ
        have h3 : (ε₀ - c • ζ) = ε₀ + (-(c • ζ)) := sub_eq_add_neg _ _
        have h4 : (-(c • ζ) : Cvs.WeilForm.WeilFormOnWindowL2.window L) = (-c) • ζ := (_root_.neg_smul c ζ).symm
        rw [h3, h4]
        rw [h4] at h1
        filter_upwards [h1, h2, hε₀, hζ] with s hs1 hs2 hs3 hs4
        rw [hs1]
        simp only [Pi.add_apply, hs2, hs3, hs4]
        ring
      have hhc : Continuous fun s => e s - c * ζf s := hec.sub (hζc.const_mul c)
      have hhs : ∀ s, s ∉ Ioo (0:ℝ) L → (fun s => e s - c * ζf s) s = 0 := fun s hs => by
        simp [hes s hs, hζs s hs]
      have hhe : ∀ s, (fun s => e s - c * ζf s) (L - s) = (fun s => e s - c * ζf s) s :=
        fun s => by simp only [hee s, hζe s]
      have hperp' : (∫ x : ℝ, (e x - c * ζf x) * ζf x) = 0 := by
        rw [← hinner (ε₀ - c • ζ) _ hrep hhs, inner_sub_right]
        have hsm : (inner ℝ ζ (c • ζ) : ℝ) = c * (inner ℝ ζ ζ : ℝ) := real_inner_smul_right ζ ζ c
        have hζpos : ‖ζ‖ ^ 2 ≠ 0 := by
          have : 0 < ‖ζ‖ := norm_pos_iff.mpr hζne
          positivity
        rw [hsm, real_inner_self_eq_norm_sq, hc, real_inner_comm ε₀ ζ, div_mul_cancel₀ _ hζpos,
          sub_self]
      have hnorm : ‖ε₀ - c • ζ‖ ^ 2 = ∫ x : ℝ, (e x - c * ζf x) ^ 2 := by
        rw [Cvs.WeilForm.OddCapTransfer.sq_norm_eq_integral_rep]
        exact integral_congr_ae (hrep.fun_comp fun y : ℝ => y ^ 2)
      rw [weilQWTrunc_eq_of_continuous N P R hhc hhs (ε₀ - c • ζ) hrep, hnorm]
      exact h _ hhc hhs hhe hperp'
    · -- the projection does not increase the distance
      have hχperp : (inner ℝ χ ζ : ℝ) = 0 := by rw [real_inner_comm]; exact hperp
      have hkey : ε₀ - c • ζ - χ = (ε₀ - χ) - ((inner ℝ (ε₀ - χ) ζ : ℝ) / ‖ζ‖ ^ 2) • ζ := by
        rw [inner_sub_left, hχperp, sub_zero, hc]; abel
      rw [hkey]
      exact (norm_sub_proj_le (ε₀ - χ) ζ hζne).trans hdist
  choose ψ hψ using happrox
  set χw : Cvs.WeilForm.WeilFormOnWindowL2.window L := χ
  have hconv : Tendsto (fun k => ((ψ k : Cvs.WeilForm.WeilFormOnWindowL2.window L)
      : Lp ℝ 2 (volume : Measure ℝ))) atTop (𝓝 (χ : Lp ℝ 2 (volume : Measure ℝ))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    rw [← Submodule.coe_sub, Submodule.norm_coe]
    exact (hψ k).2
  have hconv' : Tendsto (fun k => ψ k) atTop (𝓝 χ) := tendsto_subtype_rng.mpr hconv
  have hlimQ := Cvs.StepA.TruncatedDerivativeFormPrime.tendsto_weilQWTrunc hL.le N P R hconv
  have hlimN : Tendsto (fun k => mu2 * ‖ψ k‖ ^ 2) atTop (𝓝 (mu2 * ‖χ‖ ^ 2)) :=
    (((continuous_norm.pow 2).tendsto χ).comp hconv').const_mul _
  exact le_of_tendsto_of_tendsto hlimN hlimQ (Eventually.of_forall fun k => (hψ k).1)

/-- **The plane gap from the prime-side complement statement.** -/
theorem hplane_of_evenPerpGapTrunc (hL : 0 < L) (N P R : ℕ) {mu2 : ℝ}
    (ζ : Cvs.WeilForm.WeilFormOnWindowL2.window L) {ζf : ℝ → ℝ}
    (hζ : Cvs.WeilForm.WindowRepresentative.rep ζ =ᵐ[volume] ζf) (hζc : Continuous ζf)
    (hζs : ∀ s, s ∉ Ioo (0:ℝ) L → ζf s = 0) (hζe : ∀ s, ζf (L - s) = ζf s) (hζne : ζ ≠ 0)
    (h : EvenPerpGapTrunc N P R L ζf mu2) :
    ∀ V : Submodule ℝ (Cvs.WeilForm.FormDomain.formDomain hL.le),
      Module.finrank ℝ V = 2 → V ≤ Cvs.StepA.StepAFromTwoGaps.evenSub hL.le →
      ∃ v ∈ V, v ≠ 0 ∧ mu2 * ‖v‖ ^ 2 ≤ Cvs.WeilForm.SimplicityCriterionWindow.weilQWTrunc N P R
        (v : Cvs.WeilForm.WeilFormOnWindowL2.window L) :=
  fun V h2 hV => Cvs.WeilForm.EvenSectorSecondValue.hplane_of_perp_bound N P R ζ
    (hbd_of_evenPerpGapTrunc hL N P R ζ hζ hζc hζs hζe hζne h) V h2 hV

end Cvs.StepA.EvenPlaneGapByDensity
