import Mathlib
import Cvs.Upstream.ContinuousCompactDenseWindow
import Cvs.WeilForm.ChannelCapClosedL2
import Cvs.WeilForm.ChannelFunctionalL2
import Cvs.WeilForm.OddChannelCap
import Cvs.WeilForm.WeilFormAeClass
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.WeilPositivityStatement

/-!
# The per-channel odd cap transfers to odd `L²` window classes

    `chanInt b (rep y) ≤ (2b/(b²+t²))·‖y‖²`

for an odd `L²` window class `y`, by oddified density approximants and `Cvs.WeilForm.ChannelCapClosedL2`.
-/

noncomputable section

open MeasureTheory Set Real Filter Topology Cvs.Zeta.Explicit.Weil
open scoped ENNReal

namespace Cvs.WeilForm.OddCapTransfer

/-- The odd part of `f` about `L/2`. -/
def oddify (L : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := fun s => (f s - f (L - s)) / 2

/-- Oddification is odd under the reflection `s ↦ L - s`. -/
theorem oddify_odd (L : ℝ) (f : ℝ → ℝ) (s : ℝ) : oddify L f (L - s) = - oddify L f s := by
  simp only [oddify, sub_sub_cancel]; ring

/-- Oddification vanishes wherever `f` vanishes off the open interval. -/
theorem oddify_vanish (L : ℝ) {f : ℝ → ℝ} (hf : ∀ s, s ∉ Ioo (0:ℝ) L → f s = 0)
    {s : ℝ} (hs : s ∉ Ioo (0:ℝ) L) : oddify L f s = 0 := by
  have h1 : f s = 0 := hf s hs
  have h2 : f (L - s) = 0 :=
    hf (L - s) (fun hmem => hs ⟨by linarith [hmem.1, hmem.2], by linarith [hmem.1, hmem.2]⟩)
  simp only [oddify, h1, h2]; ring

/-- The reflection `s ↦ L - s` preserves the `L²` seminorm. -/
theorem eLpNorm_reflect (h : ℝ → ℝ) (hh : AEStronglyMeasurable h (volume : Measure ℝ)) (L : ℝ) :
    eLpNorm (fun s => h (L - s)) 2 (volume : Measure ℝ) = eLpNorm h 2 (volume : Measure ℝ) := by
  have hmp : MeasurePreserving (fun s : ℝ => L - s) (volume : Measure ℝ) (volume : Measure ℝ) :=
    (volume : Measure ℝ).measurePreserving_sub_left L
  have := eLpNorm_comp_measurePreserving (p := 2) hh hmp
  simpa [Function.comp_def] using this

/-- Oddification is a contraction in `L²`. -/
theorem eLpNorm_oddify_le (d : ℝ → ℝ) (hd : AEStronglyMeasurable d (volume : Measure ℝ)) (L : ℝ) :
    eLpNorm (oddify L d) 2 (volume : Measure ℝ) ≤ eLpNorm d 2 (volume : Measure ℝ) := by
  set r : ℝ → ℝ := fun s => d (L - s) with hr
  have hrmeas : AEStronglyMeasurable r (volume : Measure ℝ) :=
    hd.comp_measurePreserving ((volume : Measure ℝ).measurePreserving_sub_left L)
  have hfun : oddify L d = (2⁻¹ : ℝ) • (d - r) := by
    funext s; simp only [oddify, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hr]; ring
  rw [hfun, eLpNorm_const_smul]
  have hsub : eLpNorm (d - r) 2 (volume : Measure ℝ)
      ≤ eLpNorm d 2 (volume : Measure ℝ) + eLpNorm r 2 (volume : Measure ℝ) := by
    have hde : (d - r) = d + (-r) := by funext s; simp [sub_eq_add_neg]
    rw [hde]
    calc eLpNorm (d + (-r)) 2 (volume : Measure ℝ)
        ≤ eLpNorm d 2 (volume : Measure ℝ) + eLpNorm (-r) 2 (volume : Measure ℝ) :=
          eLpNorm_add_le (by norm_num)
      _ = eLpNorm d 2 (volume : Measure ℝ) + eLpNorm r 2 (volume : Measure ℝ) := by
          rw [eLpNorm_neg]
  have hreq : eLpNorm r 2 (volume : Measure ℝ) = eLpNorm d 2 (volume : Measure ℝ) :=
    eLpNorm_reflect d hd L
  rw [hreq] at hsub
  have hsub2 : eLpNorm (d - r) 2 (volume : Measure ℝ) ≤ 2 * eLpNorm d 2 (volume : Measure ℝ) := by
    rw [two_mul]; exact hsub
  have h2e : ‖(2⁻¹ : ℝ)‖ₑ = ENNReal.ofReal 2⁻¹ := by
    rw [Real.eNorm_eq_ofReal_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2⁻¹)]
  have hone : ENNReal.ofReal 2⁻¹ * (2 : ℝ≥0∞) = 1 := by
    rw [(by norm_num : (2 : ℝ≥0∞) = ENNReal.ofReal 2),
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2⁻¹)]
    norm_num
  have hfinal : ‖(2⁻¹ : ℝ)‖ₑ * (2 * eLpNorm d 2 (volume : Measure ℝ))
      = eLpNorm d 2 (volume : Measure ℝ) := by
    rw [h2e, ← mul_assoc, hone, one_mul]
  calc ‖(2⁻¹ : ℝ)‖ₑ * eLpNorm (d - r) 2 (volume : Measure ℝ)
      ≤ ‖(2⁻¹ : ℝ)‖ₑ * (2 * eLpNorm d 2 (volume : Measure ℝ)) := by
        exact mul_le_mul' le_rfl hsub2
    _ = eLpNorm d 2 (volume : Measure ℝ) := hfinal

/-- The squared norm of a window class is the integral of its representative squared. -/
theorem sq_norm_eq_integral_rep {L : ℝ} (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    ‖φ‖ ^ 2 = ∫ x, (Cvs.WeilForm.WindowRepresentative.rep φ x) ^ 2 := by
  have h1 : selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ) 0 = ‖φ‖ ^ 2 := by
    rw [← Cvs.WeilForm.WeilFormAeClass.selfConvolution_congr_ae (Cvs.WeilForm.WindowRepresentative.ae_eq_rep φ) 0]
    exact Cvs.WeilForm.WindowRepresentative.selfConvolution_zero φ
  rw [← h1]
  unfold selfConvolution
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [pow_two]

/-- A continuous, compactly supported function vanishing off the window is a window class. -/
theorem window_of_continuous {L : ℝ} {f : ℝ → ℝ} (hf : Continuous f) (hcf : HasCompactSupport f)
    (hs : ∀ s, s ∉ Ioc (0:ℝ) L → f s = 0) :
    ∃ φ : Cvs.WeilForm.WeilFormOnWindowL2.window L, Cvs.WeilForm.WindowRepresentative.rep φ =ᵐ[volume] f := by
  have hmem : MemLp f 2 (volume : Measure ℝ) := hf.memLp_of_hasCompactSupport (μ := volume) hcf
  have hwin : (hmem.toLp f) ∈ Cvs.WeilForm.WeilFormOnWindowL2.window L := by
    filter_upwards [hmem.coeFn_toLp] with x hx hxne
    rw [hx]; exact hs x hxne
  refine ⟨⟨hmem.toLp f, hwin⟩, ?_⟩
  have hfn : Cvs.WeilForm.WindowRepresentative.fn ⟨hmem.toLp f, hwin⟩ =ᵐ[volume] f := hmem.coeFn_toLp
  exact (Cvs.WeilForm.WindowRepresentative.ae_eq_rep _).symm.trans hfn

/-- **The per-channel odd cap on an odd `L²` window class.** -/
theorem odd_cap_L2 {L : ℝ} (hL : 0 < L) {b t : ℝ} (hb : 0 < b) (ht : 0 < t)
    (hfree : t * (L / 2) < Real.pi / 2 + Real.arctan (b / t))
    (y : Cvs.WeilForm.WeilFormOnWindowL2.window L)
    (hodd : ∀ᵐ s ∂(volume : Measure ℝ),
      Cvs.WeilForm.WindowRepresentative.rep y (L - s) = - Cvs.WeilForm.WindowRepresentative.rep y s) :
    Cvs.WeilForm.ChannelFunctionalL2.chanInt b (Cvs.WeilForm.WindowRepresentative.rep y)
      ≤ (2 * b / (b ^ 2 + t ^ 2)) * ‖y‖ ^ 2 := by
  set lam : ℝ := 2 * b / (b ^ 2 + t ^ 2) with hlam
  -- density approximants
  have hget : ∀ k : ℕ, ∃ g : ℝ → ℝ, Continuous g ∧ HasCompactSupport g ∧
      (∀ s, s ∉ Ioo (0:ℝ) L → g s = 0) ∧
      eLpNorm (fun s => Cvs.WeilForm.WindowRepresentative.rep y s - g s) 2 (volume : Measure ℝ)
        ≤ ENNReal.ofReal (1 / (k + 1)) :=
    fun k => Cvs.Upstream.ContinuousCompactDenseWindow.approx_by_continuous_supported hL y
      (ε := 1 / (k + 1)) (by positivity)
  choose g hgc hgcs hgsupp hgle using hget
  -- oddified approximants
  set o : ℕ → ℝ → ℝ := fun k => oddify L (g k) with ho
  -- continuity, support, oddness of each oddified approximant
  have ho_cont : ∀ k, Continuous (o k) := by
    intro k
    have : Continuous fun s => g k s - g k (L - s) :=
      (hgc k).sub ((hgc k).comp (continuous_const.sub continuous_id))
    exact this.div_const 2
  have ho_vanIoo : ∀ k, ∀ s, s ∉ Ioo (0:ℝ) L → o k s = 0 :=
    fun k s hs => oddify_vanish L (hgsupp k) hs
  have ho_vanIcc : ∀ k, ∀ s, s ∉ Icc (0:ℝ) L → o k s = 0 :=
    fun k s hs => oddify_vanish L (hgsupp k) (fun hmem => hs (Ioo_subset_Icc_self hmem))
  have ho_vanIoc : ∀ k, ∀ s, s ∉ Ioc (0:ℝ) L → o k s = 0 :=
    fun k s hs => oddify_vanish L (hgsupp k) (fun hmem => hs (Ioo_subset_Ioc_self hmem))
  have ho_hcs : ∀ k, HasCompactSupport (o k) :=
    fun k => HasCompactSupport.intro (isCompact_Icc) (fun x hx => ho_vanIcc k x hx)
  have ho_oddfun : ∀ k, ∀ s, o k (L - s) = - o k s := fun k s => oddify_odd L (g k) s
  -- window classes from the approximants
  choose φ hφ using
    (fun k => window_of_continuous (ho_cont k) (ho_hcs k) (ho_vanIoc k) :
      ∀ k, ∃ ψ : Cvs.WeilForm.WeilFormOnWindowL2.window L, Cvs.WeilForm.WindowRepresentative.rep ψ =ᵐ[volume] o k)
  -- per-term cap
  have hcap : ∀ k, Cvs.WeilForm.ChannelFunctionalL2.chanInt b (Cvs.WeilForm.WindowRepresentative.rep (φ k))
      ≤ lam * ‖φ k‖ ^ 2 := by
    intro k
    have hchan : Cvs.WeilForm.ChannelFunctionalL2.chanInt b (Cvs.WeilForm.WindowRepresentative.rep (φ k))
        = Cvs.WeilForm.ChannelFunctionalL2.chanInt b (o k) := by
      unfold Cvs.WeilForm.ChannelFunctionalL2.chanInt
      rw [Cvs.WeilForm.WeilFormAeClass.selfConvolution_eq_of_ae (hφ k)]
    have hdouble : Cvs.WeilForm.ChannelFunctionalL2.chanInt b (o k)
        = ∫ s, o k s * ∫ u, o k u * Real.exp (-(b * |s - u|)) :=
      Cvs.WeilForm.ChannelFunctionalL2.chanInt_eq_double (ho_cont k) (ho_hcs k) hb
    have hcapcont : (∫ s, o k s * ∫ u, o k u * Real.exp (-(b * |s - u|)))
        ≤ lam * ∫ x, (o k x) ^ 2 :=
      Cvs.WeilForm.OddChannelCap.odd_channel_cap (ho_cont k) (ho_vanIcc k) (ho_oddfun k) hL hb ht hfree
    have hnorm : (∫ x, (o k x) ^ 2) = ‖φ k‖ ^ 2 := by
      rw [sq_norm_eq_integral_rep (φ k)]
      refine integral_congr_ae ?_
      filter_upwards [hφ k] with x hx; rw [hx]
    rw [hchan, hdouble]
    calc (∫ s, o k s * ∫ u, o k u * Real.exp (-(b * |s - u|)))
        ≤ lam * ∫ x, (o k x) ^ 2 := hcapcont
      _ = lam * ‖φ k‖ ^ 2 := by rw [hnorm]
  -- L² convergence of the window classes to y
  have hbd : ∀ k, ‖((φ k : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))
      - ((y : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))‖ ≤ 1 / (k + 1) := by
    intro k
    rw [Lp.norm_def]
    have hcoeφ : (⇑((φ k : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)))
        =ᵐ[volume] o k :=
      (Cvs.WeilForm.WindowRepresentative.ae_eq_rep (φ k)).trans (hφ k)
    have hcoey : (⇑((y : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)))
        =ᵐ[volume] Cvs.WeilForm.WindowRepresentative.rep y :=
      Cvs.WeilForm.WindowRepresentative.ae_eq_rep y
    have hae : (⇑(((φ k : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))
          - ((y : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))))
        =ᵐ[volume] fun s => o k s - Cvs.WeilForm.WindowRepresentative.rep y s := by
      filter_upwards [Lp.coeFn_sub
        ((φ k : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))
        ((y : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)),
        hcoeφ, hcoey] with x hx hxφ hxy
      rw [hx, Pi.sub_apply, hxφ, hxy]
    rw [eLpNorm_congr_ae hae]
    -- bound the eLpNorm of the difference
    have hdmeas : AEStronglyMeasurable (fun s => g k s - Cvs.WeilForm.WindowRepresentative.rep y s)
        (volume : Measure ℝ) :=
      (hgc k).aestronglyMeasurable.sub (Cvs.WeilForm.WindowRepresentative.memLp_rep y).aestronglyMeasurable
    have hoddeq : (fun s => o k s - Cvs.WeilForm.WindowRepresentative.rep y s)
        =ᵐ[volume] oddify L (fun s => g k s - Cvs.WeilForm.WindowRepresentative.rep y s) := by
      filter_upwards [hodd] with s hs
      simp only [ho, oddify]
      rw [hs]; ring
    have hle1 : eLpNorm (fun s => o k s - Cvs.WeilForm.WindowRepresentative.rep y s) 2 (volume : Measure ℝ)
        ≤ eLpNorm (fun s => g k s - Cvs.WeilForm.WindowRepresentative.rep y s) 2 (volume : Measure ℝ) := by
      rw [eLpNorm_congr_ae hoddeq]
      exact eLpNorm_oddify_le _ hdmeas L
    have hsymm : eLpNorm (fun s => g k s - Cvs.WeilForm.WindowRepresentative.rep y s) 2 (volume : Measure ℝ)
        = eLpNorm (fun s => Cvs.WeilForm.WindowRepresentative.rep y s - g k s) 2 (volume : Measure ℝ) := by
      have : (fun s => g k s - Cvs.WeilForm.WindowRepresentative.rep y s)
          = -(fun s => Cvs.WeilForm.WindowRepresentative.rep y s - g k s) := by funext s; simp
      rw [this, eLpNorm_neg]
    have hle : eLpNorm (fun s => o k s - Cvs.WeilForm.WindowRepresentative.rep y s) 2 (volume : Measure ℝ)
        ≤ ENNReal.ofReal (1 / (k + 1)) := by
      rw [hsymm] at hle1; exact hle1.trans (hgle k)
    calc (eLpNorm (fun s => o k s - Cvs.WeilForm.WindowRepresentative.rep y s) 2 (volume : Measure ℝ)).toReal
        ≤ (ENNReal.ofReal (1 / (k + 1))).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      _ = 1 / (k + 1) := ENNReal.toReal_ofReal (by positivity)
  have htends : Tendsto
      (fun k => ((φ k : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)))
      atTop (𝓝 ((y : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun k => norm_nonneg _) hbd tendsto_one_div_add_atTop_nhds_zero_nat
  exact Cvs.WeilForm.ChannelCapClosedL2.cap_closed hb htends hcap

end Cvs.WeilForm.OddCapTransfer
