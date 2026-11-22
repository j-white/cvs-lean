import Mathlib
import Cvs.Upstream.PlancherelL1L2SpectralDensity

/-!
# A uniformly bounded, uniformly Lipschitz family is totally bounded in `L²` on a window

    `‖g‖ ≤ M`, `LipschitzWith K g` for all `g ∈ A`, `B ⊆ [a, b]`
        ⟹   `{u ∈ L² | u =ᵐ 1_B · g for some g ∈ A}` is totally bounded

by Arzelà–Ascoli on `[a, b]`, carried into `L²` by the `√(b − a)`-Lipschitz restrict-and-extend map.
-/

noncomputable section

open MeasureTheory Set Metric BoundedContinuousFunction

namespace Cvs.Upstream.LipschitzFamilyTotallyBoundedL2

variable {a b : ℝ}

/-- Restriction to `[a, b]` then extension by zero on `B` is square-integrable. -/
theorem memLp_window (hab : a ≤ b) {B : Set ℝ} (hB : MeasurableSet B) (hBsub : B ⊆ Icc a b)
    (h : Icc a b →ᵇ ℂ) :
    MemLp (B.indicator fun x => h (projIcc a b hab x)) 2 (volume : Measure ℝ) := by
  have hc : Continuous fun x : ℝ => h (projIcc a b hab x) :=
    h.continuous.comp (continuous_projIcc (h := hab))
  rw [memLp_two_iff_integrable_sq_norm (hc.aestronglyMeasurable.indicator hB)]
  have hI : IntegrableOn (fun x : ℝ => ‖h (projIcc a b hab x)‖ ^ 2) B volume :=
    ((hc.norm.pow 2).integrableOn_Icc).mono_set hBsub
  refine (hI.integrable_indicator hB).congr (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ B <;> simp [Set.indicator_apply, hx]

/-- Restriction of a function to `[a, b]`, then extension by zero on `B`, as an `L²` class. -/
def toWindow (hab : a ≤ b) {B : Set ℝ} (hB : MeasurableSet B) (hBsub : B ⊆ Icc a b)
    (h : Icc a b →ᵇ ℂ) : Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_window hab hB hBsub h).toLp _

theorem toWindow_ae (hab : a ≤ b) {B : Set ℝ} (hB : MeasurableSet B) (hBsub : B ⊆ Icc a b)
    (h : Icc a b →ᵇ ℂ) :
    ((toWindow hab hB hBsub h : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] B.indicator fun x => h (projIcc a b hab x) :=
  MemLp.coeFn_toLp (memLp_window hab hB hBsub h)

/-- **The window map is Lipschitz** with constant `√(b − a)`. -/
theorem lipschitz_toWindow (hab : a ≤ b) {B : Set ℝ} (hB : MeasurableSet B)
    (hBsub : B ⊆ Icc a b) :
    LipschitzWith ⟨Real.sqrt (b - a), Real.sqrt_nonneg _⟩ (toWindow hab hB hBsub) := by
  refine LipschitzWith.of_dist_le_mul fun h h' => ?_
  rw [dist_eq_norm, dist_eq_norm]
  set D := ‖h - h'‖ with hD
  have hD0 : 0 ≤ D := norm_nonneg _
  -- the squared norm is a set integral of a bounded function
  have hsq : ‖toWindow hab hB hBsub h - toWindow hab hB hBsub h'‖ ^ 2 ≤ (b - a) * D ^ 2 := by
    rw [Cvs.Upstream.PlancherelL1L2SpectralDensity.norm_sq_eq_integral]
    have hae : (fun x => ‖((toWindow hab hB hBsub h - toWindow hab hB hBsub h' :
        Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x‖ ^ 2)
        =ᵐ[volume] fun x => B.indicator (fun x => ‖h (projIcc a b hab x) - h' (projIcc a b hab x)‖ ^ 2) x := by
      filter_upwards [Lp.coeFn_sub (toWindow hab hB hBsub h) (toWindow hab hB hBsub h'),
        toWindow_ae hab hB hBsub h, toWindow_ae hab hB hBsub h'] with x h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3]
      by_cases hx : x ∈ B
      · simp [indicator_of_mem hx]
      · simp [indicator_of_notMem hx]
    rw [integral_congr_ae hae, integral_indicator hB]
    have hc1 : Continuous fun x : ℝ => h (projIcc a b hab x) :=
      h.continuous.comp (continuous_projIcc (h := hab))
    have hc2 : Continuous fun x : ℝ => h' (projIcc a b hab x) :=
      h'.continuous.comp (continuous_projIcc (h := hab))
    have hcont : Continuous fun x : ℝ => ‖h (projIcc a b hab x) - h' (projIcc a b hab x)‖ ^ 2 :=
      (hc1.sub hc2).norm.pow 2
    have hint : IntegrableOn (fun x : ℝ => ‖h (projIcc a b hab x) - h' (projIcc a b hab x)‖ ^ 2)
        B volume := (hcont.integrableOn_Icc).mono_set hBsub
    have hpt : ∀ x ∈ B, ‖h (projIcc a b hab x) - h' (projIcc a b hab x)‖ ^ 2 ≤ D ^ 2 := by
      intro x _
      have := h.dist_coe_le_dist (g := h') (projIcc a b hab x)
      rw [dist_eq_norm, dist_eq_norm] at this
      exact pow_le_pow_left₀ (norm_nonneg _) this 2
    calc ∫ x in B, ‖h (projIcc a b hab x) - h' (projIcc a b hab x)‖ ^ 2
        ≤ ∫ _ in B, D ^ 2 := setIntegral_mono_on hint
            ((continuous_const.integrableOn_Icc (a := a) (b := b)).mono_set hBsub) hB hpt
      _ = (volume B).toReal * D ^ 2 := by rw [setIntegral_const, smul_eq_mul, measureReal_def]
      _ ≤ (b - a) * D ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          have h1 : volume B ≤ volume (Icc a b) := measure_mono hBsub
          rw [Real.volume_Icc] at h1
          have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
          rwa [ENNReal.toReal_ofReal (by linarith)] at h2
  -- take square roots
  show ‖toWindow hab hB hBsub h - toWindow hab hB hBsub h'‖ ≤ Real.sqrt (b - a) * D
  calc ‖toWindow hab hB hBsub h - toWindow hab hB hBsub h'‖
      = Real.sqrt (‖toWindow hab hB hBsub h - toWindow hab hB hBsub h'‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((b - a) * D ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (b - a) * D := by
        rw [Real.sqrt_mul (by linarith), Real.sqrt_sq hD0]

/-- **Arzelà–Ascoli, in `L²` on a window.** -/
theorem totallyBounded_of_lipschitz (hab : a ≤ b) {M K : NNReal} (A : Set (ℝ → ℂ))
    (hbdd : ∀ g ∈ A, ∀ x, ‖g x‖ ≤ M) (hlip : ∀ g ∈ A, LipschitzWith K g)
    {B : Set ℝ} (hB : MeasurableSet B) (hBsub : B ⊆ Icc a b) :
    TotallyBounded {u : Lp ℂ 2 (volume : Measure ℝ) |
      ∃ g ∈ A, (u : ℝ → ℂ) =ᵐ[volume] B.indicator g} := by
  -- the restricted family, in the bounded continuous functions on `[a, b]`
  set Ab : Set (Icc a b →ᵇ ℂ) := {h | ∃ g ∈ A, ∀ x : Icc a b, h x = g x} with hAb
  have hcpt : IsCompact (closure Ab) := by
    refine arzela_ascoli (closedBall (0 : ℂ) M) (isCompact_closedBall _ _) Ab ?_ ?_
    · rintro h x ⟨g, hg, hgx⟩
      rw [mem_closedBall, dist_zero_right, hgx]
      exact hbdd g hg x
    · refine (LipschitzWith.uniformEquicontinuous (fun h : Ab => ⇑(h : Icc a b →ᵇ ℂ)) (K * 1)
        ?_).equicontinuous
      rintro ⟨h, g, hg, hgx⟩
      have : ⇑(h : Icc a b →ᵇ ℂ) = fun x : Icc a b => g x := funext hgx
      show LipschitzWith (K * 1) ⇑h
      rw [this]
      exact (hlip g hg).comp (LipschitzWith.subtype_val _)
  have hAbTB : TotallyBounded Ab := hcpt.totallyBounded.subset subset_closure
  have himg : TotallyBounded (toWindow hab hB hBsub '' Ab) :=
    hAbTB.image (lipschitz_toWindow hab hB hBsub).uniformContinuous
  refine himg.subset ?_
  rintro u ⟨g, hg, hu⟩
  refine ⟨mkOfCompact ⟨fun x : Icc a b => g x,
    (hlip g hg).continuous.comp continuous_subtype_val⟩, ⟨g, hg, fun x => rfl⟩, ?_⟩
  apply Lp.ext
  filter_upwards [toWindow_ae hab hB hBsub
    (mkOfCompact ⟨fun x : Icc a b => g x, (hlip g hg).continuous.comp continuous_subtype_val⟩), hu]
    with x h1 h2
  rw [h1, h2]
  by_cases hx : x ∈ B
  · rw [indicator_of_mem hx, indicator_of_mem hx, mkOfCompact_apply]
    simp [projIcc_of_mem hab (hBsub hx)]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx]

end Cvs.Upstream.LipschitzFamilyTotallyBoundedL2
