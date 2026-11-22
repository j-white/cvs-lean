import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineSubspace
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.Visibility.CaseFiniteCellFloorRates
import Cvs.Route.Visibility.ExteriorTransformHolomorphy
import Cvs.Route.Visibility.PerRungBoxBound
import Cvs.Route.Visibility.ShareBesselFromExtPairing
import Cvs.Route.Visibility.SpinePairingExteriorTransform
import Cvs.Route.Visibility.VisibilityClosingStep
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.TameWindowZeroSum
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.Xi.WindowTransformExterior
import Cvs.Zeta.CompletedZeroIndex
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.LocalCountTransfer
import Cvs.Zeta.ZeroDensityTail
import Cvs.Zeta.ZeroSideMoments
import Cvs.Zeta.ZetaSeamStatement
import Cvs.Zeta.ZetaZeroWindows

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The summable Bessel disc bound with `A = 176/π`

The pairing is `⟪r_a, U_ρ⟫ = −Re Φ_ρ/2` (Cvs.Route.Visibility.ShareBesselFromExtPairing), so `⟪r_a, U_ρ⟫² ≤ (x^δ/2)(|X(ρ)|² + |X(1 − ρ)|²)`. Each square is
at most the disc mean of `|X|²` on `D(ρ, r₀)` and `D(1 − ρ, r₀)` (Cvs.Route.Visibility.ExteriorTransformHolomorphy). A point lies in discs of total multiplicity
at most `88 log(|g| + 7/2)` (`ZeroDensityTail`'s unit-window count), and only for `|σ − ½| ≤ δ + r₀`, so Tonelli bounds each disc
sum by `88·2(δ + r₀)·M`. Bounded partial sums give summability and `Cvs.Route.Visibility.PerRungBoxBound.BesselDiscS (176/π)`.
-/

noncomputable section

open Real Set MeasureTheory Filter Complex Metric
open scoped InnerProductSpace ENNReal
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.WeilForm.ThetaSpaceParseval (mellinR)
open Cvs.Xi.WindowTransformExterior (ext)
open Cvs.Zeta.Explicit.Venue

namespace Cvs.Route.Visibility.SummableBesselDisc
open Cvs.ZeroCounting

/-! ### The local count on the zero set -/

/-- **The local count on the zero set**: zeros of a finite set with `|Im ρ − u| < ½` carry total divisor weight at
most `88 log(|u| + 7/2)`. -/
theorem sum_divisorWeight_le (F : Finset nonTrivialZeroSet) (u : ℝ)
    (hF : ∀ ρ ∈ F, |(ρ : ℂ).im - u| < 1 / 2) :
    (∑ ρ ∈ F, (Cvs.Criterion.divisorWeight ρ : ℝ)) ≤ 88 * Real.log (|u| + 7 / 2) := by
  set F' := F.map Cvs.Criterion.zeroEquiv.symm.toEmbedding
  have hsum : ∑ ρ ∈ F, Cvs.Criterion.divisorWeight ρ = ∑ v ∈ F', completedZetaZeroMultiplicity v := by
    rw [Finset.sum_map]; rfl
  have hwin : ∀ v ∈ F', u - 1 / 2 < (nontrivialZetaZeroValue v).im
      ∧ (nontrivialZetaZeroValue v).im ≤ u - 1 / 2 + 1 := by
    intro v hv
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_map.mp hv
    have h := abs_lt.mp (hF ρ hρ)
    exact ⟨by show u - 1 / 2 < (ρ : ℂ).im; linarith, by show (ρ : ℂ).im ≤ u - 1 / 2 + 1; linarith⟩
  have h1 := Cvs.Zeta.LocalCountTransfer.sum_le_Ncount F' hwin
  have h2 := Cvs.Zeta.ZeroDensityTail.localCount_le (u - 1 / 2)
  have h3 : Real.log (|u - 1 / 2| + 3) ≤ Real.log (|u| + 7 / 2) := by
    refine Real.log_le_log (by positivity) ?_
    have := abs_sub (u) (1 / 2); rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this; linarith
  calc (∑ ρ ∈ F, (Cvs.Criterion.divisorWeight ρ : ℝ)) = ((∑ ρ ∈ F, Cvs.Criterion.divisorWeight ρ : ℕ) : ℝ) := by
        push_cast; rfl
    _ ≤ (Cvs.Zeta.Base.Ncount (u - 1 / 2) (u - 1 / 2 + 1) : ℝ) := by rw [hsum]; exact_mod_cast h1
    _ ≤ 88 * Real.log (|u - 1 / 2| + 3) := h2
    _ ≤ 88 * Real.log (|u| + 7 / 2) := by linarith

/-! ### The overlap count of the discs -/

/-- The closed strip `|Re z − ½| ≤ w`. -/
def strip (w : ℝ) : Set ℂ := {z | |z.re - 1 / 2| ≤ w}

/-- **The overlap count**: for centres with `|Re c_ρ − ½| ≤ δ` and `Im c_ρ = s·Im ρ`, `s = ±1`, and `r₀ < ½`, the
discs `D(c_ρ, r₀)` cover a point `z` with total weight at most `88 log(|Im z| + 7/2)`, and only inside the strip
`|Re z − ½| ≤ δ + r₀`. -/
theorem overlap_le (F : Finset nonTrivialZeroSet) {δ r₀ s : ℝ} (hr₀ : r₀ < 1 / 2) (hs : s = 1 ∨ s = -1)
    (cen : nonTrivialZeroSet → ℂ) (hre : ∀ ρ, |(cen ρ).re - 1 / 2| ≤ δ)
    (him : ∀ ρ, (cen ρ).im = s * (ρ : ℂ).im) (z : ℂ) :
    ∑ ρ ∈ F, (Cvs.Criterion.divisorWeight ρ : ℝ) * (ball (cen ρ) r₀).indicator (fun _ => (1 : ℝ)) z
      ≤ (strip (δ + r₀)).indicator (fun z => 88 * Real.log (|z.im| + 7 / 2)) z := by
  classical
  have hs2 : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hsa : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hind : ∀ ρ, (Cvs.Criterion.divisorWeight ρ : ℝ) * (ball (cen ρ) r₀).indicator (fun _ => (1 : ℝ)) z
      = if z ∈ ball (cen ρ) r₀ then (Cvs.Criterion.divisorWeight ρ : ℝ) else 0 := fun ρ => by
    by_cases h : z ∈ ball (cen ρ) r₀ <;> simp [h]
  simp only [hind]
  rw [← Finset.sum_filter]
  set F' := F.filter fun ρ => z ∈ ball (cen ρ) r₀
  have hlog : 0 ≤ 88 * Real.log (|z.im| + 7 / 2) := by
    have := Real.log_nonneg (by linarith [abs_nonneg z.im] : (1 : ℝ) ≤ |z.im| + 7 / 2); positivity
  rcases F'.eq_empty_or_nonempty with h | ⟨ρ₀, hρ₀⟩
  · rw [h, Finset.sum_empty]
    by_cases hz : z ∈ strip (δ + r₀)
    · rw [indicator_of_mem hz]; exact hlog
    · rw [indicator_of_notMem hz]
  · have hball : ∀ ρ ∈ F', ‖z - cen ρ‖ < r₀ := fun ρ hρ => by
      have := (Finset.mem_filter.mp hρ).2; rwa [mem_ball, dist_eq_norm] at this
    have hz : z ∈ strip (δ + r₀) := by
      have h1 := hball ρ₀ hρ₀
      have h2 : |z.re - (cen ρ₀).re| < r₀ := by
        have := Complex.abs_re_le_norm (z - cen ρ₀); rw [Complex.sub_re] at this; linarith
      show |z.re - 1 / 2| ≤ δ + r₀
      have h3 := hre ρ₀
      calc |z.re - 1 / 2| = |(z.re - (cen ρ₀).re) + ((cen ρ₀).re - 1 / 2)| := by ring_nf
        _ ≤ |z.re - (cen ρ₀).re| + |(cen ρ₀).re - 1 / 2| := abs_add_le _ _
        _ ≤ δ + r₀ := by linarith
    rw [indicator_of_mem hz]
    have hcount := sum_divisorWeight_le F' (s * z.im) fun ρ hρ => by
      have h1 := hball ρ hρ
      have h2 : |z.im - (cen ρ).im| < r₀ := by
        have := Complex.abs_im_le_norm (z - cen ρ); rw [Complex.sub_im] at this; linarith
      rw [him ρ] at h2
      have e : (ρ : ℂ).im - s * z.im = -(s * (z.im - s * (ρ : ℂ).im)) := by
        rw [mul_sub, ← mul_assoc, hs2]; ring
      rw [e, abs_neg, abs_mul, hsa, one_mul]
      linarith
    rwa [abs_mul, hsa, one_mul] at hcount

/-! ### Finite sums of lower integrals -/

/-- A finite sum of lower integrals is at most the lower integral of the sum. -/
theorem sum_lintegral_le {α ι : Type*} [MeasurableSpace α] (μ : Measure α) (s : Finset ι)
    (f : ι → α → ℝ≥0∞) : ∑ i ∈ s, ∫⁻ a, f i a ∂μ ≤ ∫⁻ a, ∑ i ∈ s, f i a ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    refine (add_le_add le_rfl ih).trans ((le_lintegral_add _ _).trans_eq ?_)
    congr 1; funext a; rw [Finset.sum_insert hi]

/-! ### Tonelli over the discs -/

/-- `σ + ig` is the complex number with real part `σ` and imaginary part `g`. -/
theorem symm_equiv_real_prod (σ g : ℝ) : Complex.measurableEquivRealProd.symm (σ, g) = (σ : ℂ) + g * I := by
  apply Complex.ext <;> simp [Complex.measurableEquivRealProd_symm_apply]

/-- **The disc sum**: for `f` continuous on `Re s < 1`, centres with `|Re c_ρ − ½| ≤ δ` and `Im c_ρ = s·Im ρ`,
`s = ±1`, `0 < r₀ ≤ (½ − δ)/2`, and `∫|f(σ + ig)|² log(|g| + 7/2) dg ≤ M` (integrable) on `|σ − ½| ≤ δ + r₀`,
`Σ_ρ m_ρ ∫_{D(c_ρ, r₀)} |f|² ≤ 88·2(δ + r₀)·M` over every finite set of zeros. -/
theorem sum_ball_le {f : ℂ → ℂ} (hf : ContinuousOn f {s | s.re < 1}) {δ r₀ s M : ℝ} (hδ : 0 < δ)
    (hr₀ : 0 < r₀) (hr : r₀ ≤ (1 / 2 - δ) / 2) (hs : s = 1 ∨ s = -1) (cen : nonTrivialZeroSet → ℂ)
    (hre : ∀ ρ, |(cen ρ).re - 1 / 2| ≤ δ) (him : ∀ ρ, (cen ρ).im = s * (ρ : ℂ).im)
    (hM : ∀ σ ∈ Icc (1 / 2 - (δ + r₀)) (1 / 2 + (δ + r₀)),
      Integrable (fun g : ℝ => ‖f (σ + g * I)‖ ^ 2 * Real.log (|g| + 7 / 2))
        ∧ ∫ g : ℝ, ‖f (σ + g * I)‖ ^ 2 * Real.log (|g| + 7 / 2) ≤ M)
    (F : Finset nonTrivialZeroSet) :
    ∑ ρ ∈ F, (Cvs.Criterion.divisorWeight ρ : ℝ) * ∫ z in ball (cen ρ) r₀, ‖f z‖ ^ 2
      ≤ 88 * (2 * (δ + r₀)) * M := by
  set w := δ + r₀
  set h : ℂ → ℝ := fun z => ‖f z‖ ^ 2
  have hh0 : ∀ z, 0 ≤ h z := fun z => sq_nonneg _
  have hw : w < 1 / 2 := by simp only [w]; linarith
  -- `M ≥ 0`, from the line `σ = ½`
  have hM0 : 0 ≤ M := by
    have hmem : (1 / 2 : ℝ) ∈ Icc (1 / 2 - w) (1 / 2 + w) := ⟨by linarith, by linarith⟩
    refine le_trans (integral_nonneg fun g => ?_) (hM _ hmem).2
    exact mul_nonneg (sq_nonneg _) (Real.log_nonneg (by linarith [abs_nonneg g]))
  -- the discs lie in `Re s < 1`
  have hsub : ∀ ρ, ball (cen ρ) r₀ ⊆ {s : ℂ | s.re < 1} := fun ρ z hz => by
    have h1 : |z.re - (cen ρ).re| < r₀ := by
      have := Complex.abs_re_le_norm (z - cen ρ)
      rw [Complex.sub_re] at this; rw [mem_ball, dist_eq_norm] at hz; linarith
    have h2 := hre ρ
    show z.re < 1
    have := (abs_lt.mp h1).2; have := (abs_le.mp h2).2; linarith
  set B : nonTrivialZeroSet → ℝ≥0∞ := fun ρ => ∫⁻ z in ball (cen ρ) r₀, ENNReal.ofReal (h z)
  have hB : ∀ ρ, ∫ z in ball (cen ρ) r₀, h z = (B ρ).toReal := fun ρ =>
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hh0)
      (((hf.mono (hsub ρ)).norm.pow 2).aestronglyMeasurable measurableSet_ball)
  -- the pointwise weight
  set Φ : ℂ → ℝ := fun z => (strip w).indicator (fun z => 88 * Real.log (|z.im| + 7 / 2)) z * h z
  have hstep : ∑ ρ ∈ F, (Cvs.Criterion.divisorWeight ρ : ℝ≥0∞) * B ρ ≤ ∫⁻ z, ENNReal.ofReal (Φ z) := by
    have e : ∀ ρ, (Cvs.Criterion.divisorWeight ρ : ℝ≥0∞) * B ρ
        = ∫⁻ z, ENNReal.ofReal ((Cvs.Criterion.divisorWeight ρ : ℝ)
            * (ball (cen ρ) r₀).indicator (fun _ => (1 : ℝ)) z * h z) := fun ρ => by
      simp only [B]
      rw [← lintegral_indicator measurableSet_ball, ← lintegral_const_mul' _ _ (by simp)]
      refine lintegral_congr fun z => ?_
      by_cases hz : z ∈ ball (cen ρ) r₀
      · simp [indicator_of_mem hz, ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      · simp [indicator_of_notMem hz]
    simp only [e]
    refine (sum_lintegral_le _ _ _).trans (lintegral_mono fun z => ?_)
    have hnn : ∀ ρ ∈ F, 0 ≤ (Cvs.Criterion.divisorWeight ρ : ℝ)
        * (ball (cen ρ) r₀).indicator (fun _ => (1 : ℝ)) z * h z := fun ρ _ => by
      have : 0 ≤ (ball (cen ρ) r₀).indicator (fun _ => (1 : ℝ)) z :=
        indicator_nonneg (fun _ _ => zero_le_one) z
      have := hh0 z; positivity
    rw [← ENNReal.ofReal_sum_of_nonneg hnn]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right
      (overlap_le F (by linarith) hs cen hre him z) (hh0 z)
  -- Tonelli
  have htail : ∫⁻ z, ENNReal.ofReal (Φ z) ≤ ENNReal.ofReal (88 * M) * ENNReal.ofReal (2 * w) := by
    rw [← (Complex.volume_preserving_equiv_real_prod.symm).lintegral_comp_emb
      Complex.measurableEquivRealProd.symm.measurableEmbedding, Measure.volume_eq_prod]
    refine (lintegral_prod_le _).trans ?_
    have hin : ∀ σ : ℝ, ∫⁻ g : ℝ, ENNReal.ofReal (Φ (Complex.measurableEquivRealProd.symm (σ, g)))
        ≤ (Icc (1 / 2 - w) (1 / 2 + w)).indicator (fun _ => ENNReal.ofReal (88 * M)) σ := fun σ => by
      simp only [symm_equiv_real_prod]
      have hre' : ∀ g : ℝ, ((σ : ℂ) + g * I).re = σ := fun g => by simp
      have him' : ∀ g : ℝ, ((σ : ℂ) + g * I).im = g := fun g => by simp
      by_cases hσ : σ ∈ Icc (1 / 2 - w) (1 / 2 + w)
      · rw [indicator_of_mem hσ]
        have hmem : ∀ g : ℝ, (σ : ℂ) + g * I ∈ strip w := fun g => by
          show |((σ : ℂ) + g * I).re - 1 / 2| ≤ w
          rw [hre', abs_le]; constructor <;> linarith [hσ.1, hσ.2]
        obtain ⟨hI, hle⟩ := hM σ hσ
        have e : ∀ g : ℝ, Φ ((σ : ℂ) + g * I)
            = 88 * (‖f (σ + g * I)‖ ^ 2 * Real.log (|g| + 7 / 2)) := fun g => by
          simp only [Φ, h, indicator_of_mem (hmem g), him']; ring
        simp only [e]
        rw [← ofReal_integral_eq_lintegral_ofReal (hI.const_mul 88) (ae_of_all _ fun g =>
          mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _)
            (Real.log_nonneg (by linarith [abs_nonneg g]))))]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_const_mul]; linarith
      · rw [indicator_of_notMem hσ]
        have hnot : ∀ g : ℝ, (σ : ℂ) + g * I ∉ strip w := fun g hg => by
          apply hσ
          have : |((σ : ℂ) + g * I).re - 1 / 2| ≤ w := hg
          rw [hre', abs_le] at this
          exact ⟨by linarith, by linarith⟩
        simp [Φ, indicator_of_notMem (hnot _)]
    refine (lintegral_mono hin).trans_eq ?_
    rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc]
    congr 2; ring
  have key : ∑ ρ ∈ F, (Cvs.Criterion.divisorWeight ρ : ℝ≥0∞) * B ρ ≤ ENNReal.ofReal (88 * (2 * w) * M) := by
    refine hstep.trans (htail.trans_eq ?_)
    rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  have hfin : ∑ ρ ∈ F, (Cvs.Criterion.divisorWeight ρ : ℝ≥0∞) * B ρ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top key
  have hterm : ∀ ρ ∈ F, (Cvs.Criterion.divisorWeight ρ : ℝ≥0∞) * B ρ ≠ ⊤ := fun ρ hρ =>
    ne_top_of_le_ne_top hfin
      (Finset.single_le_sum (f := fun ρ => (Cvs.Criterion.divisorWeight ρ : ℝ≥0∞) * B ρ) (fun _ _ => zero_le) hρ)
  have hreal : ∑ ρ ∈ F, (Cvs.Criterion.divisorWeight ρ : ℝ) * ∫ z in ball (cen ρ) r₀, ‖f z‖ ^ 2
      = (∑ ρ ∈ F, (Cvs.Criterion.divisorWeight ρ : ℝ≥0∞) * B ρ).toReal := by
    rw [ENNReal.toReal_sum hterm]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ← hB ρ]
  rw [hreal]
  refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top key).trans_eq ?_
  exact ENNReal.toReal_ofReal (by positivity)

/-! ### The pairing at a zero -/

/-- **The pairing at a zero is bounded by the two exterior values**: for `|Re ρ − ½| ≤ δ`,
`⟪r_a, U_ρ⟫² ≤ (x^δ/2)(|X_a(ρ)|² + |X_a(1 − ρ)|²)`. -/
theorem sq_inner_ueVec_le {x : ℕ} (hx : 80 ≤ 2 * π * x) (hx0 : (0 : ℝ) < x) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ)
    {δ : ℝ} (ρ : nonTrivialZeroSet) (hdel : |Cvs.GaussKernel.del ρ| ≤ δ) :
    ⟪Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a),
        Cvs.Route.Visibility.VisibilityClosingStep.ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2
      ≤ (x : ℝ) ^ δ / 2 * (‖mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a)) ρ‖ ^ 2
          + ‖mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a)) (1 - ρ)‖ ^ 2) := by
  rw [Cvs.Route.Visibility.ShareBesselFromExtPairing.inner_evenPart_spineMap_ueVec hx hx0 a ρ]
  set X := mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a))
  set d := Cvs.GaussKernel.del ρ
  have hxn : 0 < x := by exact_mod_cast hx0
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hxn
  have hp : ‖(x : ℂ) ^ (((ρ : ℂ) - 1 / 2) / 2)‖ = (x : ℝ) ^ (d / 2) := by
    rw [Complex.norm_natCast_cpow_of_pos hxn]; congr 1
    simp [d, Cvs.GaussKernel.del]
  have hq : ‖(x : ℂ) ^ ((1 / 2 - (ρ : ℂ)) / 2)‖ = (x : ℝ) ^ (-d / 2) := by
    rw [Complex.norm_natCast_cpow_of_pos hxn]; congr 1
    simp [d, Cvs.GaussKernel.del]
  have hsq : ∀ e : ℝ, ((x : ℝ) ^ (e / 2)) ^ 2 = (x : ℝ) ^ e := fun e => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have hd1 : (x : ℝ) ^ d ≤ (x : ℝ) ^ δ :=
    Real.rpow_le_rpow_of_exponent_le hx1 ((le_abs_self d).trans hdel)
  have hd2 : (x : ℝ) ^ (-d) ≤ (x : ℝ) ^ δ :=
    Real.rpow_le_rpow_of_exponent_le hx1 ((neg_le_abs d).trans hdel)
  have hΦ : ‖Cvs.Route.Visibility.SpinePairingExteriorTransform.extComb x (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a) ρ‖
      ≤ (x : ℝ) ^ (d / 2) * ‖X ρ‖ + (x : ℝ) ^ (-d / 2) * ‖X (1 - ρ)‖ := by
    unfold Cvs.Route.Visibility.SpinePairingExteriorTransform.extComb
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, hp, hq]
  set u := ‖X ρ‖; set v := ‖X (1 - ρ)‖
  set p := (x : ℝ) ^ (d / 2); set q := (x : ℝ) ^ (-d / 2)
  have hp0 : 0 ≤ p := Real.rpow_nonneg hx0.le _
  have hq0 : 0 ≤ q := Real.rpow_nonneg hx0.le _
  have hre := Complex.abs_re_le_norm (Cvs.Route.Visibility.SpinePairingExteriorTransform.extComb x (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a) ρ)
  have h1 : (-(Cvs.Route.Visibility.SpinePairingExteriorTransform.extComb x (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a) ρ).re / 2) ^ 2
      ≤ (p * u + q * v) ^ 2 / 4 := by
    have h0 : 0 ≤ |(Cvs.Route.Visibility.SpinePairingExteriorTransform.extComb x (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a) ρ).re| := abs_nonneg _
    have := pow_le_pow_left₀ h0 (hre.trans hΦ) 2
    rw [sq_abs] at this
    have e : (-(Cvs.Route.Visibility.SpinePairingExteriorTransform.extComb x (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a) ρ).re / 2) ^ 2
        = (Cvs.Route.Visibility.SpinePairingExteriorTransform.extComb x (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a) ρ).re ^ 2 / 4 := by ring
    rw [e]; linarith
  have h2 : (p * u + q * v) ^ 2 ≤ 2 * (p ^ 2 * u ^ 2) + 2 * (q ^ 2 * v ^ 2) := by
    nlinarith [sq_nonneg (p * u - q * v)]
  have hp2 : p ^ 2 = (x : ℝ) ^ d := hsq d
  have hq2 : q ^ 2 = (x : ℝ) ^ (-d) := hsq (-d)
  have hu : 0 ≤ u ^ 2 := sq_nonneg _
  have hv : 0 ≤ v ^ 2 := sq_nonneg _
  have h3 : p ^ 2 * u ^ 2 ≤ (x : ℝ) ^ δ * u ^ 2 := by rw [hp2]; exact mul_le_mul_of_nonneg_right hd1 hu
  have h4 : q ^ 2 * v ^ 2 ≤ (x : ℝ) ^ δ * v ^ 2 := by rw [hq2]; exact mul_le_mul_of_nonneg_right hd2 hv
  calc _ ≤ (p * u + q * v) ^ 2 / 4 := h1
    _ ≤ (2 * (p ^ 2 * u ^ 2) + 2 * (q ^ 2 * v ^ 2)) / 4 := by linarith
    _ ≤ _ := by nlinarith

/-! ### The Bessel disc bound -/

/-- **The summable Bessel disc bound with `A = 176/π`** (bessel/PROOF.md §1–§4, `A_Z = 88` from Cvs.Zeta.ZeroDensityTail). -/
theorem besselDiscS : Cvs.Route.Visibility.PerRungBoxBound.BesselDiscS (176 / π) := by
  intro x hx0 hx δ r₀ hδ hr₀ hr hdel a M hM
  obtain ⟨G₁, hG, hG₁, hGi⟩ := Cvs.WeilForm.TameWindowZeroSum.spineG_std hx a
  have ha : (0 : ℝ) < 1 / x := by positivity
  set X := mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a))
  have hXc : ContinuousOn X {s : ℂ | s.re < 1} :=
    (Cvs.Route.Visibility.ExteriorTransformHolomorphy.mellinR_ext_holo ha hG hG₁ hGi).1.continuousOn
  have hM' : ∀ σ ∈ Icc (1 / 2 - (δ + r₀)) (1 / 2 + (δ + r₀)),
      Integrable (fun g : ℝ => ‖X (σ + g * I)‖ ^ 2 * Real.log (|g| + 7 / 2))
        ∧ ∫ g : ℝ, ‖X (σ + g * I)‖ ^ 2 * Real.log (|g| + 7 / 2) ≤ M := fun σ hσ => hM σ hσ
  have hre1 : ∀ ρ : nonTrivialZeroSet, |((ρ : ℂ)).re - 1 / 2| ≤ δ := hdel
  have hre2 : ∀ ρ : nonTrivialZeroSet, |(1 - (ρ : ℂ)).re - 1 / 2| ≤ δ := fun ρ => by
    have := hdel ρ
    rw [Complex.sub_re, Complex.one_re, show 1 - (ρ : ℂ).re - 1 / 2 = -((ρ : ℂ).re - 1 / 2) by ring, abs_neg]
    exact this
  have hS1 := sum_ball_le hXc hδ hr₀ hr (Or.inl rfl) (fun ρ => (ρ : ℂ)) hre1 (fun ρ => by simp) hM'
  have hS2 := sum_ball_le hXc hδ hr₀ hr (Or.inr rfl) (fun ρ => 1 - (ρ : ℂ)) hre2 (fun ρ => by simp) hM'
  set κ := (π * r₀ ^ 2)⁻¹
  have hκ : 0 ≤ κ := by positivity
  have hxδ : 0 ≤ (x : ℝ) ^ δ := Real.rpow_nonneg hx0.le _
  have hlt : ∀ ρ : nonTrivialZeroSet, ((ρ : ℂ)).re + r₀ < 1 ∧ (1 - (ρ : ℂ)).re + r₀ < 1 := fun ρ => by
    have h1 := abs_le.mp (hre1 ρ); have h2 := abs_le.mp (hre2 ρ)
    constructor <;> linarith
  have hpt : ∀ ρ : nonTrivialZeroSet, (Cvs.Criterion.divisorWeight ρ : ℝ)
        * ⟪Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a),
            Cvs.Route.Visibility.VisibilityClosingStep.ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2
      ≤ (x : ℝ) ^ δ / 2 * κ * ((Cvs.Criterion.divisorWeight ρ : ℝ) * (∫ z in ball (ρ : ℂ) r₀, ‖X z‖ ^ 2)
          + (Cvs.Criterion.divisorWeight ρ : ℝ) * ∫ z in ball (1 - (ρ : ℂ)) r₀, ‖X z‖ ^ 2) := fun ρ => by
    have h := sq_inner_ueVec_le hx hx0 a ρ (hdel ρ)
    have b1 : ‖X ρ‖ ^ 2 ≤ κ * ∫ z in ball (ρ : ℂ) r₀, ‖X z‖ ^ 2 :=
      Cvs.Route.Visibility.ExteriorTransformHolomorphy.norm_sq_mellinR_ext_le_ball ha hG hG₁ hGi hr₀ (hlt ρ).1
    have b2 : ‖X (1 - ρ)‖ ^ 2 ≤ κ * ∫ z in ball (1 - (ρ : ℂ)) r₀, ‖X z‖ ^ 2 :=
      Cvs.Route.Visibility.ExteriorTransformHolomorphy.norm_sq_mellinR_ext_le_ball ha hG hG₁ hGi hr₀ (hlt ρ).2
    have hm : (0 : ℝ) ≤ Cvs.Criterion.divisorWeight ρ := Nat.cast_nonneg _
    calc _ ≤ (Cvs.Criterion.divisorWeight ρ : ℝ) * ((x : ℝ) ^ δ / 2 * (‖X ρ‖ ^ 2 + ‖X (1 - ρ)‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left h hm
      _ ≤ (Cvs.Criterion.divisorWeight ρ : ℝ) * ((x : ℝ) ^ δ / 2 * (κ * (∫ z in ball (ρ : ℂ) r₀, ‖X z‖ ^ 2)
            + κ * ∫ z in ball (1 - (ρ : ℂ)) r₀, ‖X z‖ ^ 2)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add b1 b2) (by positivity)) hm
      _ = _ := by ring
  have hbound : ∀ F : Finset nonTrivialZeroSet, ∑ ρ ∈ F, (Cvs.Criterion.divisorWeight ρ : ℝ)
        * ⟪Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a),
            Cvs.Route.Visibility.VisibilityClosingStep.ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2
      ≤ (x : ℝ) ^ δ * (176 / π * (δ + r₀) / r₀ ^ 2) * M := fun F => by
    refine (Finset.sum_le_sum fun ρ _ => hpt ρ).trans ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
    have := add_le_add (hS1 F) (hS2 F)
    calc _ ≤ (x : ℝ) ^ δ / 2 * κ * (88 * (2 * (δ + r₀)) * M + 88 * (2 * (δ + r₀)) * M) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by simp only [κ]; field_simp; ring
  have hnn : 0 ≤ fun ρ : nonTrivialZeroSet => (Cvs.Criterion.divisorWeight ρ : ℝ)
        * ⟪Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a),
            Cvs.Route.Visibility.VisibilityClosingStep.ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2 := fun ρ =>
    mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  exact ⟨summable_of_sum_le hnn hbound, Real.tsum_le_of_sum_le hnn hbound⟩

/-- **Route SEP's Bessel input**: some `A ≥ 0` has `Cvs.Route.Visibility.PerRungBoxBound.BesselDiscS A`. -/
theorem exists_besselDiscS : ∃ A : ℝ, 0 ≤ A ∧ Cvs.Route.Visibility.PerRungBoxBound.BesselDiscS A :=
  ⟨176 / π, by positivity, besselDiscS⟩

end Cvs.Route.Visibility.SummableBesselDisc

end
