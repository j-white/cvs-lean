import Mathlib
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.HatFunctionWindow
import Cvs.WeilForm.SelfConvolutionClassLipschitz
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.WeilPositivityStatement

/-!
# The hat's Lévy deficit is small near the origin and bounded everywhere

    `g(0) − g(h) ≤ h² (L + h) / 2`        `g(0) − g(v) ≤ 2 g(0)`        `densityU u ≤ 2/u` on `(0, 1]`

for `g` the self-convolution of the hat, which agrees with that of its window representative.
-/

noncomputable section

open MeasureTheory Set Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.Archimedean.HatLevyDeficit

/-- **The representative of the hat class is the hat**, almost everywhere. -/
theorem rep_hatW_ae (L : ℝ) :
    Cvs.WeilForm.WindowRepresentative.rep (Cvs.WeilForm.HatFunctionWindow.hatW L) =ᵐ[volume] Cvs.WeilForm.HatFunctionWindow.hat L := by
  filter_upwards [Cvs.WeilForm.HatFunctionWindow.hatW_ae L] with x hx
  simp only [Cvs.WeilForm.WindowRepresentative.rep, Cvs.WeilForm.WindowRepresentative.fn, Set.indicator_apply]
  split_ifs with h
  · exact hx
  · exact (Cvs.WeilForm.HatFunctionWindow.hat_eq_zero_of_notMem L h).symm

/-- **The self-convolutions agree.** -/
theorem selfConvolution_rep_hatW (L v : ℝ) :
    selfConvolution (Cvs.WeilForm.WindowRepresentative.rep (Cvs.WeilForm.HatFunctionWindow.hatW L)) v
      = selfConvolution (Cvs.WeilForm.HatFunctionWindow.hat L) v := by
  unfold selfConvolution
  refine integral_congr_ae ?_
  have h1 := rep_hatW_ae L
  have h2 : (fun s => Cvs.WeilForm.WindowRepresentative.rep (Cvs.WeilForm.HatFunctionWindow.hatW L) (s + v))
      =ᵐ[volume] fun s => Cvs.WeilForm.HatFunctionWindow.hat L (s + v) := by
    have h3 := (measurePreserving_add_right (volume : Measure ℝ) v).quasiMeasurePreserving.ae_eq_comp h1
    simpa only [Function.comp_def] using h3
  filter_upwards [h1, h2] with s hs1 hs2
  rw [hs1, hs2]

/-- The hat and its shifted product are integrable. -/
theorem integrable_hat_mul (L h : ℝ) :
    Integrable fun s => Cvs.WeilForm.HatFunctionWindow.hat L s * Cvs.WeilForm.HatFunctionWindow.hat L (s + h) := by
  refine Continuous.integrable_of_hasCompactSupport
    ((Cvs.WeilForm.HatFunctionWindow.continuous_hat L).mul
      ((Cvs.WeilForm.HatFunctionWindow.continuous_hat L).comp (continuous_id.add continuous_const))) ?_
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Icc (0:ℝ) L))
    fun s hs => ?_
  by_contra hs'
  apply hs
  show Cvs.WeilForm.HatFunctionWindow.hat L s * Cvs.WeilForm.HatFunctionWindow.hat L (s + h) = 0
  rw [Cvs.WeilForm.HatFunctionWindow.hat_eq_zero_of_notMem L fun h' => hs' (Ioc_subset_Icc_self h'), zero_mul]

theorem integrable_hat_sq (L : ℝ) : Integrable fun s => Cvs.WeilForm.HatFunctionWindow.hat L s ^ 2 := by
  have := integrable_hat_mul L 0
  simpa [pow_two] using this

/-- **The Lipschitz deficit bound.** -/
theorem deficit_hat_le {L h : ℝ} (hL : 0 ≤ L) (hh : 0 ≤ h) :
    selfConvolution (Cvs.WeilForm.HatFunctionWindow.hat L) 0 - selfConvolution (Cvs.WeilForm.HatFunctionWindow.hat L) h
      ≤ h ^ 2 * (L + h) / 2 := by
  have hid := Cvs.WeilForm.SelfConvolutionFunctional.integral_sq_sub_eq h (integrable_hat_sq L) (integrable_hat_mul L h)
  -- the integrand is at most `h²` and vanishes off `[−h, L]`
  have hpt : ∀ s, (Cvs.WeilForm.HatFunctionWindow.hat L s - Cvs.WeilForm.HatFunctionWindow.hat L (s + h)) ^ 2 ≤ h ^ 2 := by
    intro s
    have := (Cvs.WeilForm.HatFunctionWindow.lipschitz_hat L).dist_le_mul s (s + h)
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul,
      show s - (s + h) = -h by ring, abs_neg, abs_of_nonneg hh] at this
    calc (Cvs.WeilForm.HatFunctionWindow.hat L s - Cvs.WeilForm.HatFunctionWindow.hat L (s + h)) ^ 2
        = |Cvs.WeilForm.HatFunctionWindow.hat L s - Cvs.WeilForm.HatFunctionWindow.hat L (s + h)| ^ 2 := (sq_abs _).symm
      _ ≤ h ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
  have hsupp : ∀ s, s ∉ Icc (-h) L →
      (Cvs.WeilForm.HatFunctionWindow.hat L s - Cvs.WeilForm.HatFunctionWindow.hat L (s + h)) ^ 2 = 0 := by
    intro s hs
    have h1 : Cvs.WeilForm.HatFunctionWindow.hat L s = 0 := by
      refine Cvs.WeilForm.HatFunctionWindow.hat_eq_zero_of_notMem L fun h' => hs ⟨by linarith [h'.1], h'.2⟩
    have h2 : Cvs.WeilForm.HatFunctionWindow.hat L (s + h) = 0 := by
      refine Cvs.WeilForm.HatFunctionWindow.hat_eq_zero_of_notMem L fun h' => hs ⟨by linarith [h'.1], ?_⟩
      linarith [h'.2]
    rw [h1, h2]; ring
  have hint : ∫ s, (Cvs.WeilForm.HatFunctionWindow.hat L s - Cvs.WeilForm.HatFunctionWindow.hat L (s + h)) ^ 2
      ≤ h ^ 2 * (L + h) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
    have hI : IntegrableOn (fun s => (Cvs.WeilForm.HatFunctionWindow.hat L s
        - Cvs.WeilForm.HatFunctionWindow.hat L (s + h)) ^ 2) (Icc (-h) L) volume :=
      ((integrable_hat_sq L).sub ((integrable_hat_mul L h).const_mul 2) |>.add
        ((integrable_hat_sq L).comp_add_right h) |>.congr (Filter.Eventually.of_forall fun s => by
          simp only [Pi.add_apply, Pi.sub_apply]; ring)).integrableOn
    calc ∫ s in Icc (-h) L, (Cvs.WeilForm.HatFunctionWindow.hat L s - Cvs.WeilForm.HatFunctionWindow.hat L (s + h)) ^ 2
        ≤ ∫ _ in Icc (-h) L, h ^ 2 :=
          setIntegral_mono_on hI (continuous_const.integrableOn_Icc) measurableSet_Icc
            fun s _ => hpt s
      _ = h ^ 2 * (L + h) := by
          rw [setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Icc,
            ENNReal.toReal_ofReal (by linarith)]
          ring
  linarith

/-- **The deficit is at most twice the mass**, for any window class. -/
theorem deficit_le_two {L : ℝ} (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) (v : ℝ) :
    selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ) 0 - selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ) v
      ≤ 2 * selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ) 0 := by
  have h0 := (Cvs.WeilForm.WindowRepresentative.weilQW_rep 0 0 φ).2
  rw [Cvs.WeilForm.SelfConvolutionClassLipschitz.selfConvolution_eq_inner φ v]
  have := abs_real_inner_le_norm (φ : Lp ℝ 2 (volume : Measure ℝ))
    (Cvs.WeilForm.SelfConvolutionClassLipschitz.tr v (φ : Lp ℝ 2 (volume : Measure ℝ)))
  rw [Cvs.WeilForm.SelfConvolutionClassLipschitz.norm_tr] at this
  have hn : ‖(φ : Lp ℝ 2 (volume : Measure ℝ))‖ * ‖(φ : Lp ℝ 2 (volume : Measure ℝ))‖ = ‖φ‖ ^ 2 := by
    rw [pow_two]; rfl
  rw [hn] at this
  have := neg_abs_le (inner ℝ (φ : Lp ℝ 2 (volume : Measure ℝ))
    (Cvs.WeilForm.SelfConvolutionClassLipschitz.tr v (φ : Lp ℝ 2 (volume : Measure ℝ))))
  linarith

/-- **`densityU u ≤ 2/u` on `(0, 1]`**, from `u + 1 ≤ eᵘ`. -/
theorem densityU_le_two_div {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    Cvs.WeilForm.Archimedean.LevyDensity.densityU u ≤ 2 / u := by
  unfold Cvs.WeilForm.Archimedean.LevyDensity.densityU
  have hexp : Real.exp (-u) ≤ 1 / (1 + u) := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by linarith) (by linarith [Real.add_one_le_exp u])
  have hden : u / 2 ≤ 1 - Real.exp (-u) := by
    have h1 : 1 - 1 / (1 + u) = u / (1 + u) := by field_simp; ring
    have h2 : u / (1 + u) ≥ u / 2 := by
      rw [ge_iff_le, div_le_div_iff₀ (by norm_num) (by linarith)]
      nlinarith
    linarith
  have hnum : Real.exp (-(u / 4)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hpos : 0 < 1 - Real.exp (-u) := by linarith
  rw [div_le_div_iff₀ hpos hu]
  nlinarith [Real.exp_pos (-(u / 4))]

end Cvs.WeilForm.Archimedean.HatLevyDeficit
