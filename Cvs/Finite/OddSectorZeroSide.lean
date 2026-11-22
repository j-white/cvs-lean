import Mathlib
import Cvs.Finite.OddSectorSineSums
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Zeta.ExplicitFormula.CompactTestAdmissibility
import Cvs.Zeta.ExplicitFormula.HannWindowShifts
import Cvs.Zeta.ExplicitFormula.QuadraticDecayZeroSide
import Cvs.Zeta.ExplicitFormula.WindowTransformByParts
import Cvs.Zeta.ExplicitFormula.WindowTransformCubicDecay
import Cvs.Zeta.ZeroSideMoments

/-!
# The zero side of the odd sector: sine sums are the sum of `|F(ρ)|²` over the zeros

A `C²` test vanishing at the window's ends has a quadratically decaying transform (one vanishing
integration by parts and one with its boundary term), so `Cvs.Zeta.ExplicitFormula.QuadraticDecayZeroSide` applies to every window sine
sum: its window Weil form is the zero-side sum over all nontrivial zeros. The same holds for a
cosine sum whose coefficients sum to zero.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Real Complex Cvs.Zeta.Explicit.Weil
open Cvs.WeilForm.SelfConvolutionTransform

namespace Cvs.Finite.OddSectorZeroSide
open Cvs.ZeroCounting

/-! ### Quadratic decay from one vanishing integration by parts -/

/-- **Quadratic decay.** One vanishing integration by parts and one with its boundary term. -/
theorem windowTransform_quadratic {L : ℝ} (hL : 0 ≤ L) {f f' f'' : ℝ → ℂ}
    (hf : ∀ s ∈ Set.uIcc (0 : ℝ) L, HasDerivAt f (f' s) s)
    (hf2 : ∀ s ∈ Set.uIcc (0 : ℝ) L, HasDerivAt f' (f'' s) s)
    (hc1 : Continuous f') (hc2 : Continuous f'')
    (h0 : f 0 = 0) (hLz : f L = 0)
    {M : ℝ} (hM : ∀ s ∈ Set.uIoc (0 : ℝ) L, ‖f'' s‖ ≤ M)
    {ξ : ℂ} (hξ : ξ ≠ 0) :
    ‖Cvs.Detection.windowTransform L f ξ‖
      ≤ (‖f' L‖ * Real.exp (L * |ξ.im|) + ‖f' 0‖
          + L * (Real.exp (L * |ξ.im|) * M)) / ‖ξ‖ ^ 2 := by
  have h1 := Cvs.Detection.windowTransform_ibp hf hc1 h0 hLz hξ
  rw [Cvs.Detection.windowTransform_ibp_general hf2 hc2 hξ] at h1
  have hfact : ∀ X Y : ℂ,
      (1 / (ξ * I)) * (-(1 / (ξ * I)) * X + (1 / (ξ * I)) * Y)
        = (1 / (ξ * I)) ^ 2 * (-X + Y) := by
    intro X Y; ring
  rw [hfact] at h1
  rw [h1, norm_mul]
  have hnI : ‖(1 : ℂ) / (ξ * I)‖ = 1 / ‖ξ‖ := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_I, mul_one]
  have hsq : ‖((1 : ℂ) / (ξ * I)) ^ 2‖ = 1 / ‖ξ‖ ^ 2 := by
    rw [norm_pow, hnI, div_pow, one_pow]
  rw [hsq]
  have hnorm : ‖-(f' L * Complex.exp (-((L : ℂ) * ξ) * I) - f' 0)
      + Cvs.Detection.windowTransform L f'' ξ‖
      ≤ ‖f' L‖ * Real.exp (L * |ξ.im|) + ‖f' 0‖
        + L * (Real.exp (L * |ξ.im|) * M) := by
    refine (norm_add_le _ _).trans ?_
    have hb : ‖-(f' L * Complex.exp (-((L : ℂ) * ξ) * I) - f' 0)‖
        ≤ ‖f' L‖ * Real.exp (L * |ξ.im|) + ‖f' 0‖ := by
      rw [norm_neg]
      refine (norm_sub_le _ _).trans ?_
      have h1 : ‖f' L * Complex.exp (-((L : ℂ) * ξ) * I)‖
          ≤ ‖f' L‖ * Real.exp (L * |ξ.im|) := by
        rw [norm_mul, Cvs.Detection.norm_char]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left (le_abs_self _) hL
      linarith
    linarith [Cvs.Detection.norm_windowTransform_le hL hM ξ]
  have hpos : (0 : ℝ) ≤ 1 / ‖ξ‖ ^ 2 := by positivity
  calc 1 / ‖ξ‖ ^ 2 * ‖-(f' L * Complex.exp (-((L : ℂ) * ξ) * I) - f' 0)
          + Cvs.Detection.windowTransform L f'' ξ‖
      ≤ 1 / ‖ξ‖ ^ 2 * (‖f' L‖ * Real.exp (L * |ξ.im|) + ‖f' 0‖
          + L * (Real.exp (L * |ξ.im|) * M)) := mul_le_mul_of_nonneg_left hnorm hpos
    _ = (‖f' L‖ * Real.exp (L * |ξ.im|) + ‖f' 0‖
          + L * (Real.exp (L * |ξ.im|) * M)) / ‖ξ‖ ^ 2 := by
          rw [div_mul_eq_mul_div, one_mul]

/-- **The strip bounds of a `C²` test vanishing at the ends.** -/
theorem admissible_of_C2 {L : ℝ} (hL : 0 < L) {f f' f'' : ℝ → ℝ}
    (hf : ∀ s, HasDerivAt f (f' s) s) (hf2 : ∀ s, HasDerivAt f' (f'' s) s)
    (hc0 : Continuous f) (hc1 : Continuous f') (hc2 : Continuous f'')
    (h0 : f 0 = 0) (hLz : f L = 0)
    {M0 M2 : ℝ} (hM0 : ∀ s, |f s| ≤ M0) (hM2 : ∀ s, |f'' s| ≤ M2) :
    ∃ C0 C2 : ℝ, 0 ≤ C0 ∧ 0 ≤ C2
      ∧ (∀ ξ : ℂ, |ξ.im| ≤ 3 / 2 → ‖Cvs.Detection.windowTransform L (cf f) ξ‖ ≤ C0)
      ∧ (∀ ξ : ℂ, ξ ≠ 0 → |ξ.im| ≤ 3 / 2 →
          ‖Cvs.Detection.windowTransform L (cf f) ξ‖ ≤ C2 / ‖ξ‖ ^ 2) := by
  have _ : Continuous f := hc0
  have hM0nn : 0 ≤ M0 := le_trans (abs_nonneg _) (hM0 0)
  have hM2nn : 0 ≤ M2 := le_trans (abs_nonneg _) (hM2 0)
  set E : ℝ := Real.exp (L * (3 / 2)) with hE
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  refine ⟨L * (E * M0), |f' L| * E + |f' 0| + L * (E * M2), by positivity, by positivity,
    fun ξ hξ => ?_, fun ξ hne hξ => ?_⟩
  · have hexp : Real.exp (L * |ξ.im|) ≤ E :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hξ hL.le)
    refine (Cvs.Detection.norm_windowTransform_le hL.le (M := M0) (fun s _ => ?_) ξ).trans ?_
    · rw [cf, Complex.norm_real, Real.norm_eq_abs]; exact hM0 s
    · gcongr
  · have hexp : Real.exp (L * |ξ.im|) ≤ E :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hξ hL.le)
    have hd1 : ∀ s ∈ Set.uIcc (0 : ℝ) L, HasDerivAt (cf f) ((f' s : ℂ)) s :=
      fun s _ => (hf s).ofReal_comp
    have hd2 : ∀ s ∈ Set.uIcc (0 : ℝ) L, HasDerivAt (fun s : ℝ => (f' s : ℂ)) ((f'' s : ℂ)) s :=
      fun s _ => (hf2 s).ofReal_comp
    have hb := windowTransform_quadratic hL.le hd1 hd2 (Complex.continuous_ofReal.comp hc1)
      (Complex.continuous_ofReal.comp hc2) (by simp [cf, h0]) (by simp [cf, hLz])
      (M := M2) (fun s _ => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hM2 s) hne
    refine hb.trans ?_
    have hpos : (0:ℝ) < ‖ξ‖ ^ 2 := by positivity
    rw [div_le_div_iff_of_pos_right hpos]
    have e1 : ‖((f' L : ℝ) : ℂ)‖ = |f' L| := by rw [Complex.norm_real, Real.norm_eq_abs]
    have e2 : ‖((f' 0 : ℝ) : ℂ)‖ = |f' 0| := by rw [Complex.norm_real, Real.norm_eq_abs]
    rw [e1, e2]
    have h1 := mul_le_mul_of_nonneg_left hexp (abs_nonneg (f' L))
    have h2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hexp hM2nn) hL.le
    linarith

/-! ### The sine polynomial -/

variable {ι : Type*} [Fintype ι]

/-- The sine polynomial behind `Cvs.Finite.OddSectorSineSums.sineSum`, on the whole line. -/
def sinePoly (L : ℝ) (mode : ι → ℤ) (o : ι → ℝ) : ℝ → ℝ :=
  fun y => ∑ i, o i * Real.sin (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i * y)

def sinePoly' (L : ℝ) (mode : ι → ℤ) (o : ι → ℝ) : ℝ → ℝ :=
  fun y => ∑ i, o i * (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i
    * Real.cos (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i * y))

def sinePoly'' (L : ℝ) (mode : ι → ℤ) (o : ι → ℝ) : ℝ → ℝ :=
  fun y => ∑ i, o i * (-(Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i ^ 2
    * Real.sin (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i * y)))

theorem sineSum_eq_indicator_sinePoly (L : ℝ) (mode : ι → ℤ) (o : ι → ℝ) :
    Cvs.Finite.OddSectorSineSums.sineSum L mode o = Set.indicator (Ioc (0:ℝ) L) (sinePoly L mode o) :=
  Cvs.Finite.OddSectorSineSums.sineSum_eq_indicator L mode o

theorem hasDerivAt_sinePoly (L : ℝ) (mode : ι → ℤ) (o : ι → ℝ) (s : ℝ) :
    HasDerivAt (sinePoly L mode o) (sinePoly' L mode o s) s := by
  unfold sinePoly sinePoly'
  refine HasDerivAt.fun_sum fun i _ => ?_
  have h := ((hasDerivAt_mul_const (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i)).sin (x := s))
  have h' : HasDerivAt (fun y => Real.sin (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i * y))
      (Real.cos (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i * s) * Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i)
      s := by simpa [mul_comm] using h
  exact (h'.const_mul (o i)).congr_deriv (by ring)

theorem hasDerivAt_sinePoly' (L : ℝ) (mode : ι → ℤ) (o : ι → ℝ) (s : ℝ) :
    HasDerivAt (sinePoly' L mode o) (sinePoly'' L mode o s) s := by
  unfold sinePoly' sinePoly''
  refine HasDerivAt.fun_sum fun i _ => ?_
  have h := ((hasDerivAt_mul_const (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i)).cos (x := s))
  have h' : HasDerivAt (fun y => Real.cos (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i * y))
      (-Real.sin (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i * s) * Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i)
      s := by simpa [mul_comm] using h
  exact ((h'.const_mul (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i)).const_mul (o i)).congr_deriv
    (by ring)

theorem continuous_sinePoly (L : ℝ) (mode : ι → ℤ) (o : ι → ℝ) : Continuous (sinePoly L mode o) := by
  unfold sinePoly; fun_prop
theorem continuous_sinePoly' (L : ℝ) (mode : ι → ℤ) (o : ι → ℝ) :
    Continuous (sinePoly' L mode o) := by
  unfold sinePoly'; fun_prop
theorem continuous_sinePoly'' (L : ℝ) (mode : ι → ℤ) (o : ι → ℝ) :
    Continuous (sinePoly'' L mode o) := by
  unfold sinePoly''; fun_prop

theorem sinePoly_zero (L : ℝ) (mode : ι → ℤ) (o : ι → ℝ) : sinePoly L mode o 0 = 0 := by
  simp [sinePoly]

theorem sinePoly_L {L : ℝ} (hL : 0 < L) (mode : ι → ℤ) (o : ι → ℝ) : sinePoly L mode o L = 0 := by
  unfold sinePoly
  refine Finset.sum_eq_zero fun i _ => ?_
  have : Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i * L = ((2 * mode i : ℤ) : ℝ) * π := by
    simp only [Cvs.Finite.TruncationZeroFreeOffAxes.omega]
    rw [div_mul_cancel₀ _ hL.ne']
    push_cast; ring
  rw [this, Real.sin_int_mul_pi, mul_zero]

theorem abs_sinePoly_le (L : ℝ) (mode : ι → ℤ) (o : ι → ℝ) (s : ℝ) :
    |sinePoly L mode o s| ≤ ∑ i, |o i| := by
  unfold sinePoly
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)

theorem abs_sinePoly''_le (L : ℝ) (mode : ι → ℤ) (o : ι → ℝ) (s : ℝ) :
    |sinePoly'' L mode o s| ≤ ∑ i, |o i| * Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i ^ 2 := by
  unfold sinePoly''
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg (sq_nonneg (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i))]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  exact mul_le_of_le_one_right (sq_nonneg _) (Real.abs_sin_le_one _)

/-- **The zero side of the odd sector.** The window Weil form of a sine sum is the sum of
`|F(ρ)|²` over all nontrivial zeros. -/
theorem zeroSide_sineSum {L : ℝ} (hL : 0 < L) (mode : ι → ℤ) (o : ι → ℝ) (lam a : ℝ) :
    Cvs.ZeroCounting.kernelZeroSide (Cvs.Detection.sqTransform L (cf (sinePoly L mode o))) lam a
      = Cvs.WeilForm.SelfConvolutionFunctional.weilForm ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊
          (Cvs.Finite.OddSectorSineSums.sineSum L mode o) := by
  obtain ⟨C0, C2, hC0, hC2, hplain, hquad⟩ := admissible_of_C2 hL (hasDerivAt_sinePoly L mode o)
    (hasDerivAt_sinePoly' L mode o) (continuous_sinePoly L mode o) (continuous_sinePoly' L mode o)
    (continuous_sinePoly'' L mode o) (sinePoly_zero L mode o) (sinePoly_L hL mode o)
    (abs_sinePoly_le L mode o) (abs_sinePoly''_le L mode o)
  rw [sineSum_eq_indicator_sinePoly]
  exact Cvs.Zeta.ExplicitFormula.QuadraticDecayZeroSide.weilForm_eq_kernelZeroSide₂ hL (continuous_sinePoly L mode o)
    (sinePoly_zero L mode o) (sinePoly_L hL mode o) hC0 hC2 hplain hquad lam a

end Cvs.Finite.OddSectorZeroSide
