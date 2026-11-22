import Mathlib
import Cvs.Finite.CosineModeOverlap
import Cvs.Finite.OddSectorZeroSide
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Zeta.ExplicitFormula.CompactTestAdmissibility
import Cvs.Zeta.ExplicitFormula.HannWindowShifts
import Cvs.Zeta.ExplicitFormula.QuadraticDecayZeroSide
import Cvs.Zeta.ZeroSideMoments

/-!
# The zero side of the even sector, off the constant

A cosine sum whose coefficients sum to zero vanishes at both ends of the window with its
derivative, so it is a `C²` test in the sense of `Cvs.Finite.OddSectorZeroSide` and its window Weil form is the
zero-side sum. The constant mode, the one even direction this leaves out, has a transform of
linear decay only and needs the approximation argument recorded in the ledger.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Real Complex Cvs.Zeta.Explicit.Weil
open Cvs.WeilForm.SelfConvolutionTransform

namespace Cvs.Finite.EvenSectorZeroSide
open Cvs.ZeroCounting

variable {ι : Type*} [Fintype ι]

/-- The cosine polynomial behind `Cvs.Finite.TruncationZeroFreeOffAxes.modeSum`, on the whole line. -/
def cosPoly (L : ℝ) (mode : ι → ℤ) (xi : ι → ℝ) : ℝ → ℝ :=
  fun y => ∑ i, xi i * Real.cos (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i * y)

def cosPoly' (L : ℝ) (mode : ι → ℤ) (xi : ι → ℝ) : ℝ → ℝ :=
  fun y => ∑ i, xi i * (-(Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i
    * Real.sin (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i * y)))

def cosPoly'' (L : ℝ) (mode : ι → ℤ) (xi : ι → ℝ) : ℝ → ℝ :=
  fun y => ∑ i, xi i * (-(Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i ^ 2
    * Real.cos (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i * y)))

theorem modeSum_eq_indicator_cosPoly (L : ℝ) (mode : ι → ℤ) (xi : ι → ℝ) :
    Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi = Set.indicator (Ioc (0:ℝ) L) (cosPoly L mode xi) :=
  Cvs.Finite.CosineModeOverlap.modeSum_eq_indicator L mode xi

theorem hasDerivAt_cosPoly (L : ℝ) (mode : ι → ℤ) (xi : ι → ℝ) (s : ℝ) :
    HasDerivAt (cosPoly L mode xi) (cosPoly' L mode xi s) s := by
  unfold cosPoly cosPoly'
  refine HasDerivAt.fun_sum fun i _ => ?_
  have h := ((hasDerivAt_mul_const (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i)).cos (x := s))
  have h' : HasDerivAt (fun y => Real.cos (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i * y))
      (-Real.sin (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i * s) * Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i)
      s := by simpa [mul_comm] using h
  exact (h'.const_mul (xi i)).congr_deriv (by ring)

theorem hasDerivAt_cosPoly' (L : ℝ) (mode : ι → ℤ) (xi : ι → ℝ) (s : ℝ) :
    HasDerivAt (cosPoly' L mode xi) (cosPoly'' L mode xi s) s := by
  unfold cosPoly' cosPoly''
  refine HasDerivAt.fun_sum fun i _ => ?_
  have h := ((hasDerivAt_mul_const (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i)).sin (x := s))
  have h' : HasDerivAt (fun y => Real.sin (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i * y))
      (Real.cos (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i * s) * Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i)
      s := by simpa [mul_comm] using h
  exact (((h'.const_mul (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i)).neg).const_mul (xi i)).congr_deriv
    (by ring)

theorem continuous_cosPoly (L : ℝ) (mode : ι → ℤ) (xi : ι → ℝ) : Continuous (cosPoly L mode xi) := by
  unfold cosPoly; fun_prop
theorem continuous_cosPoly' (L : ℝ) (mode : ι → ℤ) (xi : ι → ℝ) :
    Continuous (cosPoly' L mode xi) := by
  unfold cosPoly'; fun_prop
theorem continuous_cosPoly'' (L : ℝ) (mode : ι → ℤ) (xi : ι → ℝ) :
    Continuous (cosPoly'' L mode xi) := by
  unfold cosPoly''; fun_prop

theorem cosPoly_zero (L : ℝ) (mode : ι → ℤ) (xi : ι → ℝ) : cosPoly L mode xi 0 = ∑ i, xi i := by
  simp [cosPoly]

theorem cosPoly_L {L : ℝ} (hL : 0 < L) (mode : ι → ℤ) (xi : ι → ℝ) :
    cosPoly L mode xi L = ∑ i, xi i := by
  unfold cosPoly
  refine Finset.sum_congr rfl fun i _ => ?_
  have : Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i * L = ((mode i : ℤ) : ℝ) * (2 * π) := by
    simp only [Cvs.Finite.TruncationZeroFreeOffAxes.omega]
    rw [div_mul_cancel₀ _ hL.ne']
    ring
  rw [this, Real.cos_int_mul_two_pi, mul_one]

theorem abs_cosPoly_le (L : ℝ) (mode : ι → ℤ) (xi : ι → ℝ) (s : ℝ) :
    |cosPoly L mode xi s| ≤ ∑ i, |xi i| := by
  unfold cosPoly
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

theorem abs_cosPoly''_le (L : ℝ) (mode : ι → ℤ) (xi : ι → ℝ) (s : ℝ) :
    |cosPoly'' L mode xi s| ≤ ∑ i, |xi i| * Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i ^ 2 := by
  unfold cosPoly''
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg (sq_nonneg (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i))]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  exact mul_le_of_le_one_right (sq_nonneg _) (Real.abs_cos_le_one _)

/-- **The zero side of an even mode sum with vanishing coefficient sum.** -/
theorem zeroSide_modeSum_of_sum_zero {L : ℝ} (hL : 0 < L) (mode : ι → ℤ) {xi : ι → ℝ}
    (hsum : ∑ i, xi i = 0) (lam a : ℝ) :
    Cvs.ZeroCounting.kernelZeroSide (Cvs.Detection.sqTransform L (cf (cosPoly L mode xi))) lam a
      = Cvs.WeilForm.SelfConvolutionFunctional.weilForm ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊
          (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode xi) := by
  have h0 : cosPoly L mode xi 0 = 0 := by rw [cosPoly_zero, hsum]
  have hLz : cosPoly L mode xi L = 0 := by rw [cosPoly_L hL, hsum]
  obtain ⟨C0, C2, hC0, hC2, hplain, hquad⟩ := Cvs.Finite.OddSectorZeroSide.admissible_of_C2 hL
    (hasDerivAt_cosPoly L mode xi) (hasDerivAt_cosPoly' L mode xi) (continuous_cosPoly L mode xi)
    (continuous_cosPoly' L mode xi) (continuous_cosPoly'' L mode xi) h0 hLz
    (abs_cosPoly_le L mode xi) (abs_cosPoly''_le L mode xi)
  rw [modeSum_eq_indicator_cosPoly]
  exact Cvs.Zeta.ExplicitFormula.QuadraticDecayZeroSide.weilForm_eq_kernelZeroSide₂ hL (continuous_cosPoly L mode xi)
    h0 hLz hC0 hC2 hplain hquad lam a

end Cvs.Finite.EvenSectorZeroSide
