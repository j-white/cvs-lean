import Mathlib
import Cvs.WeilForm.WeilFormOnWindowL2

/-!
# The hat function on the window, as a nonzero class

    `hat L s = max 0 (min s (L − s))`

is `1`-Lipschitz, vanishes off `[0, L]`, equals `L/2` at the midpoint, and so is a nonzero
element of the window when `0 < L`.
-/

noncomputable section

open MeasureTheory Set

namespace Cvs.WeilForm.HatFunctionWindow

/-- The hat on `[0, L]`. -/
def hat (L : ℝ) (s : ℝ) : ℝ := max 0 (min s (L - s))

/-- **It vanishes off `(0, L]`.** -/
theorem hat_eq_zero_of_notMem (L : ℝ) {s : ℝ} (hs : s ∉ Ioc (0:ℝ) L) : hat L s = 0 := by
  unfold hat
  rcases not_and_or.mp hs with h | h
  · push_neg at h
    exact max_eq_left ((min_le_left _ _).trans h)
  · push_neg at h
    exact max_eq_left ((min_le_right _ _).trans (by linarith))

/-- **At the midpoint it is `L/2`.** -/
theorem hat_half {L : ℝ} (hL : 0 ≤ L) : hat L (L / 2) = L / 2 := by
  unfold hat
  rw [show L - L / 2 = L / 2 by ring, min_self]
  exact max_eq_right (by linarith)

/-- **It is `1`-Lipschitz.** -/
theorem lipschitz_hat (L : ℝ) : LipschitzWith 1 (hat L) := by
  refine LipschitzWith.of_dist_le_mul fun s t => ?_
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
  unfold hat
  calc |max 0 (min s (L - s)) - max 0 (min t (L - t))|
      ≤ max |0 - 0| |min s (L - s) - min t (L - t)| := abs_max_sub_max_le_max _ _ _ _
    _ ≤ max |0 - 0| (max |s - t| |(L - s) - (L - t)|) :=
        max_le_max le_rfl (abs_min_sub_min_le_max _ _ _ _)
    _ = |s - t| := by
        rw [sub_self, abs_zero, show (L - s) - (L - t) = -(s - t) by ring, abs_neg, max_self]
        exact max_eq_right (abs_nonneg _)

theorem continuous_hat (L : ℝ) : Continuous (hat L) := (lipschitz_hat L).continuous

theorem support_hat_subset (L : ℝ) : Function.support (hat L) ⊆ Icc 0 L := by
  intro s hs
  by_contra h
  exact hs (hat_eq_zero_of_notMem L fun h' => h (Ioc_subset_Icc_self h'))

theorem hasCompactSupport_hat (L : ℝ) : HasCompactSupport (hat L) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (support_hat_subset L)

theorem memLp_hat (L : ℝ) : MemLp (hat L) 2 (volume : Measure ℝ) :=
  (continuous_hat L).memLp_of_hasCompactSupport (hasCompactSupport_hat L)

/-- **The hat, as a class in the window.** -/
def hatW (L : ℝ) : Cvs.WeilForm.WeilFormOnWindowL2.window L :=
  ⟨(memLp_hat L).toLp _, by
    show ∀ᵐ x ∂(volume : Measure ℝ), x ∉ Ioc (0:ℝ) L → ((memLp_hat L).toLp _ : ℝ → ℝ) x = 0
    filter_upwards [(memLp_hat L).coeFn_toLp] with x hx hxL
    rw [hx]
    exact hat_eq_zero_of_notMem L hxL⟩

theorem hatW_ae (L : ℝ) :
    ((hatW L : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)) =ᵐ[volume] hat L :=
  (memLp_hat L).coeFn_toLp

/-- **It is a nonzero class** when the window is nondegenerate. -/
theorem hatW_ne_zero {L : ℝ} (hL : 0 < L) : hatW L ≠ 0 := by
  intro h0
  have h1 : ((hatW L : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)) = 0 := by
    rw [h0]; rfl
  have h2 : hat L =ᵐ[volume] (0 : ℝ → ℝ) := by
    have := (hatW_ae L).symm.trans (Lp.eq_zero_iff_ae_eq_zero.mp h1)
    exact this
  have h3 : hat L = 0 :=
    (Continuous.ae_eq_iff_eq (volume : Measure ℝ) (continuous_hat L) continuous_zero).mp h2
  have := congrFun h3 (L / 2)
  rw [hat_half hL.le, Pi.zero_apply] at this
  linarith

end Cvs.WeilForm.HatFunctionWindow
