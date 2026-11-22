import Mathlib
import Cvs.WeilForm.LevyDomainSpectral
import Cvs.WeilForm.PoleAndPrimeContinuousWindow
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WeilFormReflection
import Cvs.WeilForm.WindowFormTranslationInvariant
import Cvs.WeilForm.WindowReflectionSymmetry
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.WeilPositivityStatement

/-!
# The pole term on odd classes is bounded below

    `reflW φ = −φ`   ⟹   `2 A(φ) B(φ) ≥ −(e^{L/2} − e^{−L/2} − L) ‖φ‖²`

and at `L = log 2` the constant is `1/√2 − log 2 < 0.01397`.
-/

noncomputable section

open MeasureTheory Set Real

namespace Cvs.WeilForm.OddPoleTermBound

/-- The two pole functionals of a window class. -/
def A {L : ℝ} (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : ℝ :=
  ∫ s, Cvs.WeilForm.WindowRepresentative.rep φ s * Real.exp (s / 2)
def B {L : ℝ} (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : ℝ :=
  ∫ s, Cvs.WeilForm.WindowRepresentative.rep φ s * Real.exp (-(s / 2))

/-- **Oddness at the representative level.** -/
theorem rep_odd_ae {L : ℝ} {φ : Cvs.WeilForm.WeilFormOnWindowL2.window L}
    (hodd : Cvs.WeilForm.WindowReflectionSymmetry.reflW φ = -φ) :
    (fun x => Cvs.WeilForm.WindowRepresentative.rep φ (L - x)) =ᵐ[volume] fun x => -Cvs.WeilForm.WindowRepresentative.rep φ x := by
  have h1 := Cvs.WeilForm.WindowReflectionSymmetry.rep_reflW_ae φ
  rw [hodd] at h1
  have h2 := Cvs.WeilForm.LevyDomainSpectral.rep_smul_ae (-1 : ℝ) φ
  rw [neg_one_smul ℝ φ] at h2
  filter_upwards [h1, h2] with x hx1 hx2
  rw [← hx1, hx2, neg_one_mul]

/-- **`B = −e^{−L/2} A` on odd classes.** -/
theorem B_eq {L : ℝ} {φ : Cvs.WeilForm.WeilFormOnWindowL2.window L}
    (hodd : Cvs.WeilForm.WindowReflectionSymmetry.reflW φ = -φ) : B φ = -Real.exp (-(L / 2)) * A φ := by
  -- `∫ f(L − x) e^{x/2} = e^{L/2} ∫ f(−x) e^{x/2} = e^{L/2} B`
  have h1 : (∫ x, Cvs.WeilForm.WindowRepresentative.rep φ (L - x) * Real.exp (x / 2))
      = Real.exp (L / 2) * B φ := by
    have hf : (fun x => Cvs.WeilForm.WindowRepresentative.rep φ (L - x) * Real.exp (x / 2))
        = fun x => (fun y => Cvs.WeilForm.WindowRepresentative.rep φ (-y)) (x + -L) * Real.exp (x / 2) := by
      funext x
      rw [show L - x = -(x + -L) by ring]
    rw [hf, Cvs.WeilForm.WindowFormTranslationInvariant.integral_translate_exp (fun y => Cvs.WeilForm.WindowRepresentative.rep φ (-y)) (-L)]
    rw [Cvs.WeilForm.WeilFormReflection.integral_reflect_exp]
    unfold B
    ring_nf
  -- and by oddness it is also `−A`
  have h2 : (∫ x, Cvs.WeilForm.WindowRepresentative.rep φ (L - x) * Real.exp (x / 2)) = -A φ := by
    unfold A
    rw [← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [rep_odd_ae hodd] with x hx
    rw [hx]; ring
  have : B φ = Real.exp (-(L / 2)) * (Real.exp (L / 2) * B φ) := by
    rw [← mul_assoc, ← Real.exp_add]; simp
  rw [this, ← h1, h2]; ring

/-- Cauchy–Schwarz on an interval, by the discriminant. -/
theorem sq_integral_mul_le {a b : ℝ} (hab : a ≤ b) {f w : ℝ → ℝ}
    (hf : IntervalIntegrable (fun s => f s ^ 2) volume a b)
    (hw : IntervalIntegrable (fun s => w s ^ 2) volume a b)
    (hfw : IntervalIntegrable (fun s => f s * w s) volume a b) :
    (∫ s in a..b, f s * w s) ^ 2 ≤ (∫ s in a..b, f s ^ 2) * ∫ s in a..b, w s ^ 2 := by
  have key : ∀ c : ℝ, 0 ≤ (∫ s in a..b, f s ^ 2) - 2 * c * (∫ s in a..b, f s * w s)
      + c ^ 2 * ∫ s in a..b, w s ^ 2 := by
    intro c
    have hsq : (0:ℝ) ≤ ∫ s in a..b, (f s - c * w s) ^ 2 :=
      intervalIntegral.integral_nonneg hab fun s _ => sq_nonneg _
    have hexp : (∫ s in a..b, (f s - c * w s) ^ 2)
        = (∫ s in a..b, f s ^ 2) - 2 * c * (∫ s in a..b, f s * w s) + c ^ 2 * ∫ s in a..b, w s ^ 2 := by
      have hpt : ∀ s, (f s - c * w s) ^ 2 = f s ^ 2 - 2 * c * (f s * w s) + c ^ 2 * w s ^ 2 := by
        intro s; ring
      simp only [hpt]
      rw [intervalIntegral.integral_add (hf.sub (hfw.const_mul _)) (hw.const_mul _),
        intervalIntegral.integral_sub hf (hfw.const_mul _), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
    linarith [hexp ▸ hsq]
  generalize hF : (∫ s in a..b, f s ^ 2) = F at key ⊢
  generalize hG : (∫ s in a..b, w s ^ 2) = G at key ⊢
  generalize hP : (∫ s in a..b, f s * w s) = P at key ⊢
  have hG0 : 0 ≤ G := hG ▸ intervalIntegral.integral_nonneg hab fun s _ => sq_nonneg _
  rcases eq_or_lt_of_le hG0 with h | h
  · -- `G = 0`: then `P = 0`, else a large `c` makes the quadratic negative
    subst h
    by_cases hP : P = 0
    · rw [hP]; simp
    · exfalso
      have h1 := key ((F + 1) / (2 * P))
      have h2 : 2 * ((F + 1) / (2 * P)) * P = F + 1 := by
        field_simp
      simp only [mul_zero, add_zero] at h1
      linarith
  · have := key (P / G)
    have hid : G * (F - 2 * (P / G) * P + (P / G) ^ 2 * G) = G * F - P ^ 2 := by
      field_simp; ring
    nlinarith [mul_nonneg h.le this, hid]

/-- The weight `e^{s/2} − e^{(L−s)/2}`, squared and integrated over the half window. -/
theorem integral_weight_sq (L : ℝ) :
    ∫ s in (0:ℝ)..(L / 2), (Real.exp (s / 2) - Real.exp ((L - s) / 2)) ^ 2
      = Real.exp L - 1 - L * Real.exp (L / 2) := by
  have hpt : ∀ s : ℝ, (Real.exp (s / 2) - Real.exp ((L - s) / 2)) ^ 2
      = Real.exp s - 2 * Real.exp (L / 2) + Real.exp (L - s) := by
    intro s
    have e1 : Real.exp (s / 2) ^ 2 = Real.exp s := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have e2 : Real.exp ((L - s) / 2) ^ 2 = Real.exp (L - s) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have e3 : Real.exp (s / 2) * Real.exp ((L - s) / 2) = Real.exp (L / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    nlinarith [e1, e2, e3]
  simp only [hpt]
  have i1 : ∫ s in (0:ℝ)..(L / 2), Real.exp s = Real.exp (L / 2) - 1 := by
    rw [integral_exp, Real.exp_zero]
  have i2 : ∫ s in (0:ℝ)..(L / 2), Real.exp (L - s) = Real.exp L - Real.exp (L / 2) := by
    rw [intervalIntegral.integral_comp_sub_left (fun x => Real.exp x) L, integral_exp]
    ring_nf
  have i3 : ∫ s in (0:ℝ)..(L / 2), (2 * Real.exp (L / 2) : ℝ) = 2 * Real.exp (L / 2) * (L / 2) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  rw [intervalIntegral.integral_add, intervalIntegral.integral_sub, i1, i2, i3]
  · have : Real.exp L = Real.exp (L / 2) * Real.exp (L / 2) := by rw [← Real.exp_add]; congr 1; ring
    ring
  · exact continuous_exp.intervalIntegrable _ _
  · exact continuous_const.intervalIntegrable _ _
  · exact (continuous_exp.intervalIntegrable _ _).sub (continuous_const.intervalIntegrable _ _)
  · exact (continuous_exp.comp (continuous_const.sub continuous_id)).intervalIntegrable _ _

/-- **Folding the window**: on an odd class `A` is a half-window integral against the odd
weight. -/
theorem A_eq_half {L : ℝ} (hL : 0 ≤ L) {φ : Cvs.WeilForm.WeilFormOnWindowL2.window L}
    (hodd : Cvs.WeilForm.WindowReflectionSymmetry.reflW φ = -φ) :
    A φ = ∫ s in (0:ℝ)..(L / 2), Cvs.WeilForm.WindowRepresentative.rep φ s
      * (Real.exp (s / 2) - Real.exp ((L - s) / 2)) := by
  have hint := Cvs.WeilForm.PoleAndPrimeContinuousWindow.integrable_rep_mul hL φ (w := fun s => Real.exp (s / 2))
    (by fun_prop) Cvs.WeilForm.PoleAndPrimeContinuousWindow.abs_exp_half_le
  -- the whole line is the window
  have h1 : A φ = ∫ s in (0:ℝ)..L, Cvs.WeilForm.WindowRepresentative.rep φ s * Real.exp (s / 2) := by
    unfold A
    rw [intervalIntegral.integral_of_le hL, setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro s hs; simp [Cvs.WeilForm.WindowRepresentative.rep_supp φ s hs]
  -- split at the midpoint
  have h2 : (∫ s in (0:ℝ)..L, Cvs.WeilForm.WindowRepresentative.rep φ s * Real.exp (s / 2))
      = (∫ s in (0:ℝ)..(L / 2), Cvs.WeilForm.WindowRepresentative.rep φ s * Real.exp (s / 2))
        + ∫ s in (L / 2)..L, Cvs.WeilForm.WindowRepresentative.rep φ s * Real.exp (s / 2) := by
    rw [intervalIntegral.integral_add_adjacent_intervals hint.intervalIntegrable
      hint.intervalIntegrable]
  -- reflect the second half
  have h3 : (∫ s in (L / 2)..L, Cvs.WeilForm.WindowRepresentative.rep φ s * Real.exp (s / 2))
      = ∫ s in (0:ℝ)..(L / 2), Cvs.WeilForm.WindowRepresentative.rep φ (L - s) * Real.exp ((L - s) / 2) := by
    rw [intervalIntegral.integral_comp_sub_left
      (fun x => Cvs.WeilForm.WindowRepresentative.rep φ x * Real.exp (x / 2)) L]
    congr 1 <;> ring
  have h4 : (∫ s in (0:ℝ)..(L / 2), Cvs.WeilForm.WindowRepresentative.rep φ (L - s) * Real.exp ((L - s) / 2))
      = ∫ s in (0:ℝ)..(L / 2), -(Cvs.WeilForm.WindowRepresentative.rep φ s * Real.exp ((L - s) / 2)) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [rep_odd_ae hodd] with s hs _
    rw [hs]; ring
  have hint2 := Cvs.WeilForm.PoleAndPrimeContinuousWindow.integrable_rep_mul hL φ (w := fun s => Real.exp ((L - s) / 2))
    (by fun_prop) (M := Real.exp (L / 2)) (fun s hs => by
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (by linarith [hs.1, hs.2]))
  rw [h1, h2, h3, h4, intervalIntegral.integral_neg, ← sub_eq_add_neg,
    ← intervalIntegral.integral_sub hint.intervalIntegrable hint2.intervalIntegrable]
  refine intervalIntegral.integral_congr fun s _ => ?_
  ring

/-- **The half-window mass of an odd class is half its norm.** -/
theorem integral_sq_half {L : ℝ} (hL : 0 ≤ L) {φ : Cvs.WeilForm.WeilFormOnWindowL2.window L}
    (hodd : Cvs.WeilForm.WindowReflectionSymmetry.reflW φ = -φ) :
    ∫ s in (0:ℝ)..(L / 2), Cvs.WeilForm.WindowRepresentative.rep φ s ^ 2 = ‖φ‖ ^ 2 / 2 := by
  have hint := Cvs.WeilForm.WindowRepresentative.integrable_sq_rep φ
  have hn : ‖φ‖ ^ 2 = ∫ s in (0:ℝ)..L, Cvs.WeilForm.WindowRepresentative.rep φ s ^ 2 := by
    rw [← (Cvs.WeilForm.WindowRepresentative.weilQW_rep 0 0 φ).2]
    unfold Cvs.Zeta.Explicit.Weil.selfConvolution
    rw [intervalIntegral.integral_of_le hL, setIntegral_eq_integral_of_forall_compl_eq_zero]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_); simp [pow_two]
    · intro s hs; simp [Cvs.WeilForm.WindowRepresentative.rep_supp φ s hs]
  have h2 : (∫ s in (0:ℝ)..L, Cvs.WeilForm.WindowRepresentative.rep φ s ^ 2)
      = (∫ s in (0:ℝ)..(L / 2), Cvs.WeilForm.WindowRepresentative.rep φ s ^ 2)
        + ∫ s in (L / 2)..L, Cvs.WeilForm.WindowRepresentative.rep φ s ^ 2 := by
    rw [intervalIntegral.integral_add_adjacent_intervals hint.intervalIntegrable
      hint.intervalIntegrable]
  have h3a : (∫ s in (L / 2)..L, Cvs.WeilForm.WindowRepresentative.rep φ s ^ 2)
      = ∫ s in (0:ℝ)..(L / 2), Cvs.WeilForm.WindowRepresentative.rep φ (L - s) ^ 2 := by
    rw [intervalIntegral.integral_comp_sub_left (fun x => Cvs.WeilForm.WindowRepresentative.rep φ x ^ 2) L]
    congr 1 <;> ring
  have h3b : (∫ s in (0:ℝ)..(L / 2), Cvs.WeilForm.WindowRepresentative.rep φ (L - s) ^ 2)
      = ∫ s in (0:ℝ)..(L / 2), Cvs.WeilForm.WindowRepresentative.rep φ s ^ 2 := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [rep_odd_ae hodd] with s hs _
    rw [hs]; ring
  have h3 := h3a.trans h3b
  rw [hn, h2, h3]; ring

/-- **The pole term on odd classes.** -/
theorem pole_ge {L : ℝ} (hL : 0 ≤ L) {φ : Cvs.WeilForm.WeilFormOnWindowL2.window L}
    (hodd : Cvs.WeilForm.WindowReflectionSymmetry.reflW φ = -φ) :
    -(Real.exp (L / 2) - Real.exp (-(L / 2)) - L) * ‖φ‖ ^ 2 ≤ 2 * A φ * B φ := by
  rw [B_eq hodd, A_eq_half hL hodd]
  have hint := Cvs.WeilForm.PoleAndPrimeContinuousWindow.integrable_rep_mul hL φ
    (w := fun s => Real.exp (s / 2) - Real.exp ((L - s) / 2)) (by fun_prop)
    (M := Real.exp (L / 2)) (fun s hs => by
      rw [abs_le]; constructor
      · have := Real.exp_le_exp.mpr (show (L - s) / 2 ≤ L / 2 by linarith [hs.1])
        have := Real.exp_pos (s / 2); linarith
      · have := Real.exp_le_exp.mpr (show s / 2 ≤ L / 2 by linarith [hs.2])
        have := Real.exp_pos ((L - s) / 2); linarith)
  have hcs := sq_integral_mul_le (show (0:ℝ) ≤ L / 2 by linarith)
    (f := Cvs.WeilForm.WindowRepresentative.rep φ)
    (w := fun s => Real.exp (s / 2) - Real.exp ((L - s) / 2))
    (Cvs.WeilForm.WindowRepresentative.integrable_sq_rep φ).intervalIntegrable
    ((by fun_prop : Continuous fun s : ℝ =>
      (Real.exp (s / 2) - Real.exp ((L - s) / 2)) ^ 2).intervalIntegrable _ _)
    hint.intervalIntegrable
  rw [integral_sq_half hL hodd, integral_weight_sq L] at hcs
  generalize hX : (∫ s in (0:ℝ)..(L / 2), Cvs.WeilForm.WindowRepresentative.rep φ s
    * (Real.exp (s / 2) - Real.exp ((L - s) / 2))) = X at hcs ⊢
  have hE := Real.exp_pos (-(L / 2))
  have hexp : Real.exp (-(L / 2)) * Real.exp L = Real.exp (L / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hexp2 : Real.exp (-(L / 2)) * Real.exp (L / 2) = 1 := by
    rw [← Real.exp_add]; simp
  have h := mul_le_mul_of_nonneg_left hcs (by positivity : (0:ℝ) ≤ 2 * Real.exp (-(L / 2)))
  have h3 : 2 * Real.exp (-(L / 2)) * (‖φ‖ ^ 2 / 2 * (Real.exp L - 1 - L * Real.exp (L / 2)))
      = ‖φ‖ ^ 2 * (Real.exp (L / 2) - Real.exp (-(L / 2)) - L) := by
    linear_combination (‖φ‖ ^ 2) * hexp - (‖φ‖ ^ 2 * L) * hexp2
  rw [h3] at h
  nlinarith [h]

/-- **The pole constant at `L = log 2`** is `1/√2 − log 2 < 0.01397`. -/
theorem poleConst_log_two :
    Real.exp (Real.log 2 / 2) - Real.exp (-(Real.log 2 / 2)) - Real.log 2 < 1397 / 100000 := by
  have hsq : Real.exp (Real.log 2 / 2) ^ 2 = 2 := by
    rw [← Real.exp_nat_mul, show ((2:ℕ) : ℝ) * (Real.log 2 / 2) = Real.log 2 by push_cast; ring,
      Real.exp_log (by norm_num)]
  have hpos := Real.exp_pos (Real.log 2 / 2)
  set e := Real.exp (Real.log 2 / 2) with he
  have hinv : Real.exp (-(Real.log 2 / 2)) = 1 / e := by rw [Real.exp_neg, one_div]
  rw [hinv]
  -- `e = √2 ∈ (1.41421356, 1.41421357)`
  have hlo : (141421356 : ℝ) / 100000000 < e := by nlinarith
  have hhi : e < (141421357 : ℝ) / 100000000 := by nlinarith
  have hlog := Real.log_two_gt_d9
  have h2 : (100000000 : ℝ) / 141421357 < 1 / e := by
    rw [div_lt_div_iff₀ (by norm_num) hpos]; linarith
  linarith

end Cvs.WeilForm.OddPoleTermBound
