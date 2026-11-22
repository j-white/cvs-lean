import Mathlib
import Cvs.Finite.ExponentialKernelLocalises
import Cvs.Upstream.RiccatiTangentWitness
import Cvs.Upstream.RobinPoincare
import Cvs.WeilForm.ChannelGreenOddReflection

/-!
# The Robin–Poincaré bound for the channel Green's function of an odd source

    `t² ∫₀^L K² ≤ ∫₀^L K'² + b (K(0)² + K(L)²)`,   `K = convSplit b L f`,

for continuous `f` supported in `[0, L]` with `f(L−s) = −f(s)`, at a pole-free frequency `t`.
-/

noncomputable section

open MeasureTheory Set Real

namespace Cvs.WeilForm.ChannelGreenOddPoincare

variable {f : ℝ → ℝ} {L b t : ℝ}

/-- The tangent witness is regular on `[0, L/2]` when the frequency is pole-free. -/
theorem cos_ne_zero (hb : 0 < b) (ht : 0 < t) (hL : 0 < L)
    (hfree : t * (L / 2) < π / 2 + Real.arctan (b / t)) :
    ∀ x ∈ uIcc (0:ℝ) (L / 2),
      Real.cos (t * (x - Real.arctan (b / t) / t)) ≠ 0 := by
  intro x hx
  rw [uIcc_of_le (by linarith)] at hx
  have harg : t * (x - Real.arctan (b / t) / t) = t * x - Real.arctan (b / t) := by
    field_simp
  rw [harg]
  refine ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
  · have := Real.arctan_lt_pi_div_two (b / t)
    nlinarith [hx.1, mul_nonneg ht.le hx.1]
  · have hxu : t * x ≤ t * (L / 2) := by nlinarith [hx.2]
    linarith

/-- Halving an integral of a function reflection-symmetric on `[0, L/2]`. -/
theorem integral_halve_Icc (hL : 0 < L) {h : ℝ → ℝ}
    (hsym : ∀ x ∈ Icc (0:ℝ) (L / 2), h (L - x) = h x)
    (hint1 : IntervalIntegrable h volume 0 (L / 2))
    (hint2 : IntervalIntegrable h volume (L / 2) L) :
    (∫ s in (0:ℝ)..L, h s) = 2 * ∫ s in (0:ℝ)..(L / 2), h s := by
  have hupper : (∫ s in (L / 2)..L, h s) = ∫ s in (0:ℝ)..(L / 2), h s := by
    have hsub := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := L / 2) h L
    rw [show L - L / 2 = L / 2 by ring, sub_zero] at hsub
    rw [← hsub]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le (by linarith)] at hx
    exact hsym x hx
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2, hupper]; ring

/-- **The Robin–Poincaré bound for an odd source.** -/
theorem poincare_odd (hf : Continuous f) (hodd : ∀ s, f (L - s) = -f s) (hL : 0 < L)
    (hb : 0 < b) (ht : 0 < t) (hfree : t * (L / 2) < π / 2 + Real.arctan (b / t)) :
    t ^ 2 * (∫ s in (0:ℝ)..L, Cvs.Finite.ExponentialKernelLocalises.convSplit b L f s ^ 2)
      ≤ (∫ s in (0:ℝ)..L, Cvs.Finite.ExponentialKernelLocalises.convDeriv b L f s ^ 2)
        + b * (Cvs.Finite.ExponentialKernelLocalises.convSplit b L f 0 ^ 2
          + Cvs.Finite.ExponentialKernelLocalises.convSplit b L f L ^ 2) := by
  set K := Cvs.Finite.ExponentialKernelLocalises.convSplit b L f with hK
  set K' := Cvs.Finite.ExponentialKernelLocalises.convDeriv b L f with hK'
  have hKc : Continuous K := continuous_iff_continuousAt.mpr fun s =>
    (Cvs.Finite.ExponentialKernelLocalises.hasDerivAt_convSplit hf s).continuousAt
  have hK'c : Continuous K' := continuous_iff_continuousAt.mpr fun s =>
    (Cvs.Finite.ExponentialKernelLocalises.hasDerivAt_convDeriv hf s).continuousAt
  set c := Real.arctan (b / t) / t with hc
  set w := Cvs.Upstream.RiccatiTangentWitness.wit t c with hw
  -- witness regular and continuous on [0, L/2]
  have hcos := cos_ne_zero hb ht hL hfree
  have hwc : ContinuousOn w (uIcc (0:ℝ) (L / 2)) := by
    refine ContinuousOn.mul continuousOn_const ?_
    refine Real.continuousOn_tan.comp (by fun_prop) ?_
    intro x hx
    simpa [Real.tan_eq_sin_div_cos] using hcos x hx
  -- K² and K'² halve
  have hK2 : (∫ s in (0:ℝ)..L, K s ^ 2) = 2 * ∫ s in (0:ℝ)..(L / 2), K s ^ 2 := by
    refine integral_halve_Icc hL (fun x hx => ?_)
      ((hKc.pow 2).continuousOn.intervalIntegrable) ((hKc.pow 2).continuousOn.intervalIntegrable)
    simp only [hK]
    rw [Cvs.WeilForm.ChannelGreenOddReflection.convSplit_reflect hf hodd hx.1 (by linarith [hx.2, hL.le])]; ring
  have hK'2 : (∫ s in (0:ℝ)..L, K' s ^ 2) = 2 * ∫ s in (0:ℝ)..(L / 2), K' s ^ 2 := by
    refine integral_halve_Icc hL (fun x hx => ?_)
      ((hK'c.pow 2).continuousOn.intervalIntegrable) ((hK'c.pow 2).continuousOn.intervalIntegrable)
    rcases eq_or_lt_of_le hx.1 with h0 | h0
    · rw [← h0, sub_zero]
      have he : Cvs.Finite.ExponentialKernelLocalises.convSplit b L f L ^ 2
          = Cvs.Finite.ExponentialKernelLocalises.convSplit b L f 0 ^ 2 :=
        Cvs.WeilForm.ChannelGreenOddReflection.convSplit_endpoints hf hodd hL.le
      have e1 : K' L = -b * Cvs.Finite.ExponentialKernelLocalises.convSplit b L f L :=
        Cvs.Finite.ExponentialKernelLocalises.convDeriv_end
      have e2 : K' 0 = b * Cvs.Finite.ExponentialKernelLocalises.convSplit b L f 0 :=
        Cvs.Finite.ExponentialKernelLocalises.convDeriv_zero
      rw [e1, e2]
      have hX : (-b * Cvs.Finite.ExponentialKernelLocalises.convSplit b L f L) ^ 2
          = b ^ 2 * Cvs.Finite.ExponentialKernelLocalises.convSplit b L f L ^ 2 := by ring
      have hY : (b * Cvs.Finite.ExponentialKernelLocalises.convSplit b L f 0) ^ 2
          = b ^ 2 * Cvs.Finite.ExponentialKernelLocalises.convSplit b L f 0 ^ 2 := by ring
      rw [hX, hY, he]
    · rcases eq_or_lt_of_le hx.2 with hm | hm
      · rw [hm, show L - L / 2 = L / 2 by ring]
      · simp only [hK']
        rw [Cvs.WeilForm.ChannelGreenOddReflection.convDeriv_reflect hf hodd h0 (by linarith [hm])]
  -- midpoint and endpoints
  have hmid : K (L / 2) = 0 := Cvs.WeilForm.ChannelGreenOddReflection.convSplit_mid hf hodd hL.le
  have hend : K L ^ 2 = K 0 ^ 2 := Cvs.WeilForm.ChannelGreenOddReflection.convSplit_endpoints hf hodd hL.le
  -- Robin–Poincaré on [0, L/2]
  have hpoin : t ^ 2 * (∫ x in (0:ℝ)..(L / 2), K x ^ 2)
      ≤ (∫ x in (0:ℝ)..(L / 2), K' x ^ 2) + b * K 0 ^ 2 := by
    refine Cvs.Upstream.RobinPoincare.robin_poincare ht
      (fun x _ => Cvs.Finite.ExponentialKernelLocalises.hasDerivAt_convSplit hf x) hcos hmid
      ((hKc.pow 2).continuousOn.intervalIntegrable) ?_ ?_ ?_ ?_
    · exact (((hwc.pow 2).mul (hKc.pow 2).continuousOn)).intervalIntegrable
    · exact ((continuousOn_const.add (hwc.pow 2)).mul (hKc.pow 2).continuousOn).intervalIntegrable
    · exact (hwc.mul (hKc.mul hK'c).continuousOn).intervalIntegrable
    · -- `∫ (K' + wK)² ≥ 0`
      have hi_a : IntervalIntegrable (fun x => K' x ^ 2) volume 0 (L / 2) :=
        (hK'c.pow 2).continuousOn.intervalIntegrable
      have hi_b : IntervalIntegrable (fun x => 2 * (w x * (K x * K' x))) volume 0 (L / 2) :=
        (continuousOn_const.mul (hwc.mul (hKc.mul hK'c).continuousOn)).intervalIntegrable
      have hi_c : IntervalIntegrable (fun x => w x ^ 2 * K x ^ 2) volume 0 (L / 2) :=
        ((hwc.pow 2).mul (hKc.pow 2).continuousOn).intervalIntegrable
      have heq : (∫ x in (0:ℝ)..(L / 2), (K' x + w x * K x) ^ 2)
          = (∫ x in (0:ℝ)..(L / 2), K' x ^ 2)
            + 2 * (∫ x in (0:ℝ)..(L / 2), w x * (K x * K' x))
            + ∫ x in (0:ℝ)..(L / 2), w x ^ 2 * K x ^ 2 := by
        rw [show (fun x => (K' x + w x * K x) ^ 2)
            = (fun x => (K' x ^ 2 + 2 * (w x * (K x * K' x))) + w x ^ 2 * K x ^ 2) from
          funext fun x => by ring,
          intervalIntegral.integral_add (hi_a.add hi_b) hi_c,
          intervalIntegral.integral_add hi_a hi_b, intervalIntegral.integral_const_mul]
      rw [← heq]
      exact intervalIntegral.integral_nonneg (by linarith) fun x _ => sq_nonneg _
  rw [hK2, hK'2, hend]
  nlinarith [hpoin]

end Cvs.WeilForm.ChannelGreenOddPoincare
