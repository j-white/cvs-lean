import Mathlib
import Cvs.WeilForm.ChannelBandSpectralGain

/-!
# Enclosing the full channel mode sum

The channel weights of `Cvs.WeilForm.ChannelBandSpectralGain` summed over every Lévy channel form the mode gain of a single
frequency, and the elementary antiderivative `½ log(1 + (t/2)²/a²)` brackets the tail of that
sum between two explicit expressions in the cut-off.
-/

noncomputable section

open Filter Topology Set

namespace Cvs.WeilForm.ChannelModeSumEnclosure

open Cvs.WeilForm.ChannelBandSpectralGain

/-- The tail integral of the channel weight, `∫ₐ^∞ chanWeight · t`. -/
def phi (t a : ℝ) : ℝ := 1 / 2 * Real.log (a ^ 2 + (t / 2) ^ 2) - Real.log a

/-- **The tail integral in the logarithmic form.** -/
theorem phi_eq {a : ℝ} (ha : 0 < a) (t : ℝ) :
    phi t a = 1 / 2 * Real.log (1 + (t / 2) ^ 2 / a ^ 2) := by
  have ha2 : (0:ℝ) < a ^ 2 := by positivity
  have hd : (0:ℝ) < a ^ 2 + (t / 2) ^ 2 := by positivity
  have hq : 1 + (t / 2) ^ 2 / a ^ 2 = (a ^ 2 + (t / 2) ^ 2) / a ^ 2 := by
    field_simp
  rw [phi, hq, Real.log_div (ne_of_gt hd) (ne_of_gt ha2), Real.log_pow]
  push_cast
  ring

/-- **The tail integral is nonnegative.** -/
theorem phi_nonneg {a : ℝ} (ha : 0 < a) (t : ℝ) : 0 ≤ phi t a := by
  rw [phi_eq ha]
  have h1 : (1:ℝ) ≤ 1 + (t / 2) ^ 2 / a ^ 2 := by
    have : (0:ℝ) ≤ (t / 2) ^ 2 / a ^ 2 := by positivity
    linarith
  have := Real.log_nonneg h1
  linarith

/-- **The channel weight is the negative derivative of the tail integral.** -/
theorem hasDerivAt_phi {a : ℝ} (ha : 0 < a) (t : ℝ) :
    HasDerivAt (phi t) (-(chanWeight a t)) a := by
  have hd : (0:ℝ) < a ^ 2 + (t / 2) ^ 2 := by positivity
  have h1 : HasDerivAt (fun x : ℝ => x ^ 2 + (t / 2) ^ 2) (2 * a) a := by
    simpa using ((hasDerivAt_pow 2 a).add_const ((t / 2) ^ 2))
  have h2 : HasDerivAt (fun x : ℝ => Real.log (x ^ 2 + (t / 2) ^ 2)) (2 * a / (a ^ 2 + (t / 2) ^ 2)) a :=
    h1.log (ne_of_gt hd)
  have h3 : HasDerivAt Real.log a⁻¹ a := Real.hasDerivAt_log (ne_of_gt ha)
  have h4 : HasDerivAt (fun x : ℝ => 1 / 2 * Real.log (x ^ 2 + (t / 2) ^ 2) - Real.log x)
      (1 / 2 * (2 * a / (a ^ 2 + (t / 2) ^ 2)) - a⁻¹) a := (h2.const_mul (1 / 2 : ℝ)).sub h3
  have heq : 1 / 2 * (2 * a / (a ^ 2 + (t / 2) ^ 2)) - a⁻¹ = -(chanWeight a t) := by
    rw [chanWeight]
    field_simp
    ring
  rw [heq] at h4
  exact h4

/-- **The channel weight falls off in the channel index.** -/
theorem chanWeight_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (t : ℝ) :
    chanWeight b t ≤ chanWeight a t := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  rw [chanWeight_eq ha, chanWeight_eq hb]
  have hc : (0:ℝ) ≤ (t / 2) ^ 2 := sq_nonneg _
  have h1 : a * (a ^ 2 + (t / 2) ^ 2) ≤ b * (b ^ 2 + (t / 2) ^ 2) := by
    have hfac : b * (b ^ 2 + (t / 2) ^ 2) - a * (a ^ 2 + (t / 2) ^ 2)
        = (b - a) * (b ^ 2 + a * b + a ^ 2 + (t / 2) ^ 2) := by ring
    have hpos : (0:ℝ) ≤ (b - a) * (b ^ 2 + a * b + a ^ 2 + (t / 2) ^ 2) :=
      mul_nonneg (sub_nonneg.mpr hab) (by positivity)
    linarith
  have h2 : (0:ℝ) < a * (a ^ 2 + (t / 2) ^ 2) := by positivity
  gcongr

/-- **A unit step of the tail integral is a channel weight at an interior point.** -/
theorem exists_step {a : ℝ} (ha : 0 < a) (t : ℝ) :
    ∃ x ∈ Ioo a (a + 1), phi t a - phi t (a + 1) = chanWeight x t := by
  have hlt : a < a + 1 := by linarith
  have hderiv : ∀ x ∈ Ioo a (a + 1), HasDerivAt (phi t) (-(chanWeight x t)) x := by
    intro x hx
    exact hasDerivAt_phi (lt_trans ha hx.1) t
  have hcont : ContinuousOn (phi t) (Icc a (a + 1)) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    exact ((hasDerivAt_phi hx0 t).continuousAt).continuousWithinAt
  obtain ⟨x, hx, hxe⟩ :=
    exists_hasDerivAt_eq_slope (phi t) (fun x => -(chanWeight x t)) hlt hcont hderiv
  refine ⟨x, hx, ?_⟩
  have : -(chanWeight x t) = phi t (a + 1) - phi t a := by
    rw [hxe]; ring_nf
  linarith

/-- **A unit step of the tail integral is at most the channel weight at its left end.** -/
theorem step_le {a : ℝ} (ha : 0 < a) (t : ℝ) : phi t a - phi t (a + 1) ≤ chanWeight a t := by
  obtain ⟨x, hx, hxe⟩ := exists_step ha t
  rw [hxe]
  exact chanWeight_antitone ha (le_of_lt hx.1) t

/-- **A unit step of the tail integral is at least the channel weight at its right end.** -/
theorem le_step {a : ℝ} (ha : 0 < a) (t : ℝ) : chanWeight (a + 1) t ≤ phi t a - phi t (a + 1) := by
  obtain ⟨x, hx, hxe⟩ := exists_step ha t
  rw [hxe]
  exact chanWeight_antitone (lt_trans ha hx.1) (le_of_lt hx.2) t

/-- **The tail integral vanishes at infinity.** -/
theorem tendsto_phi (t : ℝ) : Tendsto (fun a : ℝ => phi t a) atTop (𝓝 0) := by
  have hq : Tendsto (fun a : ℝ => 1 + (t / 2) ^ 2 / a ^ 2) atTop (𝓝 1) := by
    have h2 : Tendsto (fun a : ℝ => a ^ 2) atTop atTop :=
      tendsto_pow_atTop (by norm_num)
    have : Tendsto (fun a : ℝ => (t / 2) ^ 2 / a ^ 2) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds h2
    simpa using tendsto_const_nhds.add this
  have hlog : Tendsto (fun a : ℝ => Real.log (1 + (t / 2) ^ 2 / a ^ 2)) atTop (𝓝 0) := by
    have h := (Real.continuousAt_log (by norm_num : (1:ℝ) ≠ 0)).tendsto.comp hq
    rw [Real.log_one] at h
    exact h
  have hhalf : Tendsto (fun a : ℝ => 1 / 2 * Real.log (1 + (t / 2) ^ 2 / a ^ 2)) atTop (𝓝 0) := by
    have := hlog.const_mul (1 / 2 : ℝ)
    simpa using this
  refine hhalf.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with a ha
  exact (phi_eq ha t).symm

/-- **The shifted partial sums telescope below the tail integral.** -/
theorem sum_shift_le {A : ℝ} (hA : 0 < A) (t : ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range n, chanWeight (A + 1 + j) t ≤ phi t A - phi t (A + n) := by
  induction n with
  | zero => simp
  | succ m ih =>
      have hAm : (0:ℝ) < A + m := by positivity
      have hstep : chanWeight (A + m + 1) t ≤ phi t (A + m) - phi t (A + m + 1) :=
        le_step hAm t
      have hcast : A + 1 + (m : ℝ) = A + m + 1 := by ring
      have hcast2 : A + ((m : ℕ) + 1 : ℕ) = A + m + 1 := by push_cast; ring
      rw [Finset.sum_range_succ, hcast, hcast2]
      linarith [ih]

/-- **The shifted partial sums telescope above the tail integral.** -/
theorem le_sum_shift {A : ℝ} (hA : 0 < A) (t : ℝ) (n : ℕ) :
    phi t A - phi t (A + n) ≤ ∑ j ∈ Finset.range n, chanWeight (A + j) t := by
  induction n with
  | zero => simp
  | succ m ih =>
      have hAm : (0:ℝ) < A + m := by positivity
      have hstep : phi t (A + m) - phi t (A + m + 1) ≤ chanWeight (A + m) t := step_le hAm t
      have hcast2 : A + ((m : ℕ) + 1 : ℕ) = A + m + 1 := by push_cast; ring
      rw [Finset.sum_range_succ, hcast2]
      linarith [ih]

/-- **The partial sums of the tail are bounded.** -/
theorem sum_tail_le {A : ℝ} (hA : 0 < A) (t : ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range n, chanWeight (A + j) t ≤ chanWeight A t + phi t A := by
  cases n with
  | zero =>
      simp
      exact add_nonneg (chanWeight_nonneg hA t) (phi_nonneg hA t)
  | succ m =>
      have hpeel : ∑ j ∈ Finset.range (m + 1), chanWeight (A + j) t
          = (∑ j ∈ Finset.range m, chanWeight (A + (j + 1 : ℕ)) t) + chanWeight (A + (0:ℕ)) t :=
        Finset.sum_range_succ' (fun j => chanWeight (A + j) t) m
      have hshift : ∀ j : ℕ, chanWeight (A + ((j : ℕ) + 1 : ℕ)) t = chanWeight (A + 1 + j) t := by
        intro j; congr 1; push_cast; ring
      have hAn : (0:ℝ) < A + m := by positivity
      have h1 := sum_shift_le hA t m
      have h2 : phi t (A + m) ≥ 0 := phi_nonneg hAn t
      rw [hpeel]
      simp only [hshift, Nat.cast_zero, add_zero]
      linarith

/-- The tail of the channel mode sum beyond a cut-off. -/
def modeTail (t A : ℝ) : ℝ := ∑' j : ℕ, chanWeight (A + j) t

/-- **The tail of the channel mode sum converges.** -/
theorem summable_tail {A : ℝ} (hA : 0 < A) (t : ℝ) :
    Summable (fun j : ℕ => chanWeight (A + j) t) :=
  summable_of_sum_range_le (fun j => chanWeight_nonneg (by positivity) t) (sum_tail_le hA t)

/-- **The tail integral vanishes along the channels.** -/
theorem tendsto_phi_nat {A : ℝ} (t : ℝ) :
    Filter.Tendsto (fun n : ℕ => phi t (A + n)) Filter.atTop (𝓝 0) := by
  have h1 : Filter.Tendsto (fun n : ℕ => A + (n : ℝ)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_left _ A tendsto_natCast_atTop_atTop
  exact (tendsto_phi t).comp h1

/-- **The channel mode tail is bracketed by the tail integral.** -/
theorem tail_enclosure {A : ℝ} (hA : 0 < A) (t : ℝ) :
    phi t A ≤ modeTail t A ∧ modeTail t A ≤ chanWeight A t + phi t A := by
  constructor
  · have hs := summable_tail hA t
    have hlim := hs.hasSum.tendsto_sum_nat
    have hphi : Filter.Tendsto (fun n : ℕ => phi t A - phi t (A + n)) Filter.atTop
        (𝓝 (phi t A - 0)) := Filter.Tendsto.const_sub _ (tendsto_phi_nat t)
    rw [sub_zero] at hphi
    exact le_of_tendsto_of_tendsto' hphi hlim (fun n => le_sum_shift hA t n)
  · exact Real.tsum_le_of_sum_range_le
      (fun j => chanWeight_nonneg (by positivity) t) (sum_tail_le hA t)

end Cvs.WeilForm.ChannelModeSumEnclosure
