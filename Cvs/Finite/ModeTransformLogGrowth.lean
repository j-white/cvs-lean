import Mathlib
import Cvs.Finite.CosineModeTransformBounds
import Cvs.Upstream.HarmonicLatticeSum
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Zeta.ExplicitFormula.HannWindowShifts

/-!
# The sum of the mode transforms grows only logarithmically in the mode count

At most two modes sit within a lattice step of `|Re ξ|`; they take the crude bound. The rest
take the far bound, whose reciprocal distances sum to `3(1 + log N)`. So
`∑_{m ≤ N} ‖W_m(ξ)‖ ≤ 2L e^{L|Im ξ|} + 3(e^{L|Im ξ|} + 1)(δ + |Im ξ|)(1 + log N)/δ²` with
`δ = 2π/L`, uniformly in `ξ`; divided by `N` this is the size of `f̂_N − f̂`.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real Complex Finset
open Cvs.WeilForm.SelfConvolutionTransform

namespace Cvs.Finite.ModeTransformLogGrowth

/-- At most two naturals lie within distance one of a real. -/
theorem card_near_le (b : ℝ) (N : ℕ) :
    ((Finset.Icc 1 N).filter (fun m : ℕ => |(m : ℝ) - b| < 1)).card ≤ 2 := by
  have hsub : (Finset.Icc 1 N).filter (fun m : ℕ => |(m : ℝ) - b| < 1)
      ⊆ {⌊b⌋₊, ⌊b⌋₊ + 1} := by
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨h1, _⟩, h2⟩ := hm
    rw [abs_lt] at h2
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast h1
    have hb0 : 0 ≤ b := by linarith
    have hf1 : (⌊b⌋₊ : ℝ) ≤ b := Nat.floor_le hb0
    have hf2 : b < ⌊b⌋₊ + 1 := Nat.lt_floor_add_one b
    have hlo : (⌊b⌋₊ : ℝ) - 1 < m := by linarith
    have hhi : (m : ℝ) < ⌊b⌋₊ + 2 := by linarith
    have hlo' : ⌊b⌋₊ ≤ m := by
      have : (⌊b⌋₊ : ℝ) < m + 1 := by linarith
      exact_mod_cast Nat.lt_add_one_iff.mp (by exact_mod_cast this)
    have hhi' : m ≤ ⌊b⌋₊ + 1 := by
      have : (m : ℝ) < ⌊b⌋₊ + 1 + 1 := by linarith
      have : m < ⌊b⌋₊ + 1 + 1 := by exact_mod_cast this
      omega
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  exact (Finset.card_le_card hsub).trans (Finset.card_le_two)

/-- **The sum of the mode transforms up to `N`.** -/
theorem sum_norm_windowTransform_cos_le {L : ℝ} (hL : 0 < L) (N : ℕ) (ξ : ℂ) :
    ∑ m ∈ Finset.Icc 1 N,
        ‖Cvs.Detection.windowTransform L (cf fun y => Real.cos (2 * π * m / L * y)) ξ‖
      ≤ 2 * L * Real.exp (L * |ξ.im|)
        + 3 * (Real.exp (L * |ξ.im|) + 1) * (2 * π / L + |ξ.im|) * (1 + Real.log N)
          / (2 * π / L) ^ 2 := by
  set δ : ℝ := 2 * π / L with hδ
  have hδ0 : 0 < δ := by positivity
  set b : ℝ := |ξ.re| / δ with hb
  have hb0 : 0 ≤ b := by positivity
  set E : ℝ := Real.exp (L * |ξ.im|) with hE
  have hE0 : 0 < E := Real.exp_pos _
  set W : ℕ → ℝ := fun m =>
    ‖Cvs.Detection.windowTransform L (cf fun y => Real.cos (2 * π * m / L * y)) ξ‖ with hW
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N) (fun m : ℕ => |(m : ℝ) - b| < 1)]
  -- the near modes: at most two, each at most `L E`
  have hnear : ∑ m ∈ (Finset.Icc 1 N).filter (fun m : ℕ => |(m : ℝ) - b| < 1), W m ≤ 2 * L * E := by
    calc ∑ m ∈ (Finset.Icc 1 N).filter (fun m : ℕ => |(m : ℝ) - b| < 1), W m
        ≤ ∑ _m ∈ (Finset.Icc 1 N).filter (fun m : ℕ => |(m : ℝ) - b| < 1), L * E :=
          Finset.sum_le_sum fun m _ => Cvs.Finite.CosineModeTransformBounds.norm_windowTransform_cos_le hL.le _ ξ
      _ = ((Finset.Icc 1 N).filter (fun m : ℕ => |(m : ℝ) - b| < 1)).card * (L * E) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * (L * E) := by
          have := card_near_le b N
          have h2 : (((Finset.Icc 1 N).filter (fun m : ℕ => |(m : ℝ) - b| < 1)).card : ℝ) ≤ 2 := by
            exact_mod_cast this
          exact mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = 2 * L * E := by ring
  -- the far modes: the far bound, then the harmonic sum
  have hfar : ∑ m ∈ (Finset.Icc 1 N).filter (fun m : ℕ => ¬ |(m : ℝ) - b| < 1), W m
      ≤ 3 * (E + 1) * (δ + |ξ.im|) * (1 + Real.log N) / δ ^ 2 := by
    have hfilt : (Finset.Icc 1 N).filter (fun m : ℕ => ¬ |(m : ℝ) - b| < 1)
        = (Finset.Icc 1 N).filter (fun m : ℕ => 1 ≤ |(m : ℝ) - b|) := by
      refine Finset.filter_congr fun m _ => ?_
      rw [not_lt]
    rw [hfilt]
    have hterm : ∀ m ∈ (Finset.Icc 1 N).filter (fun m : ℕ => 1 ≤ |(m : ℝ) - b|),
        W m ≤ ((E + 1) * (δ + |ξ.im|) / δ ^ 2) * (1 / |(m : ℝ) - b|) := by
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_Icc] at hm
      obtain ⟨⟨hm1, _⟩, hmb⟩ := hm
      have hωm : (2 * π * m / L : ℝ) = δ * m := by rw [hδ]; ring
      have hx : |ξ.re| = δ * b := by rw [hb]; field_simp
      -- off the resonance
      have hne : (2 * π * m / L : ℝ) ^ 2 ≠ ξ.re ^ 2 := by
        rw [hωm, ← sq_abs ξ.re, hx]
        intro h
        have h' : (δ * m) ^ 2 - (δ * b) ^ 2 = 0 := sub_eq_zero.mpr h
        have h'' : δ ^ 2 * ((m : ℝ) - b) * ((m : ℝ) + b) = 0 := by linear_combination h'
        have hmpos : (0 : ℝ) < (m : ℝ) + b := by
          have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
          linarith
        rcases mul_eq_zero.mp h'' with h3 | h3
        · rcases mul_eq_zero.mp h3 with h4 | h4
          · exact absurd h4 (by positivity)
          · rw [h4, abs_zero] at hmb; linarith
        · exact absurd h3 hmpos.ne'
      have hne' : (2 * π * ((m : ℤ) : ℝ) / L : ℝ) ^ 2 ≠ ξ.re ^ 2 := by
        rw [Int.cast_natCast]; exact hne
      have hfarb := Cvs.Finite.CosineModeTransformBounds.norm_windowTransform_cos_far hL (m : ℤ) (ξ := ξ) hne'
      simp only [Int.cast_natCast] at hfarb
      rw [← hE] at hfarb
      refine hfarb.trans ?_
      -- rewrite the denominator through `δ` and `b`
      have hden : |(2 * π * m / L : ℝ) ^ 2 - ξ.re ^ 2| = δ ^ 2 * |(m : ℝ) - b| * ((m : ℝ) + b) := by
        rw [hωm, ← sq_abs ξ.re, hx]
        have hmpos : (0 : ℝ) ≤ (m : ℝ) + b := by positivity
        rw [show (δ * m) ^ 2 - (δ * b) ^ 2 = δ ^ 2 * (((m : ℝ) - b) * ((m : ℝ) + b)) by ring,
          abs_mul, abs_mul, abs_of_nonneg (sq_nonneg δ), abs_of_nonneg hmpos]
        ring
      rw [hden]
      have hξle : ‖ξ‖ ≤ δ * b + |ξ.im| := by
        rw [← hx]
        exact (Complex.norm_le_abs_re_add_abs_im ξ)
      have hmb1 : (1 : ℝ) ≤ (m : ℝ) + b := by
        have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
        linarith
      have hpos1 : 0 < |(m : ℝ) - b| := by linarith
      have hpos2 : 0 < (m : ℝ) + b := by linarith
      have hkey : ‖ξ‖ ≤ (δ + |ξ.im|) * ((m : ℝ) + b) := by
        calc ‖ξ‖ ≤ δ * b + |ξ.im| := hξle
          _ ≤ δ * ((m : ℝ) + b) + |ξ.im| * ((m : ℝ) + b) := by
              have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
              nlinarith [abs_nonneg ξ.im, hδ0]
          _ = (δ + |ξ.im|) * ((m : ℝ) + b) := by ring
      have hE1 : 0 ≤ E + 1 := by positivity
      have hq : ‖ξ‖ / ((m : ℝ) + b) ≤ δ + |ξ.im| := by
        rw [div_le_iff₀ hpos2]; exact hkey
      calc ‖ξ‖ * (E + 1) / (δ ^ 2 * |(m : ℝ) - b| * ((m : ℝ) + b))
          = ((E + 1) / (δ ^ 2 * |(m : ℝ) - b|)) * (‖ξ‖ / ((m : ℝ) + b)) := by
            field_simp
        _ ≤ ((E + 1) / (δ ^ 2 * |(m : ℝ) - b|)) * (δ + |ξ.im|) :=
            mul_le_mul_of_nonneg_left hq (by positivity)
        _ = ((E + 1) * (δ + |ξ.im|) / δ ^ 2) * (1 / |(m : ℝ) - b|) := by
            field_simp
    calc ∑ m ∈ (Finset.Icc 1 N).filter (fun m : ℕ => 1 ≤ |(m : ℝ) - b|), W m
        ≤ ∑ m ∈ (Finset.Icc 1 N).filter (fun m : ℕ => 1 ≤ |(m : ℝ) - b|),
            ((E + 1) * (δ + |ξ.im|) / δ ^ 2) * (1 / |(m : ℝ) - b|) := Finset.sum_le_sum hterm
      _ = ((E + 1) * (δ + |ξ.im|) / δ ^ 2)
          * ∑ m ∈ (Finset.Icc 1 N).filter (fun m : ℕ => 1 ≤ |(m : ℝ) - b|), 1 / |(m : ℝ) - b| := by
          rw [Finset.mul_sum]
      _ ≤ ((E + 1) * (δ + |ξ.im|) / δ ^ 2) * (3 * (1 + Real.log N)) := by
          gcongr
          exact Cvs.Upstream.HarmonicLatticeSum.sum_inv_dist_le hb0 N
      _ = 3 * (E + 1) * (δ + |ξ.im|) * (1 + Real.log N) / δ ^ 2 := by ring
  simp only [hW] at hnear hfar
  linarith [hnear, hfar]

end Cvs.Finite.ModeTransformLogGrowth
