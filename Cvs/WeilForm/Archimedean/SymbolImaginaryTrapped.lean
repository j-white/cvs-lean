import Mathlib
import Cvs.WeilForm.Archimedean.SymbolImaginaryHalf

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The symbol's imaginary half is trapped near `π/2`

The terms of the imaginary half's series are a decreasing function of the pole, whose integral
is an arctangent; comparing the series with the integral from both sides traps
`Im ψ(1/4 + iy)` between `π/2 − arctan(1/(4y))` and that plus the first term, for every `y > 0`.
-/

noncomputable section

open Real Finset

namespace Cvs.WeilForm.Archimedean.SymbolImaginaryTrapped

open Cvs.WeilForm.Archimedean.SymbolImaginaryHalf

/-- The term as a function of the pole: `y / ((u + 1/4)² + y²)`. -/
def poleTerm (y u : ℝ) : ℝ := y / ((u + 1 / 4) ^ 2 + y ^ 2)

theorem imTerm_eq_poleTerm (t : ℝ) (k : ℕ) : imTerm t k = poleTerm (t / 2) k := by
  unfold imTerm poleTerm; ring_nf

theorem poleTerm_nonneg {y : ℝ} (hy : 0 ≤ y) (u : ℝ) : 0 ≤ poleTerm y u := by
  unfold poleTerm; positivity

theorem poleTerm_antitoneOn {y : ℝ} (hy : 0 < y) : AntitoneOn (poleTerm y) (Set.Ici 0) := by
  intro u hu v hv huv
  unfold poleTerm
  have hu0 : (0 : ℝ) ≤ u := hu
  have hv0 : (0 : ℝ) ≤ v := hv
  apply div_le_div_of_nonneg_left hy.le (by positivity)
  have : (u + 1 / 4) ^ 2 ≤ (v + 1 / 4) ^ 2 := by
    apply pow_le_pow_left₀ (by linarith) (by linarith)
  linarith

/-- **The integral of the term is an arctangent.** -/
theorem integral_poleTerm {y : ℝ} (hy : 0 < y) (a b : ℝ) :
    ∫ u in a..b, poleTerm y u = Real.arctan ((b + 1 / 4) / y) - Real.arctan ((a + 1 / 4) / y) := by
  have hd : ∀ u, HasDerivAt (fun u => Real.arctan ((u + 1 / 4) / y)) (poleTerm y u) u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => (u + 1 / 4) / y) (1 / y) u := by
      have := ((hasDerivAt_id u).add_const (1 / 4)).div_const y
      simpa [one_div] using this
    have := h1.arctan
    convert this using 1
    unfold poleTerm
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)]
  have hc : Continuous (poleTerm y) := by
    unfold poleTerm
    exact continuous_const.div₀ (by fun_prop) (fun u => by positivity)
  exact hc.intervalIntegrable a b

/-- **The partial sums from above**: the first term plus the integral. -/
theorem sum_le {y : ℝ} (hy : 0 < y) (n : ℕ) :
    ∑ k ∈ range n, poleTerm y k ≤ poleTerm y 0 + (π / 2 - Real.arctan (1 / (4 * y))) := by
  rcases n with _ | n
  · simp only [Finset.sum_range_zero]
    have : Real.arctan (1 / (4 * y)) < π / 2 := Real.arctan_lt_pi_div_two _
    have := poleTerm_nonneg hy.le 0
    linarith
  rw [Finset.sum_range_succ']
  have hmono : AntitoneOn (poleTerm y) (Set.Icc (0 : ℝ) (0 + n)) :=
    (poleTerm_antitoneOn hy).mono (fun u hu => hu.1)
  have h := hmono.sum_le_integral
  simp only [zero_add, Nat.cast_add, Nat.cast_one] at h
  have hint := integral_poleTerm hy 0 n
  have hlt : Real.arctan (((n : ℝ) + 1 / 4) / y) < π / 2 := Real.arctan_lt_pi_div_two _
  have e : Real.arctan ((0 + 1 / 4) / y) = Real.arctan (1 / (4 * y)) := by
    congr 1; ring
  rw [hint, e] at h
  have : ∑ k ∈ range n, poleTerm y ((k : ℝ) + 1) = ∑ k ∈ range n, poleTerm y (((k + 1 : ℕ) : ℝ)) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast; rfl
  simp only [Nat.cast_zero] at *
  linarith

/-- **The partial sums from below**: the integral to the end of the range. -/
theorem integral_le_sum {y : ℝ} (hy : 0 < y) (n : ℕ) :
    Real.arctan (((n : ℝ) + 1 / 4) / y) - Real.arctan (1 / (4 * y)) ≤ ∑ k ∈ range n, poleTerm y k := by
  have hmono : AntitoneOn (poleTerm y) (Set.Icc (0 : ℝ) (0 + n)) :=
    (poleTerm_antitoneOn hy).mono (fun u hu => hu.1)
  have h := hmono.integral_le_sum
  simp only [zero_add] at h
  have hint := integral_poleTerm hy 0 n
  have e : Real.arctan ((0 + 1 / 4) / y) = Real.arctan (1 / (4 * y)) := by
    congr 1; ring
  rw [hint, e] at h
  exact h

/-- **The imaginary half, trapped**: `π/2 − arctan(1/(4y)) ≤ Im ψ(1/4 + iy)`, and at most the first
term more. -/
theorem archSymbolIm_bounds {t : ℝ} (ht : 0 < t) :
    π / 2 - Real.arctan (1 / (4 * (t / 2))) ≤ archSymbolIm t
      ∧ archSymbolIm t ≤ (t / 2) / (1 / 16 + (t / 2) ^ 2) + (π / 2 - Real.arctan (1 / (4 * (t / 2)))) := by
  have hy : 0 < t / 2 := by positivity
  have hs := hasSum_imTerm t
  have hsum : Summable (imTerm t) := hs.summable
  have heq : ∀ k, imTerm t k = poleTerm (t / 2) k := imTerm_eq_poleTerm t
  constructor
  · -- the limit of the lower bounds
    have hlim : Filter.Tendsto (fun n : ℕ => ∑ k ∈ range n, imTerm t k) Filter.atTop
        (nhds (archSymbolIm t)) := hs.tendsto_sum_nat
    have hlow : Filter.Tendsto
        (fun n : ℕ => Real.arctan (((n : ℝ) + 1 / 4) / (t / 2)) - Real.arctan (1 / (4 * (t / 2))))
        Filter.atTop (nhds (π / 2 - Real.arctan (1 / (4 * (t / 2))))) := by
      refine Filter.Tendsto.sub ?_ tendsto_const_nhds
      have h1 : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1 / 4) / (t / 2)) Filter.atTop Filter.atTop := by
        apply Filter.Tendsto.atTop_div_const hy
        exact Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      exact (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp h1
    refine le_of_tendsto_of_tendsto hlow hlim (Filter.Eventually.of_forall fun n => ?_)
    simp only [heq]
    exact integral_le_sum hy n
  · have h0 : poleTerm (t / 2) 0 = (t / 2) / (1 / 16 + (t / 2) ^ 2) := by
      unfold poleTerm; norm_num
    rw [← h0, ← hs.tsum_eq]
    refine tsum_le_of_sum_range_le (fun k => by rw [heq]; exact poleTerm_nonneg hy.le k) fun n => ?_
    simp only [heq]
    exact sum_le hy n

theorem arctan_le_self' {x : ℝ} (hx : 0 ≤ x) : Real.arctan x ≤ x := by
  rcases hx.lt_or_eq with h | h
  · have ha : 0 < Real.arctan x := Real.arctan_pos.mpr h
    have := Real.lt_tan ha (Real.arctan_lt_pi_div_two x)
    rw [Real.tan_arctan] at this
    exact this.le
  · subst h; simp

end Cvs.WeilForm.Archimedean.SymbolImaginaryTrapped
