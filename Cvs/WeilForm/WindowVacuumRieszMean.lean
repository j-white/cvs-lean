import Mathlib
import Cvs.Prolate.GevreyTailCircle
import Cvs.Route.OneCellLaplaceTransform
import Cvs.WeilForm.MaskedShift.DirichletConvolutionComposition
import Cvs.WeilForm.MaskedShift.MaskedShiftComposition
import Cvs.WeilForm.MaskedShift.MasksCompose
import Cvs.WeilForm.MaskedShift.PrimeAtomRealisation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The window's vacuum: the partition function is the Riesz mean, and the box is the vacuum

On `L²(𝕋)` the constant `1` (the box of the window) has `⟨1, S β 1⟩ = 1 − β`, so `⟨1, Op a 1⟩ = Σ_{n<c} a(n) n^{−1/2}
(1 − log n / log c)`: the vacuum expectation of `DirichletConvolutionComposition`'s operator Euler product is the Riesz mean of the Dirichlet
series. For `a = Λ` it is the prime side of the one-cell function: `log c · ⟨1, Op Λ 1⟩ = primeSide (log c)`.
-/

noncomputable section

open MeasureTheory Real
open scoped NNReal ArithmeticFunction

namespace Cvs.WeilForm.WindowVacuumRieszMean

open Cvs.Operator Cvs.WeilForm.MaskedShift.PrimeAtomRealisation Cvs.WeilForm.MaskedShift.DirichletConvolutionComposition

/-- The vacuum: the constant function `1` on the circle, i.e. the box of the window. -/
def vac : L2 := Lp.const 2 volume (1 : ℝ)

theorem coeFn_vac : (vac : T1 → ℝ) =ᵐ[volume] fun _ => 1 := Lp.coeFn_const 2 volume (1 : ℝ)

/-- The forward mask has measure `1 − β`. -/
theorem integral_indicator_maskFwd {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    ∫ z : T1, (maskFwd β).indicator (fun _ => (1 : ℝ)) z = 1 - β := by
  rw [show (∫ z : T1, (maskFwd β).indicator (fun _ => (1 : ℝ)) z)
      = ∫ x in Set.Ioc (0 : ℝ) 1, (maskFwd β).indicator (fun _ => (1 : ℝ)) ((x : ℝ) : T1) by
    rw [← AddCircle.integral_preimage (1 : ℝ) 0]; simp]
  rw [integral_Ioc_eq_integral_Ioo]
  have h : Set.EqOn (fun x : ℝ => (maskFwd β).indicator (fun _ => (1 : ℝ)) ((x : ℝ) : T1))
      ((Set.Iio (1 - β)).indicator fun _ => (1 : ℝ)) (Set.Ioo 0 1) := by
    intro x hx
    simp only
    have hr := rep_coe x hx.1.le hx.2
    by_cases hx' : x < 1 - β
    · rw [Set.indicator_of_mem (show ((x : ℝ) : T1) ∈ maskFwd β by
        simp only [maskFwd, Set.mem_ofPred_eq, hr]; linarith), Set.indicator_of_mem (Set.mem_Iio.2 hx')]
    · rw [Set.indicator_of_notMem (show ((x : ℝ) : T1) ∉ maskFwd β by
        simp only [maskFwd, Set.mem_ofPred_eq, hr]; linarith), Set.indicator_of_notMem (fun h => hx' (Set.mem_Iio.1 h))]
  rw [setIntegral_congr_fun measurableSet_Ioo h, integral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio, setIntegral_const]
  have hset : Set.Iio (1 - β) ∩ Set.Ioo (0 : ℝ) 1 = Set.Ioo 0 (1 - β) := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioo]; constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
  rw [hset, measureReal_def, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith), smul_eq_mul, mul_one]
  ring

/-- **The vacuum expectation of a walk**: `⟨1, S β 1⟩ = 1 − β`. -/
theorem inner_vac_S {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    inner ℝ vac (S β vac) = 1 - β := by
  rw [L2.inner_def, ← integral_indicator_maskFwd hβ0 hβ1]
  refine integral_congr_ae ?_
  have h2 := (quasi_shift β).ae_eq_comp coeFn_vac
  filter_upwards [coeFn_vac, coeFn_S β vac, h2] with x hx1 hx2 hx3
  rw [hx1, hx2]
  simp only [Function.comp_apply] at hx3
  by_cases hm : x ∈ maskFwd β
  · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm, Function.comp_apply, hx3]; simp
  · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm]; simp

/-- The vacuum expectation of `ρ n`: `n^{−1/2} (1 − log n / log c)` for `1 ≤ n < c`. -/
theorem inner_vac_rho {c n : ℕ} (hc : 1 < c) (hn : 1 ≤ n) (hnc : n < c) :
    inner ℝ vac (rho c n vac) = (n : ℝ) ^ (-(1 / 2 : ℝ)) * (1 - Real.log n / Real.log c) := by
  have hL : 0 < Real.log c := Real.log_pos (by exact_mod_cast hc)
  have h0 : 0 ≤ Real.log n / Real.log c :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hn)) hL.le
  have h1 : Real.log n / Real.log c ≤ 1 := by
    rw [div_le_one hL]; exact Real.log_le_log (by exact_mod_cast hn) (by exact_mod_cast hnc.le)
  have hrot : ((rot c n : ℝ≥0) : ℝ) = Real.log n / Real.log c := Real.coe_toNNReal _ h0
  simp only [rho, smul_apply, inner_smul_right, Snn, hrot]
  rw [inner_vac_S h0 h1]

/-- **The vacuum expectation of a Dirichlet operator is the Riesz mean of its series**. -/
theorem inner_vac_Op {c : ℕ} (hc : 1 < c) (a : ArithmeticFunction ℝ) :
    inner ℝ vac (Op c a vac)
      = ∑ n ∈ Finset.range c, a n * ((n : ℝ) ^ (-(1 / 2 : ℝ)) * (1 - Real.log n / Real.log c)) := by
  unfold Op
  rw [sum_apply, inner_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [smul_apply, inner_smul_right]
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
  · rw [inner_vac_rho hc hpos (Finset.mem_range.1 hn)]

/-- **The prime side of the one-cell function is the vacuum expectation of the prime operator**:
`primeSide (log c) = log c · ⟨1, Op Λ 1⟩`. -/
theorem primeSide_eq_vac {c : ℕ} (hc : 1 < c) :
    Cvs.Route.OneCellLaplaceTransform.primeSide (Real.log c) = Real.log c * inner ℝ vac (Op c Λ vac) := by
  have hL : 0 < Real.log c := Real.log_pos (by exact_mod_cast hc)
  rw [inner_vac_Op hc, Finset.mul_sum, Cvs.Route.OneCellLaplaceTransform.primeSide]
  rw [tsum_eq_sum (s := Finset.range c)]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp
    have hnc := Finset.mem_range.1 hn
    have hle : Real.log n ≤ Real.log c :=
      Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hnc.le)
    rw [max_eq_left (by linarith), Real.rpow_neg (Nat.cast_nonneg _), ← Real.sqrt_eq_rpow]
    field_simp
  · intro n hn
    have hcn : c ≤ n := not_lt.1 (fun h => hn (Finset.mem_range.2 h))
    have : Real.log c ≤ Real.log n := Real.log_le_log (by positivity) (by exact_mod_cast hcn)
    rw [max_eq_right (by linarith), mul_zero]

end Cvs.WeilForm.WindowVacuumRieszMean
