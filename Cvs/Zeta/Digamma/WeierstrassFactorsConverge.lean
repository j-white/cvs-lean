import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

open Complex Set Filter Topology

namespace Cvs.Digamma

/-!
# The Weierstrass factors converge locally uniformly
-/

/-- The Weierstrass factor at index `n`, minus one. -/
noncomputable def wTerm (n : ℕ) (z : ℂ) : ℂ :=
  (1 + z / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1))) - 1

/-- The cancellation that makes the product converge: `(1+w)e^{-w}` differs from
`1` by `O(‖w‖²)`, not `O(‖w‖)`. -/
theorem norm_one_add_mul_exp_neg_sub_one_le {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖(1 + w) * Complex.exp (-w) - 1‖ ≤ 3 * ‖w‖ ^ 2 := by
  have key : (1 + w) * Complex.exp (-w) - 1
      = (1 + w) * (Complex.exp (-w) - 1 - (-w)) - w ^ 2 := by ring
  have h1 : ‖Complex.exp (-w) - 1 - (-w)‖ ≤ ‖w‖ ^ 2 := by
    have := Complex.norm_exp_sub_one_sub_id_le (x := -w) (by simpa using hw)
    simpa using this
  have h2 : ‖1 + w‖ ≤ 2 := by
    have := norm_add_le (1 : ℂ) w
    simp only [norm_one] at this
    linarith
  calc ‖(1 + w) * Complex.exp (-w) - 1‖
      = ‖(1 + w) * (Complex.exp (-w) - 1 - (-w)) - w ^ 2‖ := by rw [key]
    _ ≤ ‖(1 + w) * (Complex.exp (-w) - 1 - (-w))‖ + ‖w ^ 2‖ := norm_sub_le _ _
    _ = ‖1 + w‖ * ‖Complex.exp (-w) - 1 - (-w)‖ + ‖w‖ ^ 2 := by rw [norm_mul, norm_pow]
    _ ≤ 2 * ‖w‖ ^ 2 + ‖w‖ ^ 2 :=
        add_le_add (mul_le_mul h2 h1 (norm_nonneg _) (by norm_num)) le_rfl
    _ = 3 * ‖w‖ ^ 2 := by ring

/-- `‖(n:ℂ) + 1‖` is `n + 1`. -/
theorem norm_natCast_add_one (n : ℕ) : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
  rw [show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
  push_cast; ring

/-- The uniform `O(n^{-2})` bound on a ball of radius `M`, valid once `n + 1 ≥ M`. -/
theorem norm_wTerm_le {M : ℝ} {n : ℕ} {z : ℂ} (hz : ‖z‖ ≤ M)
    (hn : M ≤ (n : ℝ) + 1) :
    ‖wTerm n z‖ ≤ 3 * M ^ 2 / ((n : ℝ) + 1) ^ 2 := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hnw : ‖z / ((n : ℂ) + 1)‖ = ‖z‖ / ((n : ℝ) + 1) := by
    rw [norm_div, norm_natCast_add_one]
  have hle1 : ‖z / ((n : ℂ) + 1)‖ ≤ 1 := by
    rw [hnw, div_le_one hpos]
    linarith
  have := norm_one_add_mul_exp_neg_sub_one_le hle1
  rw [← wTerm] at this
  refine this.trans ?_
  rw [hnw, div_pow, ← mul_div_assoc]
  gcongr

/-- `∑ C/(n+1)²` converges. Mathlib's `summable_pow_div_add` states exactly this
but does not elaborate here, so it is rebuilt from the `p`-series. -/
theorem summable_const_div_sq (C : ℝ) : Summable fun n : ℕ => C / ((n : ℝ) + 1) ^ 2 := by
  have h2 : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ)) ^ 2) := by
    rw [Real.summable_one_div_nat_pow]; norm_num
  have h3 : Summable (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ)) : ℝ) ^ 2) :=
    (summable_nat_add_iff 1).mpr h2
  have h4 : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2) := by
    refine h3.congr fun n => ?_
    push_cast
    ring
  refine (h4.mul_left C).congr fun n => ?_
  ring

/-- Uniform convergence on any compact set. -/
theorem hasProdUniformlyOn_wTerm {Z : Set ℂ} (hZ : IsCompact Z) :
    HasProdUniformlyOn (fun n : ℕ => fun z : ℂ => 1 + wTerm n z)
      (fun z => ∏' n : ℕ, (1 + wTerm n z)) Z := by
  obtain ⟨s, hs⟩ := bddAbove_def.mp (hZ.bddAbove_image continuous_norm.continuousOn)
  obtain ⟨M, hM0, hzM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ Z, ‖z‖ ≤ M :=
    ⟨max s 0, le_max_right _ _, fun z hz => (hs _ ⟨z, hz, rfl⟩).trans (le_max_left _ _)⟩
  have hbd : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Z,
      ‖wTerm n z‖ ≤ 3 * M ^ 2 / ((n : ℝ) + 1) ^ 2 := by
    filter_upwards [eventually_ge_atTop ⌈M⌉₊] with n hn z hzZ
    have hMn : M ≤ (n : ℝ) + 1 := by
      have h1 : M ≤ (⌈M⌉₊ : ℝ) := Nat.le_ceil M
      have h2 : ((⌈M⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
      linarith
    exact norm_wTerm_le (hzM z hzZ) hMn
  have hcts : ∀ n : ℕ, ContinuousOn (fun z : ℂ => wTerm n z) Z := by
    intro n
    simp only [wTerm]
    fun_prop
  exact Summable.hasProdUniformlyOn_nat_one_add hZ (summable_const_div_sq (3 * M ^ 2)) hbd hcts

/-- **The Weierstrass factors converge locally uniformly on all of `ℂ`.** This is
the input Mathlib's `logDeriv_tendsto` needs and does not have for `Γ`. -/
theorem hasProdLocallyUniformlyOn_wTerm :
    HasProdLocallyUniformlyOn (fun n : ℕ => fun z : ℂ => 1 + wTerm n z)
      (fun z => ∏' n : ℕ, (1 + wTerm n z)) univ := by
  refine hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ ?_
  intro S _ hSC
  exact hasProdUniformlyOn_wTerm hSC

/-- The terms are absolutely summable at each point. -/
theorem summable_norm_wTerm (z : ℂ) : Summable fun n : ℕ => ‖wTerm n z‖ := by
  refine (summable_const_div_sq (3 * ‖z‖ ^ 2)).of_norm_bounded_eventually ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop ⌈‖z‖⌉₊] with n hn
  have hMn : ‖z‖ ≤ (n : ℝ) + 1 := by
    have h1 : ‖z‖ ≤ (⌈‖z‖⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈‖z‖⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact norm_wTerm_le le_rfl hMn

/-- The Weierstrass product converges at every point of `ℂ`. -/
theorem multipliable_wTerm (z : ℂ) : Multipliable fun n : ℕ => (1 + wTerm n z) :=
  multipliable_one_add_of_summable (summable_norm_wTerm z)

end Cvs.Digamma
