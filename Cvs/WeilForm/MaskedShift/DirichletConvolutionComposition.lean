import Mathlib
import Cvs.WeilForm.MaskedShift.CoherentFamilyDefs
import Cvs.WeilForm.MaskedShift.MaskedShiftComposition
import Cvs.WeilForm.MaskedShift.MaskedShiftNilpotent
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
# The multiplicative representation of the window, and Dirichlet convolution as composition

At scale `c > 1`, `ρ n = n^{−1/2} · S(log n / log c)` is a representation of `(ℕ_{≥1}, ×)` on `L²(𝕋)` that vanishes
from `n = c` on. So `Op a = Σ_{n<c} a(n) ρ(n)` turns Dirichlet convolution into composition, exactly:
`Op a * Op b = Op (a * b)`, with `Op Λ = Op log * Op μ` and `Op μ * Op ζ = 1`.
-/

noncomputable section

set_option maxSynthPendingDepth 3

open MeasureTheory Real
open scoped NNReal ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Cvs.WeilForm.MaskedShift.DirichletConvolutionComposition

open Cvs.Operator Cvs.WeilForm.MaskedShift.PrimeAtomRealisation ArithmeticFunction

/-- The masked shift by zero is the identity. -/
theorem S_zero : S 0 = 1 := by
  refine ContinuousLinearMap.ext fun f => ?_
  refine Lp.ext ?_
  filter_upwards [coeFn_S 0 f] with x hx
  rw [hx]
  have hm : x ∈ maskFwd 0 := by
    simp only [maskFwd, Set.mem_ofPred_eq, add_zero]; exact rep_lt_one x
  simp [Set.indicator_of_mem hm]

/-- The rotation number is additive on positive integers. -/
theorem rot_mul {c m n : ℕ} (hc : 1 < c) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    rot c (m * n) = rot c m + rot c n := by
  have hL : 0 < Real.log c := Real.log_pos (by exact_mod_cast hc)
  have h1 : 0 ≤ Real.log m / Real.log c :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hm)) hL.le
  have h2 : 0 ≤ Real.log n / Real.log c :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hn)) hL.le
  unfold rot
  rw [← Real.toNNReal_add h1 h2, Nat.cast_mul,
    Real.log_mul (by positivity) (by positivity), add_div]

/-- The window's representation: `ρ n = n^{−1/2} · S(log n / log c)`. -/
def rho (c n : ℕ) : L2 →L[ℝ] L2 := ((n : ℝ) ^ (-(1 / 2 : ℝ))) • Snn (rot c n)

/-- `ρ` is multiplicative on positive integers. -/
theorem rho_mul {c m n : ℕ} (hc : 1 < c) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    rho c (m * n) = rho c m * rho c n := by
  unfold rho
  rw [rot_mul hc hm hn, ← isCoherent_S.compose, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _), smul_mul_smul_comm]
  rfl

/-- `ρ 1 = 1`. -/
theorem rho_one (c : ℕ) : rho c 1 = 1 := by
  simp [rho, rot, Snn, S_zero]

/-- `ρ` vanishes from `n = c` on: the hop leaves the window. -/
theorem rho_eq_zero {c n : ℕ} (hc : 1 < c) (hn : c ≤ n) : rho c n = 0 := by
  have hL : 0 < Real.log c := Real.log_pos (by exact_mod_cast hc)
  have hge : 1 ≤ Real.log n / Real.log c := by
    rw [le_div_iff₀ hL, one_mul]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hn)
  have hrot : ((rot c n : ℝ≥0) : ℝ) = Real.log n / Real.log c :=
    Real.coe_toNNReal _ (by linarith)
  simp only [rho, Snn, hrot, S_eq_zero hge, smul_zero]

/-- The Dirichlet operator of an arithmetic function on the window. -/
def Op (c : ℕ) (a : ArithmeticFunction ℝ) : L2 →L[ℝ] L2 :=
  ∑ n ∈ Finset.range c, a n • rho c n

/-- **Dirichlet convolution is composition on the window**: `Op a * Op b = Op (a * b)`. -/
theorem Op_mul {c : ℕ} (hc : 1 < c) (a b : ArithmeticFunction ℝ) :
    Op c a * Op c b = Op c (a * b) := by
  unfold Op
  rw [Finset.sum_mul_sum]
  simp_rw [smul_mul_smul_comm]
  rw [← Finset.sum_product']
  simp_rw [ArithmeticFunction.mul_apply, Finset.sum_smul]
  rw [Finset.sum_sigma']
  symm
  refine Finset.sum_bij_ne_zero (fun x _ _ => x.2) ?_ ?_ ?_ ?_
  · rintro ⟨k, i, j⟩ hx _
    simp only [Finset.mem_sigma, Finset.mem_range, Nat.mem_divisorsAntidiagonal] at hx
    obtain ⟨hk, hij, hk0⟩ := hx
    simp only [Finset.mem_product, Finset.mem_range]
    have hi : i ≠ 0 := by rintro rfl; simp at hij; exact hk0 hij.symm
    have hj : j ≠ 0 := by rintro rfl; simp at hij; exact hk0 hij.symm
    constructor
    · calc i ≤ i * j := Nat.le_mul_of_pos_right i (Nat.pos_of_ne_zero hj)
        _ < c := by rw [hij]; exact hk
    · calc j ≤ i * j := Nat.le_mul_of_pos_left j (Nat.pos_of_ne_zero hi)
        _ < c := by rw [hij]; exact hk
  · rintro ⟨k, i, j⟩ hx _ ⟨k', i', j'⟩ hx' _ h
    simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal] at hx hx'
    simp only at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    have : k = k' := by rw [← hx.2.1, ← hx'.2.1]
    subst this; rfl
  · rintro ⟨i, j⟩ hmem hne
    have hi : i ≠ 0 := by rintro rfl; simp at hne
    have hj : j ≠ 0 := by rintro rfl; simp at hne
    have hij : i * j < c := by
      by_contra h
      apply hne
      rw [← rho_mul hc (Nat.one_le_iff_ne_zero.2 hi) (Nat.one_le_iff_ne_zero.2 hj),
        rho_eq_zero hc (not_lt.1 h), smul_zero]
    refine ⟨⟨i * j, i, j⟩, ?_, ?_, rfl⟩
    · simp only [Finset.mem_sigma, Finset.mem_range, Nat.mem_divisorsAntidiagonal]
      refine ⟨hij, ?_⟩
      simp [hi, hj]
    · simp only at hne ⊢
      rw [rho_mul hc (Nat.one_le_iff_ne_zero.2 hi) (Nat.one_le_iff_ne_zero.2 hj)]
      exact hne
  · rintro ⟨k, i, j⟩ hx _
    simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal] at hx
    obtain ⟨_, hij, hk0⟩ := hx
    have hi : i ≠ 0 := by rintro rfl; simp at hij; exact hk0 hij.symm
    have hj : j ≠ 0 := by rintro rfl; simp at hij; exact hk0 hij.symm
    simp only
    rw [← hij, rho_mul hc (Nat.one_le_iff_ne_zero.2 hi) (Nat.one_le_iff_ne_zero.2 hj)]

/-- `Op 1 = 1`. -/
theorem Op_one {c : ℕ} (hc : 1 < c) : Op c 1 = 1 := by
  unfold Op
  rw [Finset.sum_eq_single 1]
  · simp [rho_one]
  · intro n _ hn; simp [one_apply_ne hn]
  · intro h; exact absurd (Finset.mem_range.2 hc) h

/-- **Möbius inversion on the window**: `Op μ * Op ζ = 1`, so `Op ζ` is invertible. -/
theorem Op_moebius_mul_zeta {c : ℕ} (hc : 1 < c) :
    Op c (μ : ArithmeticFunction ℝ) * Op c (ζ : ArithmeticFunction ℝ) = 1 := by
  rw [Op_mul hc, ← Op_one hc]
  congr 1
  simp

/-- **The prime operator factors**: `Op Λ = Op log * Op μ`. -/
theorem Op_vonMangoldt {c : ℕ} (hc : 1 < c) :
    Op c ArithmeticFunction.vonMangoldt = Op c log * Op c (μ : ArithmeticFunction ℝ) := by
  rw [Op_mul hc, log_mul_moebius_eq_vonMangoldt]

end Cvs.WeilForm.MaskedShift.DirichletConvolutionComposition
