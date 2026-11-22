import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.L2a.ProlateFamilySpine
import Cvs.L2a.WindowFormDeepSpan
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.EvenLevelIndexLemma
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RegularSolutionEdge

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A quarter of the prolate family at `c = 2πx` is deep

Sturm comparison of `regSol (sqC c) (c² − 5c)` with `sin(cξ/2)/√(1 − ξ²)` on `[0, 1/2]` gives `⌊c/4π⌋` zeros, hence
`⌊c/4π⌋` even levels below `c² − 5c`. At `c = 2πx` the indices `j < (⌊x/2⌋ + 1)/2` are deep, so `1, 2 ∈ deepSet x`
and the levels of index `2` and `4` named by `ProlateFamilySpine`'s spine instance exist once `c0 ≤ 2πx`.
-/

noncomputable section

open Real Set Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.RegularSolutionEdge Cvs.Prolate.EdgeCentreSign Cvs.Prolate.EvenLevelIndexLemma Cvs.Prolate.EvenRungsByIndex Cvs.Approximant.DeepIndexSpineSpan

namespace Cvs.L2a.ProlateFamilyQuarterDeep

open Cvs.L2a.WindowFormDeepSpan (c0 Hx)

/-! ### The sine comparison function -/

/-- The comparison function `z = sin(cξ/2)/√(1 − ξ²)`. -/
def zS (c ξ : ℝ) : ℝ := sin (c / 2 * ξ) / √(1 - ξ ^ 2)

/-- The flux `(ξ² − 1)z'` of the comparison function. -/
def fS (c ξ : ℝ) : ℝ := -(c / 2 * √(1 - ξ ^ 2) * cos (c / 2 * ξ) + ξ * sin (c / 2 * ξ) / √(1 - ξ ^ 2))

/-- The comparison potential `R = 1 + ξ²/(1 − ξ²) − (c²/4)(1 − ξ²)`: `((ξ² − 1)z')' = −R z`. -/
def rS (c ξ : ℝ) : ℝ := 1 + ξ ^ 2 / (1 - ξ ^ 2) - c ^ 2 / 4 * (1 - ξ ^ 2)

theorem hasDerivAt_sqrt_one_sub_sq {ξ : ℝ} (h1 : -1 < ξ) (h2 : ξ < 1) :
    HasDerivAt (fun y => √(1 - y ^ 2)) (-ξ / √(1 - ξ ^ 2)) ξ := by
  have hp : 0 < 1 - ξ ^ 2 := by nlinarith
  have h := (((hasDerivAt_id ξ).pow 2).const_sub 1).sqrt hp.ne'
  refine h.congr_deriv ?_
  have hs : √(1 - ξ ^ 2) ≠ 0 := (Real.sqrt_pos.2 hp).ne'
  simp only [id, Pi.pow_apply, Nat.cast_ofNat]
  field_simp
  ring

/-- `z' = fS/pP`. -/
theorem hasDerivAt_zS (c : ℝ) {ξ : ℝ} (h1 : -1 < ξ) (h2 : ξ < 1) :
    HasDerivAt (zS c) (fS c ξ / pP ξ) ξ := by
  have hp : 0 < 1 - ξ ^ 2 := by nlinarith
  have hS := hasDerivAt_sqrt_one_sub_sq h1 h2
  have hS0 : √(1 - ξ ^ 2) ≠ 0 := (Real.sqrt_pos.2 hp).ne'
  have hθ : HasDerivAt (fun y => c / 2 * y) (c / 2) ξ := by
    simpa using (hasDerivAt_id ξ).const_mul (c / 2)
  have d := hθ.sin.div hS hS0
  show HasDerivAt (fun y => sin (c / 2 * y) / √(1 - y ^ 2)) _ ξ
  refine d.congr_deriv ?_
  have hm2 : 1 - ξ ^ 2 = √(1 - ξ ^ 2) ^ 2 := (sq_sqrt hp.le).symm
  rw [show pP ξ = -(1 - ξ ^ 2) by unfold pP; ring]
  simp only [fS]
  generalize √(1 - ξ ^ 2) = S at hS0 hm2 ⊢
  rw [hm2]
  field_simp
  ring

/-- `(fS)' = −rS · zS`. -/
theorem hasDerivAt_fS (c : ℝ) {ξ : ℝ} (h1 : -1 < ξ) (h2 : ξ < 1) :
    HasDerivAt (fS c) (-(rS c ξ * zS c ξ)) ξ := by
  have hp : 0 < 1 - ξ ^ 2 := by nlinarith
  have hS := hasDerivAt_sqrt_one_sub_sq h1 h2
  have hS0 : √(1 - ξ ^ 2) ≠ 0 := (Real.sqrt_pos.2 hp).ne'
  have hθ : HasDerivAt (fun y => c / 2 * y) (c / 2) ξ := by
    simpa using (hasDerivAt_id ξ).const_mul (c / 2)
  have d := (((hS.const_mul (c / 2)).mul hθ.cos).add (((hasDerivAt_id ξ).mul hθ.sin).div hS hS0)).neg
  show HasDerivAt (fun y => -(c / 2 * √(1 - y ^ 2) * cos (c / 2 * y) + y * sin (c / 2 * y) / √(1 - y ^ 2))) _ ξ
  refine d.congr_deriv ?_
  have hm2 : 1 - ξ ^ 2 = √(1 - ξ ^ 2) ^ 2 := (sq_sqrt hp.le).symm
  simp only [rS, zS, id, Pi.mul_apply]
  generalize √(1 - ξ ^ 2) = S at hS0 hm2 ⊢
  rw [hm2]
  field_simp
  ring

/-- **The comparison inequality on `[0, 1/2]`**: `c²ξ² − (c² − 5c) < rS` for `c ≥ 10`. -/
theorem sub_lt_rS {c ξ : ℝ} (hc : 10 ≤ c) (h0 : 0 ≤ ξ) (h1 : ξ ≤ 1 / 2) :
    c ^ 2 * ξ ^ 2 - (c ^ 2 - 5 * c) < rS c ξ := by
  have hp : 3 / 4 ≤ 1 - ξ ^ 2 := by nlinarith
  have hq : 0 ≤ ξ ^ 2 / (1 - ξ ^ 2) := div_nonneg (sq_nonneg ξ) (by linarith)
  have key : c ^ 2 * ξ ^ 2 - (c ^ 2 - 5 * c) + c ^ 2 / 4 * (1 - ξ ^ 2) = 5 * c - 3 / 4 * c ^ 2 * (1 - ξ ^ 2) := by
    ring
  have hc2 : 9 / 16 * c ^ 2 ≤ 3 / 4 * c ^ 2 * (1 - ξ ^ 2) := by nlinarith
  unfold rS
  nlinarith

/-! ### Zeros of `regSol` at `c² − 5c` -/

/-- **`⌊c/4π⌋` zeros at `χ = c² − 5c`**: one between consecutive zeros `2πk/c` of `sin(cξ/2)` in `[0, 1/2]`. -/
theorem hasZeros_five_c {c : ℝ} (hc : 10 ≤ c) : Cvs.Prolate.EvenLevelIndexLemma.HasZeros (sqC c) (c ^ 2 - 5 * c) ⌊c / (4 * π)⌋₊ := by
  have hc0 : 0 < c := by linarith
  set K := ⌊c / (4 * π)⌋₊ with hKdef
  have hK : (K : ℝ) ≤ c / (4 * π) := Nat.floor_le (by positivity)
  set ζ : ℕ → ℝ := fun k => 2 * π * k / c with hζdef
  have hζ0 : ∀ k, 0 ≤ ζ k := fun k => by simp only [hζdef]; positivity
  have hζK : ∀ k ≤ K, ζ k ≤ 1 / 2 := by
    intro k hk
    have hk' : (k : ℝ) ≤ c / (4 * π) := le_trans (by exact_mod_cast hk) hK
    simp only [hζdef]
    rw [div_le_iff₀ hc0]
    have : 2 * π * (k : ℝ) ≤ 2 * π * (c / (4 * π)) := mul_le_mul_of_nonneg_left hk' (by positivity)
    have e : 2 * π * (c / (4 * π)) = 1 / 2 * c := by field_simp; ring
    linarith
  have hζlt : ∀ k, ζ k < ζ (k + 1) := fun k => by
    simp only [hζdef]
    apply div_lt_div_of_pos_right _ hc0
    push_cast
    nlinarith [Real.pi_pos]
  have hζθ : ∀ k, c / 2 * ζ k = (k : ℝ) * π := fun k => by
    simp only [hζdef]; field_simp
  have hzζ : ∀ k, zS c (ζ k) = 0 := fun k => by
    simp only [zS, hζθ, Real.sin_nat_mul_pi, zero_div]
  have hz : ∀ i : Fin K, ∃ x ∈ Ioo (ζ i) (ζ (i + 1)), regSol (sqC c) (c ^ 2 - 5 * c) x = 0 := by
    intro i
    have hα0 := hζ0 i
    have hβ := hζK (i + 1) (by omega)
    have hlo : ∀ ξ ∈ Icc (ζ i) (ζ (i + 1)), -1 < ξ := fun ξ hξ => by linarith [hξ.1]
    have hhi : ∀ ξ ∈ Icc (ζ i) (ζ (i + 1)), ξ < 1 := fun ξ hξ => by linarith [hξ.2]
    refine exists_zero_of_comparison (Q := fun ξ => sqC c ξ) (R := rS c)
      (U := regU (sqC c) (c ^ 2 - 5 * c)) (χ := c ^ 2 - 5 * c) (z := zS c) (Z := fS c) (by linarith)
      (hζlt i) (by linarith) (fun ξ hξ => ?_) (fun ξ hξ => ?_) (fun ξ hξ => ?_) (fun ξ hξ => ?_) (hzζ i)
      (by exact_mod_cast hzζ (i + 1)) (fun ξ hξ => ?_) (fun ξ hξ => ?_)
    · have hp : pP ξ ≠ 0 := by
        have := hlo ξ hξ; have := hhi ξ hξ; unfold pP; nlinarith
      have h := hasDerivAt_regSol (sqC c) (c ^ 2 - 5 * c) (hlo ξ hξ)
      rwa [← pP_mul_regV (sqC c) (c ^ 2 - 5 * c) (hlo ξ hξ), mul_div_cancel_left₀ _ hp]
    · exact hasDerivAt_regU (sqC c) (c ^ 2 - 5 * c) (hlo ξ hξ)
    · exact hasDerivAt_zS c (hlo ξ hξ) (hhi ξ hξ)
    · exact hasDerivAt_fS c (hlo ξ hξ) (hhi ξ hξ)
    · have hp : 0 < 1 - ξ ^ 2 := by
        have := hlo ξ (Ioo_subset_Icc_self hξ); have := hhi ξ (Ioo_subset_Icc_self hξ); nlinarith
      refine div_ne_zero (fun hs => ?_) (Real.sqrt_pos.2 hp).ne'
      obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hs
      have hl1 : c / 2 * ζ i < c / 2 * ξ := mul_lt_mul_of_pos_left hξ.1 (by positivity)
      have hl2 : c / 2 * ξ < c / 2 * ζ (i + 1) := mul_lt_mul_of_pos_left hξ.2 (by positivity)
      rw [hζθ, ← hn] at hl1
      rw [hζθ, ← hn] at hl2
      have h1 : ((i : ℕ) : ℝ) < n := lt_of_mul_lt_mul_right (by simpa using hl1) pi_pos.le
      have h2 : (n : ℝ) < ((i : ℕ) : ℝ) + 1 := by
        have : (n : ℝ) * π < (((i : ℕ) : ℝ) + 1) * π := by simpa using hl2
        exact lt_of_mul_lt_mul_right this pi_pos.le
      have h1' : ((i : ℕ) : ℤ) < n := by exact_mod_cast h1
      have h2' : n < ((i : ℕ) : ℤ) + 1 := by exact_mod_cast h2
      omega
    · exact sub_lt_rS hc (by linarith [hξ.1]) (by linarith [hξ.2])
  choose x hxI hx0 using hz
  refine ⟨x, fun i j hij => ?_, fun i => ⟨?_, ?_⟩, hx0⟩
  · have hij' : (i : ℕ) + 1 ≤ j := hij
    have h1 : ζ ((i : ℕ) + 1) ≤ ζ j := by
      simp only [hζdef]
      apply div_le_div_of_nonneg_right _ hc0.le
      have : (((i : ℕ) + 1 : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hij'
      push_cast at this ⊢
      nlinarith [Real.pi_pos]
    linarith [(hxI i).2, (hxI j).1]
  · linarith [(hxI i).1, hζ0 i]
  · linarith [(hxI i).2, hζK ((i : ℕ) + 1) (by omega)]

/-- **`⌊c/4π⌋` even levels below `c² − 5c`** for `c ≥ 10`. -/
theorem floor_le_count_five_c {c : ℝ} (hc : 10 ≤ c) :
    ⌊c / (4 * π)⌋₊ ≤ (evenSpec (sqC c) ∩ Iio (c ^ 2 - 5 * c)).ncard :=
  le_ncard_evenSpec (hasZeros_five_c hc)

/-! ### Depth at `c = 2πx` -/

/-- `⌊2πx/4π⌋ = ⌊x/2⌋`. -/
theorem floor_two_pi_x (x : ℕ) : ⌊2 * π * x / (4 * π)⌋₊ = x / 2 := by
  have e : 2 * π * (x : ℝ) / (4 * π) = (x : ℝ) / (2 : ℕ) := by
    have := Real.pi_pos.ne'
    push_cast
    field_simp
    ring
  rw [e, Nat.floor_div_natCast, Nat.floor_natCast]

/-- **A quarter of the family is deep**: at `c = 2πx ≥ 80` every `j < (⌊x/2⌋ + 1)/2` lies in `deepSet x`. -/
theorem range_quarter_subset_deepSet {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    Finset.range ((x / 2 + 1) / 2) ⊆ deepSet x := by
  intro j hj
  have hj' : j < (x / 2 + 1) / 2 := Finset.mem_range.mp hj
  have hcount := floor_le_count_five_c (c := 2 * π * x) (by linarith)
  rw [floor_two_pi_x] at hcount
  exact mem_deepSet_of_lt_ncard (by omega) (by omega)

/-- `c0 ≤ 2πx` forces `x ≥ 10`. -/
theorem ten_le_of_c0 {x : ℕ} (hx : c0 ≤ 2 * π * x) : 10 ≤ x := by
  have hc : (10 : ℝ) ^ 16 ≤ 2 * π * x := c0_ge.trans hx
  have h8 : 2 * π * (x : ℝ) ≤ 8 * x := by
    have := Real.pi_lt_four
    nlinarith [(Nat.cast_nonneg x : (0 : ℝ) ≤ x)]
  have : (10 : ℝ) ≤ x := by nlinarith
  exact_mod_cast this

/-- **`1` and `2` are deep** once `c0 ≤ 2πx`. -/
theorem one_two_mem_deepSet {x : ℕ} (hx : c0 ≤ 2 * π * x) : 1 ∈ deepSet x ∧ 2 ∈ deepSet x := by
  have h10 := ten_le_of_c0 hx
  have h80 : (80 : ℝ) ≤ 2 * π * x := by
    have hc : (10 : ℝ) ^ 16 ≤ 2 * π * x := c0_ge.trans hx
    linarith
  have hsub := range_quarter_subset_deepSet h80
  have h3 : 3 ≤ (x / 2 + 1) / 2 := by omega
  exact ⟨hsub (Finset.mem_range.mpr (by omega)), hsub (Finset.mem_range.mpr (by omega))⟩

/-- **The spine instance is not vacuous**: `D₀` has a member, the levels of index `2` and `4` exist, `λ₈ < 1` and
`λ₀ > 0` at `c = 2πx ≥ c0`. -/
theorem L2a_spine_instance_nonvacuous {x : ℕ} (hx : c0 ≤ 2 * π * x) :
    Nonempty ((deepSet x).filter (2 ≤ ·)) ∧ IsLevelIdx (2 * π * x) 4 (lev (2 * π * x) 4) ∧
      IsLevelIdx (2 * π * x) 2 (lev (2 * π * x) 2) ∧ 0 < 1 - lamR (2 * π * x) 4 ∧ 0 < lamR (2 * π * x) 0 := by
  obtain ⟨h1, h2⟩ := one_two_mem_deepSet hx
  have hc0 : 0 < 2 * π * (x : ℝ) := lt_of_lt_of_le (by norm_num) (c0_ge.trans hx)
  have e4 : ∃ χ, IsLevelIdx (2 * π * x) 4 χ := (mem_deepSet.mp h2).2.1
  have e2 : ∃ χ, IsLevelIdx (2 * π * x) 2 χ := (mem_deepSet.mp h1).2.1
  refine ⟨⟨⟨2, Finset.mem_filter.mpr ⟨h2, le_rfl⟩⟩⟩, lev_spec e4, lev_spec e2, ?_, lamR_zero_pos hc0⟩
  linarith [lamR_lt_one hc0 e4 (by norm_num)]

/-- **Both spine factors are positive** at `c = 2πx ≥ c0`: the `D₀` factor with `1 − λ₈` and the `R_D` factor with
`1 − λ₄`. -/
theorem spine_factors_pos {x : ℕ} (hx : c0 ≤ 2 * π * x) :
    0 < π / (8 * (2 * π * x) * Hx (2 * π * x) * (1 + 2 * (2 * π * x) / (π * lamR (2 * π * x) 0)))
        * (1 - lamR (2 * π * x) 4) ∧
      0 < π / (8 * (2 * π * x) * Hx (2 * π * x) * (1 + 2 * (2 * π * x) / (π * lamR (2 * π * x) 0)))
        * (1 - lamR (2 * π * x) 2) := by
  obtain ⟨h1, h2⟩ := one_two_mem_deepSet hx
  exact ⟨Cvs.L2a.ProlateFamilySpine.spine_factor_pos x hx (mem_deepSet.mp h2).2.1,
    Cvs.L2a.ProlateFamilySpine.spine_factor_pos_RD x hx (mem_deepSet.mp h1).2.1⟩
