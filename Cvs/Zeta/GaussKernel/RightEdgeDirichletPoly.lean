import Mathlib
import Cvs.PNT.ResidueCalcOnRectangles
import Cvs.Zeta.GaussKernel.SmoothedGaussMellin
import Cvs.Zeta.GaussKernel.SmoothedRectangleBounds
import Cvs.Zeta.MollifiedDetectorSeries
import Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Right-edge Dirichlet polynomial approximation and 2D strip `L²` bound

Truncating `Cvs.Zeta.GaussKernel.SmoothedGaussMellin.rightEdge_eq_tsum` at `N = ⌊T^{1 + c²/8}⌋₊` and applying `Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint.mean_value_bound_vertical` with `Cvs.Zeta.MollifiedDetectorSeries`
and `Cvs.Zeta.GaussKernel.SmoothedRectangleBounds` yields `∫_{[1/2+c, 3/2] ×ℂ [T-1, 2T+1]} ‖mollifiedDetector ⌊T^c⌋₊ z‖² ≤ C_A T^{1 - c²/2}`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology Finset Asymptotics
open scoped Interval
open Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint (dirichletPolyC truncMoebiusSum mean_value_bound_vertical intervalIntegrable_normSq_dirichletPolyC sq_add_le_two_mul)
open Cvs.Zeta.MollifiedDetectorSeries (mollifiedDetector differentiableOn_mollifiedDetector norm_truncMoebiusSum_le_self divSqConst divSqConst_nonneg sum_truncMoebiusSum_sq_tail_le)
open Cvs.Zeta.GaussKernel.SmoothedGaussMellin (gaussMellin norm_gaussMellin_le norm_gaussMellin_le_main norm_gaussMellin_tail_le rightEdge_eq_tsum)
open Cvs.Zeta.GaussKernel.SmoothedRectangleBounds (one_lt_log_of_ge_32 botEdge topEdge rightEdge leftEdge norm_mollifiedDetector_sq_le_edges norm_horizEdges_sq_le leftMajorant continuous_leftMajorant norm_leftEdge_sq_le_leftMajorant integral_leftMajorant_le)

namespace Cvs.Zeta.GaussKernel.RightEdgeDirichletPoly

/-! ### Right-edge truncation at `N = ⌊T^{1 + ε}⌋₊` -/

/-- Absolute constant `∑'_{n : ℕ} n^{-2}`. -/
def zetaTwoConst : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-(2 : ℝ))

/-- Dirichlet coefficients of `rightEdge X T α` supported on `n > X`. -/
def rightCoeff (X : ℕ) (T α : ℝ) (n : ℕ) : ℂ :=
  if X < n then (truncMoebiusSum X n : ℂ) * gaussMellin (3 - α) (Real.log T) (T / n) else 0

/-- **Pointwise right-edge approximation** at `N = ⌊T^{1 + ε}⌋₊`:
for `0 < ε ≤ 1/4`, `X ≥ 1`, `α ∈ [1/2, 3/2]`, and `T ≥ max 32 (exp (64 / ε²))`,
`‖rightEdge X T α t - dirichletPolyC (rightCoeff X T α) ⌊T^{1+ε}⌋₊ (α + it)‖ ≤ zetaTwoConst · T^{-3}`. -/
theorem norm_rightEdge_sub_dirichletPolyC_le {X : ℕ} (hX : 1 ≤ X) {T α t ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 4) (hα : α ∈ Icc (1 / 2 : ℝ) (3 / 2))
    (hT : max 32 (Real.exp (64 / ε ^ 2)) ≤ T) :
    ‖rightEdge X T α t - dirichletPolyC (rightCoeff X T α) ⌊T ^ (1 + ε)⌋₊ ((α : ℂ) + (t : ℂ) * I)‖
      ≤ zetaTwoConst * T ^ (-(3 : ℝ)) := by
  have hT32 : 32 ≤ T := (le_max_left _ _).trans hT
  have hT_exp : Real.exp (64 / ε ^ 2) ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := by linarith
  set L := Real.log T
  have hL0 : 0 < L := lt_trans zero_lt_one (one_lt_log_of_ge_32 hT32)
  set z : ℂ := (α : ℂ) + (t : ℂ) * I
  set β : ℝ := 3 - α
  have hβ0 : 0 < β := by dsimp only [β]; linarith [hα.2]
  set N : ℕ := ⌊T ^ (1 + ε)⌋₊
  set g : ℕ → ℂ := fun n => rightCoeff X T α n * (n : ℂ) ^ (-z)
  -- `rightEdge` equals `∑' n, g n`
  have hright_eq : rightEdge X T α t = ∑' n : ℕ, g n := by
    have hts := rightEdge_eq_tsum hX hT0 hL0 (t := t) hα
    unfold rightEdge Cvs.Zeta.GaussKernel.SmoothedRectangleBounds.rectIntegrand
    rw [← smul_eq_mul, hts]
    refine tsum_congr fun n => ?_
    dsimp only [g, rightCoeff]
    split_ifs <;> ring
  -- `g` is summable (`O_T(n^{-2})`)
  have hp2_sum : Summable (fun n : ℕ => (n : ℝ) ^ (-(2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hg_sum : Summable g := by
    set K_dom : ℝ := (Real.exp (β ^ 2) * T ^ β / (2 * β))
    refine Summable.of_norm_bounded (hp2_sum.mul_left K_dom) fun n => ?_
    dsimp only [g, rightCoeff]
    split_ifs with hnX
    · have hn1 : 1 ≤ n := by omega
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have hq0 : 0 < T / n := div_pos hT0 hn0
      rw [mul_assoc, norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos hn1]
      have hre : (-z).re = -α := by simp [z]
      rw [hre]
      have h1 := norm_truncMoebiusSum_le_self X n
      have h2 := norm_gaussMellin_le hβ0 hL0.le hq0
      have h3 : (T / n) ^ β = T ^ β * (n : ℝ) ^ (-β) := by
        rw [div_eq_mul_inv, Real.mul_rpow hT0.le (inv_nonneg.mpr hn0.le), Real.inv_rpow hn0.le,
          ← Real.rpow_neg hn0.le]
      have h4 : (n : ℝ) * (n : ℝ) ^ (-β) * (n : ℝ) ^ (-α) = (n : ℝ) ^ (-(2 : ℝ)) := by
        calc (n : ℝ) * (n : ℝ) ^ (-β) * (n : ℝ) ^ (-α)
            = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-β) * (n : ℝ) ^ (-α) := by rw [Real.rpow_one]
          _ = (n : ℝ) ^ (-(2 : ℝ)) := by
              rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]
              congr 1; dsimp only [β]; ring
      calc ‖(truncMoebiusSum X n : ℂ)‖ * (‖gaussMellin β L (T / n)‖ * (n : ℝ) ^ (-α))
          ≤ (n : ℝ) * ((Real.exp (β ^ 2) * (T ^ β * (n : ℝ) ^ (-β)) / (2 * β)) * (n : ℝ) ^ (-α)) := by
            refine mul_le_mul h1 (mul_le_mul_of_nonneg_right ?_ (by positivity))
              (by positivity) (by positivity)
            rwa [h3] at h2
        _ = K_dom * ((n : ℝ) * (n : ℝ) ^ (-β) * (n : ℝ) ^ (-α)) := by dsimp only [K_dom]; ring
        _ = K_dom * (n : ℝ) ^ (-(2 : ℝ)) := by rw [h4]
    · rw [ zero_mul, norm_zero ]; positivity
  -- head sum over `range (N + 1)` matches `dirichletPolyC` on `Icc 1 N` since `g 0 = 0`
  have hhead : ∑ n ∈ Finset.range (N + 1), g n = dirichletPolyC (rightCoeff X T α) N z := by
    rw [dirichletPolyC]
    symm
    refine Finset.sum_subset (fun n hn => Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hn).2; omega))
      fun n hn hnot => ?_
    have hn0 : n = 0 := by
      rw [Finset.mem_range] at hn
      rw [Finset.mem_Icc, not_and_or] at hnot
      omega
    subst hn0
    simp [rightCoeff]
  -- isolate tail over `(Finset.range (N + 1))ᶜ`
  set S_tail : Set ℕ := ((Finset.range (N + 1) : Finset ℕ) : Set ℕ)ᶜ
  have hsub_eq : rightEdge X T α t - dirichletPolyC (rightCoeff X T α) N z
      = ∑' x : S_tail, g x.1 := by
    rw [hright_eq, ← hg_sum.sum_add_tsum_compl (s := Finset.range (N + 1)), hhead,
      add_sub_cancel_left]
  rw [hsub_eq]
  -- bound each tail term `x.1 ≥ N + 1 > T^{1 + ε}`
  have htail_pt : ∀ x : S_tail, ‖g x.1‖ ≤ T ^ (-(3 : ℝ)) * (x.1 : ℝ) ^ (-(2 : ℝ)) := by
    intro x
    have hx_ge : N + 1 ≤ x.1 := by
      have hm := x.2
      simp only [S_tail, Set.mem_compl_iff, Finset.mem_coe, Finset.mem_range, not_lt] at hm
      exact hm
    have hx1 : 1 ≤ x.1 := by omega
    have hx0 : (0 : ℝ) < x.1 := by exact_mod_cast hx1
    have hx_gt : T ^ (1 + ε) < (x.1 : ℝ) := by
      have hfl : T ^ (1 + ε) < (N : ℝ) + 1 := Nat.lt_floor_add_one _
      have hle : (N : ℝ) + 1 ≤ (x.1 : ℝ) := by exact_mod_cast hx_ge
      linarith
    dsimp only [g, rightCoeff]
    split_ifs with hnX
    · rw [mul_assoc, norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos hx1]
      have hre : (-z).re = -α := by simp [z]
      rw [hre]
      have h1 := norm_truncMoebiusSum_le_self X x.1
      have h2 := norm_gaussMellin_tail_le hε0 hε1 hα hT_exp hx_gt
      have h3 : (x.1 : ℝ) * (x.1 : ℝ) ^ (-(3 : ℝ)) = (x.1 : ℝ) ^ (-(2 : ℝ)) := by
        calc (x.1 : ℝ) * (x.1 : ℝ) ^ (-(3 : ℝ))
            = (x.1 : ℝ) ^ (1 : ℝ) * (x.1 : ℝ) ^ (-(3 : ℝ)) := by rw [Real.rpow_one]
          _ = (x.1 : ℝ) ^ (-(2 : ℝ)) := by rw [← Real.rpow_add hx0]; norm_num
      calc ‖(truncMoebiusSum X x.1 : ℂ)‖ * (‖gaussMellin (3 - α) L (T / x.1)‖ * (x.1 : ℝ) ^ (-α))
          ≤ (x.1 : ℝ) * (T ^ (-(3 : ℝ)) * (x.1 : ℝ) ^ (-(3 : ℝ))) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = T ^ (-(3 : ℝ)) * ((x.1 : ℝ) * (x.1 : ℝ) ^ (-(3 : ℝ))) := by ring
        _ = T ^ (-(3 : ℝ)) * (x.1 : ℝ) ^ (-(2 : ℝ)) := by rw [h3]
    · rw [zero_mul, norm_zero]; positivity
  have hdom_full : Summable (fun n : ℕ => T ^ (-(3 : ℝ)) * (n : ℝ) ^ (-(2 : ℝ))) :=
    hp2_sum.mul_left _
  have hdom_sub : Summable (fun x : S_tail => T ^ (-(3 : ℝ)) * (x.1 : ℝ) ^ (-(2 : ℝ))) :=
    hdom_full.subtype (· ∈ S_tail)
  have hnorm_sum : Summable (fun x : S_tail => ‖g x.1‖) :=
    (hg_sum.subtype (· ∈ S_tail)).norm
  calc ‖∑' x : S_tail, g x.1‖
      ≤ ∑' x : S_tail, ‖g x.1‖ := norm_tsum_le_tsum_norm hnorm_sum
    _ ≤ ∑' x : S_tail, T ^ (-(3 : ℝ)) * (x.1 : ℝ) ^ (-(2 : ℝ)) :=
        hnorm_sum.tsum_le_tsum htail_pt hdom_sub
    _ = ∑' n : ℕ, S_tail.indicator (fun n => T ^ (-(3 : ℝ)) * (n : ℝ) ^ (-(2 : ℝ))) n :=
        tsum_subtype S_tail (fun n : ℕ => T ^ (-(3 : ℝ)) * (n : ℝ) ^ (-(2 : ℝ)))
    _ ≤ ∑' n : ℕ, T ^ (-(3 : ℝ)) * (n : ℝ) ^ (-(2 : ℝ)) :=
        (hdom_full.indicator S_tail).tsum_le_tsum
          (fun n => by
            by_cases hn : n ∈ S_tail
            · rw [indicator_of_mem hn]
            · rw [indicator_of_notMem hn]; positivity) hdom_full
    _ = zetaTwoConst * T ^ (-(3 : ℝ)) := by
        rw [tsum_mul_left, zetaTwoConst, mul_comm]

/-- Squared pointwise upper bound on `rightEdge`:
`‖rightEdge X T α t‖² ≤ 2 ‖dirichletPolyC ...‖² + 2 zetaTwoConst² T^{-6}`. -/
theorem norm_rightEdge_sq_le {X : ℕ} (hX : 1 ≤ X) {T α t ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 4) (hα : α ∈ Icc (1 / 2 : ℝ) (3 / 2))
    (hT : max 32 (Real.exp (64 / ε ^ 2)) ≤ T) :
    ‖rightEdge X T α t‖ ^ 2
      ≤ 2 * ‖dirichletPolyC (rightCoeff X T α) ⌊T ^ (1 + ε)⌋₊ ((α : ℂ) + (t : ℂ) * I)‖ ^ 2
        + 2 * zetaTwoConst ^ 2 * T ^ (-(6 : ℝ)) := by
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hT)
  set P : ℂ := dirichletPolyC (rightCoeff X T α) ⌊T ^ (1 + ε)⌋₊ ((α : ℂ) + (t : ℂ) * I)
  have hdiff := norm_rightEdge_sub_dirichletPolyC_le hX hε0 hε1 hα (t := t) hT
  have htri : ‖rightEdge X T α t‖ ≤ ‖P‖ + zetaTwoConst * T ^ (-(3 : ℝ)) := by
    linarith [norm_sub_norm_le (rightEdge X T α t) P, hdiff]
  have hsq := (pow_le_pow_left₀ (norm_nonneg _) htri 2).trans (sq_add_le_two_mul _ _)
  have hT6 : (T ^ (-(3 : ℝ))) ^ 2 = T ^ (-(6 : ℝ)) := by
    rw [← Real.rpow_natCast (T ^ (-(3 : ℝ))) 2, ← Real.rpow_mul hT0.le]; norm_num
  calc ‖rightEdge X T α t‖ ^ 2
      ≤ 2 * ‖P‖ ^ 2 + 2 * (zetaTwoConst * T ^ (-(3 : ℝ))) ^ 2 := hsq
    _ = 2 * ‖P‖ ^ 2 + 2 * zetaTwoConst ^ 2 * (T ^ (-(3 : ℝ))) ^ 2 := by ring
    _ = 2 * ‖P‖ ^ 2 + 2 * zetaTwoConst ^ 2 * T ^ (-(6 : ℝ)) := by rw [hT6]

/-! ### Vertical mean-value bound for the truncated right-edge polynomial -/

/-- **Integrated `L²` bound on `dirichletPolyC (rightCoeff ⌊T^c⌋₊ T α) ⌊T^{1+c²/8}⌋₊`** over
`t ∈ [T - 1, 2T + 1]`: bounded uniformly in `α ∈ [1/2 + c, 3/2]` by `C_R(c) · T^{1 - c²/2}`. -/
theorem integral_rightPoly_sq_le {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1 / 4) :
    ∃ C_R T_R : ℝ, 0 ≤ C_R ∧ 32 ≤ T_R ∧ ∀ {T α : ℝ}, T_R ≤ T →
      α ∈ Icc (1 / 2 + c) (3 / 2) →
      ∫ t in (T - 1)..(2 * T + 1),
          ‖dirichletPolyC (rightCoeff ⌊T ^ c⌋₊ T α) ⌊T ^ (1 + c ^ 2 / 8)⌋₊
            ((α : ℂ) + (t : ℂ) * I)‖ ^ 2
        ≤ C_R * T ^ (1 - c ^ 2 / 2) := by
  set ε : ℝ := c ^ 2 / 8
  have hε0 : 0 < ε := by dsimp only [ε]; positivity
  have hε_qtr : ε ≤ 1 / 4 := by dsimp only [ε]; nlinarith
  have hε1 : ε ≤ 1 := by linarith
  set C_R : ℝ := (10 + 8 / ε) * (2 * (Real.exp 1 / ε) ^ 2 * divSqConst c)
  have hCR_nonneg : 0 ≤ C_R := by
    dsimp only [C_R]
    have := divSqConst_nonneg c
    positivity
  set T_R : ℝ := max (max 32 (Real.exp 5)) ((2 : ℝ) ^ (1 / c))
  refine ⟨C_R, T_R, hCR_nonneg, (le_max_left _ _).trans (le_max_left _ _),
    fun {T α} hT hα => ?_⟩
  have hT32 : 32 ≤ T := ((le_max_left _ _).trans (le_max_left _ _)).trans hT
  have hTe5 : Real.exp 5 ≤ T := ((le_max_right _ _).trans (le_max_left _ _)).trans hT
  have hT2c : (2 : ℝ) ^ (1 / c) ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  set X : ℕ := ⌊T ^ c⌋₊
  set N : ℕ := ⌊T ^ (1 + ε)⌋₊
  -- `2 ≤ T ^ c`, hence `1 ≤ X` and `T ^ c / 2 ≤ X`, so `X^{-c} ≤ 2 T^{-c²}`
  have hTc2 : 2 ≤ T ^ c := by
    have h1 := Real.rpow_le_rpow (by positivity) hT2c hc0.le
    rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hc0.ne', Real.rpow_one] at h1
    exact h1
  have hX1 : 1 ≤ X := Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr (by linarith)).ne'
  have hX_pos : (0 : ℝ) < X := by exact_mod_cast hX1
  have hX_half : T ^ c / 2 ≤ (X : ℝ) := by
    have hfl : T ^ c < (X : ℝ) + 1 := Nat.lt_floor_add_one _
    have h1X : (1 : ℝ) ≤ X := by exact_mod_cast hX1
    linarith
  have hX_neg_c : (X : ℝ) ^ (-c) ≤ 2 * T ^ (-(c ^ 2)) := by
    have h1 : (X : ℝ) ^ (-c) ≤ (T ^ c / 2) ^ (-c) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hX_half (by linarith)
    have h2 : (T ^ c / 2) ^ (-c) = (2 : ℝ) ^ c * T ^ (-(c ^ 2)) := by
      rw [div_eq_mul_inv, Real.mul_rpow (by positivity) (by norm_num),
        ← Real.rpow_mul hT0.le, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num),
        neg_neg]
      ring_nf
    have h2c : (2 : ℝ) ^ c ≤ (2 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    rw [Real.rpow_one] at h2c
    exact h1.trans (h2.trans_le (mul_le_mul_of_nonneg_right h2c (by positivity)))
  -- bound `6T + 4N(1 + log N) ≤ (10 + 8/ε) T^{1 + 2ε}`
  have hN1 : 1 ≤ N :=
    Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr (Real.one_le_rpow hT1 (by linarith))).ne'
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN_le : (N : ℝ) ≤ T ^ (1 + ε) := Nat.floor_le (by positivity)
  have hlogT_le : Real.log T ≤ (1 / ε) * T ^ ε := by
    have h1 : Real.log (T ^ ε) ≤ T ^ ε - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_rpow hT0] at h1
    rw [one_div_mul_eq_div, le_div_iff₀ hε0]
    linarith
  have hpref : 2 * (3 * T) + 4 * (N : ℝ) * (1 + Real.log N) ≤ (10 + 8 / ε) * T ^ (1 + 2 * ε) := by
    have hlogN : Real.log N ≤ (2 / ε) * T ^ ε := by
      have h1 : Real.log N ≤ Real.log (T ^ (1 + ε)) := Real.log_le_log hN_pos hN_le
      rw [Real.log_rpow hT0] at h1
      have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg hT1
      calc Real.log N ≤ (1 + ε) * Real.log T := h1
        _ ≤ 2 * ((1 / ε) * T ^ ε) := mul_le_mul (by linarith) hlogT_le hlogT0 (by norm_num)
        _ = (2 / ε) * T ^ ε := by ring
    have h1_le_Tε : 1 ≤ T ^ ε := Real.one_le_rpow hT1 hε0.le
    have h1logN : 1 + Real.log N ≤ (1 + 2 / ε) * T ^ ε := by
      calc 1 + Real.log N ≤ T ^ ε + (2 / ε) * T ^ ε := add_le_add h1_le_Tε hlogN
        _ = (1 + 2 / ε) * T ^ ε := by ring
    have h4N : 4 * (N : ℝ) * (1 + Real.log N) ≤ 4 * (1 + 2 / ε) * T ^ (1 + 2 * ε) := by
      have hlogN0 : 0 ≤ 1 + Real.log N := by linarith [Real.log_natCast_nonneg N]
      calc 4 * (N : ℝ) * (1 + Real.log N)
          ≤ (4 * T ^ (1 + ε)) * ((1 + 2 / ε) * T ^ ε) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hN_le (by norm_num)) h1logN hlogN0 (by positivity)
        _ = 4 * (1 + 2 / ε) * (T ^ (1 + ε) * T ^ ε) := by ring
        _ = 4 * (1 + 2 / ε) * T ^ (1 + 2 * ε) := by
            rw [← Real.rpow_add hT0]; congr 2; ring
    have h6T : 2 * (3 * T) ≤ 6 * T ^ (1 + 2 * ε) := by
      have hT_le : T ≤ T ^ (1 + 2 * ε) := by
        conv_lhs => rw [← Real.rpow_one T]
        exact Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
      linarith
    calc 2 * (3 * T) + 4 * (N : ℝ) * (1 + Real.log N)
        ≤ 6 * T ^ (1 + 2 * ε) + 4 * (1 + 2 / ε) * T ^ (1 + 2 * ε) := add_le_add h6T h4N
      _ = (10 + 8 / ε) * T ^ (1 + 2 * ε) := by ring
  -- bound the weighted coefficient sum `∑_{n=1}^N ‖rightCoeff‖² n^{-2α}`
  have hβ_mem : 3 - α ∈ Icc (3 / 2 : ℝ) (5 / 2) := ⟨by linarith [hα.2], by linarith [hα.1]⟩
  have hcoeff_sum : ∑ n ∈ Finset.Icc 1 N, ‖rightCoeff X T α n‖ ^ 2 * (n : ℝ) ^ (-(2 * α))
      ≤ (2 * (Real.exp 1 / ε) ^ 2 * divSqConst c) * T ^ (2 * ε - c ^ 2) := by
    have hterm : ∀ n ∈ Finset.Icc 1 N,
        ‖rightCoeff X T α n‖ ^ 2 * (n : ℝ) ^ (-(2 * α))
          ≤ ((Real.exp 1 / ε) ^ 2 * T ^ (2 * ε))
            * (if X < n then ‖(truncMoebiusSum X n : ℂ)‖ ^ 2 * (n : ℝ) ^ (-(2 * α)) else 0) := by
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      dsimp only [rightCoeff]
      split_ifs with hnX
      · rw [norm_mul, mul_pow]
        have hm := norm_gaussMellin_le_main hTe5 hβ_mem hε0 hε1 hn1
        have hm2 : ‖gaussMellin (3 - α) (Real.log T) (T / n)‖ ^ 2
            ≤ (Real.exp 1 / ε) ^ 2 * T ^ (2 * ε) := by
          refine (pow_le_pow_left₀ (norm_nonneg _) hm 2).trans_eq ?_
          rw [mul_pow, ← Real.rpow_natCast (T ^ ε) 2, ← Real.rpow_mul hT0.le]
          ring_nf
        calc ‖(truncMoebiusSum X n : ℂ)‖ ^ 2
              * ‖gaussMellin (3 - α) (Real.log T) (T / n)‖ ^ 2 * (n : ℝ) ^ (-(2 * α))
            = ‖gaussMellin (3 - α) (Real.log T) (T / n)‖ ^ 2
                * (‖(truncMoebiusSum X n : ℂ)‖ ^ 2 * (n : ℝ) ^ (-(2 * α))) := by ring
          _ ≤ ((Real.exp 1 / ε) ^ 2 * T ^ (2 * ε))
                * (‖(truncMoebiusSum X n : ℂ)‖ ^ 2 * (n : ℝ) ^ (-(2 * α))) :=
              mul_le_mul_of_nonneg_right hm2 (by positivity)
      · simp
    calc ∑ n ∈ Finset.Icc 1 N, ‖rightCoeff X T α n‖ ^ 2 * (n : ℝ) ^ (-(2 * α))
        ≤ ∑ n ∈ Finset.Icc 1 N, ((Real.exp 1 / ε) ^ 2 * T ^ (2 * ε))
            * (if X < n then ‖(truncMoebiusSum X n : ℂ)‖ ^ 2 * (n : ℝ) ^ (-(2 * α)) else 0) :=
          Finset.sum_le_sum hterm
      _ = ((Real.exp 1 / ε) ^ 2 * T ^ (2 * ε)) * ∑ n ∈ Finset.Icc 1 N,
            (if X < n then ‖(truncMoebiusSum X n : ℂ)‖ ^ 2 * (n : ℝ) ^ (-(2 * α)) else 0) := by
          rw [← Finset.mul_sum]
      _ ≤ ((Real.exp 1 / ε) ^ 2 * T ^ (2 * ε)) * (divSqConst c * (X : ℝ) ^ (-c)) :=
          mul_le_mul_of_nonneg_left (sum_truncMoebiusSum_sq_tail_le hc0 hα.1 hX1 N) (by positivity)
      _ ≤ ((Real.exp 1 / ε) ^ 2 * T ^ (2 * ε)) * (divSqConst c * (2 * T ^ (-(c ^ 2)))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hX_neg_c (divSqConst_nonneg c)) (by positivity)
      _ = (2 * (Real.exp 1 / ε) ^ 2 * divSqConst c) * (T ^ (2 * ε) * T ^ (-(c ^ 2))) := by ring
      _ = (2 * (Real.exp 1 / ε) ^ 2 * divSqConst c) * T ^ (2 * ε - c ^ 2) := by
          rw [← Real.rpow_add hT0, sub_eq_add_neg]
  -- apply `mean_value_bound_vertical` on `[-(3T), 3T] ⊇ [T - 1, 2T + 1]`
  have hsub_int : (∫ t in (T - 1)..(2 * T + 1),
        ‖dirichletPolyC (rightCoeff X T α) N ((α : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ ∫ t in (-(3 * T))..(3 * T),
        ‖dirichletPolyC (rightCoeff X T α) N ((α : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
    intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
      (ae_of_all _ fun _ => sq_nonneg _)
      (intervalIntegrable_normSq_dirichletPolyC (rightCoeff X T α) N α (3 * T))
  have hmv_raw := (abs_le.mp (mean_value_bound_vertical (rightCoeff X T α) N α (3 * T))).2
  have hmv : (∫ t in (-(3 * T))..(3 * T),
        ‖dirichletPolyC (rightCoeff X T α) N ((α : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ (2 * (3 * T) + 4 * (N : ℝ) * (1 + Real.log N))
        * ∑ n ∈ Finset.Icc 1 N, ‖rightCoeff X T α n‖ ^ 2 * (n : ℝ) ^ (-(2 * α)) := by
    have hring : (2 * (3 * T) + 4 * (N : ℝ) * (1 + Real.log N))
          * ∑ n ∈ Finset.Icc 1 N, ‖rightCoeff X T α n‖ ^ 2 * (n : ℝ) ^ (-(2 * α))
        = 2 * (3 * T) * (∑ n ∈ Finset.Icc 1 N, ‖rightCoeff X T α n‖ ^ 2 * (n : ℝ) ^ (-(2 * α)))
          + 4 * (N : ℝ) * (1 + Real.log N)
            * ∑ n ∈ Finset.Icc 1 N, ‖rightCoeff X T α n‖ ^ 2 * (n : ℝ) ^ (-(2 * α)) := by ring
    linarith
  have hexp_tot : T ^ (1 + 2 * ε) * T ^ (2 * ε - c ^ 2) = T ^ (1 - c ^ 2 / 2) := by
    rw [← Real.rpow_add hT0]
    congr 1; dsimp only [ε]; ring
  have hS0 : 0 ≤ ∑ n ∈ Finset.Icc 1 N, ‖rightCoeff X T α n‖ ^ 2 * (n : ℝ) ^ (-(2 * α)) :=
    Finset.sum_nonneg fun _ _ => by positivity
  calc (∫ t in (T - 1)..(2 * T + 1),
          ‖dirichletPolyC (rightCoeff X T α) N ((α : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ (2 * (3 * T) + 4 * (N : ℝ) * (1 + Real.log N))
          * ∑ n ∈ Finset.Icc 1 N, ‖rightCoeff X T α n‖ ^ 2 * (n : ℝ) ^ (-(2 * α)) :=
        hsub_int.trans hmv
    _ ≤ ((10 + 8 / ε) * T ^ (1 + 2 * ε))
          * ((2 * (Real.exp 1 / ε) ^ 2 * divSqConst c) * T ^ (2 * ε - c ^ 2)) :=
        mul_le_mul hpref hcoeff_sum hS0 (by positivity)
    _ = C_R * (T ^ (1 + 2 * ε) * T ^ (2 * ε - c ^ 2)) := by dsimp only [C_R]; ring
    _ = C_R * T ^ (1 - c ^ 2 / 2) := by rw [hexp_tot]

/-! ### Full 2D strip area `L²` bound on `Icc (1/2 + c) (3/2) ×ℂ Icc (T - 1) (2T + 1)` -/

/-- **2D strip area `L²` bound for `mollifiedDetector`**: for `0 < c < 1/4`, there exist `C_A ≥ 0`
and `T_A ≥ 32` such that for all `T ≥ T_A`,
`∫_{[1/2 + c, 3/2] ×ℂ [T - 1, 2T + 1]} ‖mollifiedDetector ⌊T^c⌋₊ z‖² ≤ C_A · T^{1 - c²/2}`. -/
theorem integral_strip_mollifiedDetector_sq_le {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1 / 4) :
    ∃ C_A T_A : ℝ, 0 ≤ C_A ∧ 32 ≤ T_A ∧ ∀ {T : ℝ}, T_A ≤ T →
      ∫ z in Icc (1 / 2 + c) (3 / 2) ×ℂ Icc (T - 1) (2 * T + 1),
          ‖mollifiedDetector ⌊T ^ c⌋₊ z‖ ^ 2
        ≤ C_A * T ^ (1 - c ^ 2 / 2) := by
  obtain ⟨T_hor, hThor32, hhor⟩ := norm_horizEdges_sq_le
  obtain ⟨C_L, hCL0, hleft_pt⟩ := norm_leftEdge_sq_le_leftMajorant hc0 hc1
  obtain ⟨C_R, T_R, hCR0, hTR32, hright_int⟩ := integral_rightPoly_sq_le hc0 hc1
  set ε : ℝ := c ^ 2 / 8
  have hε0 : 0 < ε := by dsimp only [ε]; positivity
  have hε1 : ε ≤ 1 / 4 := by dsimp only [ε]; nlinarith
  set C_A : ℝ := (32 + 32 * zetaTwoConst ^ 2) + 8 * C_R + 4 * C_L * (4 + 10 * Real.pi)
  have hCA0 : 0 ≤ C_A := by dsimp only [C_A]; positivity
  set T_A : ℝ := max (max T_hor T_R) (Real.exp (64 / ε ^ 2))
  refine ⟨C_A, T_A, hCA0, hThor32.trans ((le_max_left _ _).trans (le_max_left _ _)),
    fun {T} hT => ?_⟩
  have hT_hor : T_hor ≤ T := ((le_max_left _ _).trans (le_max_left _ _)).trans hT
  have hT_R : T_R ≤ T := ((le_max_right _ _).trans (le_max_left _ _)).trans hT
  have hT_exp : Real.exp (64 / ε ^ 2) ≤ T := (le_max_right _ _).trans hT
  have hT32 : 32 ≤ T := hThor32.trans hT_hor
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  set X : ℕ := ⌊T ^ c⌋₊
  set N : ℕ := ⌊T ^ (1 + ε)⌋₊
  have hX1 : 1 ≤ X :=
    Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr (Real.one_le_rpow hT1 hc0.le)).ne'
  have hXT : (X : ℝ) ≤ T :=
    (Nat.floor_le (by positivity)).trans
      ((Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)).trans_eq (Real.rpow_one T))
  -- Step 1: vertical line bound for each `α ∈ Icc (1 / 2 + c) (3 / 2)`
  have hline_bound : ∀ α ∈ Icc (1 / 2 + c) (3 / 2),
      ∫ t in Icc (T - 1) (2 * T + 1), ‖mollifiedDetector X ((α : ℂ) + (t : ℂ) * I)‖ ^ 2
        ≤ C_A * T ^ (1 - c ^ 2 / 2) := by
    intro α hα
    have hα_wide : α ∈ Icc (1 / 2 : ℝ) (3 / 2) := ⟨by linarith [hα.1], hα.2⟩
    have hab_t : T - 1 ≤ 2 * T + 1 := by linarith
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab_t]
    -- continuity of `t ↦ ‖mollifiedDetector X (α + t * I)‖ ^ 2` on `Icc (T - 1) (2T + 1)`
    have hdet_cont : ContinuousOn
        (fun t : ℝ => ‖mollifiedDetector X ((α : ℂ) + (t : ℂ) * I)‖ ^ 2)
        (Icc (T - 1) (2 * T + 1)) := by
      refine ContinuousOn.pow (ContinuousOn.norm ?_) 2
      refine (Cvs.Zeta.MollifiedDetectorSeries.differentiableOn_mollifiedDetector X).continuousOn.comp
        (by fun_prop) fun t ht => ?_
      intro h1
      have him := congrArg Complex.im (Set.mem_singleton_iff.mp h1)
      simp at him
      linarith [ht.1]
    set K_const : ℝ := 4 * (2 * T ^ (-(4 : ℝ)) + 2 * zetaTwoConst ^ 2 * T ^ (-(6 : ℝ)))
    set maj : ℝ → ℝ := fun t =>
      (K_const + 8 * ‖dirichletPolyC (rightCoeff X T α) N ((α : ℂ) + (t : ℂ) * I)‖ ^ 2)
        + 4 * leftMajorant C_L c X T t
    have hi_const : IntervalIntegrable (fun _t : ℝ => K_const) volume (T - 1) (2 * T + 1) :=
      intervalIntegrable_const
    have hi_right : IntervalIntegrable
        (fun t : ℝ => 8 * ‖dirichletPolyC (rightCoeff X T α) N ((α : ℂ) + (t : ℂ) * I)‖ ^ 2)
        volume (T - 1) (2 * T + 1) := by
      have hfull := intervalIntegrable_normSq_dirichletPolyC (rightCoeff X T α) N α (3 * T)
      exact (hfull.mono_set (Set.uIcc_subset_uIcc (by rw [Set.uIcc_of_le (by linarith)]; constructor <;> linarith)
        (by rw [Set.uIcc_of_le (by linarith)]; constructor <;> linarith))).const_mul 8
    have hi_left : IntervalIntegrable (fun t : ℝ => 4 * leftMajorant C_L c X T t)
        volume (T - 1) (2 * T + 1) :=
      ((continuous_leftMajorant C_L c X T).const_mul 4).intervalIntegrable _ _
    have hpt_maj : ∀ t ∈ Icc (T - 1) (2 * T + 1),
        ‖mollifiedDetector X ((α : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤ maj t := by
      intro t ht
      have he := norm_mollifiedDetector_sq_le_edges X hT32 hα_wide ht
      have hh := hhor hT_hor hXT hα_wide ht
      have hr := norm_rightEdge_sq_le hX1 hε0 hε1 hα_wide (t := t) (max_le hT32 hT_exp)
      have hl := hleft_pt X hT32 hα ht
      dsimp only [maj, K_const]
      linarith
    have hmono := intervalIntegral.integral_mono_on hab_t
      (hdet_cont.intervalIntegrable_of_Icc hab_t)
      ((hi_const.add hi_right).add hi_left) hpt_maj
    rw [intervalIntegral.integral_add (hi_const.add hi_right) hi_left,
      intervalIntegral.integral_add hi_const hi_right,
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, smul_eq_mul] at hmono
    -- bound each of the three integrated pieces by multiples of `T^{1 - c²/2}`
    have hexp_pos : 0 ≤ 1 - c ^ 2 / 2 := by nlinarith
    have hone_le_Texp : 1 ≤ T ^ (1 - c ^ 2 / 2) := Real.one_le_rpow hT1 hexp_pos
    have hpiece1 : (2 * T + 1 - (T - 1)) * K_const
        ≤ (32 + 32 * zetaTwoConst ^ 2) * T ^ (1 - c ^ 2 / 2) := by
      have hlen : 2 * T + 1 - (T - 1) ≤ 4 * T := by linarith
      have hT_m3 : T * T ^ (-(4 : ℝ)) ≤ 1 := by
        calc T * T ^ (-(4 : ℝ)) = T ^ (1 : ℝ) * T ^ (-(4 : ℝ)) := by rw [Real.rpow_one]
          _ = T ^ (-(3 : ℝ)) := by rw [← Real.rpow_add hT0]; norm_num
          _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hT1 (by norm_num)
      have hT_m5 : T * T ^ (-(6 : ℝ)) ≤ 1 := by
        calc T * T ^ (-(6 : ℝ)) = T ^ (1 : ℝ) * T ^ (-(6 : ℝ)) := by rw [Real.rpow_one]
          _ = T ^ (-(5 : ℝ)) := by rw [← Real.rpow_add hT0]; norm_num
          _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hT1 (by norm_num)
      have hK0 : 0 ≤ K_const := by dsimp only [K_const]; positivity
      have h1 : (2 * T + 1 - (T - 1)) * K_const ≤ 32 + 32 * zetaTwoConst ^ 2 := by
        calc (2 * T + 1 - (T - 1)) * K_const
            ≤ (4 * T) * K_const := mul_le_mul_of_nonneg_right hlen hK0
          _ = 32 * (T * T ^ (-(4 : ℝ))) + 32 * zetaTwoConst ^ 2 * (T * T ^ (-(6 : ℝ))) := by
              dsimp only [K_const]; ring
          _ ≤ 32 * 1 + 32 * zetaTwoConst ^ 2 * 1 :=
              add_le_add (mul_le_mul_of_nonneg_left hT_m3 (by norm_num))
                (mul_le_mul_of_nonneg_left hT_m5 (by positivity))
          _ = 32 + 32 * zetaTwoConst ^ 2 := by ring
      calc (2 * T + 1 - (T - 1)) * K_const
          ≤ (32 + 32 * zetaTwoConst ^ 2) * 1 := by linarith
        _ ≤ (32 + 32 * zetaTwoConst ^ 2) * T ^ (1 - c ^ 2 / 2) :=
            mul_le_mul_of_nonneg_left hone_le_Texp (by positivity)
    have hpiece2 : 8 * (∫ t in (T - 1)..(2 * T + 1),
          ‖dirichletPolyC (rightCoeff X T α) N ((α : ℂ) + (t : ℂ) * I)‖ ^ 2)
        ≤ 8 * C_R * T ^ (1 - c ^ 2 / 2) := by
      linarith [hright_int hT_R hα]
    have hpiece3 : 4 * (∫ t in (T - 1)..(2 * T + 1), leftMajorant C_L c X T t)
        ≤ 4 * C_L * (4 + 10 * Real.pi) * T ^ (1 - c ^ 2 / 2) := by
      have hl_int := integral_leftMajorant_le hCL0 hc0 hc1 hT32
      have hexp_cmp : T ^ (1 - c / 2) ≤ T ^ (1 - c ^ 2 / 2) :=
        Real.rpow_le_rpow_of_exponent_le hT1 (by nlinarith)
      calc 4 * (∫ t in (T - 1)..(2 * T + 1), leftMajorant C_L c X T t)
          ≤ 4 * (C_L * (4 + 10 * Real.pi) * T ^ (1 - c / 2)) :=
            mul_le_mul_of_nonneg_left hl_int (by norm_num)
        _ ≤ 4 * (C_L * (4 + 10 * Real.pi) * T ^ (1 - c ^ 2 / 2)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hexp_cmp (by positivity)) (by norm_num)
        _ = 4 * C_L * (4 + 10 * Real.pi) * T ^ (1 - c ^ 2 / 2) := by ring
    dsimp only [C_A]
    linarith
  -- Step 2: integrate over `α ∈ Icc (1 / 2 + c) (3 / 2)` via `measurableEquivRealProd` + `setIntegral_prod`
  set S_C : Set ℂ := Icc (1 / 2 + c) (3 / 2) ×ℂ Icc (T - 1) (2 * T + 1)
  set S_R : Set (ℝ × ℝ) := Icc (1 / 2 + c) (3 / 2) ×ˢ Icc (T - 1) (2 * T + 1)
  set h : ℝ × ℝ → ℝ := fun p => ‖mollifiedDetector X ((p.1 : ℂ) + (p.2 : ℂ) * I)‖ ^ 2
  have hsymm : ∀ p : ℝ × ℝ, measurableEquivRealProd.symm p = (p.1 : ℂ) + (p.2 : ℂ) * I :=
    fun p => by apply Complex.ext <;> simp [measurableEquivRealProd]
  have hh_cont : ContinuousOn h S_R := by
    refine ContinuousOn.pow (ContinuousOn.norm ?_) 2
    refine (Cvs.Zeta.MollifiedDetectorSeries.differentiableOn_mollifiedDetector X).continuousOn.comp
      (by fun_prop) fun p hp => ?_
    intro h1
    have him := congrArg Complex.im (Set.mem_singleton_iff.mp h1)
    simp at him
    linarith [hp.2.1]
  have hh_int : IntegrableOn h S_R :=
    hh_cont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hmeas_SC : MeasurableSet S_C := by
    change MeasurableSet (measurableEquivRealProd ⁻¹' S_R)
    exact measurableEquivRealProd.measurable (measurableSet_Icc.prod measurableSet_Icc)
  have heq_2d : (∫ z in S_C, ‖mollifiedDetector X z‖ ^ 2) = ∫ p in S_R, h p := by
    rw [← integral_indicator hmeas_SC,
      ← (Complex.volume_preserving_equiv_real_prod.symm).integral_comp
        measurableEquivRealProd.symm.measurableEmbedding,
      ← integral_indicator (measurableSet_Icc.prod measurableSet_Icc)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    dsimp only
    rw [hsymm]
    have hmem : ((p.1 : ℂ) + (p.2 : ℂ) * I) ∈ S_C ↔ p ∈ S_R := by
      simp only [S_C, S_R, mem_reProdIm, mem_prod, add_re, ofReal_re, mul_re, I_re, mul_zero,
        ofReal_im, I_im, mul_one, sub_self, add_zero, add_im, mul_im, zero_add]
    by_cases hp : p ∈ S_R
    · rw [indicator_of_mem (hmem.mpr hp), indicator_of_mem hp]
    · rw [indicator_of_notMem (mt hmem.mp hp), indicator_of_notMem hp]
  have hfub : (∫ p in S_R, h p)
      = ∫ α in Icc (1 / 2 + c) (3 / 2), ∫ t in Icc (T - 1) (2 * T + 1), h (α, t) := by
    rw [Measure.volume_eq_prod]
    exact setIntegral_prod h (by rw [← Measure.volume_eq_prod]; exact hh_int)
  have hα_int : (∫ α in Icc (1 / 2 + c) (3 / 2), ∫ t in Icc (T - 1) (2 * T + 1), h (α, t))
      ≤ ∫ _α in Icc (1 / 2 + c) (3 / 2), C_A * T ^ (1 - c ^ 2 / 2) := by
    refine integral_mono_of_nonneg
      (ae_of_all _ fun _ => setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _)
      (integrable_const _)
      ((ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun α hα => hline_bound α hα))
  have hconst_eval : (∫ _α in Icc (1 / 2 + c) (3 / 2), C_A * T ^ (1 - c ^ 2 / 2))
      ≤ C_A * T ^ (1 - c ^ 2 / 2) := by
    rw [setIntegral_const, Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith),
      smul_eq_mul]
    have hwid : 3 / 2 - (1 / 2 + c) ≤ 1 := by linarith
    calc (3 / 2 - (1 / 2 + c)) * (C_A * T ^ (1 - c ^ 2 / 2))
        ≤ 1 * (C_A * T ^ (1 - c ^ 2 / 2)) := mul_le_mul_of_nonneg_right hwid (by positivity)
      _ = C_A * T ^ (1 - c ^ 2 / 2) := one_mul _
  linarith [heq_2d, hfub, hα_int, hconst_eval]

end Cvs.Zeta.GaussKernel.RightEdgeDirichletPoly

end
