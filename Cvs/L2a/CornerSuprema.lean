import Mathlib
import Cvs.L2a.FarFarBound
import Cvs.L2a.FarIntegrationByParts
import Cvs.L2a.OrbitGapIntegerM
import Cvs.L2a.RampTopQuadratic
import Cvs.L2a.TopCornerConstants
import Cvs.Zeta.Digamma.WeierstrassGammaSeq

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Corner suprema: the closed forms behind `r̄_bot`, `R̄₁` and `T̄_bot`

`S(M) ≤ 1/3` from its harmonic closed form, the far bound `L_far < 5/(8π²(m²−1)(M−m))`, the near
tail, `Σ (L_near + L_far) ≤ r̄_bot²` for every `M`, the monotone step making `R̄₁` maximal at
`M = 4`, the majorant `T̄_bot`, `arcosh X/√X ≤ 2√2/e`, and two-sided bounds on `Θ₂`.
-/

noncomputable section

open Real Finset

namespace Cvs.L2a.CornerSuprema

/-! ### Harmonic sums -/

/-- Telescoping over `Ico a b`. -/
theorem sum_Ico_telescope (g : ℕ → ℝ) {a b : ℕ} (h : a ≤ b) :
    ∑ m ∈ Ico a b, (g m - g (m + 1)) = g a - g b := by
  induction b, h using Nat.le_induction with
  | base => simp
  | succ n hn ih => rw [Finset.sum_Ico_succ_top hn, ih]; ring

/-- `H_n ≤ (n + 1)/2`. -/
theorem harmonic_le_half (n : ℕ) : (harmonic n : ℝ) ≤ ((n : ℝ) + 1) / 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [harmonic_succ]; push_cast
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; norm_num
    · have hk : (1 : ℝ) ≤ k := by exact_mod_cast h
      have : ((k : ℝ) + 1)⁻¹ ≤ 1 / 2 := by
        rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
      linarith

/-- `Σ_{2 ≤ m < M} 1/(m − 1) = H_{M−2}`. -/
theorem sum_inv_sub_one (M : ℕ) :
    ∑ m ∈ Ico 2 M, 1 / ((m : ℝ) - 1) = harmonic (M - 2) := by
  rw [Finset.sum_Ico_eq_sum_range, harmonic]; push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [one_div]; ring_nf

/-- `Σ_{a ≤ m < M} 1/(m + j) = H_{M+j−1} − H_{a+j−1}`, written with `a + j = n + 1`. -/
theorem sum_inv_add (M a j n : ℕ) (hn : a + j = n + 1) :
    ∑ m ∈ Ico a M, 1 / ((m : ℝ) + j) = harmonic (n + (M - a)) - harmonic n := by
  rw [Finset.sum_Ico_eq_sum_range, harmonic, harmonic, Finset.sum_range_add]; push_cast
  rw [add_sub_cancel_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : ((a : ℝ) + k + j) = (n : ℝ) + k + 1 := by
    have : ((a + j : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) := by rw [hn]
    push_cast at this; linarith
  rw [this, one_div]

/-! ### `S(M)` -/

/-- `S(M) = Σ_{2 ≤ m < M} 1/((m² − 1)(M − m))`. -/
def farSum (M : ℕ) : ℝ := ∑ m ∈ Ico 2 M, 1 / (((m : ℝ) ^ 2 - 1) * ((M : ℝ) - m))

/-- **Harmonic closed form**: `S(M) = H_{M−2}/(2(M−1)) − (H_M − 3/2)/(2(M+1)) + H_{M−2}/(M²−1)`. -/
theorem farSum_eq (M : ℕ) (hM : 2 ≤ M) :
    farSum M = harmonic (M - 2) / (2 * ((M : ℝ) - 1)) - ((harmonic M : ℝ) - 3 / 2) / (2 * ((M : ℝ) + 1))
      + harmonic (M - 2) / ((M : ℝ) ^ 2 - 1) := by
  have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hpf : ∀ m ∈ Ico 2 M, 1 / (((m : ℝ) ^ 2 - 1) * ((M : ℝ) - m)) =
      1 / (2 * ((M : ℝ) - 1)) * (1 / ((m : ℝ) - 1)) - 1 / (2 * ((M : ℝ) + 1)) * (1 / ((m : ℝ) + (1 : ℕ)))
        + 1 / ((M : ℝ) ^ 2 - 1) * (1 / ((M : ℝ) - m)) := by
    intro m hm
    simp only [mem_Ico] at hm
    have h1 : (2 : ℝ) ≤ m := by exact_mod_cast hm.1
    have h2 : (m : ℝ) + 1 ≤ M := by exact_mod_cast hm.2
    have : (M : ℝ) - m ≠ 0 := by linarith
    have : (m : ℝ) - 1 ≠ 0 := by linarith
    have : (M : ℝ) - 1 ≠ 0 := by linarith
    have : (M : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    have : (m : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    have : (M : ℝ) + 1 ≠ 0 := by linarith
    have : (m : ℝ) + 1 ≠ 0 := by linarith
    push_cast
    field_simp
    ring
  unfold farSum
  rw [Finset.sum_congr rfl hpf, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, sum_inv_sub_one M, sum_inv_add M 2 1 2 rfl,
    Cvs.L2a.TopCornerConstants.sum_inv_sub_eq_harmonic M hM]
  have hM2 : 2 + (M - 2) = M := by omega
  rw [hM2]
  have : (harmonic 2 : ℝ) = 3 / 2 := by norm_num [harmonic]
  rw [this]
  ring

/-- **`S(M) ≤ 1/3`** for every `M`, from the harmonic closed form and `H_n ≤ (n + 1)/2`. -/
theorem farSum_le (M : ℕ) : farSum M ≤ 1 / 3 := by
  rcases Nat.lt_or_ge M 3 with h | h
  · unfold farSum
    interval_cases M <;> simp
  have hMr : (3 : ℝ) ≤ M := by exact_mod_cast h
  rw [farSum_eq M (by omega)]
  have hHM : (harmonic M : ℝ) = harmonic (M - 2) + 1 / ((M : ℝ) - 1) + 1 / (M : ℝ) := by
    obtain ⟨k, rfl⟩ : ∃ k, M = k + 2 := ⟨M - 2, by omega⟩
    rw [show k + 2 - 2 = k by omega, harmonic_succ, harmonic_succ]; push_cast
    rw [one_div, one_div]; ring_nf
  have hH := harmonic_le_half (M - 2)
  rw [Nat.cast_sub (by omega)] at hH; push_cast at hH
  set H : ℝ := (harmonic (M - 2) : ℝ)
  rw [hHM]
  have e : H / (2 * ((M : ℝ) - 1)) - (H + 1 / ((M : ℝ) - 1) + 1 / M - 3 / 2) / (2 * ((M : ℝ) + 1))
      + H / ((M : ℝ) ^ 2 - 1) =
      (4 * H - 1 - ((M : ℝ) - 1) / M + 3 * ((M : ℝ) - 1) / 2) / (2 * ((M : ℝ) ^ 2 - 1)) := by
    have : (M : ℝ) - 1 ≠ 0 := by linarith
    have : (M : ℝ) + 1 ≠ 0 := by linarith
    have : (M : ℝ) ≠ 0 := by linarith
    have : (M : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    field_simp
    ring
  rw [e, div_le_iff₀ (by nlinarith)]
  have hx : 0 < (M : ℝ) := by linarith
  have : ((M : ℝ) - 1) / M = 1 - 1 / M := by field_simp
  rw [this]
  have hinv : 1 / (M : ℝ) ≤ 1 / 3 := by
    rw [div_le_div_iff₀ hx (by norm_num)]; linarith
  nlinarith [mul_nonneg (sub_nonneg.2 hMr) (sub_nonneg.2 hMr)]

/-! ### The far part -/

/-- `b_m = m²/√(m² − 1)`, the far pole of the bottom cut at `m`. -/
def bm (m : ℝ) : ℝ := m ^ 2 / √(m ^ 2 - 1)

theorem bm_sub_eq {m : ℝ} (hm : 1 < m) : bm m - m = m * Cvs.L2a.TopCornerConstants.dY m := by
  unfold bm Cvs.L2a.TopCornerConstants.dY Cvs.L2a.OrbitGapIntegerM.Ymax
  have : 0 < √(m ^ 2 - 1) := Real.sqrt_pos.2 (by nlinarith)
  field_simp

theorem bm_sq {m : ℝ} (hm : 1 < m) : bm m ^ 2 = m ^ 4 / (m ^ 2 - 1) := by
  unfold bm; rw [div_pow, Real.sq_sqrt (by nlinarith)]; ring

theorem lt_bm {m : ℝ} (hm : 1 < m) : m < bm m := by
  have h := bm_sub_eq hm
  have hd : 0 ≤ Cvs.L2a.TopCornerConstants.dY m := Cvs.L2a.TopCornerConstants.dY_nonneg hm
  have hs : √(m ^ 2 - 1) < m := by
    rw [Real.sqrt_lt' (by linarith)]; linarith
  unfold bm
  rw [lt_div_iff₀ (Real.sqrt_pos.2 (by nlinarith))]
  nlinarith

/-- `b_m − m < m/(2(m² − 1))`, from `ΔY m < 1/(2(m² − 1))`. -/
theorem bm_sub_lt {m : ℝ} (hm : 1 < m) : bm m - m < m / (2 * (m ^ 2 - 1)) := by
  rw [bm_sub_eq hm]
  have := Cvs.L2a.TopCornerConstants.dY_lt hm
  calc m * Cvs.L2a.TopCornerConstants.dY m < m * (1 / (2 * (m ^ 2 - 1))) :=
        mul_lt_mul_of_pos_left this (by linarith)
    _ = m / (2 * (m ^ 2 - 1)) := by ring

/-- `b_m − m < 1/3` for `m ≥ 2`. -/
theorem bm_sub_lt_third {m : ℝ} (hm : 2 ≤ m) : bm m - m < 1 / 3 := by
  have h := bm_sub_lt (by linarith : 1 < m)
  have : m / (2 * (m ^ 2 - 1)) ≤ 1 / 3 := by
    rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]; nlinarith
  linarith

/-- `L_far(m, M) = (2π²m)⁻¹ [ln((M + b_m)/(M − b_m)) − ln((M + m)/(M − m))]`. -/
def Lfar (m M : ℝ) : ℝ :=
  (2 * π ^ 2 * m)⁻¹ * (Real.log ((M + bm m) / (M - bm m)) - Real.log ((M + m) / (M - m)))

theorem Lfar_nonneg {m M : ℝ} (hm : 2 ≤ m) (hM : m + 1 ≤ M) : 0 ≤ Lfar m M := by
  have hb := lt_bm (by linarith : 1 < m)
  have hb3 := bm_sub_lt_third hm
  have h1 : 0 < M - bm m := by linarith
  have h2 : 0 < M - m := by linarith
  unfold Lfar
  apply mul_nonneg (by positivity)
  rw [sub_nonneg]
  apply Real.log_le_log (by apply div_pos <;> linarith)
  rw [div_le_div_iff₀ h2 h1]; nlinarith

/-- `L_far(m, M) ≤ M(b_m − m)/(π² m (M − b_m)(M + m))`, from `log x ≤ x − 1`. -/
theorem Lfar_le {m M : ℝ} (hm : 2 ≤ m) (hM : m + 1 ≤ M) :
    Lfar m M ≤ M * (bm m - m) / (π ^ 2 * m * (M - bm m) * (M + m)) := by
  have hb := lt_bm (by linarith : 1 < m)
  have hb3 := bm_sub_lt_third hm
  have h1 : 0 < M - bm m := by linarith
  have h2 : 0 < M - m := by linarith
  have hA : 0 < (M + bm m) / (M - bm m) := by apply div_pos <;> linarith
  have hB : 0 < (M + m) / (M - m) := by apply div_pos <;> linarith
  unfold Lfar
  rw [← Real.log_div hA.ne' hB.ne']
  have hl := Real.log_le_sub_one_of_pos (div_pos hA hB)
  have he : (M + bm m) / (M - bm m) / ((M + m) / (M - m)) - 1 =
      2 * M * (bm m - m) / ((M - bm m) * (M + m)) := by
    have : M + m ≠ 0 := by linarith
    field_simp; ring
  rw [he] at hl
  have hπ : 0 < π ^ 2 * m := by have := pi_pos; positivity
  calc (2 * π ^ 2 * m)⁻¹ * Real.log ((M + bm m) / (M - bm m) / ((M + m) / (M - m)))
      ≤ (2 * π ^ 2 * m)⁻¹ * (2 * M * (bm m - m) / ((M - bm m) * (M + m))) :=
        mul_le_mul_of_nonneg_left hl (by positivity)
    _ = M * (bm m - m) / (π ^ 2 * m * (M - bm m) * (M + m)) := by
        field_simp

/-- **The far bound**: `L_far(m, M) < 5/(8π²(m² − 1)(M − m))` for `2 ≤ m ≤ M − 1`. -/
theorem Lfar_lt {m M : ℝ} (hm : 2 ≤ m) (hM : m + 1 ≤ M) :
    Lfar m M < 5 / (8 * π ^ 2 * (m ^ 2 - 1) * (M - m)) := by
  have hb := lt_bm (by linarith : 1 < m)
  have hb3 := bm_sub_lt_third hm
  have hbl := bm_sub_lt (by linarith : 1 < m)
  have h1 : 0 < M - bm m := by linarith
  have h2 : 0 < M - m := by linarith
  have hm1 : 0 < m ^ 2 - 1 := by nlinarith
  have hπ := pi_pos
  have hD : 0 < π ^ 2 * m * (M - bm m) * (M + m) := by
    apply mul_pos (mul_pos (mul_pos (by positivity) (by linarith)) h1) (by linarith)
  refine (Lfar_le hm hM).trans_lt ?_
  calc M * (bm m - m) / (π ^ 2 * m * (M - bm m) * (M + m))
      < M * (m / (2 * (m ^ 2 - 1))) / (π ^ 2 * m * (M - bm m) * (M + m)) := by
        apply div_lt_div_of_pos_right _ hD
        exact mul_lt_mul_of_pos_left hbl (by linarith)
    _ = M / (2 * π ^ 2 * (m ^ 2 - 1) * (M - bm m) * (M + m)) := by
        field_simp
    _ ≤ 5 / (8 * π ^ 2 * (m ^ 2 - 1) * (M - m)) := by
        have hp1 : 0 < 2 * π ^ 2 * (m ^ 2 - 1) * (M - bm m) * (M + m) := by
          apply mul_pos (mul_pos (mul_pos (by positivity) hm1) h1) (by linarith)
        have hp2 : 0 < 8 * π ^ 2 * (m ^ 2 - 1) * (M - m) := by
          apply mul_pos (mul_pos (by positivity) hm1) h2
        rw [div_le_div_iff₀ hp1 hp2]
        have key : 4 * M * (M - m) ≤ 5 * ((M - bm m) * (M + m)) := by nlinarith
        have hc : 0 ≤ 2 * π ^ 2 * (m ^ 2 - 1) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left key hc]

/-- `Σ_{2 ≤ m < M} L_far(m, M) ≤ (5/(8π²)) S(M)`. -/
theorem sum_Lfar_le_farSum (M : ℕ) :
    ∑ m ∈ Ico 2 M, Lfar m M ≤ 5 / (8 * π ^ 2) * farSum M := by
  unfold farSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m hm
  simp only [mem_Ico] at hm
  have h1 : (2 : ℝ) ≤ m := by exact_mod_cast hm.1
  have h2 : (m : ℝ) + 1 ≤ M := by exact_mod_cast hm.2
  refine (Lfar_lt h1 h2).le.trans (le_of_eq ?_)
  have : (m : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have : (M : ℝ) - m ≠ 0 := by linarith
  have := pi_pos
  field_simp

/-- **The far sum is uniform in `M`**: `Σ_{2 ≤ m < M} L_far(m, M) ≤ 5/(24π²)`. -/
theorem sum_Lfar_le (M : ℕ) : ∑ m ∈ Ico 2 M, Lfar m M ≤ 5 / (24 * π ^ 2) := by
  have h := sum_Lfar_le_farSum M
  have hS := farSum_le M
  have hπ : 0 < π ^ 2 := by have := pi_pos; positivity
  calc _ ≤ 5 / (8 * π ^ 2) * farSum M := h
    _ ≤ 5 / (8 * π ^ 2) * (1 / 3) := mul_le_mul_of_nonneg_left hS (by positivity)
    _ = 5 / (24 * π ^ 2) := by field_simp; ring

/-! ### The weight `w = 1 − wF` on `(1, 2)` -/

open Cvs.L2a.FarIntegrationByParts in
theorem one_sub_wF_eq_sin {t : ℝ} (ht : t ∈ Set.Icc (3 / 2 : ℝ) 2) :
    1 - wF t = Real.sin (π * t) ^ 2 := by
  rw [Cvs.L2a.RampTopQuadratic.one_sub_wF_eq ht, show π * (2 - t) = 2 * π - π * t by ring,
    Real.sin_two_pi_sub, neg_sq]

open Cvs.L2a.FarIntegrationByParts in
theorem continuous_one_sub_wF : Continuous fun t => 1 - wF t :=
  continuous_const.sub continuous_wF.1

open Cvs.L2a.FarIntegrationByParts in
/-- `∫₁² (1 − wF)^k = 1/2 + π⁻¹ ∫_{3π/2}^{2π} sin^{2k}`. -/
theorem integral_one_sub_wF_pow (k : ℕ) :
    ∫ t in (1 : ℝ)..2, (1 - wF t) ^ k =
      1 / 2 + π⁻¹ * ∫ x in (π / 2 + π)..(2 * π), Real.sin x ^ (2 * k) := by
  have hc : Continuous fun t => (1 - wF t) ^ k := continuous_one_sub_wF.pow k
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 3 / 2)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have h1 : ∫ t in (1 : ℝ)..(3 / 2), (1 - wF t) ^ k = ∫ _ in (1 : ℝ)..(3 / 2), (1 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    simp [Cvs.L2a.FarFarBound.wF_eq_zero_of_le ht.2]
  have h2 : ∫ t in (3 / 2 : ℝ)..2, (1 - wF t) ^ k =
      ∫ t in (3 / 2 : ℝ)..2, Real.sin (π * t) ^ (2 * k) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    simp only [one_sub_wF_eq_sin ht, ← pow_mul]
  rw [h1, h2, intervalIntegral.integral_const,
    intervalIntegral.integral_comp_mul_left (fun x => Real.sin x ^ (2 * k)) pi_ne_zero]
  rw [show π * (3 / 2) = π / 2 + π by ring, show π * 2 = 2 * π by ring]
  simp only [smul_eq_mul]
  norm_num

/-- `∫_{3π/2}^{2π} sin² = π/4`. -/
theorem integral_sin_sq_quarter : ∫ x in (π / 2 + π)..(2 * π), Real.sin x ^ 2 = π / 4 := by
  rw [integral_sin_sq]
  simp [Real.sin_add_pi, Real.cos_add_pi]
  ring

open Cvs.L2a.FarIntegrationByParts in
/-- `∫₁² w = 3/4`. -/
theorem integral_weight : ∫ t in (1 : ℝ)..2, (1 - wF t) = 3 / 4 := by
  have h := integral_one_sub_wF_pow 1
  simp only [pow_one, mul_one] at h
  rw [h, integral_sin_sq_quarter]
  field_simp
  ring

open Cvs.L2a.FarIntegrationByParts in
/-- `∫₁² w² = 11/16`. -/
theorem integral_weight_sq : ∫ t in (1 : ℝ)..2, (1 - wF t) ^ 2 = 11 / 16 := by
  rw [integral_one_sub_wF_pow 2, show 2 * 2 = 2 + 2 by rfl, integral_sin_pow, integral_sin_sq_quarter]
  simp [Real.sin_add_pi, Real.cos_add_pi]
  field_simp
  ring

/-! ### The near part -/

/-- `f_m(t) = 1/(m² − t²) − (b_m/m)/(b_m² − t²)`. -/
def fm (m t : ℝ) : ℝ := 1 / (m ^ 2 - t ^ 2) - bm m / m / (bm m ^ 2 - t ^ 2)

/-- The near term `(m²/2 + 5/2 − 2/m²)/((m² − 4)(m² − 2)²)`. -/
def nearTerm (m : ℝ) : ℝ := (m ^ 2 / 2 + 5 / 2 - 2 / m ^ 2) / ((m ^ 2 - 4) * (m ^ 2 - 2) ^ 2)

open Cvs.L2a.FarIntegrationByParts in
/-- `L_near(m) = π⁻² ∫₁² (1 − wF t) f_m(t) dt`. -/
def Lnear (m : ℝ) : ℝ := (π ^ 2)⁻¹ * ∫ t in (1 : ℝ)..2, (1 - wF t) * fm m t

/-- `b_m² − u ≥ (b_m/m)(m² − u)` for `u ≥ 0`. -/
theorem bm_sq_sub_ge {m u : ℝ} (hm : 1 < m) (hu : 0 ≤ u) :
    bm m / m * (m ^ 2 - u) ≤ bm m ^ 2 - u := by
  have hb := lt_bm hm
  have hm0 : 0 < m := by linarith
  have e : bm m ^ 2 - u - bm m / m * (m ^ 2 - u) = (bm m - m) * (bm m + u / m) := by
    field_simp; ring
  have : 0 ≤ (bm m - m) * (bm m + u / m) := by
    apply mul_nonneg (by linarith); have := div_nonneg hu hm0.le; linarith
  linarith

theorem fm_nonneg {m t : ℝ} (hm : 1 < m) (ht : t ^ 2 < m ^ 2) : 0 ≤ fm m t := by
  have hb := lt_bm hm
  have hm0 : 0 < m := by linarith
  have hA : 0 < m ^ 2 - t ^ 2 := by linarith
  have key := bm_sq_sub_ge hm (sq_nonneg t)
  have hr : 0 < bm m / m := div_pos (by linarith) hm0
  have hB : 0 < bm m ^ 2 - t ^ 2 := lt_of_lt_of_le (mul_pos hr hA) key
  unfold fm
  rw [sub_nonneg, div_le_div_iff₀ hB hA, one_mul]
  exact key

/-- `f_m` increases in `t²` on `t² ≤ 4`: `f_m(t) ≤ f_m(2)` for `m > 2`. -/
theorem fm_le_two {m t : ℝ} (hm : 2 < m) (ht : t ^ 2 ≤ 4) : fm m t ≤ fm m 2 := by
  have hb := lt_bm (by linarith : 1 < m)
  have hm0 : 0 < m := by linarith
  set r := bm m / m with hr_def
  have hr1 : 1 ≤ r := by rw [hr_def, le_div_iff₀ hm0]; linarith
  set A := m ^ 2 - 4 with hA_def
  set B := m ^ 2 - t ^ 2 with hB_def
  set C := bm m ^ 2 - 4 with hC_def
  set D := bm m ^ 2 - t ^ 2 with hD_def
  have hA : 0 < A := by rw [hA_def]; nlinarith
  have hB : 0 < B := by rw [hB_def]; nlinarith
  have hCA : r * A ≤ C := by
    have := bm_sq_sub_ge (by linarith : 1 < m) (show (0 : ℝ) ≤ 2 ^ 2 by norm_num); norm_num at this
    exact this
  have hDB : r * B ≤ D := bm_sq_sub_ge (by linarith : 1 < m) (sq_nonneg t)
  have hC : 0 < C := lt_of_lt_of_le (by positivity) hCA
  have hD : 0 < D := lt_of_lt_of_le (by positivity) hDB
  have hkey : r * A * B ≤ C * D := by
    have h1 : r * A * (r * B) ≤ C * D := mul_le_mul hCA hDB (by positivity) hC.le
    have h2 : r * A * B ≤ r * A * (r * B) := by
      have : r * A * B * 1 ≤ r * A * B * r := mul_le_mul_of_nonneg_left hr1 (by positivity)
      nlinarith
    linarith
  have e : fm m t - fm m 2 = (A - B) * (C * D - r * A * B) / (A * B * C * D) := by
    unfold fm
    rw [← hr_def, ← hB_def, ← hD_def, show (2 : ℝ) ^ 2 = 4 by norm_num, ← hA_def, ← hC_def]
    field_simp
    ring
  have hAB : A - B ≤ 0 := by rw [hA_def, hB_def]; linarith
  have : fm m t - fm m 2 ≤ 0 := by
    rw [e]
    apply div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hAB (by linarith))
    positivity
  linarith

/-- `f_m(2) = 1/(m² − 4) − m√(m² − 1)/(m² − 2)²`. -/
theorem fm_two_eq {m : ℝ} (hm : 2 < m) :
    fm m 2 = 1 / (m ^ 2 - 4) - m * √(m ^ 2 - 1) / (m ^ 2 - 2) ^ 2 := by
  have h1 : 0 < m ^ 2 - 1 := by nlinarith
  have hb2 := bm_sq (by linarith : 1 < m)
  have e1 : bm m / m = m / √(m ^ 2 - 1) := by
    unfold bm; have : 0 < √(m ^ 2 - 1) := Real.sqrt_pos.2 h1
    have : m ≠ 0 := by linarith
    field_simp
  have e2 : bm m ^ 2 - 2 ^ 2 = (m ^ 2 - 2) ^ 2 / (m ^ 2 - 1) := by
    rw [hb2]; field_simp; ring
  unfold fm
  rw [e1, e2]
  set s := √(m ^ 2 - 1) with hs_def
  have hs : 0 < s := Real.sqrt_pos.2 h1
  have hs2 : s ^ 2 = m ^ 2 - 1 := Real.sq_sqrt h1.le
  have hm2 : 0 < m ^ 2 - 2 := by nlinarith
  rw [← hs2]
  have : s ^ 2 ≠ 0 := by positivity
  have : m ^ 2 - 2 ≠ 0 := hm2.ne'
  field_simp
  norm_num

/-- **`f_m(2)` is at most the near term**, from `m√(m² − 1) ≥ m² − 1/2 − 1/(2m²)`. -/
theorem fm_two_le {m : ℝ} (hm : 2 < m) : fm m 2 ≤ nearTerm m := by
  rw [fm_two_eq hm]
  have hm2 : 0 < m ^ 2 := by positivity
  have hs2 : √(m ^ 2 - 1) ^ 2 = m ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
  have hs : 0 ≤ √(m ^ 2 - 1) := Real.sqrt_nonneg _
  have hlow : m ^ 2 - 1 / 2 - 1 / (2 * m ^ 2) ≤ m * √(m ^ 2 - 1) := by
    have hq : 0 ≤ m ^ 2 - 1 / 2 - 1 / (2 * m ^ 2) := by
      have : 1 / (2 * m ^ 2) ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
      nlinarith
    refine (pow_le_pow_iff_left₀ hq (by positivity) two_ne_zero).1 ?_
    · rw [mul_pow, hs2]
      have e : (m ^ 2 - 1 / 2 - 1 / (2 * m ^ 2)) ^ 2 =
          m ^ 2 * (m ^ 2 - 1) - 3 / 4 + 1 / (2 * m ^ 2) + 1 / (4 * (m ^ 2) ^ 2) := by
        field_simp; ring
      rw [e]
      have h1 : 1 / (2 * m ^ 2) ≤ 1 / 8 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
      have h2 : 1 / (4 * (m ^ 2) ^ 2) ≤ 1 / 64 := by
        have h4 : 4 ≤ m ^ 2 := by nlinarith
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [mul_le_mul h4 h4 (by norm_num) (by positivity)]
      linarith
  have hA : 0 < m ^ 2 - 4 := by nlinarith
  have hC : 0 < (m ^ 2 - 2) ^ 2 := by have : 0 < m ^ 2 - 2 := by nlinarith
                                      positivity
  calc 1 / (m ^ 2 - 4) - m * √(m ^ 2 - 1) / (m ^ 2 - 2) ^ 2
      ≤ 1 / (m ^ 2 - 4) - (m ^ 2 - 1 / 2 - 1 / (2 * m ^ 2)) / (m ^ 2 - 2) ^ 2 := by
        have := div_le_div_of_nonneg_right hlow hC.le
        linarith
    _ = nearTerm m := by
        unfold nearTerm
        have : m ^ 2 - 2 ≠ 0 := by nlinarith
        have : m ≠ 0 := by linarith
        field_simp
        ring

open Cvs.L2a.FarIntegrationByParts in
theorem continuousOn_fm {m : ℝ} (hm : 2 < m) : ContinuousOn (fm m) (Set.Icc 1 2) := by
  have hb := lt_bm (by linarith : 1 < m)
  unfold fm
  have c1 : ContinuousOn (fun t : ℝ => m ^ 2 - t ^ 2) (Set.Icc 1 2) := by fun_prop
  have c2 : ContinuousOn (fun t : ℝ => bm m ^ 2 - t ^ 2) (Set.Icc 1 2) := by fun_prop
  apply ContinuousOn.sub
  · have h : ∀ t ∈ Set.Icc (1 : ℝ) 2, m ^ 2 - t ^ 2 ≠ 0 := by
      intro t ht; nlinarith [ht.1, ht.2]
    exact ContinuousOn.div₀ (f := fun _ : ℝ => (1 : ℝ)) continuousOn_const c1 h
  · have h : ∀ t ∈ Set.Icc (1 : ℝ) 2, bm m ^ 2 - t ^ 2 ≠ 0 := by
      intro t ht; nlinarith [ht.1, ht.2]
    exact ContinuousOn.div₀ (f := fun _ : ℝ => bm m / m) continuousOn_const c2 h

open Cvs.L2a.FarIntegrationByParts in
theorem Lnear_nonneg {m : ℝ} (hm : 2 ≤ m) : 0 ≤ Lnear m := by
  unfold Lnear
  apply mul_nonneg (by positivity)
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro t ht
  have hw : 0 ≤ 1 - wF t := by linarith [(Cvs.L2a.FarFarBound.wF_bounds t).2.1]
  rcases lt_or_eq_of_le ht.2 with h | h
  · exact mul_nonneg hw (fm_nonneg (by linarith) (by nlinarith [ht.1]))
  · rw [h, (wF_of_two_le le_rfl).1]; simp

open Cvs.L2a.FarIntegrationByParts in
/-- **The near bound**: `L_near(m) ≤ (3/(4π²)) f_m(2) ≤ (3/(4π²)) · nearTerm m` for `m > 2`. -/
theorem Lnear_le {m : ℝ} (hm : 2 < m) : Lnear m ≤ 3 / (4 * π ^ 2) * nearTerm m := by
  have hπ : 0 < π ^ 2 := by have := pi_pos; positivity
  have hmono : ∫ t in (1 : ℝ)..2, (1 - wF t) * fm m t ≤ ∫ t in (1 : ℝ)..2, (1 - wF t) * fm m 2 := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le (by norm_num)]
      exact continuous_one_sub_wF.continuousOn.mul (continuousOn_fm hm)
    · exact (continuous_one_sub_wF.mul continuous_const).intervalIntegrable _ _
    · intro t ht
      have hw : 0 ≤ 1 - wF t := by linarith [(Cvs.L2a.FarFarBound.wF_bounds t).2.1]
      exact mul_le_mul_of_nonneg_left (fm_le_two hm (by nlinarith [ht.1, ht.2])) hw
  rw [intervalIntegral.integral_mul_const, integral_weight] at hmono
  unfold Lnear
  calc (π ^ 2)⁻¹ * ∫ t in (1 : ℝ)..2, (1 - wF t) * fm m t ≤ (π ^ 2)⁻¹ * (3 / 4 * fm m 2) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ ≤ (π ^ 2)⁻¹ * (3 / 4 * nearTerm m) := by
        gcongr; exact fm_two_le hm
    _ = 3 / (4 * π ^ 2) * nearTerm m := by field_simp

/-! ### The near tail and `r̄_bot` -/

/-- The near tail `Σ_{m ≥ 3} nearTerm m`. -/
def nearTail : ℝ := ∑' k : ℕ, nearTerm ((k + 3 : ℕ) : ℝ)

theorem nearTerm_nonneg {m : ℝ} (hm : 3 ≤ m) : 0 ≤ nearTerm m := by
  unfold nearTerm
  have h9 : 9 ≤ m ^ 2 := by nlinarith
  have : 2 / m ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  apply div_nonneg (by nlinarith)
  apply mul_nonneg (by nlinarith) (sq_nonneg _)

/-- `nearTerm m ≤ 1/((m − 1)m(m + 1)(m + 2))` for `m ≥ 6`. -/
theorem nearTerm_le_quartic {m : ℝ} (hm : 6 ≤ m) :
    nearTerm m ≤ 1 / ((m - 1) * m * (m + 1) * (m + 2)) := by
  unfold nearTerm
  have hm0 : 0 < m := by linarith
  have e : (m ^ 2 / 2 + 5 / 2 - 2 / m ^ 2) = (m ^ 4 + 5 * m ^ 2 - 4) / (2 * m ^ 2) := by
    field_simp; ring
  rw [e, div_div, div_le_div_iff₀ (by have : 0 < m ^ 2 - 4 := by nlinarith
                                      have : 0 < m ^ 2 - 2 := by nlinarith
                                      positivity) (by
    have : 0 < m - 1 := by linarith
    positivity)]
  have hpoly : 0 ≤ m ^ 6 / 2 - 2 * m ^ 5 - 6 * m ^ 4 + 8 * m ^ 3 + 17 / 2 * m ^ 2 - 8 * m - 2 := by
    have h1 : 0 ≤ m ^ 4 * (m ^ 2 / 2 - 2 * m - 6) := by
      apply mul_nonneg (by positivity); nlinarith
    have h2 : 0 ≤ 8 * m ^ 3 + 17 / 2 * m ^ 2 - 8 * m - 2 := by nlinarith
    nlinarith
  have hfac : 2 * m ^ 2 * (m ^ 2 - 4) * (m ^ 2 - 2) ^ 2 - (m ^ 4 + 5 * m ^ 2 - 4) * ((m - 1) * m * (m + 1) * (m + 2))
      = 2 * m * (m + 2) * (m ^ 6 / 2 - 2 * m ^ 5 - 6 * m ^ 4 + 8 * m ^ 3 + 17 / 2 * m ^ 2 - 8 * m - 2) := by
    ring
  nlinarith [mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * m) (by linarith : (0 : ℝ) ≤ m + 2)) hpoly]

/-- **The near tail, finite form**: `Σ_{3 ≤ m < N} nearTerm m ≤ Σ_{3 ≤ m < 8} nearTerm m + 1/1512`. -/
theorem sum_nearTerm_le (N : ℕ) :
    ∑ m ∈ Ico 3 N, nearTerm m ≤ ∑ m ∈ Ico (3 : ℕ) 8, nearTerm (m : ℝ) + 1 / 1512 := by
  have hnn : ∀ m ∈ Ico 3 (max N 8), 0 ≤ nearTerm (m : ℝ) := by
    intro m hm; simp only [mem_Ico] at hm
    exact nearTerm_nonneg (by exact_mod_cast hm.1)
  have hsub : ∑ m ∈ Ico 3 N, nearTerm m ≤ ∑ m ∈ Ico 3 (max N 8), nearTerm m :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico le_rfl (le_max_left _ _))
      (fun m hm _ => hnn m hm)
  refine hsub.trans ?_
  rw [← Finset.sum_Ico_consecutive _ (by norm_num : 3 ≤ 8) (le_max_right N 8)]
  gcongr
  set g : ℕ → ℝ := fun m => 1 / (3 * ((m : ℝ) - 1) * m * ((m : ℝ) + 1)) with hg
  have htel : ∀ m ∈ Ico 8 (max N 8), nearTerm (m : ℝ) ≤ g m - g (m + 1) := by
    intro m hm; simp only [mem_Ico] at hm
    have h8 : (8 : ℝ) ≤ m := by exact_mod_cast hm.1
    refine (nearTerm_le_quartic (by linarith)).trans (le_of_eq ?_)
    simp only [hg]; push_cast
    rw [show (m : ℝ) + 1 - 1 = m by ring]
    have : (m : ℝ) - 1 ≠ 0 := by linarith
    have : (m : ℝ) ≠ 0 := by linarith
    have : (m : ℝ) + 1 ≠ 0 := by linarith
    have : (m : ℝ) + 2 ≠ 0 := by linarith
    field_simp; ring
  calc ∑ m ∈ Ico 8 (max N 8), nearTerm (m : ℝ) ≤ ∑ m ∈ Ico 8 (max N 8), (g m - g (m + 1)) :=
        Finset.sum_le_sum htel
    _ = g 8 - g (max N 8) := sum_Ico_telescope g (le_max_right _ _)
    _ ≤ 1 / 1512 := by
        have : 0 ≤ g (max N 8) := by
          simp only [hg]
          have : (8 : ℝ) ≤ (max N 8 : ℕ) := by exact_mod_cast le_max_right N 8
          apply div_nonneg zero_le_one
          apply mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
        simp only [hg] at this ⊢; norm_num at this ⊢; linarith

theorem nearTerm_succ_nonneg (k : ℕ) : 0 ≤ nearTerm ((k + 3 : ℕ) : ℝ) :=
  nearTerm_nonneg (by push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])

theorem sum_range_nearTerm (n : ℕ) :
    ∑ k ∈ range n, nearTerm ((k + 3 : ℕ) : ℝ) = ∑ m ∈ Ico 3 (n + 3), nearTerm m := by
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  exact Finset.sum_congr rfl fun k _ => by rw [add_comm k 3]

theorem summable_nearTerm : Summable fun k : ℕ => nearTerm ((k + 3 : ℕ) : ℝ) :=
  summable_of_sum_range_le nearTerm_succ_nonneg fun n => by
    rw [sum_range_nearTerm]; exact sum_nearTerm_le _

/-- **The near tail**: `Σ_{m ≥ 3} nearTerm m ≤ 7/200`. -/
theorem nearTail_le : nearTail ≤ 7 / 200 := by
  have h : ∑ m ∈ Ico (3 : ℕ) 8, nearTerm (m : ℝ) + 1 / 1512 ≤ 7 / 200 := by
    simp only [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_zero, nearTerm]
    norm_num
  unfold nearTail
  refine Real.tsum_le_of_sum_range_le nearTerm_succ_nonneg fun n => ?_
  rw [sum_range_nearTerm]; exact (sum_nearTerm_le _).trans h

theorem nearTail_nonneg : 0 ≤ nearTail := tsum_nonneg nearTerm_succ_nonneg

theorem sum_Ico_nearTerm_le_nearTail (N : ℕ) : ∑ m ∈ Ico 3 N, nearTerm m ≤ nearTail := by
  rcases Nat.lt_or_ge N 3 with h | h
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]; exact nearTail_nonneg
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 3 := ⟨N - 3, by omega⟩
  rw [← sum_range_nearTerm]
  exact summable_nearTerm.sum_le_tsum _ (fun k _ => nearTerm_succ_nonneg k)

/-- `r̄_bot² = L_near(2) + (3/(4π²)) Σ_{m ≥ 3} nearTerm m + 5/(24π²)`. -/
def rbarBotSq : ℝ := Lnear 2 + 3 / (4 * π ^ 2) * nearTail + 5 / (24 * π ^ 2)

/-- **`r̄_bot` dominates every truncation of `r_bot(M)²`**: for `K ≤ M`,
`Σ_{2 ≤ m < K} (L_near(m) + L_far(m, M)) ≤ r̄_bot²`. -/
theorem rbot_le (M K : ℕ) (hK : K ≤ M) :
    ∑ m ∈ Ico 2 K, (Lnear m + Lfar m M) ≤ rbarBotSq := by
  have hπ : 0 < π ^ 2 := by have := pi_pos; positivity
  rw [Finset.sum_add_distrib]
  have hfar : ∑ m ∈ Ico 2 K, Lfar m M ≤ 5 / (24 * π ^ 2) := by
    refine le_trans ?_ (sum_Lfar_le M)
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico le_rfl hK)
    intro m hm _
    simp only [mem_Ico] at hm
    exact Lfar_nonneg (by exact_mod_cast hm.1) (by exact_mod_cast hm.2)
  have hnear : ∑ m ∈ Ico 2 K, Lnear m ≤ Lnear 2 + 3 / (4 * π ^ 2) * nearTail := by
    rcases Nat.lt_or_ge 2 K with h | h
    · rw [Finset.sum_eq_sum_Ico_succ_bot h]
      push_cast
      gcongr
      calc ∑ m ∈ Ico 3 K, Lnear m ≤ ∑ m ∈ Ico 3 K, 3 / (4 * π ^ 2) * nearTerm m := by
            apply Finset.sum_le_sum; intro m hm; simp only [mem_Ico] at hm
            have h3 : (3 : ℝ) ≤ m := by exact_mod_cast hm.1
            exact Lnear_le (by linarith)
        _ ≤ 3 / (4 * π ^ 2) * nearTail := by
            rw [← Finset.mul_sum]
            exact mul_le_mul_of_nonneg_left (sum_Ico_nearTerm_le_nearTail K) (by positivity)
    · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
      have := Lnear_nonneg (le_refl (2 : ℝ))
      have := nearTail_nonneg
      positivity
  unfold rbarBotSq
  linarith

/-! ### `Θ_m`, `N(M)` and the monotone step for `R̄₁` -/

open Cvs.L2a.FarIntegrationByParts in
/-- `Θ_m = (∫₁² w(t)²/(1 − t²/m²)² dt)^{1/2}`. -/
def Theta (m : ℝ) : ℝ := √(∫ t in (1 : ℝ)..2, (1 - wF t) ^ 2 / (1 - t ^ 2 / m ^ 2) ^ 2)

open Cvs.L2a.FarIntegrationByParts in
/-- `Θ_m ≤ (√11/4) m²/(m² − 4)` for `m > 2`, from `∫₁² w² = 11/16`. -/
theorem Theta_le {m : ℝ} (hm : 2 < m) : Theta m ≤ √11 / 4 * (m ^ 2 / (m ^ 2 - 4)) := by
  have hm4 : 0 < m ^ 2 - 4 := by nlinarith
  have hm0 : 0 < m ^ 2 := by positivity
  set c := m ^ 2 / (m ^ 2 - 4) with hc
  have hc0 : 0 ≤ c := by positivity
  have hden : ∀ t ∈ Set.Icc (1 : ℝ) 2, (m ^ 2 - 4) / m ^ 2 ≤ 1 - t ^ 2 / m ^ 2 := by
    intro t ht
    have : t ^ 2 ≤ 4 := by nlinarith [ht.1, ht.2]
    rw [show (m ^ 2 - 4) / m ^ 2 = 1 - 4 / m ^ 2 by field_simp]
    have : t ^ 2 / m ^ 2 ≤ 4 / m ^ 2 := div_le_div_of_nonneg_right this hm0.le
    linarith
  have hmono : ∫ t in (1 : ℝ)..2, (1 - wF t) ^ 2 / (1 - t ^ 2 / m ^ 2) ^ 2 ≤
      ∫ t in (1 : ℝ)..2, (1 - wF t) ^ 2 * c ^ 2 := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le (by norm_num)]
      apply (continuous_one_sub_wF.pow 2).continuousOn.div (by fun_prop)
      intro t ht
      have := hden t ht
      have : 0 < (m ^ 2 - 4) / m ^ 2 := by positivity
      exact pow_ne_zero _ (by linarith)
    · exact ((continuous_one_sub_wF.pow 2).mul continuous_const).intervalIntegrable _ _
    · intro t ht
      have h1 := hden t ht
      have h2 : 0 < (m ^ 2 - 4) / m ^ 2 := by positivity
      rw [div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      have hc' : c = ((m ^ 2 - 4) / m ^ 2)⁻¹ := by rw [hc, inv_div]
      rw [hc', inv_pow]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ h2.le h1 2)
  rw [intervalIntegral.integral_mul_const, integral_weight_sq] at hmono
  unfold Theta
  calc √(∫ t in (1 : ℝ)..2, (1 - wF t) ^ 2 / (1 - t ^ 2 / m ^ 2) ^ 2) ≤ √(11 / 16 * c ^ 2) :=
        Real.sqrt_le_sqrt hmono
    _ = √11 / 4 * c := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hc0, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 16),
          show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- `Σ_{a ≤ m < M} 1/(m − j) = H_{n+(M−a)} − H_n`, written with `a = n + 1 + j`. -/
theorem sum_inv_sub (M a j n : ℕ) (hn : a = n + 1 + j) :
    ∑ m ∈ Ico a M, 1 / ((m : ℝ) - j) = harmonic (n + (M - a)) - harmonic n := by
  rw [Finset.sum_Ico_eq_sum_range, harmonic, harmonic, Finset.sum_range_add]; push_cast
  rw [add_sub_cancel_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : ((a : ℝ) + k - j) = (n : ℝ) + k + 1 := by
    have : ((a : ℕ) : ℝ) = ((n + 1 + j : ℕ) : ℝ) := by rw [hn]
    push_cast at this; linarith
  rw [this, one_div]

/-- `Σ_{3 ≤ m < M} m/(m² − 4) = (H_{M−3} + H_{M+1} − 25/12)/2`. -/
theorem sum_div_sq_sub_four (M : ℕ) (hM : 3 ≤ M) :
    ∑ m ∈ Ico 3 M, (m : ℝ) / ((m : ℝ) ^ 2 - 4) =
      ((harmonic (M - 3) : ℝ) + harmonic (M + 1) - 25 / 12) / 2 := by
  have hpf : ∀ m ∈ Ico 3 M, (m : ℝ) / ((m : ℝ) ^ 2 - 4) =
      (1 / ((m : ℝ) - (2 : ℕ)) + 1 / ((m : ℝ) + (2 : ℕ))) / 2 := by
    intro m hm; simp only [mem_Ico] at hm
    have h3 : (3 : ℝ) ≤ m := by exact_mod_cast hm.1
    have : (m : ℝ) - 2 ≠ 0 := by linarith
    have : (m : ℝ) + 2 ≠ 0 := by linarith
    have : (m : ℝ) ^ 2 - 4 ≠ 0 := by nlinarith
    push_cast; field_simp; ring
  rw [Finset.sum_congr rfl hpf, ← Finset.sum_div, Finset.sum_add_distrib,
    sum_inv_sub M 3 2 0 rfl, sum_inv_add M 3 2 4 rfl]
  have e : 4 + (M - 3) = M + 1 := by omega
  rw [e, zero_add]
  have : (harmonic 4 : ℝ) = 25 / 12 := by norm_num [harmonic]
  rw [this]; simp only [harmonic_zero, Rat.cast_zero, sub_zero]; ring

/-- `N(M) = Θ₂/2 + (√11/8)(H_{M−3} + H_{M+1} − 25/12)`, with `Θ₂ = θ`. -/
def Nbar (θ : ℝ) (M : ℕ) : ℝ :=
  θ / 2 + √11 / 8 * ((harmonic (M - 3) : ℝ) + harmonic (M + 1) - 25 / 12)

/-- **`Σ Θ_m/m ≤ N(M)`**: any `Θ` with `Θ_m ≤ (√11/4) m²/(m² − 4)` for `m ≥ 3`. -/
theorem sum_div_le_Nbar (Θ : ℝ → ℝ) (hΘ : ∀ m : ℝ, 3 ≤ m → Θ m ≤ √11 / 4 * (m ^ 2 / (m ^ 2 - 4)))
    (M : ℕ) (hM : 3 ≤ M) : ∑ m ∈ Ico 2 M, Θ m / m ≤ Nbar (Θ 2) M := by
  rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : 2 < M)]
  unfold Nbar
  push_cast
  have h := sum_div_sq_sub_four M hM
  have : ∑ m ∈ Ico 3 M, Θ m / m ≤ ∑ m ∈ Ico 3 M, √11 / 4 * ((m : ℝ) / ((m : ℝ) ^ 2 - 4)) := by
    apply Finset.sum_le_sum; intro m hm; simp only [mem_Ico] at hm
    have h3 : (3 : ℝ) ≤ m := by exact_mod_cast hm.1
    have hb := hΘ m h3
    have : √11 / 4 * ((m : ℝ) ^ 2 / ((m : ℝ) ^ 2 - 4)) / m = √11 / 4 * ((m : ℝ) / ((m : ℝ) ^ 2 - 4)) := by
      have : (m : ℝ) ≠ 0 := by linarith
      field_simp
    rw [← this]
    exact div_le_div_of_nonneg_right hb (by linarith)
  rw [← Finset.mul_sum, h] at this
  linarith

theorem Nbar_three (θ : ℝ) : Nbar θ 3 = θ / 2 := by
  unfold Nbar; norm_num [harmonic]

theorem Nbar_four (θ : ℝ) : Nbar θ 4 = θ / 2 + 3 * √11 / 20 := by
  unfold Nbar; norm_num [harmonic]; ring

/-- `N(M + 1) = N(M) + (√11/4) M/(M² − 4)`. -/
theorem Nbar_succ (θ : ℝ) (M : ℕ) (hM : 3 ≤ M) :
    Nbar θ (M + 1) = Nbar θ M + √11 / 4 * ((M : ℝ) / ((M : ℝ) ^ 2 - 4)) := by
  unfold Nbar
  rw [show M + 1 - 3 = (M - 3) + 1 by omega, show M + 1 + 1 = (M + 1) + 1 by rfl, harmonic_succ,
    harmonic_succ]
  push_cast
  rw [Nat.cast_sub (by omega)]
  have hMr : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have : (M : ℝ) - ((3 : ℕ) : ℝ) + 1 = M - 2 := by norm_num; ring
  rw [this]
  have : (M : ℝ) - 2 ≠ 0 := by linarith
  have : (M : ℝ) + 1 + 1 ≠ 0 := by linarith
  have : (M : ℝ) ^ 2 - 4 ≠ 0 := by nlinarith
  field_simp
  ring

theorem Nbar_le_succ (θ : ℝ) (M : ℕ) (hM : 3 ≤ M) : Nbar θ M ≤ Nbar θ (M + 1) := by
  rw [Nbar_succ θ M hM]
  have hMr : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have : 0 ≤ (M : ℝ) / ((M : ℝ) ^ 2 - 4) := div_nonneg (by linarith) (by nlinarith)
  have : 0 ≤ √11 / 4 := by positivity
  nlinarith

theorem Nbar_mono (θ : ℝ) {M K : ℕ} (hM : 3 ≤ M) (hMK : M ≤ K) : Nbar θ M ≤ Nbar θ K := by
  induction K, hMK using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact ih.trans (Nbar_le_succ θ n (hM.trans hn))

theorem Nbar_nonneg {θ : ℝ} (hθ : 0 ≤ θ) (M : ℕ) (hM : 3 ≤ M) : 0 ≤ Nbar θ M := by
  have := Nbar_mono θ (le_refl 3) hM
  rw [Nbar_three] at this; linarith

/-- `R̄₁(M) = N(M)/(π√(M² − 1))`. -/
def R1bar (θ : ℝ) (M : ℕ) : ℝ := Nbar θ M / (π * √((M : ℝ) ^ 2 - 1))

/-- `(√2/π)√(ΔY M) · Σ_{2 ≤ m < M} Θ_m/m ≤ R̄₁(M)`, from `ΔY M < 1/(2(M² − 1))`. -/
theorem r1flat_le (Θ : ℝ → ℝ) (hΘ : ∀ m : ℝ, 3 ≤ m → Θ m ≤ √11 / 4 * (m ^ 2 / (m ^ 2 - 4)))
    (hΘ2 : 0 ≤ Θ 2) (M : ℕ) (hM : 3 ≤ M) :
    √2 / π * √(Cvs.L2a.TopCornerConstants.dY M) * ∑ m ∈ Ico 2 M, Θ m / m ≤ R1bar (Θ 2) M := by
  have hMr : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hS := sum_div_le_Nbar Θ hΘ M hM
  have hN := Nbar_nonneg hΘ2 M hM
  have hπ := pi_pos
  have hM1 : 0 < (M : ℝ) ^ 2 - 1 := by nlinarith
  have hsq : 0 < √((M : ℝ) ^ 2 - 1) := Real.sqrt_pos.2 hM1
  have hdY := Cvs.L2a.TopCornerConstants.dY_lt (by linarith : (1 : ℝ) < M)
  have hdY0 := Cvs.L2a.TopCornerConstants.dY_nonneg (by linarith : (1 : ℝ) < M)
  have hkey : √2 * √(Cvs.L2a.TopCornerConstants.dY M) ≤ 1 / √((M : ℝ) ^ 2 - 1) := by
    rw [← Real.sqrt_mul (by norm_num), one_div, ← Real.sqrt_inv]
    apply Real.sqrt_le_sqrt
    have : 2 * Cvs.L2a.TopCornerConstants.dY M < 2 * (1 / (2 * ((M : ℝ) ^ 2 - 1))) := by linarith
    rw [show 2 * (1 / (2 * ((M : ℝ) ^ 2 - 1))) = ((M : ℝ) ^ 2 - 1)⁻¹ by field_simp] at this
    exact this.le
  calc √2 / π * √(Cvs.L2a.TopCornerConstants.dY M) * ∑ m ∈ Ico 2 M, Θ m / m
      ≤ √2 / π * √(Cvs.L2a.TopCornerConstants.dY M) * Nbar (Θ 2) M :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ = (√2 * √(Cvs.L2a.TopCornerConstants.dY M)) * Nbar (Θ 2) M / π := by ring
    _ ≤ (1 / √((M : ℝ) ^ 2 - 1)) * Nbar (Θ 2) M / π := by gcongr
    _ = R1bar (Θ 2) M := by unfold R1bar; field_simp

/-- **The monotone step**: if `(5√11/36)(1 + √(8/5)) ≤ N(4)`, then `R̄₁(M + 1) ≤ R̄₁(M)` for `M ≥ 4`. -/
theorem R1bar_succ_le {θ : ℝ} (hstep : √11 / 4 * (5 / 9) * (1 + √(8 / 5)) ≤ Nbar θ 4)
    (M : ℕ) (hM : 4 ≤ M) : R1bar θ (M + 1) ≤ R1bar θ M := by
  have x4 : (4 : ℝ) ≤ M := by exact_mod_cast hM
  have hsucc := Nbar_succ θ M (by omega)
  have hN4 : Nbar θ 4 ≤ Nbar θ M := Nbar_mono θ (by norm_num) hM
  set N := Nbar θ M with hN
  set x : ℝ := (M : ℝ) with hx
  set δ := √11 / 4 * (x / (x ^ 2 - 4)) with hδ
  have hp1 : 0 < x ^ 2 - 1 := by nlinarith
  have hq1 : 0 < x ^ 2 + 2 * x := by nlinarith
  set p := √(x ^ 2 - 1) with hp
  set q := √(x ^ 2 + 2 * x) with hq
  set ρ := √(8 / 5 : ℝ) with hρ
  have hp0 : 0 < p := Real.sqrt_pos.2 hp1
  have hq0 : 0 < q := Real.sqrt_pos.2 hq1
  have hp2 : p ^ 2 = x ^ 2 - 1 := Real.sq_sqrt hp1.le
  have hq2 : q ^ 2 = x ^ 2 + 2 * x := Real.sq_sqrt hq1.le
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hqρ : q ≤ ρ * p := by
    rw [hq, hρ, hp, ← Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_le_sqrt; nlinarith
  have hpoly : δ * (x ^ 2 - 1) ≤ √11 / 4 * (5 / 9) * (2 * x + 1) := by
    rw [hδ]
    have h11 : 0 ≤ √11 / 4 := by positivity
    have hx4 : 0 < x ^ 2 - 4 := by nlinarith
    have : x / (x ^ 2 - 4) * (x ^ 2 - 1) ≤ 5 / 9 * (2 * x + 1) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hx4]
      nlinarith [mul_nonneg (sub_nonneg.2 x4) (by nlinarith : (0 : ℝ) ≤ x ^ 2 + 9 * x + 5)]
    calc √11 / 4 * (x / (x ^ 2 - 4)) * (x ^ 2 - 1) = √11 / 4 * (x / (x ^ 2 - 4) * (x ^ 2 - 1)) := by ring
      _ ≤ √11 / 4 * (5 / 9 * (2 * x + 1)) := mul_le_mul_of_nonneg_left this h11
      _ = _ := by ring
  have hδ0 : 0 ≤ δ := by
    rw [hδ]; apply mul_nonneg (by positivity); apply div_nonneg (by linarith); nlinarith
  -- `δ p (q + p) ≤ N (q² − p²)`
  have hmain : δ * p * (q + p) ≤ N * (q ^ 2 - p ^ 2) := by
    have h1 : δ * p * (q + p) ≤ δ * (x ^ 2 - 1) * (1 + ρ) := by
      rw [← hp2]
      have : p * (q + p) ≤ p ^ 2 * (1 + ρ) := by nlinarith
      nlinarith
    have h2 : δ * (x ^ 2 - 1) * (1 + ρ) ≤ √11 / 4 * (5 / 9) * (2 * x + 1) * (1 + ρ) :=
      mul_le_mul_of_nonneg_right hpoly (by linarith)
    have h3 : √11 / 4 * (5 / 9) * (2 * x + 1) * (1 + ρ) ≤ N * (2 * x + 1) := by
      have : √11 / 4 * (5 / 9) * (1 + ρ) ≤ N := hstep.trans hN4
      nlinarith
    rw [hq2, hp2]
    nlinarith
  have hstep2 : (N + δ) * p ≤ N * q := by
    have hqp : 0 < q + p := by linarith
    have : δ * p ≤ N * (q - p) := by
      have e : N * (q ^ 2 - p ^ 2) = N * (q - p) * (q + p) := by ring
      rw [e] at hmain
      exact le_of_mul_le_mul_right hmain hqp
    nlinarith
  unfold R1bar
  rw [hsucc]
  push_cast
  rw [← hx, show (x + 1) ^ 2 - 1 = x ^ 2 + 2 * x by ring, ← hq, ← hp]
  have hπ := pi_pos
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hstep2 hπ.le]

/-- **`R̄₁` is maximal at `M = 4`**, given the step at `4` and `R̄₁(3) ≤ R̄₁(4)`. -/
theorem R1bar_le_four {θ : ℝ} (hstep : √11 / 4 * (5 / 9) * (1 + √(8 / 5)) ≤ Nbar θ 4)
    (h3 : R1bar θ 3 ≤ R1bar θ 4) (M : ℕ) (hM : 3 ≤ M) : R1bar θ M ≤ R1bar θ 4 := by
  rcases Nat.lt_or_ge M 4 with h | h
  · have : M = 3 := by omega
    subst this; exact h3
  induction M, h using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact (R1bar_succ_le hstep n hn).trans (ih (by omega))

/-- `θ ≥ 11/10` gives the step at `4`. -/
theorem step_of_ge {θ : ℝ} (hθ : 11 / 10 ≤ θ) : √11 / 4 * (5 / 9) * (1 + √(8 / 5)) ≤ Nbar θ 4 := by
  rw [Nbar_four]
  have h11 : √11 ≤ 33167 / 10000 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h11' : 33166 / 10000 ≤ √11 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have h85 : √(8 / 5 : ℝ) ≤ 1265 / 1000 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h0 : 0 ≤ √11 := Real.sqrt_nonneg _
  have h0' : 0 ≤ √(8 / 5 : ℝ) := Real.sqrt_nonneg _
  nlinarith [mul_le_mul h11 h85 h0' (by norm_num)]

/-- `θ ≤ 13/5` gives `R̄₁(3) ≤ R̄₁(4)`. -/
theorem R1bar_three_le_four {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ 13 / 5) : R1bar θ 3 ≤ R1bar θ 4 := by
  unfold R1bar
  rw [Nbar_three, Nbar_four]
  norm_num
  have hπ := pi_pos
  have h8 : 0 < √8 := by positivity
  have h15 : 0 < √15 := by positivity
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have a1 : √15 ≤ 3873 / 1000 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have a2 : 2828 / 1000 ≤ √8 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have a3 : 33166 / 10000 ≤ √11 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have key : θ / 2 * √15 ≤ (θ / 2 + 3 * √11 / 20) * √8 := by
    nlinarith [mul_le_mul a3 a2 (by norm_num) (Real.sqrt_nonneg _), mul_nonneg hθ0 (Real.sqrt_nonneg 8)]
  nlinarith [mul_le_mul_of_nonneg_left key hπ.le]

/-- `r₁^glob` majorant `2√κ N(M)/√(M² − 1)`. -/
def r1globBar (κ θ : ℝ) (M : ℕ) : ℝ := 2 * √κ * Nbar θ M / √((M : ℝ) ^ 2 - 1)

theorem r1globBar_eq (κ θ : ℝ) (M : ℕ) : r1globBar κ θ M = 2 * √κ * π * R1bar θ M := by
  unfold r1globBar R1bar
  have := pi_pos
  rcases eq_or_ne (√((M : ℝ) ^ 2 - 1)) 0 with h | h
  · rw [h]; simp
  · field_simp

/-- **`r₁^glob` is antitone from `M = 4`** under the step at `4`. -/
theorem r1glob_antitone {κ θ : ℝ} (hstep : √11 / 4 * (5 / 9) * (1 + √(8 / 5)) ≤ Nbar θ 4)
    {M K : ℕ} (hM : 4 ≤ M) (hMK : M ≤ K) : r1globBar κ θ K ≤ r1globBar κ θ M := by
  rw [r1globBar_eq, r1globBar_eq]
  have hc : 0 ≤ 2 * √κ * π := by have := pi_pos; positivity
  apply mul_le_mul_of_nonneg_left _ hc
  induction K, hMK using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact (R1bar_succ_le hstep n (hM.trans hn)).trans ih

/-! ### `arcosh X/√X` and the far primitive -/

/-- **`arcosh X/√X ≤ 2√2/e`** for `X ≥ 1`, from `arcosh X ≤ log 2X` and `log y ≤ y/e`. -/
theorem arcosh_div_sqrt_le {X : ℝ} (hX : 1 ≤ X) : Real.arcosh X / √X ≤ 2 * √2 / exp 1 := by
  have hX0 : 0 < X := by linarith
  have hsX : 0 < √X := Real.sqrt_pos.2 hX0
  have h1 : Real.arcosh X ≤ Real.log (2 * X) := by
    unfold Real.arcosh
    have hs : √(X ^ 2 - 1) ≤ X := by
      rw [Real.sqrt_le_left (by linarith)]; linarith
    apply Real.log_le_log (by positivity) (by linarith)
  have h2X : 0 < 2 * X := by linarith
  have hy : 0 < √(2 * X) := Real.sqrt_pos.2 h2X
  have hlog : Real.log (2 * X) = 2 * Real.log √(2 * X) := by
    have : Real.log (2 * X) = Real.log (√(2 * X) ^ 2) := by rw [Real.sq_sqrt h2X.le]
    rw [this, Real.log_pow]; norm_num
  have he : 0 < exp 1 := exp_pos 1
  have hle : Real.log √(2 * X) ≤ √(2 * X) / exp 1 := by
    have := Real.log_le_sub_one_of_pos (div_pos hy he)
    rw [Real.log_div hy.ne' he.ne', Real.log_exp] at this
    linarith
  have h2 : √(2 * X) = √2 * √X := Real.sqrt_mul (by norm_num) X
  rw [div_le_div_iff₀ hsX he]
  calc Real.arcosh X * exp 1 ≤ Real.log (2 * X) * exp 1 := mul_le_mul_of_nonneg_right h1 he.le
    _ = 2 * Real.log √(2 * X) * exp 1 := by rw [hlog]
    _ ≤ 2 * (√(2 * X) / exp 1) * exp 1 := by gcongr
    _ = 2 * √2 * √X := by rw [h2]; field_simp

/-- The far primitive `F_M(x) = (log x − log(M + √(M² − x²)))/M`. -/
def farPrim (M x : ℝ) : ℝ := (Real.log x - Real.log (M + √(M ^ 2 - x ^ 2))) / M

/-- The far density `h_M(x) = 1/(x√(M² − x²))`. -/
def farDens (M x : ℝ) : ℝ := 1 / (x * √(M ^ 2 - x ^ 2))

theorem hasDerivAt_farPrim {M x : ℝ} (hx : 0 < x) (hxM : x < M) :
    HasDerivAt (farPrim M) (farDens M x) x := by
  have hM : 0 < M := by linarith
  have hq : 0 < M ^ 2 - x ^ 2 := by nlinarith
  set r := √(M ^ 2 - x ^ 2) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hq
  have hr2 : r ^ 2 = M ^ 2 - x ^ 2 := Real.sq_sqrt hq.le
  have d1 : HasDerivAt (fun y => M ^ 2 - y ^ 2) (-(2 * x)) x := by
    simpa using (hasDerivAt_pow 2 x).const_sub (M ^ 2)
  have d2 : HasDerivAt (fun y => √(M ^ 2 - y ^ 2)) (-(2 * x) / (2 * r)) x := d1.sqrt hq.ne'
  have d3 : HasDerivAt (fun y => Real.log (M + √(M ^ 2 - y ^ 2))) ((-(2 * x) / (2 * r)) / (M + r)) x :=
    (d2.const_add M).log (by positivity)
  have d4 := ((Real.hasDerivAt_log hx.ne').sub d3).div_const M
  have key : (x⁻¹ - (-(2 * x) / (2 * r)) / (M + r)) / M = farDens M x := by
    unfold farDens
    rw [← hr]
    have hMr : 0 < M + r := by linarith
    rw [div_eq_div_iff hM.ne' (by positivity)]
    field_simp
    linear_combination hr2
  exact d4.congr_deriv key

theorem farDens_pos {M x : ℝ} (hx : 0 < x) (hxM : x < M) : 0 < farDens M x := by
  have hq : 0 < M ^ 2 - x ^ 2 := by nlinarith
  unfold farDens; have := Real.sqrt_pos.2 hq; positivity

/-- Midpoint convexity of `h_M`: `h(m + y) + h(m − y) ≥ 2h(m)`. -/
theorem farDens_midpoint {M m y : ℝ} (hy : 0 ≤ y) (hmy : 0 < m - y) (hmyM : m + y < M) :
    2 * farDens M m ≤ farDens M (m + y) + farDens M (m - y) := by
  have hm : 0 < m := by linarith
  have hmM : m < M := by linarith
  have hA : 0 < M ^ 2 - (m + y) ^ 2 := by nlinarith
  have hB : 0 < M ^ 2 - (m - y) ^ 2 := by nlinarith
  have hC : 0 < M ^ 2 - m ^ 2 := by nlinarith
  set u := farDens M (m + y)
  set v := farDens M (m - y)
  set w := farDens M m
  have hu : 0 < u := farDens_pos (by linarith) hmyM
  have hv : 0 < v := farDens_pos hmy (by linarith)
  have hw : 0 < w := farDens_pos hm hmM
  -- `u v ≥ w²`
  have hprod : w ^ 2 ≤ u * v := by
    have ek : ∀ z : ℝ, 0 < z → z < M → farDens M z = 1 / √(z ^ 2 * (M ^ 2 - z ^ 2)) := by
      intro z hz hzM
      unfold farDens
      rw [Real.sqrt_mul (sq_nonneg z), Real.sqrt_sq hz.le]
    have ew : w ^ 2 = 1 / (m ^ 2 * (M ^ 2 - m ^ 2)) := by
      simp only [w]; rw [ek m hm hmM, div_pow, Real.sq_sqrt (by positivity)]; simp
    have euv : u * v = 1 / √((m + y) ^ 2 * (M ^ 2 - (m + y) ^ 2) * ((m - y) ^ 2 * (M ^ 2 - (m - y) ^ 2))) := by
      simp only [u, v]
      rw [ek _ (by linarith) hmyM, ek _ hmy (by linarith), one_div_mul_one_div,
        ← Real.sqrt_mul (show 0 ≤ (m + y) ^ 2 * (M ^ 2 - (m + y) ^ 2) by positivity)]
    rw [ew, euv]
    apply one_div_le_one_div_of_le (Real.sqrt_pos.2 (by positivity))
    rw [Real.sqrt_le_left (by positivity)]
    -- `k(m+y) k(m−y) ≤ k(m)²`
    have hP : ((m + y) * (m - y)) ^ 2 ≤ (m ^ 2) ^ 2 := by
      have h0 : 0 ≤ (m + y) * (m - y) := by nlinarith
      have h1 : (m + y) * (m - y) ≤ m ^ 2 := by nlinarith
      exact pow_le_pow_left₀ h0 h1 2
    have hQ : (M ^ 2 - (m + y) ^ 2) * (M ^ 2 - (m - y) ^ 2) ≤ (M ^ 2 - m ^ 2) ^ 2 := by
      have e : (M ^ 2 - (m + y) ^ 2) * (M ^ 2 - (m - y) ^ 2) = (M ^ 2 - m ^ 2 - y ^ 2) ^ 2 - 4 * m ^ 2 * y ^ 2 := by
        ring
      rw [e]
      have hs : 0 ≤ M ^ 2 - m ^ 2 - y ^ 2 := by nlinarith
      nlinarith [sq_nonneg (m * y)]
    have e2 : (m + y) ^ 2 * (M ^ 2 - (m + y) ^ 2) * ((m - y) ^ 2 * (M ^ 2 - (m - y) ^ 2)) =
        ((m + y) * (m - y)) ^ 2 * ((M ^ 2 - (m + y) ^ 2) * (M ^ 2 - (m - y) ^ 2)) := by ring
    rw [e2, show (m ^ 2 * (M ^ 2 - m ^ 2)) ^ 2 = (m ^ 2) ^ 2 * (M ^ 2 - m ^ 2) ^ 2 by ring]
    exact mul_le_mul hP hQ (by positivity) (by positivity)
  nlinarith [sq_nonneg (u - v), sq_nonneg (u + v - 2 * w)]

/-- **Hermite–Hadamard for `h_M`**: `h_M(m) ≤ F_M(m + 1/2) − F_M(m − 1/2)`. -/
theorem farDens_le_prim {M m : ℝ} (hm : 1 / 2 < m) (hmM : m + 1 / 2 < M) :
    farDens M m ≤ farPrim M (m + 1 / 2) - farPrim M (m - 1 / 2) := by
  set G : ℝ → ℝ := fun y => farPrim M (m + y) - farPrim M (m - y) - 2 * y * farDens M m with hG
  have hderiv : ∀ y ∈ Set.Icc (0 : ℝ) (1 / 2),
      HasDerivAt G (farDens M (m + y) + farDens M (m - y) - 2 * farDens M m) y := by
    intro y hy
    have h1 : HasDerivAt (fun y => farPrim M (m + y)) (farDens M (m + y)) y := by
      exact HasDerivAt.comp_const_add m y
        (hasDerivAt_farPrim (M := M) (x := m + y) (by linarith [hy.1]) (by linarith [hy.2]))
    have h2 : HasDerivAt (fun y => farPrim M (m - y)) (-farDens M (m - y)) y := by
      exact HasDerivAt.comp_const_sub m y
        (hasDerivAt_farPrim (M := M) (x := m - y) (by linarith [hy.2]) (by linarith [hy.1]))
    have h3 : HasDerivAt (fun y => 2 * y * farDens M m) (2 * farDens M m) y := by
      simpa using ((hasDerivAt_id y).const_mul 2).mul_const (farDens M m)
    exact ((h1.sub h2).sub h3).congr_deriv (by ring)
  have hmono : MonotoneOn G (Set.Icc 0 (1 / 2)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 (1 / 2))
    · intro y hy; exact (hderiv y hy).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      exact (hderiv y (Set.Ioo_subset_Icc_self hy)).hasDerivWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      have := farDens_midpoint (M := M) (m := m) (y := y) hy.1.le (by linarith [hy.2]) (by linarith [hy.2])
      linarith
  have := hmono ⟨le_rfl, by norm_num⟩ ⟨by norm_num, le_rfl⟩ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  simp only [hG, add_zero, sub_zero, mul_zero, zero_mul, sub_self] at this
  linarith

/-- `−F_M(a) = arcosh(M/a)/M` for `0 < a ≤ M`. -/
theorem neg_farPrim_eq {M a : ℝ} (ha : 0 < a) (haM : a ≤ M) :
    -farPrim M a = Real.arcosh (M / a) / M := by
  have hM : 0 < M := by linarith
  have hq : 0 ≤ M ^ 2 - a ^ 2 := by nlinarith
  unfold farPrim Real.arcosh
  have e : M / a + √((M / a) ^ 2 - 1) = (M + √(M ^ 2 - a ^ 2)) / a := by
    have : (M / a) ^ 2 - 1 = (M ^ 2 - a ^ 2) / a ^ 2 := by field_simp
    rw [this, Real.sqrt_div' _ (sq_nonneg a), Real.sqrt_sq ha.le]
    field_simp
  rw [e, Real.log_div (by positivity) ha.ne']
  ring

theorem farPrim_nonpos {M x : ℝ} (hx : 0 < x) (hxM : x ≤ M) : farPrim M x ≤ 0 := by
  have hM : 0 < M := by linarith
  unfold farPrim
  apply div_nonpos_of_nonpos_of_nonneg _ hM.le
  rw [sub_nonpos]
  exact Real.log_le_log hx (by have := Real.sqrt_nonneg (M ^ 2 - x ^ 2); linarith)

/-- **The far density sum**: `Σ_{a + 1/2 ≤ m < M} h_M(m) ≤ arcosh(M/a)/M` over integers, `a = m* − 1/2`. -/
theorem sum_farDens_le (ms M : ℕ) (hms : 1 ≤ ms) (hM : ms ≤ M) :
    ∑ m ∈ Ico ms M, farDens M m ≤ Real.arcosh (M / ((ms : ℝ) - 1 / 2)) / M := by
  have hmsr : (1 : ℝ) ≤ ms := by exact_mod_cast hms
  have hMr : (ms : ℝ) ≤ M := by exact_mod_cast hM
  have hle : ∑ m ∈ Ico ms M, farDens M m ≤
      ∑ m ∈ Ico ms M, (farPrim M ((m : ℝ) + 1 / 2) - farPrim M ((m : ℝ) - 1 / 2)) := by
    apply Finset.sum_le_sum; intro m hm; simp only [mem_Ico] at hm
    have h1 : (1 : ℝ) ≤ m := by exact_mod_cast (le_trans hms hm.1)
    have h2 : (m : ℝ) + 1 ≤ M := by exact_mod_cast hm.2
    exact farDens_le_prim (by linarith) (by linarith)
  have htel : ∑ m ∈ Ico ms M, (farPrim M ((m : ℝ) + 1 / 2) - farPrim M ((m : ℝ) - 1 / 2)) =
      farPrim M ((M : ℝ) - 1 / 2) - farPrim M ((ms : ℝ) - 1 / 2) := by
    have := sum_Ico_telescope (fun m : ℕ => -farPrim M ((m : ℝ) - 1 / 2)) hM
    simp only [Nat.cast_add, Nat.cast_one, show ∀ z : ℝ, z + 1 - 1 / 2 = z + 1 / 2 from
      fun z => by ring] at this
    rw [show farPrim M ((M : ℝ) - 1 / 2) - farPrim M ((ms : ℝ) - 1 / 2) =
      -farPrim M ((ms : ℝ) - 1 / 2) - -farPrim M ((M : ℝ) - 1 / 2) by ring, ← this]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [htel] at hle
  rcases eq_or_lt_of_le hM with h | h
  · subst h; simp only [Finset.Ico_self, Finset.sum_empty]
    apply div_nonneg (Real.arcosh_nonneg ?_) (by linarith)
    rw [le_div_iff₀ (by linarith)]; linarith
  have hMr' : (ms : ℝ) + 1 ≤ M := by exact_mod_cast h
  have hneg := farPrim_nonpos (M := M) (x := (M : ℝ) - 1 / 2) (by linarith) (by linarith)
  have heq := neg_farPrim_eq (M := M) (a := (ms : ℝ) - 1 / 2) (by linarith) (by linarith)
  linarith

/-! ### `T̄_bot` -/

/-- `𝔑_m = 2/(m² − 4) − 1/(m² − 1)`. -/
def nearN (m : ℝ) : ℝ := 2 / (m ^ 2 - 4) - 1 / (m ^ 2 - 1)

/-- `𝔉_m(M) = M/(M² − b_m²)`. -/
def farF (m M : ℝ) : ℝ := M / (M ^ 2 - bm m ^ 2)

/-- `θ(m*) = 1 − m*²/((m*² − 1)(2m* + 1))`. -/
def thetaT (m : ℝ) : ℝ := 1 - m ^ 2 / ((m ^ 2 - 1) * (2 * m + 1))

/-- `T̄_bot(m*) = 2√κ [1/(m* − 2) + θ^{−1/2}(1 − a^{−2})^{−1/2}(2√2/e) a^{−1/2}]`, `a = m* − 1/2`. -/
def Tbar (κ m : ℝ) : ℝ :=
  2 * √κ * (1 / (m - 2) + (√(thetaT m))⁻¹ * (√(1 - 1 / (m - 1 / 2) ^ 2))⁻¹ * (2 * √2 / exp 1)
    * (√(m - 1 / 2))⁻¹)

theorem sqrt_add_le_add {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : √(x + y) ≤ √x + √y := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, Real.sqrt_nonneg x, Real.sqrt_nonneg y,
    mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]

theorem nearN_nonneg {m : ℝ} (hm : 3 ≤ m) : 0 ≤ nearN m := by
  unfold nearN
  have h1 : 0 < m ^ 2 - 4 := by nlinarith
  have h2 : 0 < m ^ 2 - 1 := by nlinarith
  rw [sub_nonneg, div_le_div_iff₀ h2 h1]; nlinarith

/-- `√(𝔑_m/(m² − 1)) ≤ 1/(m − 2) − 1/(m − 1)` for `m ≥ 3`. -/
theorem sqrt_nearN_le {m : ℝ} (hm : 3 ≤ m) :
    √(nearN m / (m ^ 2 - 1)) ≤ 1 / (m - 2) - 1 / (m - 1) := by
  have h1 : 0 < m - 2 := by linarith
  have h2 : 0 < m - 1 := by linarith
  have e : 1 / (m - 2) - 1 / (m - 1) = 1 / ((m - 2) * (m - 1)) := by field_simp; ring
  rw [e]
  rw [Real.sqrt_le_left (by positivity)]
  have eN : nearN m / (m ^ 2 - 1) = (m ^ 2 + 2) / ((m ^ 2 - 4) * (m ^ 2 - 1) ^ 2) := by
    unfold nearN
    have : m ^ 2 - 4 ≠ 0 := by nlinarith
    have : m ^ 2 - 1 ≠ 0 := by nlinarith
    field_simp; ring
  have h4 : 0 < m ^ 2 - 4 := by nlinarith
  have h5 : 0 < m ^ 2 - 1 := by nlinarith
  rw [eN, div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  have key : (m ^ 2 - 4) * (m ^ 2 - 1) ^ 2 - (m ^ 2 + 2) * ((m - 2) * (m - 1)) ^ 2 =
      (m - 2) * (m - 1) ^ 2 * (6 * m ^ 2 + 3 * m + 6) := by ring
  have : 0 ≤ (m - 2) * (m - 1) ^ 2 * (6 * m ^ 2 + 3 * m + 6) := by positivity
  linarith

/-- `Σ_{m* ≤ m < M} √(𝔑_m/(m² − 1)) ≤ 1/(m* − 2)`. -/
theorem sum_sqrt_nearN_le (ms M : ℕ) (hms : 3 ≤ ms) :
    ∑ m ∈ Ico ms M, √(nearN m / ((m : ℝ) ^ 2 - 1)) ≤ 1 / ((ms : ℝ) - 2) := by
  have hmsr : (3 : ℝ) ≤ ms := by exact_mod_cast hms
  rcases Nat.lt_or_ge M ms with h | h
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    apply div_nonneg zero_le_one; linarith
  set g : ℕ → ℝ := fun m => 1 / ((m : ℝ) - 2) with hg
  calc ∑ m ∈ Ico ms M, √(nearN m / ((m : ℝ) ^ 2 - 1)) ≤ ∑ m ∈ Ico ms M, (g m - g (m + 1)) := by
        apply Finset.sum_le_sum; intro m hm; simp only [mem_Ico] at hm
        have h3 : (3 : ℝ) ≤ m := by exact_mod_cast le_trans hms hm.1
        refine (sqrt_nearN_le h3).trans (le_of_eq ?_)
        simp only [hg]; push_cast; ring
    _ = g ms - g M := sum_Ico_telescope g h
    _ ≤ 1 / ((ms : ℝ) - 2) := by
        have : 0 ≤ g M := by
          simp only [hg]
          have : (3 : ℝ) ≤ M := by exact_mod_cast le_trans hms h
          apply div_nonneg zero_le_one; linarith
        simp only [hg] at this ⊢; linarith

theorem thetaT_pos {m : ℝ} (hm : 2 ≤ m) : 0 < thetaT m := by
  unfold thetaT
  have h1 : 0 < (m ^ 2 - 1) * (2 * m + 1) := by apply mul_pos <;> nlinarith
  rw [sub_pos, div_lt_one h1]; nlinarith

/-- `M² − b_m² ≥ θ(m*)(M² − m²)` for `2 ≤ m* ≤ m ≤ M − 1`. -/
theorem gap_ge_theta {ms m M : ℝ} (hms : 2 ≤ ms) (hm : ms ≤ m) (hM : m + 1 ≤ M) :
    thetaT ms * (M ^ 2 - m ^ 2) ≤ M ^ 2 - bm m ^ 2 := by
  have hm2 : 2 ≤ m := by linarith
  have hb2 := bm_sq (by linarith : 1 < m)
  have h1 : 0 < m ^ 2 - 1 := by nlinarith
  have hs1 : 0 < ms ^ 2 - 1 := by nlinarith
  have hdec : m ^ 2 / ((m ^ 2 - 1) * (2 * m + 1)) ≤ ms ^ 2 / ((ms ^ 2 - 1) * (2 * ms + 1)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hA : m ^ 2 * (ms ^ 2 - 1) ≤ ms ^ 2 * (m ^ 2 - 1) := by nlinarith
    have hB : 2 * ms + 1 ≤ 2 * m + 1 := by linarith
    nlinarith [mul_le_mul hA hB (by positivity) (by positivity)]
  have hMm : 2 * m + 1 ≤ M ^ 2 - m ^ 2 := by nlinarith
  unfold thetaT
  rw [hb2]
  have e : M ^ 2 - m ^ 4 / (m ^ 2 - 1) = (M ^ 2 - m ^ 2) - m ^ 2 / (m ^ 2 - 1) := by
    field_simp; ring
  rw [e]
  have hk : m ^ 2 / (m ^ 2 - 1) ≤ ms ^ 2 / ((ms ^ 2 - 1) * (2 * ms + 1)) * (M ^ 2 - m ^ 2) := by
    calc m ^ 2 / (m ^ 2 - 1) = m ^ 2 / ((m ^ 2 - 1) * (2 * m + 1)) * (2 * m + 1) := by
          field_simp
      _ ≤ ms ^ 2 / ((ms ^ 2 - 1) * (2 * ms + 1)) * (M ^ 2 - m ^ 2) :=
          mul_le_mul hdec hMm (by linarith) (by positivity)
  nlinarith

/-- `√(𝔉_m(M)/(m² − 1)) ≤ θ^{−1/2}(1 − a^{−2})^{−1/2} √M h_M(m)` for `a ≤ m* ≤ m ≤ M − 1`. -/
theorem sqrt_farF_le {ms m M : ℝ} (hms : 3 ≤ ms) (hm : ms ≤ m) (hM : m + 1 ≤ M) :
    √(farF m M / (m ^ 2 - 1)) ≤
      (√(thetaT ms))⁻¹ * (√(1 - 1 / (ms - 1 / 2) ^ 2))⁻¹ * √M * farDens M m := by
  set a := ms - 1 / 2 with ha
  have ha1 : 5 / 2 ≤ a := by rw [ha]; linarith
  have hθ := thetaT_pos (by linarith : (2 : ℝ) ≤ ms)
  have hA : 0 < 1 - 1 / a ^ 2 := by
    have : 1 / a ^ 2 < 1 := by rw [div_lt_one (by positivity)]; nlinarith
    linarith
  have hm0 : 0 < m := by linarith
  have hM0 : 0 < M := by linarith
  have hq : 0 < M ^ 2 - m ^ 2 := by nlinarith
  have hgap := gap_ge_theta (by linarith) hm hM
  have hg0 : 0 < M ^ 2 - bm m ^ 2 := lt_of_lt_of_le (by positivity) hgap
  have hm1 : (1 - 1 / a ^ 2) * m ^ 2 ≤ m ^ 2 - 1 := by
    have : 1 ≤ m ^ 2 / a ^ 2 := by rw [le_div_iff₀ (by positivity)]; nlinarith
    have e : (1 - 1 / a ^ 2) * m ^ 2 = m ^ 2 - m ^ 2 / a ^ 2 := by field_simp
    linarith
  have hR : 0 ≤ (√(thetaT ms))⁻¹ * (√(1 - 1 / a ^ 2))⁻¹ * √M * farDens M m := by
    have := farDens_pos (M := M) (x := m) hm0 (by linarith); positivity
  rw [Real.sqrt_le_left hR]
  have eR : ((√(thetaT ms))⁻¹ * (√(1 - 1 / a ^ 2))⁻¹ * √M * farDens M m) ^ 2 =
      M / (thetaT ms * (1 - 1 / a ^ 2) * (m ^ 2 * (M ^ 2 - m ^ 2))) := by
    unfold farDens
    rw [mul_pow, mul_pow, mul_pow, inv_pow, inv_pow, Real.sq_sqrt hθ.le, Real.sq_sqrt hA.le,
      Real.sq_sqrt hM0.le, div_pow, mul_pow, Real.sq_sqrt hq.le]
    field_simp
  rw [eR]
  unfold farF
  rw [div_div, div_le_div_iff₀ (mul_pos hg0 (by nlinarith)) (by positivity)]
  apply mul_le_mul_of_nonneg_left _ hM0.le
  calc thetaT ms * (1 - 1 / a ^ 2) * (m ^ 2 * (M ^ 2 - m ^ 2))
      = (thetaT ms * (M ^ 2 - m ^ 2)) * ((1 - 1 / a ^ 2) * m ^ 2) := by ring
    _ ≤ (M ^ 2 - bm m ^ 2) * (m ^ 2 - 1) :=
        mul_le_mul hgap hm1 (by positivity) hg0.le

theorem farF_nonneg {m M : ℝ} (hm : 2 ≤ m) (hM : m + 1 ≤ M) : 0 ≤ farF m M := by
  have h := gap_ge_theta (le_refl m |>.trans' hm |> fun _ => hm) (le_refl m) hM
  have hθ := thetaT_pos hm
  have hq : 0 < M ^ 2 - m ^ 2 := by nlinarith
  unfold farF
  exact div_nonneg (by linarith) (le_trans (by positivity) h)

theorem Tbar_nonneg {κ m : ℝ} (hm : 3 ≤ m) : 0 ≤ Tbar κ m := by
  unfold Tbar
  have : 0 ≤ 1 / (m - 2) := div_nonneg zero_le_one (by linarith)
  have : 0 ≤ √(m - 1 / 2) := Real.sqrt_nonneg _
  positivity

/-- **`T̄_bot` dominates the bottom T0 tail uniformly in `M`**:
`2 Σ_{m* ≤ m < M} √(κ(𝔑_m + 𝔉_m(M))/(m² − 1)) ≤ T̄_bot(m*)` for `m* ≥ 3`. -/
theorem Tbot_le {κ : ℝ} (hκ : 0 ≤ κ) (ms M : ℕ) (hms : 3 ≤ ms) :
    2 * ∑ m ∈ Ico ms M, √(κ * (nearN m + farF m M) / ((m : ℝ) ^ 2 - 1)) ≤ Tbar κ ms := by
  have hmsr : (3 : ℝ) ≤ ms := by exact_mod_cast hms
  rcases Nat.lt_or_ge ms M with h | h
  swap
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, mul_zero]; exact Tbar_nonneg hmsr
  have hMr : (ms : ℝ) + 1 ≤ M := by exact_mod_cast h
  set a : ℝ := (ms : ℝ) - 1 / 2 with ha
  set C := (√(thetaT ms))⁻¹ * (√(1 - 1 / a ^ 2))⁻¹ with hC
  have hC0 : 0 ≤ C := by positivity
  have hterm : ∀ m ∈ Ico ms M, √(κ * (nearN m + farF m M) / ((m : ℝ) ^ 2 - 1)) ≤
      √κ * (√(nearN m / ((m : ℝ) ^ 2 - 1)) + C * √M * farDens M m) := by
    intro m hm; simp only [mem_Ico] at hm
    have h3 : (ms : ℝ) ≤ m := by exact_mod_cast hm.1
    have h4 : (m : ℝ) + 1 ≤ M := by exact_mod_cast hm.2
    have hm1 : 0 < (m : ℝ) ^ 2 - 1 := by nlinarith
    rw [mul_div_assoc, Real.sqrt_mul hκ, add_div]
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    refine (sqrt_add_le_add (div_nonneg (nearN_nonneg (by linarith)) hm1.le)
      (div_nonneg (farF_nonneg (by linarith) h4) hm1.le)).trans ?_
    gcongr
    have := sqrt_farF_le hmsr h3 h4
    rw [hC]; convert this using 2
  calc 2 * ∑ m ∈ Ico ms M, √(κ * (nearN m + farF m M) / ((m : ℝ) ^ 2 - 1))
      ≤ 2 * ∑ m ∈ Ico ms M, √κ * (√(nearN m / ((m : ℝ) ^ 2 - 1)) + C * √M * farDens M m) := by
        gcongr with m hm; exact hterm m hm
    _ = 2 * √κ * (∑ m ∈ Ico ms M, √(nearN m / ((m : ℝ) ^ 2 - 1)) +
          C * √M * ∑ m ∈ Ico ms M, farDens M m) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]; ring
    _ ≤ 2 * √κ * (1 / ((ms : ℝ) - 2) + C * √M * (Real.arcosh (M / a) / M)) := by
        gcongr
        · exact sum_sqrt_nearN_le ms M hms
        · exact sum_farDens_le ms M (by omega) h.le
    _ ≤ Tbar κ ms := by
        unfold Tbar
        rw [← ha, ← hC]
        have ha0 : 0 < a := by rw [ha]; linarith
        have hM0 : 0 < (M : ℝ) := by linarith
        have hX : 1 ≤ (M : ℝ) / a := by rw [le_div_iff₀ ha0]; linarith
        have hb := arcosh_div_sqrt_le hX
        have e : √M * (Real.arcosh (M / a) / M) = Real.arcosh (M / a) / √((M : ℝ) / a) * (√a)⁻¹ := by
          rw [Real.sqrt_div' _ ha0.le]
          have : 0 < √(M : ℝ) := Real.sqrt_pos.2 hM0
          have : 0 < √a := Real.sqrt_pos.2 ha0
          field_simp
          rw [Real.sq_sqrt hM0.le]
        have hfar : C * √M * (Real.arcosh (M / a) / M) ≤ C * (2 * √2 / exp 1) * (√a)⁻¹ := by
          rw [mul_assoc C, e, mul_assoc C]
          apply mul_le_mul_of_nonneg_left _ hC0
          exact mul_le_mul_of_nonneg_right hb (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith

/-! ### Two-sided bounds on `Θ₂` -/

open Cvs.L2a.FarIntegrationByParts in
/-- The `Θ₂²` integrand `w(t)²/(1 − t²/4)²`. -/
def theta2Int (t : ℝ) : ℝ := (1 - wF t) ^ 2 / (1 - t ^ 2 / 2 ^ 2) ^ 2

theorem Theta_two_sq : Theta 2 = √(∫ t in (1 : ℝ)..2, theta2Int t) := rfl

open Cvs.L2a.FarIntegrationByParts in
theorem theta2Int_eq (t : ℝ) :
    theta2Int t = 16 * (1 - wF t) ^ 2 / ((2 - t) ^ 2 * (2 + t) ^ 2) := by
  unfold theta2Int
  rw [show (1 - t ^ 2 / 2 ^ 2) ^ 2 = (2 - t) ^ 2 * (2 + t) ^ 2 / 16 by ring, div_div_eq_mul_div]
  ring

theorem theta2Int_nonneg (t : ℝ) : 0 ≤ theta2Int t := by
  unfold theta2Int; positivity

open Cvs.L2a.FarIntegrationByParts in
theorem theta2Int_le_cap (t : ℝ) : theta2Int t ≤ 16 / ((2 - t) ^ 2 * (2 + t) ^ 2) := by
  rw [theta2Int_eq]
  have h0 : 0 ≤ 1 - wF t := by linarith [(Cvs.L2a.FarFarBound.wF_bounds t).2.1]
  have h1 : 1 - wF t ≤ 1 := by linarith [(Cvs.L2a.FarFarBound.wF_bounds t).1]
  have : (1 - wF t) ^ 2 ≤ 1 := by nlinarith
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

open Cvs.L2a.FarIntegrationByParts in
/-- `w(t)²/(1 − t²/4)² ≤ 16π⁴(2 − t)²/(2 + t)²`, from `w ≤ π²(2 − t)²`. -/
theorem theta2Int_le_quad {t : ℝ} (ht : 1 ≤ t) : theta2Int t ≤ 16 * π ^ 4 * (2 - t) ^ 2 / (2 + t) ^ 2 := by
  rcases eq_or_ne t 2 with h | h
  · subst h; unfold theta2Int; norm_num
  rw [theta2Int_eq]
  have h0 : 0 ≤ 1 - wF t := by linarith [(Cvs.L2a.FarFarBound.wF_bounds t).2.1]
  have h1 := Cvs.L2a.RampTopQuadratic.one_sub_wF_le t
  have hs : (2 - t) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.2 (Ne.symm h))
  have h2 : (1 - wF t) ^ 2 ≤ π ^ 4 * (2 - t) ^ 4 := by
    have := pow_le_pow_left₀ h0 h1 2; nlinarith
  calc 16 * (1 - wF t) ^ 2 / ((2 - t) ^ 2 * (2 + t) ^ 2)
      ≤ 16 * (π ^ 4 * (2 - t) ^ 4) / ((2 - t) ^ 2 * (2 + t) ^ 2) := by gcongr
    _ = 16 * π ^ 4 * (2 - t) ^ 2 / (2 + t) ^ 2 := by
        have : (2 + t) ^ 2 ≠ 0 := by positivity
        field_simp

open Cvs.L2a.FarIntegrationByParts in
theorem theta2Int_ge {t : ℝ} (ht1 : 1 ≤ t) (ht2 : t ≤ 3 / 2) :
    1 / (2 - t) ^ 2 + 7 / 16 ≤ theta2Int t := by
  rw [theta2Int_eq, Cvs.L2a.FarFarBound.wF_eq_zero_of_le ht2]
  have ha : 0 < 2 - t := by linarith
  have hb : 0 < 2 + t := by linarith
  rw [div_add' _ _ _ (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  have key : (1 + 7 / 16 * (2 - t) ^ 2) * (2 + t) ^ 2 ≤ 16 := by
    have u0 : 0 ≤ t - 1 := by linarith
    have u1 : 0 ≤ 3 / 2 - t := by linarith
    nlinarith [mul_nonneg u0 u1, mul_nonneg (mul_nonneg u0 u1) u0, mul_nonneg (mul_nonneg u0 u1) u1,
      mul_nonneg u0 u0, mul_nonneg u1 u1]
  nlinarith [mul_le_mul_of_nonneg_left key (sq_nonneg (2 - t))]

theorem measurable_theta2Int : Measurable theta2Int := by
  unfold theta2Int
  exact ((continuous_one_sub_wF.pow 2).measurable).div (by fun_prop)

theorem intervalIntegrable_theta2Int : IntervalIntegrable theta2Int MeasureTheory.volume 1 2 := by
  refine IntervalIntegrable.mono_fun' (g := fun _ => 16 * π ^ 4) intervalIntegrable_const
    measurable_theta2Int.aestronglyMeasurable ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc fun t ht => ?_
  rw [Set.uIoc_of_le (by norm_num)] at ht
  show ‖theta2Int t‖ ≤ 16 * π ^ 4
  rw [Real.norm_of_nonneg (theta2Int_nonneg t)]
  refine (theta2Int_le_quad ht.1.le).trans ?_
  have h1 : (2 - t) ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
  have h2 : 1 ≤ (2 + t) ^ 2 := by nlinarith [ht.1, ht.2]
  rw [div_le_iff₀ (by positivity)]
  have : 0 ≤ 16 * π ^ 4 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 this, mul_le_mul_of_nonneg_left h2 this]

/-- **`Θ₂² ≥ 39/32`**, from `w = 1` on `[1, 3/2]`. -/
theorem theta2_sq_ge : 39 / 32 ≤ ∫ t in (1 : ℝ)..2, theta2Int t := by
  have hI := intervalIntegrable_theta2Int
  have s1 : Set.uIcc (1 : ℝ) (3 / 2) ⊆ Set.uIcc 1 2 := by
    rw [Set.uIcc_of_le (by norm_num), Set.uIcc_of_le (by norm_num)]
    exact Set.Icc_subset_Icc le_rfl (by norm_num)
  have s2 : Set.uIcc (3 / 2 : ℝ) 2 ⊆ Set.uIcc 1 2 := by
    rw [Set.uIcc_of_le (by norm_num), Set.uIcc_of_le (by norm_num)]
    exact Set.Icc_subset_Icc (by norm_num) le_rfl
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 3 / 2) (hI.mono_set s1) (hI.mono_set s2)]
  have h2 : 0 ≤ ∫ t in (3 / 2 : ℝ)..2, theta2Int t :=
    intervalIntegral.integral_nonneg (by norm_num) fun t _ => theta2Int_nonneg t
  have hderiv : ∀ x ∈ Set.uIcc (1 : ℝ) (3 / 2),
      HasDerivAt (fun t => (2 - t)⁻¹ + 7 / 16 * t) (1 / (2 - x) ^ 2 + 7 / 16) x := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    have hne : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have := (((hasDerivAt_id' x).const_sub 2).inv hne).add ((hasDerivAt_id' x).const_mul (7 / 16))
    exact this.congr_deriv (by field_simp)
  have hcont : IntervalIntegrable (fun x : ℝ => 1 / (2 - x) ^ 2 + 7 / 16) MeasureTheory.volume 1 (3 / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num)]
    apply ContinuousOn.add _ continuousOn_const
    have c1 : ContinuousOn (fun x : ℝ => (2 - x) ^ 2) (Set.Icc 1 (3 / 2)) := by fun_prop
    have h : ∀ x ∈ Set.Icc (1 : ℝ) (3 / 2), (2 - x) ^ 2 ≠ 0 := by
      intro x hx; have : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
      positivity
    exact ContinuousOn.div₀ (f := fun _ : ℝ => (1 : ℝ)) continuousOn_const c1 h
  have h1 : ∫ t in (1 : ℝ)..(3 / 2), (1 / (2 - t) ^ 2 + 7 / 16) ≤ ∫ t in (1 : ℝ)..(3 / 2), theta2Int t := by
    apply intervalIntegral.integral_mono_on (by norm_num) hcont (hI.mono_set s1)
    intro t ht; exact theta2Int_ge ht.1 ht.2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont] at h1
  norm_num at h1
  linarith

/-- **`Θ₂ ≥ 11/10`**. -/
theorem Theta_two_ge : 11 / 10 ≤ Theta 2 := by
  rw [Theta_two_sq, Real.le_sqrt (by norm_num) (by linarith [theta2_sq_ge])]
  linarith [theta2_sq_ge]

/-- The capped closed form on `[1, 2 − 1/π]`: `π − 1/(4 − 1/π) + (log(4 − 1/π) + log π − log 3)/2 − 2/3`. -/
def thetaA : ℝ := π - 1 / (4 - 1 / π) + (Real.log (4 - 1 / π) + Real.log π - Real.log 3) / 2 - 2 / 3

/-- The quadratic closed form on `[2 − 1/π, 2]`: `π/3 + 1/8 + 3/(80π) + 1/(96π²) + 3/(896π³)`. -/
def thetaB : ℝ := π / 3 + 1 / 8 + 3 / (80 * π) + 1 / (96 * π ^ 2) + 3 / (896 * π ^ 3)

/-- The quartic majorant `π⁴ s² (1 + s/2 + 3s²/16 + s³/16 + 3s⁴/128)` of `16π⁴s²/(4 − s)²`. -/
def polyB (s : ℝ) : ℝ := π ^ 4 * (s ^ 2 + s ^ 3 / 2 + 3 * s ^ 4 / 16 + s ^ 5 / 16 + 3 * s ^ 6 / 128)

theorem sq_div_le_polyB {s : ℝ} (hs : s ≤ 1 / 3) :
    16 * π ^ 4 * s ^ 2 / (4 - s) ^ 2 ≤ polyB s := by
  have h4 : 0 < (4 - s) ^ 2 := by have : 0 < 4 - s := by linarith
                                  positivity
  rw [div_le_iff₀ h4]
  unfold polyB
  have key : (4 - s) ^ 2 * (1 + s / 2 + 3 * s ^ 2 / 16 + s ^ 3 / 16 + 3 * s ^ 4 / 128) - 16 =
      s ^ 4 * (1 / 16 - s / 8 + 3 * s ^ 2 / 128) := by ring
  have : 0 ≤ s ^ 4 * (1 / 16 - s / 8 + 3 * s ^ 2 / 128) := by
    apply mul_nonneg (by positivity); nlinarith
  have hp : 0 ≤ π ^ 4 * s ^ 2 := by positivity
  nlinarith [mul_nonneg hp this]

/-- **`Θ₂² ≤ thetaA + thetaB`**: `w ≤ 1` on `[1, 2 − 1/π]` and `w ≤ π²(2 − t)²` on `[2 − 1/π, 2]`. -/
theorem theta2_sq_le : ∫ t in (1 : ℝ)..2, theta2Int t ≤ thetaA + thetaB := by
  have hπ := pi_gt_three
  have hπ0 : 0 < π := pi_pos
  set c : ℝ := 2 - 1 / π with hc
  have hq : 1 / π < 1 / 3 := by rw [div_lt_div_iff₀ hπ0 (by norm_num)]; linarith
  have hq0 : 0 < 1 / π := by positivity
  have hc1 : 1 ≤ c := by rw [hc]; linarith
  have hc2 : c < 2 := by rw [hc]; linarith
  have hI := intervalIntegrable_theta2Int
  have s1 : Set.uIcc (1 : ℝ) c ⊆ Set.uIcc 1 2 := by
    rw [Set.uIcc_of_le hc1, Set.uIcc_of_le (by norm_num)]
    exact Set.Icc_subset_Icc le_rfl hc2.le
  have s2 : Set.uIcc c 2 ⊆ Set.uIcc 1 2 := by
    rw [Set.uIcc_of_le hc2.le, Set.uIcc_of_le (by norm_num)]
    exact Set.Icc_subset_Icc hc1 le_rfl
  have hIA : IntervalIntegrable theta2Int MeasureTheory.volume 1 c := hI.mono_set s1
  have hIB : IntervalIntegrable theta2Int MeasureTheory.volume c 2 := hI.mono_set s2
  rw [← intervalIntegral.integral_add_adjacent_intervals hIA hIB]
  -- the capped piece
  set gA : ℝ → ℝ := fun t => 16 / ((2 - t) ^ 2 * (2 + t) ^ 2) with hgA
  set G : ℝ → ℝ := fun t => (2 - t)⁻¹ - (2 + t)⁻¹ + (Real.log (2 + t) - Real.log (2 - t)) / 2 with hG
  have hGd : ∀ x ∈ Set.uIcc 1 c, HasDerivAt G (gA x) x := by
    intro x hx
    rw [Set.uIcc_of_le hc1] at hx
    have h1 : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
    have h2 : 0 < (2 : ℝ) + x := by linarith [hx.1]
    have d1 := ((hasDerivAt_id' x).const_sub 2).inv h1
    have d2 := ((hasDerivAt_id' x).const_add 2).inv h2.ne'
    have d3 := ((hasDerivAt_id' x).const_add 2).log h2.ne'
    have d4 := ((hasDerivAt_id' x).const_sub 2).log h1
    refine ((d1.sub d2).add ((d3.sub d4).div_const 2)).congr_deriv ?_
    simp only [hgA]
    have : (2 : ℝ) + x ≠ 0 := h2.ne'
    field_simp
    ring
  have hgAc : IntervalIntegrable gA MeasureTheory.volume 1 c := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hc1]
    have c0 : Continuous (fun x : ℝ => (2 - x) ^ 2 * (2 + x) ^ 2) :=
      ((continuous_const.sub continuous_id).pow 2).mul ((continuous_const.add continuous_id).pow 2)
    have c1 : ContinuousOn (fun x : ℝ => (2 - x) ^ 2 * (2 + x) ^ 2) (Set.Icc 1 c) := c0.continuousOn
    have h : ∀ x ∈ Set.Icc (1 : ℝ) c, (2 - x) ^ 2 * (2 + x) ^ 2 ≠ 0 := by
      intro x hx
      have : (2 : ℝ) - x ≠ 0 := by linarith [hx.2]
      have : (2 : ℝ) + x ≠ 0 := by linarith [hx.1]
      positivity
    exact ContinuousOn.div₀ (f := fun _ : ℝ => (16 : ℝ)) continuousOn_const c1 h
  have hA : ∫ t in (1 : ℝ)..c, theta2Int t ≤ thetaA := by
    have hmono : ∫ t in (1 : ℝ)..c, theta2Int t ≤ ∫ t in (1 : ℝ)..c, gA t :=
      intervalIntegral.integral_mono_on hc1 hIA hgAc (fun t _ => theta2Int_le_cap t)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hGd hgAc] at hmono
    refine hmono.trans (le_of_eq ?_)
    simp only [hG, hc]
    rw [show (2 : ℝ) - (2 - 1 / π) = π⁻¹ by ring, show (2 : ℝ) + (2 - 1 / π) = 4 - 1 / π by ring,
      Real.log_inv, inv_inv]
    unfold thetaA
    norm_num
    ring
  -- the quadratic piece
  have hgB : ∀ t ∈ Set.Icc c 2, theta2Int t ≤ polyB (2 - t) := by
    intro t ht
    refine (theta2Int_le_quad (by linarith [ht.1])).trans ?_
    have h := sq_div_le_polyB (s := 2 - t) (by rw [hc] at ht; linarith [ht.1])
    rw [show (2 : ℝ) + t = 4 - (2 - t) by ring]
    exact h
  have hpolyc : Continuous polyB := by unfold polyB; fun_prop
  have hB : ∫ t in c..2, theta2Int t ≤ thetaB := by
    have hcB : Continuous fun t => polyB (2 - t) := by unfold polyB; fun_prop
    have hmono := intervalIntegral.integral_mono_on hc2.le hIB (hcB.intervalIntegrable _ _) hgB
    rw [intervalIntegral.integral_comp_sub_left (fun s => polyB s) 2] at hmono
    rw [show (2 : ℝ) - 2 = 0 by ring, show (2 : ℝ) - c = 1 / π by rw [hc]; ring] at hmono
    set QB : ℝ → ℝ := fun s => π ^ 4 * (s ^ 3 / 3 + s ^ 4 / 8 + 3 * s ^ 5 / 80 + s ^ 6 / 96 + 3 * s ^ 7 / 896)
      with hQB
    have hQ : ∀ x ∈ Set.uIcc 0 (1 / π), HasDerivAt QB (polyB x) x := by
      intro x _
      have e3 := (hasDerivAt_pow 3 x).div_const 3
      have e4 := (hasDerivAt_pow 4 x).div_const 8
      have e5 := ((hasDerivAt_pow 5 x).const_mul 3).div_const 80
      have e6 := (hasDerivAt_pow 6 x).div_const 96
      have e7 := ((hasDerivAt_pow 7 x).const_mul 3).div_const 896
      have := ((((e3.add e4).add e5).add e6).add e7).const_mul (π ^ 4)
      refine this.congr_deriv ?_
      unfold polyB; push_cast; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hQ (hpolyc.intervalIntegrable _ _)] at hmono
    refine hmono.trans (le_of_eq ?_)
    simp only [hQB]
    unfold thetaB
    field_simp
    ring
  linarith

/-- **Certified evaluation**: `thetaA + thetaB ≤ 4.06344`. -/
theorem thetaAB_le : thetaA + thetaB ≤ 406344 / 100000 := by
  have h1 : (3141592 / 1000000 : ℝ) < π := by have := Real.pi_gt_d6; norm_num at this ⊢; linarith
  have h2 : π < (3141593 / 1000000 : ℝ) := by have := Real.pi_lt_d6; norm_num at this ⊢; linarith
  have hπ0 : 0 < π := pi_pos
  set x : ℝ := (13 - 4 * π) / 12 with hx
  have hxlo : (361356 : ℝ) / 10 ^ 7 ≤ x := by rw [hx]; linarith
  have hxhi : x ≤ (361361 : ℝ) / 10 ^ 7 := by rw [hx]; linarith
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hxlo
  have hlog : Real.log (4 - 1 / π) + Real.log π - Real.log 3 = 2 * Real.log 2 + Real.log (1 - x) := by
    have h4 : 0 < 4 - 1 / π := by
      have : 1 / π < 1 := by rw [div_lt_one hπ0]; linarith
      linarith
    rw [← Real.log_mul h4.ne' hπ0.ne', ← Real.log_div (by positivity) (by norm_num)]
    rw [show (4 - 1 / π) * π / 3 = 2 ^ 2 * (1 - x) by rw [hx]; field_simp; ring]
    rw [Real.log_mul (by norm_num) (by linarith), Real.log_pow]
    push_cast; ring
  have hser := Real.abs_log_sub_add_sum_range_le (x := x) (by rw [abs_lt]; constructor <;> linarith) 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_of_pos hx0] at hser
  have hlog1 : Real.log (1 - x) ≤ -(x + x ^ 2 / 2 + x ^ 3 / 3) + x ^ 4 / (1 - x) := by
    have := (abs_le.1 hser).2
    norm_num at this ⊢
    linarith
  have hx4 : x ^ 4 / (1 - x) ≤ 2 * ((361361 : ℝ) / 10 ^ 7) ^ 4 := by
    rw [div_le_iff₀ (by linarith)]
    have : x ^ 4 ≤ ((361361 : ℝ) / 10 ^ 7) ^ 4 := pow_le_pow_left₀ hx0.le hxhi 4
    have : 0 ≤ x ^ 4 := by positivity
    nlinarith
  have hx2 : ((361356 : ℝ) / 10 ^ 7) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by norm_num) hxlo 2
  have hx3 : ((361356 : ℝ) / 10 ^ 7) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) hxlo 3
  have hl2 := Real.log_two_lt_d9
  have hinv : 1 / (4 - 1 / (3141593 / 1000000 : ℝ)) ≤ 1 / (4 - 1 / π) := by
    have a : 1 / (3141593 / 1000000 : ℝ) ≤ 1 / π :=
      one_div_le_one_div_of_le hπ0 h2.le
    have b : 0 < 4 - 1 / π := by
      have : 1 / π < 1 := by rw [div_lt_one hπ0]; linarith
      linarith
    exact one_div_le_one_div_of_le b (by linarith)
  have hb1 : 3 / (80 * π) ≤ 3 / (80 * (3141592 / 1000000 : ℝ)) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hb2 : 1 / (96 * π ^ 2) ≤ 1 / (96 * (3141592 / 1000000 : ℝ) ^ 2) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    have := pow_le_pow_left₀ (by norm_num) h1.le 2; linarith
  have hb3 : 3 / (896 * π ^ 3) ≤ 3 / (896 * (3141592 / 1000000 : ℝ) ^ 3) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    have := pow_le_pow_left₀ (by norm_num) h1.le 3; linarith
  unfold thetaA thetaB
  rw [hlog]
  norm_num at hinv hb1 hb2 hb3 hx2 hx3 hx4 ⊢
  linarith

/-- **`Θ₂ ≤ 2.0158`**. -/
theorem Theta_two_le : Theta 2 ≤ 20158 / 10000 := by
  rw [Theta_two_sq, Real.sqrt_le_left (by norm_num)]
  linarith [theta2_sq_le, thetaAB_le]

/-- **`R̄₁` is maximal at `M = 4`** at `θ = Θ₂`. -/
theorem R1bar_Theta_le_four (M : ℕ) (hM : 3 ≤ M) : R1bar (Theta 2) M ≤ R1bar (Theta 2) 4 :=
  R1bar_le_four (step_of_ge Theta_two_ge)
    (R1bar_three_le_four (by linarith [Theta_two_ge]) (by linarith [Theta_two_le])) M hM

/-- **Certified evaluation**: `R̄₁(4) ≤ 0.1238` at `θ = Θ₂`. -/
theorem R1bar_four_le : R1bar (Theta 2) 4 ≤ 1238 / 10000 := by
  unfold R1bar
  rw [Nbar_four]
  have hθ := Theta_two_le
  have hπ : (314159 / 100000 : ℝ) ≤ π := by have := Real.pi_gt_d6; norm_num at this ⊢; linarith
  have h15 : (38729 / 10000 : ℝ) ≤ √((4 : ℕ) ^ 2 - 1 : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have h11 : √11 ≤ 33167 / 10000 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hden : (314159 / 100000 : ℝ) * (38729 / 10000) ≤ π * √((4 : ℕ) ^ 2 - 1 : ℝ) :=
    mul_le_mul hπ h15 (by norm_num) (by linarith)
  rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) hden)]
  nlinarith

/-- `r̄_bot² ≤ L_near(2) + (3/(4π²))(7/200) + 5/(24π²)`. -/
theorem rbarBotSq_le : rbarBotSq ≤ Lnear 2 + 3 / (4 * π ^ 2) * (7 / 200) + 5 / (24 * π ^ 2) := by
  unfold rbarBotSq
  have : 0 ≤ 3 / (4 * π ^ 2) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left nearTail_le this]

end Cvs.L2a.CornerSuprema

end
