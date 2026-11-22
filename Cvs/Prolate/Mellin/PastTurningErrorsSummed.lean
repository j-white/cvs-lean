import Mathlib
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Mellin.FarRegionStepDecay
import Cvs.Prolate.Mellin.ForcingSmallBound
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.NearRegionBetaStep
import Cvs.Prolate.Mellin.PastTurningContraction
import Cvs.Prolate.Mellin.PastTurningRootSizes
import Cvs.Prolate.Mellin.PastTurningStepErrors
import Cvs.Prolate.Mellin.PastTurningStepForcing
import Cvs.Prolate.Mellin.TrueRatioDownwardStep
import Cvs.Upstream.RecursionFrozenForcingSum

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The step errors past the turning point, summed

With `m_k = s₀ + 2k + 3/2` on a line in the region of Cvs.Prolate.Mellin.PastTurningContraction: `|m_k|² ≥ 4c² + (2k + 2)²`, and
`1/(a² + y²) ≤ 1/(y + a − 2) − 1/(y + a)` telescopes to `Σ_k 1/|m_k|² ≤ 1/(2c)`. The unrolled contraction gives
`|v_k| ≤ 5280c²/(ε|m_k|³)`, so `Σ|v_k|² ≤ 871200/(ε²c)`, and with `RecursionFrozenForcingSum`'s summed identity
`|Σ_{k<K} (log(1 + v_k) − β_k)| ≤ E1U(ε, c) + (1 + 4/√ε)|v_K|`, `E1U(ε, c) = O(ε^{−5/2}/c)`.
-/

noncomputable section

open Complex Filter Topology Finset

namespace Cvs.Prolate.Mellin.PastTurningErrorsSummed

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity (rhoStar)
open Cvs.Prolate.Mellin.ForcingSmallBound (Af Bf)
open Cvs.Prolate.Mellin.NearRegionBetaStep (betaf)
open Cvs.Prolate.Mellin.TrueRatioDownwardStep (Pk vk sk_succ)
open Cvs.Prolate.Mellin.PastTurningContraction (Up)
open Cvs.Prolate.Mellin.PastTurningStepErrors (VU bootstrap line_step VU_le)

variable {ε c : ℝ} {s₀ : ℂ}

/-- **The telescoping sum**: `Σ_{k<K} 1/(a² + (2k + 2)²) ≤ 1/a − 1/(2K + a)`. -/
theorem sum_inv_le {a : ℝ} (ha : 0 < a) :
    ∀ K : ℕ, ∑ k ∈ range K, 1 / (a ^ 2 + (2 * k + 2) ^ 2) ≤ 1 / a - 1 / (2 * K + a) := by
  intro K
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ]
    have hK := K.cast_nonneg (α := ℝ)
    have hstep : 1 / (a ^ 2 + (2 * K + 2) ^ 2) ≤ 1 / (2 * K + a) - 1 / (2 * K + 2 + a) := by
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (2 * (K : ℝ) + 2 - a)]
    push_cast
    have : 2 * ((K : ℝ) + 1) + a = 2 * K + 2 + a := by ring
    rw [this]
    linarith

theorem sum_inv_le' {a : ℝ} (ha : 0 < a) (K : ℕ) : ∑ k ∈ range K, 1 / (a ^ 2 + (2 * k + 2) ^ 2) ≤ 1 / a := by
  have := sum_inv_le ha K
  have : 0 ≤ 1 / (2 * (K : ℝ) + a) := by positivity
  linarith

variable {χ : ℝ}

/-- `|m_k|² ≥ 4c² + (2k + 2)²`. -/
theorem Up.norm_m_sq_ge (h : Up ε c χ s₀) (k : ℕ) :
    (2 * c) ^ 2 + (2 * k + 2) ^ 2 ≤ ‖s₀ + 2 * k + 3 / 2‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hre : (s₀ + 2 * (k : ℂ) + 3 / 2).re = s₀.re + 2 * k + 3 / 2 := by simp
  have him : (s₀ + 2 * (k : ℂ) + 3 / 2).im = s₀.im := by simp
  rw [hre, him]
  have h1 : 2 * (k : ℝ) + 2 ≤ s₀.re + 2 * k + 3 / 2 := by linarith [h.hre]
  have h2 : 2 * c ≤ s₀.im := Cvs.Prolate.Mellin.PastTurningRootSizes.Up.two_c_le h
  have hk := k.cast_nonneg (α := ℝ)
  have hc := h.c_pos
  nlinarith

theorem Up.two_c_le_norm_m (h : Up ε c χ s₀) (k : ℕ) : 2 * c ≤ ‖s₀ + 2 * k + 3 / 2‖ := by
  have := Cvs.Prolate.Mellin.PastTurningStepForcing.Up.norm_m_ge (Cvs.Prolate.Mellin.PastTurningStepErrors.Up.line h k); exact this

theorem Up.norm_m_pos (h : Up ε c χ s₀) (k : ℕ) : 0 < ‖s₀ + 2 * k + 3 / 2‖ := by
  have := Up.two_c_le_norm_m h k; have := h.c_pos; linarith

/-- `Σ_{k<K} 1/|m_k|² ≤ 1/(2c)`. -/
theorem Up.sum_inv_sq_le (h : Up ε c χ s₀) (K : ℕ) : ∑ k ∈ range K, 1 / ‖s₀ + 2 * k + 3 / 2‖ ^ 2 ≤ 1 / (2 * c) := by
  have hc := h.c_pos
  refine le_trans (sum_le_sum fun k _ => ?_) (sum_inv_le' (a := 2 * c) (by positivity) K)
  exact one_div_le_one_div_of_le (by positivity) (Up.norm_m_sq_ge h k)

/-- `Σ_{k<K} 1/|m_k|³ ≤ 1/(4c²)`. -/
theorem Up.sum_inv_cube_le (h : Up ε c χ s₀) (K : ℕ) :
    ∑ k ∈ range K, 1 / ‖s₀ + 2 * k + 3 / 2‖ ^ 3 ≤ 1 / (4 * c ^ 2) := by
  have hc := h.c_pos
  calc ∑ k ∈ range K, 1 / ‖s₀ + 2 * k + 3 / 2‖ ^ 3
      ≤ ∑ k ∈ range K, 1 / (2 * c) * (1 / ‖s₀ + 2 * k + 3 / 2‖ ^ 2) := by
        refine sum_le_sum fun k _ => ?_
        have hm := Up.two_c_le_norm_m h k
        have hp := Up.norm_m_pos h k
        rw [div_mul_div_comm, one_mul, pow_succ]
        exact one_div_le_one_div_of_le (by positivity) (by rw [mul_comm]; gcongr)
    _ = 1 / (2 * c) * ∑ k ∈ range K, 1 / ‖s₀ + 2 * k + 3 / 2‖ ^ 2 := by rw [mul_sum]
    _ ≤ 1 / (2 * c) * (1 / (2 * c)) := by gcongr; exact Up.sum_inv_sq_le h K
    _ = 1 / (4 * c ^ 2) := by field_simp; ring

/-- `Σ_{k<K} 1/|m_k|⁶ ≤ 1/(32c⁵)`. -/
theorem Up.sum_inv_six_le (h : Up ε c χ s₀) (K : ℕ) :
    ∑ k ∈ range K, 1 / ‖s₀ + 2 * k + 3 / 2‖ ^ 6 ≤ 1 / (32 * c ^ 5) := by
  have hc := h.c_pos
  calc ∑ k ∈ range K, 1 / ‖s₀ + 2 * k + 3 / 2‖ ^ 6
      ≤ ∑ k ∈ range K, 1 / (2 * c) ^ 4 * (1 / ‖s₀ + 2 * k + 3 / 2‖ ^ 2) := by
        refine sum_le_sum fun k _ => ?_
        have hm := Up.two_c_le_norm_m h k
        have hp := Up.norm_m_pos h k
        rw [div_mul_div_comm, one_mul, show ‖s₀ + 2 * (k : ℂ) + 3 / 2‖ ^ 6
          = ‖s₀ + 2 * (k : ℂ) + 3 / 2‖ ^ 4 * ‖s₀ + 2 * (k : ℂ) + 3 / 2‖ ^ 2 by ring]
        exact one_div_le_one_div_of_le (by positivity) (by gcongr)
    _ = 1 / (2 * c) ^ 4 * ∑ k ∈ range K, 1 / ‖s₀ + 2 * k + 3 / 2‖ ^ 2 := by rw [mul_sum]
    _ ≤ 1 / (2 * c) ^ 4 * (1 / (2 * c)) := by gcongr; exact Up.sum_inv_sq_le h K
    _ = 1 / (32 * c ^ 5) := by field_simp; ring

/-- The step error as a frozen step: `v_k = A(s_k)·(−v_{k+1}/(1 + v_{k+1})) + B(s_k)`. -/
theorem vk_eq (h : Up ε c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀) (hcb : 6000 / ε ^ 2 ≤ c) (k : ℕ) :
    vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ k
      = Af c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (s₀ + 2 * k) * (-vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ (k + 1) / (1 + vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ (k + 1)))
        + Bf c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (s₀ + 2 * k) := by
  set χ := Cvs.Prolate.EvenRungsByIndex.lev c 0
  have hb := bootstrap h hcb
  have hV := VU_le h.hε h.hε1 hcb
  have hr1 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.mpr h.hε1
  have hv1 := (hb (k + 1)).2
  have h1v : 1 + vk c χ s₀ (k + 1) ≠ 0 := by
    intro h0
    have : ‖vk c χ s₀ (k + 1)‖ = 1 := by rw [show vk c χ s₀ (k + 1) = -1 by linear_combination h0]; simp
    linarith
  have hstep := line_step h k (hb (k + 1)).1 (hb (k + 2)).1 h1v
  have hρ := Cvs.Prolate.Mellin.PastTurningStepErrors.Up.rho_ne (Cvs.Prolate.Mellin.PastTurningStepErrors.Up.line h k)
  have hP1 := (hb (k + 1)).1
  set w := Af c χ (s₀ + 2 * k) * (-vk c χ s₀ (k + 1) / (1 + vk c χ s₀ (k + 1))) + Bf c χ (s₀ + 2 * k)
  have ew : 1 + Af c χ (s₀ + 2 * k) * (-vk c χ s₀ (k + 1) / (1 + vk c χ s₀ (k + 1))) + Bf c χ (s₀ + 2 * k)
      = 1 + w := by simp only [w]; ring
  rw [ew] at hstep
  unfold vk
  rw [hstep]; field_simp; ring

/-- **The recursion** `v_k = −A v_{k+1} + β(1 + A) + A v_{k+1}²/(1 + v_{k+1})`. -/
theorem recur (h : Up ε c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀) (hcb : 6000 / ε ^ 2 ≤ c) (k : ℕ) :
    vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ k = -Af c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (s₀ + 2 * (k : ℂ)) * vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ (k + 1)
      + betaf c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (s₀ + 2 * (k : ℂ)) * (1 + Af c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (s₀ + 2 * (k : ℂ)))
      + Af c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (s₀ + 2 * (k : ℂ)) * vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ (k + 1) ^ 2
          / (1 + vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ (k + 1)) := by
  rw [vk_eq h hcb k]
  set χ := Cvs.Prolate.EvenRungsByIndex.lev c 0 with hχ
  have hk := Cvs.Prolate.Mellin.PastTurningStepErrors.Up.line h k
  have hb := bootstrap h hcb
  have hV := VU_le h.hε h.hε1 hcb
  have hr1 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.mpr h.hε1
  have hv1 := (hb (k + 1)).2
  have h1v : 1 + vk c χ s₀ (k + 1) ≠ 0 := by
    intro h0
    have : ‖vk c χ s₀ (k + 1)‖ = 1 := by rw [show vk c χ s₀ (k + 1) = -1 by linear_combination h0]; simp
    linarith
  have h1A : 1 + Af c χ (s₀ + 2 * (k : ℂ)) ≠ 0 := by
    intro h0
    have := Cvs.Prolate.Mellin.PastTurningStepForcing.Up.norm_one_add_Af_ge hk
    rw [h0, norm_zero] at this
    have := Real.sqrt_pos.mpr h.hε
    linarith
  unfold betaf
  field_simp
  ring

/-- **The profile**: `|v_k| ≤ 5280c²/(ε|m_k|³)`. -/
theorem profile (h : Up ε c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀) (hcb : 6000 / ε ^ 2 ≤ c) (k : ℕ) :
    ‖vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ k‖ ≤ 5280 * c ^ 2 / (ε * ‖s₀ + 2 * k + 3 / 2‖ ^ 3) := by
  set χ := Cvs.Prolate.EvenRungsByIndex.lev c 0
  have hc := h.c_pos
  have hε := h.hε
  set r := Real.sqrt ε
  have hr0 : 0 < r := Real.sqrt_pos.mpr hε
  have hr1 : r ≤ 1 := Real.sqrt_le_one.mpr h.hε1
  have hrr : r ^ 2 = ε := Real.sq_sqrt hε.le
  have hb := bootstrap h hcb
  have hV := VU_le hε h.hε1 hcb
  set b : ℕ → ℝ := fun j => 660 * c ^ 2 / (r * ‖s₀ + 2 * j + 3 / 2‖ ^ 3)
  have hmono : ∀ j : ℕ, ‖s₀ + 2 * (j : ℂ) + 3 / 2‖ ≤ ‖s₀ + 2 * ((j + 1 : ℕ) : ℂ) + 3 / 2‖ := by
    intro j
    have := Cvs.Prolate.Mellin.PastTurningRootSizes.norm_add_mono (s := s₀ + 2 * j + 3 / 2) (by simp; linarith [h.hre])
      (a := 0) (b := 2) le_rfl (by norm_num)
    push_cast at this ⊢
    rw [show s₀ + 2 * ((j : ℂ) + 1) + 3 / 2 = s₀ + 2 * j + 3 / 2 + 2 by ring]
    simpa using this
  have key := Cvs.Prolate.Mellin.FarRegionStepDecay.le_of_contract (v := fun j => ‖vk c χ s₀ j‖) (b := b) (q := 1 - r / 8)
    (M := VU ε c) (K₀ := 0) (by linarith) (by linarith)
    (fun j _ => by
      simp only [b]
      apply div_le_div_of_nonneg_left (by positivity) (by have := Up.norm_m_pos h j; positivity)
      gcongr; exact hmono j)
    (fun j _ => by simp only [b]; have := Up.norm_m_pos h j; positivity)
    (fun j _ => (hb j).2) (fun j _ => norm_nonneg _)
    (fun j _ => by
      have hj := Cvs.Prolate.Mellin.PastTurningStepErrors.Up.line h j
      have hA := Cvs.Prolate.Mellin.PastTurningStepForcing.Up.norm_Af_le hj
      have hB := Cvs.Prolate.Mellin.PastTurningStepForcing.Up.norm_Bf_le hj
      have hv1 := (hb (j + 1)).2
      have h1 : 1 - r / 8 ≤ ‖1 + vk c χ s₀ (j + 1)‖ := by
        have := norm_sub_norm_le (1 : ℂ) (-vk c χ s₀ (j + 1))
        rw [norm_neg, sub_neg_eq_add, norm_one] at this; linarith
      show ‖vk c χ s₀ j‖ ≤ (1 - r / 8) * ‖vk c χ s₀ (j + 1)‖ + b j
      rw [vk_eq h hcb j]
      have hu : ‖-vk c χ s₀ (j + 1) / (1 + vk c χ s₀ (j + 1))‖ ≤ ‖vk c χ s₀ (j + 1)‖ / (1 - r / 8) := by
        rw [norm_div, norm_neg]; exact div_le_div_of_nonneg_left (norm_nonneg _) (by linarith) h1
      have hA' : 0 ≤ 1 - r / 4 := by linarith
      calc ‖Af c χ (s₀ + 2 * j) * (-vk c χ s₀ (j + 1) / (1 + vk c χ s₀ (j + 1))) + Bf c χ (s₀ + 2 * j)‖
          ≤ (1 - r / 4) * (‖vk c χ s₀ (j + 1)‖ / (1 - r / 8)) + b j := by
            refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
            · rw [norm_mul]; exact mul_le_mul hA hu (norm_nonneg _) hA'
            · simp only [b]; exact hB
        _ ≤ (1 - r / 8) * ‖vk c χ s₀ (j + 1)‖ + b j := by
            have : (1 - r / 4) * (‖vk c χ s₀ (j + 1)‖ / (1 - r / 8)) ≤ (1 - r / 8) * ‖vk c χ s₀ (j + 1)‖ := by
              rw [mul_div_assoc', div_le_iff₀ (by linarith)]
              nlinarith [sq_nonneg r, norm_nonneg (vk c χ s₀ (j + 1))]
            linarith)
    k (Nat.zero_le k)
  refine key.trans (le_of_eq ?_)
  simp only [b]
  rw [← hrr]
  have := Up.norm_m_pos h k
  have hr0' : r ≠ 0 := hr0.ne'
  rw [show (1 : ℝ) - (1 - r / 8) = r / 8 by ring, div_div_eq_mul_div, div_mul_eq_mul_div, div_div,
    div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- **Sum of squares**: `Σ_{k<K} |v_{k+e}|² ≤ 871200/(ε²c)`. -/
theorem sum_sq_le (h : Up ε c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀) (hcb : 6000 / ε ^ 2 ≤ c) (e K : ℕ) :
    ∑ k ∈ range K, ‖vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ (k + e)‖ ^ 2 ≤ 871200 / (ε ^ 2 * c) := by
  have hc := h.c_pos
  have hε := h.hε
  have he : Up ε c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (s₀ + 2 * e) := Cvs.Prolate.Mellin.PastTurningStepErrors.Up.line h e
  have hsum := Up.sum_inv_six_le he K
  calc ∑ k ∈ range K, ‖vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ (k + e)‖ ^ 2
      ≤ ∑ k ∈ range K, (5280 * c ^ 2 / ε) ^ 2 * (1 / ‖s₀ + 2 * e + 2 * k + 3 / 2‖ ^ 6) := by
        refine sum_le_sum fun k _ => ?_
        have hp := profile h hcb (k + e)
        have e1 : s₀ + 2 * ((k + e : ℕ) : ℂ) + 3 / 2 = s₀ + 2 * e + 2 * k + 3 / 2 := by push_cast; ring
        rw [e1] at hp
        have hm := Up.norm_m_pos he k
        calc ‖vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ (k + e)‖ ^ 2
            ≤ (5280 * c ^ 2 / (ε * ‖s₀ + 2 * e + 2 * k + 3 / 2‖ ^ 3)) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) hp 2
          _ = _ := by field_simp
    _ = (5280 * c ^ 2 / ε) ^ 2 * ∑ k ∈ range K, 1 / ‖s₀ + 2 * e + 2 * k + 3 / 2‖ ^ 6 := by rw [mul_sum]
    _ ≤ (5280 * c ^ 2 / ε) ^ 2 * (1 / (32 * c ^ 5)) := by gcongr
    _ = 871200 / (ε ^ 2 * c) := by field_simp; ring

/-- **Total variation of `A`**: `Σ_{k<K} |A(s_{k+1}) − A(s_k)| ≤ 335/√ε`. -/
theorem sum_dA_le (h : Up ε c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀) (K : ℕ) :
    ∑ k ∈ range K, ‖Af c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (s₀ + 2 * k + 2) - Af c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (s₀ + 2 * k)‖
      ≤ 335 / Real.sqrt ε := by
  have hc := h.c_pos
  have hse : 0 < Real.sqrt ε := Real.sqrt_pos.mpr h.hε
  calc ∑ k ∈ range K, ‖Af c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (s₀ + 2 * k + 2) - Af c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (s₀ + 2 * k)‖
      ≤ ∑ k ∈ range K, 1340 * c ^ 2 / Real.sqrt ε * (1 / ‖s₀ + 2 * k + 3 / 2‖ ^ 3) := by
        refine sum_le_sum fun k _ => ?_
        have := Cvs.Prolate.Mellin.PastTurningStepForcing.Up.norm_Af_step_le (Cvs.Prolate.Mellin.PastTurningStepErrors.Up.line h k)
        have hm := Up.norm_m_pos h k
        refine this.trans (le_of_eq ?_)
        field_simp
    _ = 1340 * c ^ 2 / Real.sqrt ε * ∑ k ∈ range K, 1 / ‖s₀ + 2 * k + 3 / 2‖ ^ 3 := by rw [mul_sum]
    _ ≤ 1340 * c ^ 2 / Real.sqrt ε * (1 / (4 * c ^ 2)) := by gcongr; exact Up.sum_inv_cube_le h K
    _ = 335 / Real.sqrt ε := by field_simp; ring

/-- The step-error budget past the turning point. -/
def E1U (ε c : ℝ) : ℝ :=
  871200 / (ε ^ 2 * c) * (1 + 40 / (7 * Real.sqrt ε)) + (1 + 4 / Real.sqrt ε) * (660 / (ε * c))
    + 660 / (ε * c) * (16 / ε) * (335 / Real.sqrt ε)

/-- **Step errors against the frozen forcing** past the turning point. -/
theorem sum_log_sub_le (h : Up ε c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀) (hcb : 6000 / ε ^ 2 ≤ c) (K : ℕ) (hK : 1 ≤ K) :
    ‖∑ k ∈ Ico 0 K, (Complex.log (1 + vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ k) - betaf c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (s₀ + 2 * (k : ℂ)))‖
      ≤ E1U ε c + (1 + 4 / Real.sqrt ε) * ‖vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ K‖ := by
  set χ := Cvs.Prolate.EvenRungsByIndex.lev c 0
  have hc := h.c_pos
  have hε := h.hε
  set r := Real.sqrt ε
  have hr0 : 0 < r := Real.sqrt_pos.mpr hε
  have hr1 : r ≤ 1 := Real.sqrt_le_one.mpr h.hε1
  have hrr : r ^ 2 = ε := Real.sq_sqrt hε.le
  have hb := bootstrap h hcb
  have hV := VU_le hε h.hε1 hcb
  have hV0 : 0 ≤ VU ε c := (norm_nonneg _).trans (hb 0).2
  have hsmall : ∀ k, ‖vk c χ s₀ k‖ ≤ 1 / 8 := fun k => (hb k).2.trans (hV.trans (by linarith))
  set v := vk c χ s₀
  set A := fun k : ℕ => Af c χ (s₀ + 2 * (k : ℂ))
  set β := fun k : ℕ => betaf c χ (s₀ + 2 * (k : ℂ))
  set n := fun k : ℕ => A k * v (k + 1) ^ 2 / (1 + v (k + 1))
  have hA0 : ∀ k, r / 4 ≤ ‖1 + A k‖ := fun k =>
    Cvs.Prolate.Mellin.PastTurningStepForcing.Up.norm_one_add_Af_ge (Cvs.Prolate.Mellin.PastTurningStepErrors.Up.line h k)
  have hAne : ∀ k, 1 + A k ≠ 0 := fun k h0 => by have := hA0 k; rw [h0, norm_zero] at this; linarith
  have ha : ∀ k, ‖(1 + A k)⁻¹‖ ≤ 4 / r := fun k =>
    Cvs.Prolate.Mellin.PastTurningStepForcing.Up.norm_inv_one_add_Af_le (Cvs.Prolate.Mellin.PastTurningStepErrors.Up.line h k)
  have hsq0 := sum_sq_le h hcb 0 K
  have hsq1 := sum_sq_le h hcb 1 K
  simp only [Nat.add_zero] at hsq0
  rw [Finset.range_eq_Ico] at hsq0 hsq1
  have esplit : ∑ k ∈ Ico 0 K, (Complex.log (1 + v k) - β k)
      = ∑ k ∈ Ico 0 K, (Complex.log (1 + v k) - v k) + ∑ k ∈ Ico 0 K, (v k - β k) := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [esplit]
  have hlog : ‖∑ k ∈ Ico 0 K, (Complex.log (1 + v k) - v k)‖ ≤ 871200 / (ε ^ 2 * c) := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun k _ => ?_).trans hsq0)
    have hk := hsmall k
    have := Complex.norm_log_one_add_sub_self_le (z := v k) (by linarith)
    refine this.trans ?_
    have h1 : (1 - ‖v k‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have := sq_nonneg ‖v k‖
    calc ‖v k‖ ^ 2 * (1 - ‖v k‖)⁻¹ / 2 ≤ ‖v k‖ ^ 2 * 2 / 2 := by gcongr
      _ = ‖v k‖ ^ 2 := by ring
  have hmain := Cvs.Upstream.RecursionFrozenForcingSum.norm_sum_sub_le (A := A) (β := β) (n := n) (v := v) (m := 0) (K := K)
    (by omega) (fun k _ _ => hAne k) (fun k _ _ => recur h hcb k)
  have hn : ∑ k ∈ Ico 0 K, ‖(1 + A k)⁻¹‖ * ‖n k‖ ≤ 32 / (7 * r) * (871200 / (ε ^ 2 * c)) := by
    have hpt : ∀ k ∈ Ico 0 K, ‖(1 + A k)⁻¹‖ * ‖n k‖ ≤ 32 / (7 * r) * ‖v (k + 1)‖ ^ 2 := by
      intro k _
      have hv := hsmall (k + 1)
      have h1v : 7 / 8 ≤ ‖1 + v (k + 1)‖ := by
        have := norm_sub_norm_le (1 : ℂ) (-v (k + 1))
        rw [norm_neg, sub_neg_eq_add, norm_one] at this; linarith
      have hAk : ‖A k‖ ≤ 1 := (Cvs.Prolate.Mellin.PastTurningStepForcing.Up.norm_Af_le (Cvs.Prolate.Mellin.PastTurningStepErrors.Up.line h k)).trans
        (by linarith)
      have hnk : ‖n k‖ ≤ 8 / 7 * ‖v (k + 1)‖ ^ 2 := by
        simp only [n]; rw [norm_div, norm_mul, norm_pow, div_le_iff₀ (by linarith)]
        have := sq_nonneg ‖v (k + 1)‖
        nlinarith
      calc _ ≤ 4 / r * (8 / 7 * ‖v (k + 1)‖ ^ 2) := mul_le_mul (ha k) hnk (norm_nonneg _) (by positivity)
        _ = _ := by field_simp; ring
    calc _ ≤ ∑ k ∈ Ico 0 K, 32 / (7 * r) * ‖v (k + 1)‖ ^ 2 := Finset.sum_le_sum hpt
      _ = 32 / (7 * r) * ∑ k ∈ Ico 0 K, ‖v (k + 1)‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ _ := by gcongr
  have hK1 : (1 + ‖(1 + A (K - 1))⁻¹‖) * ‖v K‖ ≤ (1 + 4 / r) * ‖v K‖ := by gcongr; exact ha _
  have h01 : (1 + ‖(1 + A 0)⁻¹‖) * ‖v 0‖ ≤ (1 + 4 / r) * (660 / (ε * c)) :=
    mul_le_mul (by linarith [ha 0]) (hb 0).2 (norm_nonneg _) (by positivity)
  -- the variation term
  have hdv : ∑ k ∈ Ico (0 + 1) K, ‖v k‖ * ‖(1 + A k)⁻¹ - (1 + A (k - 1))⁻¹‖
      ≤ 660 / (ε * c) * (16 / ε) * (335 / r) := by
    have hpt : ∀ k ∈ Ico (0 + 1) K, ‖v k‖ * ‖(1 + A k)⁻¹ - (1 + A (k - 1))⁻¹‖
        ≤ 660 / (ε * c) * (16 / ε) * ‖Af c χ (s₀ + 2 * ((k - 1 : ℕ) : ℂ) + 2) - Af c χ (s₀ + 2 * ((k - 1 : ℕ) : ℂ))‖ := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      have hkk : s₀ + 2 * (k : ℂ) = s₀ + 2 * ((k - 1 : ℕ) : ℂ) + 2 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      have e : (1 + A k)⁻¹ - (1 + A (k - 1))⁻¹ = (A (k - 1) - A k) * ((1 + A k)⁻¹ * (1 + A (k - 1))⁻¹) := by
        field_simp [hAne k, hAne (k - 1)]; ring
      rw [e, norm_mul, norm_mul]
      have hd : ‖A (k - 1) - A k‖ = ‖Af c χ (s₀ + 2 * ((k - 1 : ℕ) : ℂ) + 2) - Af c χ (s₀ + 2 * ((k - 1 : ℕ) : ℂ))‖ := by
        simp only [A]; rw [norm_sub_rev, hkk]
      rw [hd]
      have hab : ‖(1 + A k)⁻¹‖ * ‖(1 + A (k - 1))⁻¹‖ ≤ 16 / ε := by
        calc _ ≤ 4 / r * (4 / r) := mul_le_mul (ha k) (ha (k - 1)) (norm_nonneg _) (by positivity)
          _ = 16 / ε := by rw [← hrr]; field_simp; ring
      have hvk := (hb k).2
      unfold VU at hvk
      calc ‖v k‖ * (‖Af c χ (s₀ + 2 * ((k - 1 : ℕ) : ℂ) + 2) - Af c χ (s₀ + 2 * ((k - 1 : ℕ) : ℂ))‖
            * (‖(1 + A k)⁻¹‖ * ‖(1 + A (k - 1))⁻¹‖))
          ≤ 660 / (ε * c) * (‖Af c χ (s₀ + 2 * ((k - 1 : ℕ) : ℂ) + 2) - Af c χ (s₀ + 2 * ((k - 1 : ℕ) : ℂ))‖
            * (16 / ε)) := by gcongr
        _ = _ := by ring
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [← Finset.mul_sum]
    gcongr
    have hre : ∑ k ∈ Ico (0 + 1) K, ‖Af c χ (s₀ + 2 * ((k - 1 : ℕ) : ℂ) + 2) - Af c χ (s₀ + 2 * ((k - 1 : ℕ) : ℂ))‖
        = ∑ k ∈ range (K - 1), ‖Af c χ (s₀ + 2 * (k : ℂ) + 2) - Af c χ (s₀ + 2 * (k : ℂ))‖ := by
      rw [Finset.range_eq_Ico, Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr (by congr 1) fun k _ => ?_
      congr 3 <;> simp
    rw [hre]
    exact sum_dA_le h (K - 1)
  have := norm_add_le (∑ k ∈ Ico 0 K, (Complex.log (1 + v k) - v k)) (∑ k ∈ Ico 0 K, (v k - β k))
  unfold E1U
  have e40 : 871200 / (ε ^ 2 * c) * (1 + 40 / (7 * r))
      = 871200 / (ε ^ 2 * c) + 40 / (7 * r) * (871200 / (ε ^ 2 * c)) := by ring
  have h32 : 32 / (7 * r) * (871200 / (ε ^ 2 * c)) ≤ 40 / (7 * r) * (871200 / (ε ^ 2 * c)) := by
    gcongr; norm_num
  linarith

end Cvs.Prolate.Mellin.PastTurningErrorsSummed
