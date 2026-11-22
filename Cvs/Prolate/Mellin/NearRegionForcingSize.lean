import Mathlib
import Cvs.Prolate.Mellin.ForcingSmallBound
import Cvs.Prolate.Mellin.FrozenRootCoreBound
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.FrozenRootFirstDifference
import Cvs.Prolate.Mellin.NearRegionBetaStep
import Cvs.Prolate.Mellin.StepAmplification
import Cvs.Prolate.Mellin.UniformRootBounds

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Size of the near-region forcing on a line

With `J = ⌈(2c − Re s₀)/2⌉` the first index of the far region, `‖β(s_j)‖ ≤ 2712/(cε)` and
`Σ_{k<j<J} ‖β(s_j) − β(s_{j−1})‖ ≤ 3·10⁵ (2/5 + ½ log c)/(cε²) + 2·10⁷ (c + 1)/(c²ε²)`.
-/

noncomputable section

open Finset

namespace Cvs.Prolate.Mellin.NearRegionForcingSize

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity Cvs.Prolate.Mellin.UniformRootBounds Cvs.Prolate.Mellin.ForcingSmallBound Cvs.Prolate.Mellin.StepAmplification Cvs.Prolate.Mellin.NearRegionBetaStep

/-- The first index of the far region on the line from `s₀`. -/
def Jn (c : ℝ) (s₀ : ℂ) : ℕ := ⌈(2 * c - s₀.re) / 2⌉₊

/-- The near-region forcing budget. -/
def DS (ε c : ℝ) : ℝ := 300000 / (c * ε ^ 2) * (2 / 5 + 1 / 2 * Real.log c) + 20000000 * (c + 1) / (c ^ 2 * ε ^ 2)

variable {ε c χ : ℝ} {s₀ : ℂ}

theorem re_line (s₀ : ℂ) (i : ℕ) : (s₀ + 2 * (i : ℂ)).re = s₀.re + 2 * i := by simp

theorem re_lt_of_lt_Jn {i : ℕ} (hi : i < Jn c s₀) : s₀.re + 2 * i < 2 * c := by
  unfold Jn at hi
  have := Nat.lt_ceil.mp hi
  linarith

theorem le_re_Jn : 2 * c ≤ s₀.re + 2 * Jn c s₀ := by
  unfold Jn
  have := Nat.le_ceil ((2 * c - s₀.re) / 2)
  linarith

theorem Jn_le (h : Hyp ε c χ s₀) : (Jn c s₀ : ℝ) ≤ c + 1 := by
  unfold Jn
  have := h.hre
  by_cases hn : 0 ≤ (2 * c - s₀.re) / 2
  · have h1 := Nat.ceil_lt_add_one hn
    linarith
  · rw [Nat.ceil_eq_zero.mpr (by linarith)]; push_cast; linarith [h.c_ge]

/-- **`‖β‖ ≤ 2712/(cε)`** on the region. -/
theorem Hyp.norm_betaf_le (h : Hyp ε c χ s₀) (hε4 : ε ≤ 1 / 4) : ‖betaf c χ s₀‖ ≤ 2712 / (c * ε) := by
  have hc := h.c_pos
  have hε := h.hε
  set a := (csqrt (tau c χ s₀ ^ 2 + 1)).re
  have ha := Cvs.Prolate.Mellin.FrozenRootFirstDifference.Hyp.a_pos h
  have ha2 := Hyp.a_sq_ge h
  have hB := Hyp.norm_Bf_le h hε4
  have hA := Hyp.norm_one_add_Af_ge h hε4
  have hsq : ε ≤ Real.sqrt ε := by
    have := Real.sqrt_le_sqrt (show ε ^ 2 ≤ ε by nlinarith [h.hε1])
    rwa [Real.sqrt_sq hε.le] at this
  have haε : Real.sqrt ε / 2 ≤ a := by
    rw [div_le_iff₀ (by norm_num), Real.sqrt_le_left]
    · nlinarith
    · linarith
  unfold betaf
  rw [norm_div]
  have hpos : 0 < min (1 / 2) (a / 6) := lt_min (by norm_num) (by positivity)
  rw [div_le_iff₀ (lt_of_lt_of_le hpos hA)]
  refine hB.trans ?_
  rcases le_total (1 / 2) (a / 6) with hm | hm
  · rw [min_eq_left hm] at hA
    calc 113 / (c * a) ≤ 113 / (c * (Real.sqrt ε / 2)) := by gcongr
      _ ≤ 113 / (c * (ε / 2)) := by gcongr
      _ = 2712 / (c * ε) * (1 / 12) := by field_simp; ring
      _ ≤ 2712 / (c * ε) * (1 / 2) := by
          have : 0 ≤ 2712 / (c * ε) := by positivity
          nlinarith
      _ ≤ 2712 / (c * ε) * ‖1 + Af c χ s₀‖ := by gcongr
  · rw [min_eq_right hm] at hA
    calc 113 / (c * a) = 678 / (c * a ^ 2) * (a / 6) := by field_simp; ring
      _ ≤ 678 / (c * (ε / 4)) * (a / 6) := by gcongr
      _ = 2712 / (c * ε) * (a / 6) := by field_simp; ring
      _ ≤ 2712 / (c * ε) * ‖1 + Af c χ s₀‖ := by gcongr

/-- **The near-region forcing variation** along a line. -/
theorem sum_betaf_step_le (h : Hyp ε c χ s₀) (hε16 : ε ≤ 1 / 16) (k : ℕ) :
    ∑ j ∈ Ico (k + 1) (Jn c s₀), ‖betaf c χ (s₀ + 2 * (j : ℕ)) - betaf c χ (s₀ + 2 * ((j - 1 : ℕ) : ℂ))‖
      ≤ DS ε c := by
  have hc := h.c_pos
  have hε := h.hε
  have hx0 := h.hre
  set J := Jn c s₀
  set a := s₀.re + 2
  have ha : 0 < a := by linarith
  have hterm : ∀ j ∈ Ico (k + 1) J,
      ‖betaf c χ (s₀ + 2 * (j : ℕ)) - betaf c χ (s₀ + 2 * ((j - 1 : ℕ) : ℂ))‖
        ≤ 300000 / (c * ε ^ 2) * (1 / (a + 2 * ((j - 1 : ℕ) : ℝ))) + 20000000 / (c ^ 2 * ε ^ 2) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    have hl := hyp_line h (j - 1)
    have hnear : (s₀ + 2 * ((j - 1 : ℕ) : ℂ)).re ≤ 2 * c := by
      rw [re_line]; exact (re_lt_of_lt_Jn (show j - 1 < J by omega)).le
    have hst := Hyp.norm_betaf_step_le hl hε16 hnear
    have e : s₀ + 2 * ((j - 1 : ℕ) : ℂ) + 2 = s₀ + 2 * (j : ℕ) := by
      have : ((j - 1 : ℕ) : ℂ) = (j : ℂ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
      rw [this]; ring
    rw [e] at hst
    refine hst.trans ?_
    have hn : a + 2 * ((j - 1 : ℕ) : ℝ) ≤ ‖s₀ + 2 * (j : ℂ)‖ := by
      have := Complex.re_le_norm (s₀ + 2 * (j : ℂ))
      rw [re_line] at this
      have : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
      simp only [a]; linarith
    have hpos : 0 < a + 2 * ((j - 1 : ℕ) : ℝ) := by positivity
    have hnp : 0 < ‖s₀ + 2 * (j : ℂ)‖ := lt_of_lt_of_le hpos hn
    rw [show 300000 / (c * ε ^ 2 * ‖s₀ + 2 * (j : ℂ)‖) = 300000 / (c * ε ^ 2) * (1 / ‖s₀ + 2 * (j : ℂ)‖) by
      field_simp]
    gcongr
  -- the count and the harmonic sum
  have hJ := Jn_le (c := c) h
  have hcount : ((Ico (k + 1) J).card : ℝ) ≤ c + 1 := by
    rw [Nat.card_Ico]; have : ((J - (k + 1) : ℕ) : ℝ) ≤ J := by exact_mod_cast Nat.sub_le _ _
    linarith
  have hharm : ∑ j ∈ Ico (k + 1) J, 1 / (a + 2 * ((j - 1 : ℕ) : ℝ)) ≤ 2 / 5 + 1 / 2 * Real.log c := by
    by_cases hkJ : k + 1 < J
    · have hsub : ∑ j ∈ Ico (k + 1) J, 1 / (a + 2 * ((j - 1 : ℕ) : ℝ))
          ≤ ∑ i ∈ range ((J - 2) + 1), 1 / (a + 2 * (i : ℝ)) := by
        rw [← Finset.sum_image (s := Ico (k + 1) J) (g := fun j => j - 1) (f := fun i : ℕ => 1 / (a + 2 * (i : ℝ)))
          (fun x hx y hy hxy => by simp only [Finset.coe_Ico, Set.mem_Ico] at hx hy; simp at hxy; omega)]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => by positivity)
        intro i hi; rw [Finset.mem_image] at hi; obtain ⟨j, hj, rfl⟩ := hi
        rw [Finset.mem_Ico] at hj; rw [Finset.mem_range]; omega
      refine hsub.trans ((Cvs.Prolate.Mellin.FrozenRootCoreBound.sum_inv_le_log ha _).trans ?_)
      have h1 : 1 / a ≤ 2 / 5 := by rw [div_le_div_iff₀ ha (by norm_num)]; linarith
      have hJ2 : ((J - 2 : ℕ) : ℝ) ≤ (J : ℝ) - 1 := by
        have : 2 ≤ J := by omega
        rw [Nat.cast_sub this]; push_cast; linarith
      have hJr : s₀.re + 2 * ((J - 1 : ℕ) : ℝ) < 2 * c := re_lt_of_lt_Jn (by omega)
      have hJ1 : ((J - 1 : ℕ) : ℝ) = (J : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
      have h2 : (a + 2 * ((J - 2 : ℕ) : ℝ)) / a ≤ c := by
        rw [div_le_iff₀ ha]; simp only [a]; rw [hJ1] at hJr; nlinarith [h.c_ge]
      have h3 : Real.log ((a + 2 * ((J - 2 : ℕ) : ℝ)) / a) ≤ Real.log c :=
        Real.log_le_log (by positivity) h2
      linarith
    · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
      have := Real.log_nonneg (show (1 : ℝ) ≤ c by linarith [h.c_ge]); positivity
  calc _ ≤ ∑ j ∈ Ico (k + 1) J, (300000 / (c * ε ^ 2) * (1 / (a + 2 * ((j - 1 : ℕ) : ℝ)))
          + 20000000 / (c ^ 2 * ε ^ 2)) := Finset.sum_le_sum hterm
    _ = 300000 / (c * ε ^ 2) * ∑ j ∈ Ico (k + 1) J, 1 / (a + 2 * ((j - 1 : ℕ) : ℝ))
          + (Ico (k + 1) J).card * (20000000 / (c ^ 2 * ε ^ 2)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    _ ≤ 300000 / (c * ε ^ 2) * (2 / 5 + 1 / 2 * Real.log c) + (c + 1) * (20000000 / (c ^ 2 * ε ^ 2)) := by
        gcongr
    _ = DS ε c := by unfold DS; ring

end Cvs.Prolate.Mellin.NearRegionForcingSize
