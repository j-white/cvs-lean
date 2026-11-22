import Mathlib
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Mellin.FarRegionStepDecay
import Cvs.Prolate.Mellin.ForcingSmallBound
import Cvs.Prolate.Mellin.FrozenRootStep
import Cvs.Prolate.Mellin.NearRegionBetaStep
import Cvs.Prolate.Mellin.NearRegionBootstrap
import Cvs.Prolate.Mellin.NearRegionForcingSize
import Cvs.Prolate.Mellin.PropagationFactorSizes
import Cvs.Prolate.Mellin.StepAmplification
import Cvs.Prolate.Mellin.TrueRatioDownwardStep
import Cvs.Prolate.Mellin.UniformRootBounds
import Cvs.Upstream.RecursionFrozenForcingSum

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The ground law ratio's step errors against the frozen forcing

Under the near-bootstrap conditions, on the whole line `P_k ≠ 0`, `|v_k| ≤ N = 2ΓΛ₁` and the recursion holds at every
index; for `K > J`, `Σ_{k<K} |v_{k+e}|² ≤ (c+2)N² + 1125000/c` and
`|Σ_{k<K} (log(1 + v_k) − β_k)| ≤ E₁(ε, c) + (1 + 12/√ε)|v_K|`.
-/

noncomputable section

open Finset

namespace Cvs.Prolate.Mellin.GroundRatioStepErrors

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity Cvs.Prolate.Mellin.UniformRootBounds Cvs.Prolate.Mellin.ForcingSmallBound Cvs.Prolate.Mellin.StepAmplification Cvs.Prolate.Mellin.NearRegionBetaStep Cvs.Prolate.Mellin.TrueRatioDownwardStep Cvs.Prolate.Mellin.NearRegionForcingSize Cvs.Prolate.Mellin.NearRegionBootstrap

/-- The near level `N = 2ΓΛ₁`. -/
def NV (ε c : ℝ) : ℝ := 2 * Γc c * Λc ε c

theorem inv_cube_le {X y : ℝ} (hX : 2 ≤ X) (hy : X ≤ y) : 1 / y ^ 3 ≤ 1 / X * (1 / y - 1 / (y + 2)) := by
  have hX0 : 0 < X := by linarith
  have hy0 : 0 < y := by linarith
  rw [show 1 / y - 1 / (y + 2) = 2 / (y * (y + 2)) by field_simp; ring]
  rw [div_le_iff₀ (by positivity)]
  rw [show 1 / X * (2 / (y * (y + 2))) * y ^ 3 = 2 * y ^ 2 / (X * (y + 2)) by field_simp; try ring]
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- The standing conditions. -/
structure Std (ε c : ℝ) (s₀ : ℂ) : Prop where
  h : Hyp ε c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀
  hε16 : ε ≤ 1 / 16
  hc7 : 7500 ≤ c
  hs1 : 40 / 9 * Λc ε c * Γc c * Tc c ≤ 1
  hs2 : 2 * Γc c * Λc ε c ≤ 1 / 10

variable {ε c : ℝ} {s₀ : ℂ}

theorem Std.far (S : Std ε c s₀) (k : ℕ) (hk : Jn c s₀ ≤ k) :
    Pk c s₀ k ≠ 0 ∧ ‖vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ k‖ ≤ 750 / c :=
  far_bootstrap S.h (by linarith [S.hε16]) S.hc7 _ le_re_Jn k hk

theorem Std.far_decay (S : Std ε c s₀) (k : ℕ) (hk : Jn c s₀ ≤ k) :
    ‖vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ k‖ ≤ 6000 * c ^ 2 / (s₀.re + 2 * k) ^ 3 :=
  Cvs.Prolate.Mellin.FarRegionStepDecay.far_decay S.h (by linarith [S.hε16]) S.hc7 _ le_re_Jn k hk

theorem Std.Λ_nonneg (S : Std ε c s₀) : 0 ≤ Λc ε c := by
  have hc := S.h.c_pos; have hε := S.h.hε
  have : 0 ≤ DS ε c := by
    unfold DS; have := Real.log_nonneg (show (1 : ℝ) ≤ c by linarith [S.h.c_ge]); positivity
  unfold Λc; positivity

theorem Std.NV_le (S : Std ε c s₀) : NV ε c ≤ 1 / 10 := S.hs2

/-- **The profile on the whole line.** -/
theorem Std.profile (S : Std ε c s₀) (k : ℕ) :
    Pk c s₀ k ≠ 0 ∧ ‖vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ k‖ ≤ NV ε c := by
  have hc := S.h.c_pos
  by_cases hk : k ≤ Jn c s₀
  · obtain ⟨hP, hv⟩ := near_bootstrap S.h S.hε16 S.hc7 S.hs1 S.hs2 k hk
    refine ⟨hP, hv.trans ?_⟩
    have := γL_le S.h k; have := S.Λ_nonneg
    unfold NV; nlinarith
  · obtain ⟨hP, hv⟩ := S.far k (by omega)
    refine ⟨hP, hv.trans ?_⟩
    have hΓ : 1 ≤ Γc c := (one_le_γL S.h 0).trans (γL_le S.h 0)
    have : 750 / c ≤ Λc ε c := by
      have := S.h.hε
      have : 0 ≤ DS ε c := by
        unfold DS; have := Real.log_nonneg (show (1 : ℝ) ≤ c by linarith [S.h.c_ge]); positivity
      unfold Λc; have : 0 ≤ 5424 / (c * ε) := by positivity
      linarith
    have := S.Λ_nonneg
    unfold NV; nlinarith

theorem Std.small (S : Std ε c s₀) (k : ℕ) : ‖vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ k‖ ≤ 1 / 10 :=
  (S.profile k).2.trans S.NV_le

/-- **The recursion at every index.** -/
theorem Std.recur (S : Std ε c s₀) (k : ℕ) :
    vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ k = -Af c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (s₀ + 2 * (k : ℂ)) * vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ (k + 1)
      + betaf c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (s₀ + 2 * (k : ℂ)) * (1 + Af c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (s₀ + 2 * (k : ℂ)))
      + Af c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (s₀ + 2 * (k : ℂ)) * vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ (k + 1) ^ 2
          / (1 + vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ (k + 1)) :=
  rec_at S.h (by linarith [S.hε16]) k (S.profile (k + 1)).1 (S.profile (k + 2)).1 (S.small (k + 1))

/-- **The far squares telescope.** -/
theorem Std.sq_far (S : Std ε c s₀) (e k : ℕ) (hk : Jn c s₀ ≤ k) :
    ‖vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ (k + e)‖ ^ 2
      ≤ 2250000 * (1 / (s₀.re + 2 * k) - 1 / (s₀.re + 2 * (k + 1 : ℕ))) := by
  have hc := S.h.c_pos
  have hx : 2 * c ≤ s₀.re + 2 * k := by
    have := le_re_Jn (c := c) (s₀ := s₀)
    have : (Jn c s₀ : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  set x := s₀.re + 2 * (k : ℝ)
  have hx0 : 0 < x := by linarith
  have hv := S.far_decay (k + e) (by omega)
  have hxe : x ≤ s₀.re + 2 * ((k + e : ℕ) : ℝ) := by push_cast; have := e.cast_nonneg (α := ℝ); linarith
  have hv' : ‖vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ (k + e)‖ ≤ 6000 * c ^ 2 / x ^ 3 :=
    hv.trans (div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ hx0.le hxe 3))
  have hsq : ‖vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ (k + e)‖ ^ 2 ≤ (6000 * c ^ 2 / x ^ 3) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hv' 2
  have h8 : 8 * c ^ 3 ≤ x ^ 3 := by
    have := pow_le_pow_left₀ (by positivity) hx 3; nlinarith
  have hcube := inv_cube_le (X := 2 * c) (y := x) (by linarith [S.h.c_ge]) hx
  have e1 : s₀.re + 2 * ((k + 1 : ℕ) : ℝ) = x + 2 := by push_cast; ring
  rw [e1]
  have e2 : (6000 * c ^ 2 / x ^ 3) ^ 2 = 36000000 * c ^ 4 / x ^ 3 * (1 / x ^ 3) := by
    field_simp; ring
  have h3 : 36000000 * c ^ 4 / x ^ 3 ≤ 4500000 * c := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [pow_pos hc 3]
  calc _ ≤ (6000 * c ^ 2 / x ^ 3) ^ 2 := hsq
    _ = 36000000 * c ^ 4 / x ^ 3 * (1 / x ^ 3) := e2
    _ ≤ 4500000 * c * (1 / (2 * c) * (1 / x - 1 / (x + 2))) := by
        gcongr
    _ = 2250000 * (1 / x - 1 / (x + 2)) := by field_simp; ring

/-- **Sum of squares** along the line. -/
theorem Std.sum_sq_le (S : Std ε c s₀) (e K : ℕ) (hK : Jn c s₀ + 1 ≤ K) :
    ∑ k ∈ Ico 0 K, ‖vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ (k + e)‖ ^ 2 ≤ (c + 2) * NV ε c ^ 2 + 1125000 / c := by
  have hc := S.h.c_pos
  set J := Jn c s₀
  rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le (J + 1)) hK]
  have hnear : ∑ k ∈ Ico 0 (J + 1), ‖vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ (k + e)‖ ^ 2 ≤ (c + 2) * NV ε c ^ 2 := by
    calc _ ≤ ∑ k ∈ Ico 0 (J + 1), NV ε c ^ 2 :=
          Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _) (S.profile (k + e)).2 2
      _ = (J + 1 : ℕ) * NV ε c ^ 2 := by simp
      _ ≤ (c + 2) * NV ε c ^ 2 := by
          gcongr; push_cast; linarith [Jn_le (c := c) S.h]
  have hfar : ∑ k ∈ Ico (J + 1) K, ‖vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ (k + e)‖ ^ 2 ≤ 1125000 / c := by
    set φ := fun k : ℕ => 2250000 * (1 / (s₀.re + 2 * (k : ℝ)))
    calc _ ≤ ∑ k ∈ Ico (J + 1) K, (φ k - φ (k + 1)) := Finset.sum_le_sum fun k hk => by
          rw [Finset.mem_Ico] at hk
          have := S.sq_far e k (by omega)
          simp only [φ]; push_cast at this ⊢; linarith
      _ = φ (J + 1) - φ K := Cvs.Prolate.Mellin.StepAmplification.sum_Ico_sub hK
      _ ≤ φ (J + 1) := by
          have : 0 ≤ φ K := by
            simp only [φ]; have := S.h.hre; have := K.cast_nonneg (α := ℝ); positivity
          linarith
      _ ≤ 1125000 / c := by
          simp only [φ]
          have := le_re_Jn (c := c) (s₀ := s₀)
          have hx : 2 * c ≤ s₀.re + 2 * ((J + 1 : ℕ) : ℝ) := by push_cast; linarith
          rw [show (1125000 : ℝ) / c = 2250000 * (1 / (2 * c)) by field_simp; ring]
          gcongr
  linarith

/-- The forcing-variation budget. -/
def DV (ε c : ℝ) : ℝ :=
  144 / ε * NV ε c * ((c + 1) * (4050 / (7 * c * Real.sqrt ε)) + 27 / 8)
    + 216000 / ε * (8100 / (14 * c) + 81 / (32 * c ^ 2))

/-- The total budget `E₁`. -/
def E1 (ε c : ℝ) : ℝ :=
  (225 / (2 * Real.sqrt ε) + 1) * ((c + 2) * NV ε c ^ 2 + 1125000 / c) + (1 + 12 / Real.sqrt ε) * NV ε c + DV ε c

theorem shift_eq (s₀ : ℂ) {k : ℕ} (hk : 1 ≤ k) : s₀ + 2 * (k : ℂ) = s₀ + 2 * ((k - 1 : ℕ) : ℂ) + 2 := by
  have : ((k - 1 : ℕ) : ℂ) = (k : ℂ) - 1 := by rw [Nat.cast_sub hk]; simp
  rw [this]; ring

/-- **The variation term.** -/
theorem Std.sum_dv_le (S : Std ε c s₀) (K : ℕ) (hK : Jn c s₀ + 1 ≤ K) :
    ∑ k ∈ Ico 1 K, ‖vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ k‖
        * ‖(1 + Af c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (s₀ + 2 * (k : ℂ)))⁻¹ - (1 + Af c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (s₀ + 2 * ((k - 1 : ℕ) : ℂ)))⁻¹‖
      ≤ DV ε c := by
  set χ := Cvs.Prolate.EvenRungsByIndex.lev c 0
  set J := Jn c s₀
  have hc := S.h.c_pos
  have hε := S.h.hε
  have hε4 : ε ≤ 1 / 4 := by linarith [S.hε16]
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hx0 := S.h.hre
  have hNV : 0 ≤ NV ε c := (norm_nonneg _).trans (S.profile 0).2
  -- the step of `1/(1 + A)` in terms of the step of `A`
  have hΔ : ∀ k : ℕ, 1 ≤ k → ‖(1 + Af c χ (s₀ + 2 * (k : ℂ)))⁻¹ - (1 + Af c χ (s₀ + 2 * ((k - 1 : ℕ) : ℂ)))⁻¹‖
      ≤ 144 / ε * ‖Af c χ (s₀ + 2 * ((k - 1 : ℕ) : ℂ) + 2) - Af c χ (s₀ + 2 * ((k - 1 : ℕ) : ℂ))‖ := by
    intro k hk
    have hl := Cvs.Prolate.Mellin.StepAmplification.hyp_line S.h (k - 1)
    have hl' := Cvs.Prolate.Mellin.FrozenRootStep.Hyp.add_two hl
    rw [shift_eq s₀ hk]
    exact Cvs.Prolate.Mellin.PropagationFactorSizes.norm_inv_sub_le hε (Cvs.Prolate.Mellin.PropagationFactorSizes.Hyp.norm_one_add_Af_ge' hl hε4)
      (Cvs.Prolate.Mellin.PropagationFactorSizes.Hyp.norm_one_add_Af_ge' hl' hε4)
  rw [← Finset.sum_Ico_consecutive _ (show 1 ≤ J + 1 by omega) hK]
  -- near part
  have hnear : ∑ k ∈ Ico 1 (J + 1), ‖vk c χ s₀ k‖
        * ‖(1 + Af c χ (s₀ + 2 * (k : ℂ)))⁻¹ - (1 + Af c χ (s₀ + 2 * ((k - 1 : ℕ) : ℂ)))⁻¹‖
      ≤ 144 / ε * NV ε c * ((c + 1) * (4050 / (7 * c * Real.sqrt ε)) + 27 / 8) := by
    set ψ := fun k : ℕ => 1 / (2 * (s₀.re + 2 * (k : ℝ) - 1))
    have hpt : ∀ k ∈ Ico 1 (J + 1), ‖vk c χ s₀ k‖
        * ‖(1 + Af c χ (s₀ + 2 * (k : ℂ)))⁻¹ - (1 + Af c χ (s₀ + 2 * ((k - 1 : ℕ) : ℂ)))⁻¹‖
          ≤ 144 / ε * NV ε c * (4050 / (7 * c * Real.sqrt ε) + 81 / 8 * (ψ k - ψ (k + 1))) := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      have hl := Cvs.Prolate.Mellin.StepAmplification.hyp_line S.h (k - 1)
      have hst := Cvs.Prolate.Mellin.PropagationFactorSizes.Hyp.norm_Af_step_le' hl hε4
      have hre : (s₀ + 2 * ((k - 1 : ℕ) : ℂ)).re = s₀.re + 2 * (k : ℝ) - 2 := by
        rw [re_line]; rw [Nat.cast_sub hk.1]; push_cast; ring
      rw [hre] at hst
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk.1
      have hq : 81 / (8 * ((s₀.re + 2 * (k : ℝ) - 2 + 1) * (s₀.re + 2 * (k : ℝ) - 2 + 3)))
          = 81 / 8 * (ψ k - ψ (k + 1)) := by
        simp only [ψ]; push_cast
        have hu : 0 < s₀.re + 2 * (k : ℝ) - 1 := by linarith
        rw [show s₀.re + 2 * (k : ℝ) - 2 + 1 = s₀.re + 2 * (k : ℝ) - 1 by ring,
          show s₀.re + 2 * (k : ℝ) - 2 + 3 = s₀.re + 2 * (k : ℝ) - 1 + 2 by ring,
          show s₀.re + 2 * ((k : ℝ) + 1) - 1 = s₀.re + 2 * (k : ℝ) - 1 + 2 by ring]
        generalize s₀.re + 2 * (k : ℝ) - 1 = u at hu ⊢
        have hu2 : 0 < u + 2 := by linarith
        field_simp; ring
      rw [hq] at hst
      have hv := (S.profile k).2
      calc _ ≤ NV ε c * (144 / ε * (4050 / (7 * c * Real.sqrt ε) + 81 / 8 * (ψ k - ψ (k + 1)))) :=
            mul_le_mul hv ((hΔ k hk.1).trans (by gcongr)) (norm_nonneg _) hNV
        _ = _ := by ring
    have hψ : ∀ k, 1 ≤ k → ψ (k + 1) ≤ ψ k := fun k hk => by
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      simp only [ψ]; push_cast
      apply one_div_le_one_div_of_le (by linarith); linarith
    calc _ ≤ ∑ k ∈ Ico 1 (J + 1), 144 / ε * NV ε c * (4050 / (7 * c * Real.sqrt ε) + 81 / 8 * (ψ k - ψ (k + 1))) :=
          Finset.sum_le_sum hpt
      _ = 144 / ε * NV ε c * ((J : ℝ) * (4050 / (7 * c * Real.sqrt ε)) + 81 / 8 * (ψ 1 - ψ (J + 1))) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum,
            Cvs.Prolate.Mellin.StepAmplification.sum_Ico_sub (by omega)]
          rw [Nat.card_Ico, nsmul_eq_mul, Nat.add_sub_cancel]
      _ ≤ 144 / ε * NV ε c * ((c + 1) * (4050 / (7 * c * Real.sqrt ε)) + 27 / 8) := by
          have hJ := Jn_le (c := c) S.h
          have h1 : ψ 1 ≤ 1 / 3 := by
            simp only [ψ]; push_cast
            rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
          have h2 : 0 ≤ ψ (J + 1) := by
            simp only [ψ]; push_cast; have := (J : ℕ).cast_nonneg (α := ℝ)
            apply div_nonneg zero_le_one; linarith
          gcongr
          linarith
  -- far part
  have hfar : ∑ k ∈ Ico (J + 1) K, ‖vk c χ s₀ k‖
        * ‖(1 + Af c χ (s₀ + 2 * (k : ℂ)))⁻¹ - (1 + Af c χ (s₀ + 2 * ((k - 1 : ℕ) : ℂ)))⁻¹‖
      ≤ 216000 / ε * (8100 / (14 * c) + 81 / (32 * c ^ 2)) := by
    set D0 := 8100 / (14 * c) + 81 / (32 * c ^ 2)
    set φ := fun k : ℕ => 1 / (s₀.re + 2 * (k : ℝ))
    have hpt : ∀ k ∈ Ico (J + 1) K, ‖vk c χ s₀ k‖
        * ‖(1 + Af c χ (s₀ + 2 * (k : ℂ)))⁻¹ - (1 + Af c χ (s₀ + 2 * ((k - 1 : ℕ) : ℂ)))⁻¹‖
          ≤ 144 / ε * D0 * (3000 * c) * (φ k - φ (k + 1)) := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      have hl := Cvs.Prolate.Mellin.StepAmplification.hyp_line S.h (k - 1)
      have hJx := le_re_Jn (c := c) (s₀ := s₀)
      have hJk : (J : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (show J ≤ k - 1 by omega)
      have hfx : 2 * c ≤ (s₀ + 2 * ((k - 1 : ℕ) : ℂ)).re := by rw [re_line]; linarith
      have hst := Cvs.Prolate.Mellin.PropagationFactorSizes.Hyp.norm_Af_step_le_far hl hε4 hfx
      have hD : 8100 / (7 * (s₀ + 2 * ((k - 1 : ℕ) : ℂ)).re) + 81 / (8 * (s₀ + 2 * ((k - 1 : ℕ) : ℂ)).re ^ 2) ≤ D0 := by
        set y := (s₀ + 2 * ((k - 1 : ℕ) : ℂ)).re
        have hy : 0 < y := by linarith
        have a1 : 8100 / (7 * y) ≤ 8100 / (14 * c) := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity); linarith
        have a2 : 81 / (8 * y ^ 2) ≤ 81 / (32 * c ^ 2) := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity); nlinarith
        simp only [D0]; linarith
      have hxk : 2 * c ≤ s₀.re + 2 * (k : ℝ) := by
        have : (J : ℝ) ≤ k := by exact_mod_cast (show J ≤ k by omega)
        linarith
      have hv := S.far_decay k (by omega)
      have hcube := inv_cube_le (X := 2 * c) (y := s₀.re + 2 * (k : ℝ)) (by linarith [S.h.c_ge]) hxk
      have hv' : ‖vk c χ s₀ k‖ ≤ 3000 * c * (φ k - φ (k + 1)) := by
        refine hv.trans ?_
        simp only [φ]; push_cast
        rw [show s₀.re + 2 * ((k : ℝ) + 1) = s₀.re + 2 * k + 2 by ring]
        calc 6000 * c ^ 2 / (s₀.re + 2 * k) ^ 3 = 6000 * c ^ 2 * (1 / (s₀.re + 2 * k) ^ 3) := by ring
          _ ≤ 6000 * c ^ 2 * (1 / (2 * c) * (1 / (s₀.re + 2 * k) - 1 / (s₀.re + 2 * k + 2))) := by gcongr
          _ = _ := by field_simp; ring
      have hφ : 0 ≤ φ k - φ (k + 1) := by
        simp only [φ]; push_cast
        have : 0 < s₀.re + 2 * (k : ℝ) := by linarith
        rw [sub_nonneg]; apply one_div_le_one_div_of_le this; linarith
      calc _ ≤ (3000 * c * (φ k - φ (k + 1))) * (144 / ε * D0) :=
            mul_le_mul hv' ((hΔ k (by omega)).trans (by gcongr; exact hst.trans hD)) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    calc _ ≤ ∑ k ∈ Ico (J + 1) K, 144 / ε * D0 * (3000 * c) * (φ k - φ (k + 1)) := Finset.sum_le_sum hpt
      _ = 144 / ε * D0 * (3000 * c) * (φ (J + 1) - φ K) := by rw [← Finset.mul_sum, Cvs.Prolate.Mellin.StepAmplification.sum_Ico_sub hK]
      _ ≤ 144 / ε * D0 * (3000 * c) * (1 / (2 * c)) := by
          have hD0 : 0 ≤ D0 := by positivity
          gcongr
          have := le_re_Jn (c := c) (s₀ := s₀)
          have h1 : φ (J + 1) ≤ 1 / (2 * c) := by
            simp only [φ]; push_cast; apply one_div_le_one_div_of_le (by positivity); linarith
          have h2 : 0 ≤ φ K := by simp only [φ]; have := K.cast_nonneg (α := ℝ); positivity
          linarith
      _ = 216000 / ε * D0 := by field_simp; ring
  unfold DV; linarith

/-- **Step errors against the frozen forcing.** -/
theorem Std.sum_log_sub_le (S : Std ε c s₀) (K : ℕ) (hK : Jn c s₀ + 1 ≤ K) :
    ‖∑ k ∈ Ico 0 K, (Complex.log (1 + vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ k) - betaf c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (s₀ + 2 * (k : ℂ)))‖
      ≤ E1 ε c + (1 + 12 / Real.sqrt ε) * ‖vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ K‖ := by
  set χ := Cvs.Prolate.EvenRungsByIndex.lev c 0
  have hc := S.h.c_pos
  have hε := S.h.hε
  have hε4 : ε ≤ 1 / 4 := by linarith [S.hε16]
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hNV : 0 ≤ NV ε c := (norm_nonneg _).trans (S.profile 0).2
  set v := vk c χ s₀
  set A := fun k : ℕ => Af c χ (s₀ + 2 * (k : ℂ))
  set β := fun k : ℕ => betaf c χ (s₀ + 2 * (k : ℂ))
  set n := fun k : ℕ => A k * v (k + 1) ^ 2 / (1 + v (k + 1))
  have hA0 : ∀ k, Real.sqrt ε / 12 ≤ ‖1 + A k‖ := fun k =>
    Cvs.Prolate.Mellin.PropagationFactorSizes.Hyp.norm_one_add_Af_ge' (Cvs.Prolate.Mellin.StepAmplification.hyp_line S.h k) hε4
  have hAne : ∀ k, 1 + A k ≠ 0 := fun k h0 => by have := hA0 k; rw [h0, norm_zero] at this; linarith
  have ha : ∀ k, ‖(1 + A k)⁻¹‖ ≤ 12 / Real.sqrt ε := fun k =>
    Cvs.Prolate.Mellin.PropagationFactorSizes.Hyp.norm_inv_one_add_Af_le (Cvs.Prolate.Mellin.StepAmplification.hyp_line S.h k) hε4
  have hsq0 := S.sum_sq_le 0 K hK
  have hsq1 := S.sum_sq_le 1 K hK
  simp only [Nat.add_zero] at hsq0
  -- split
  have esplit : ∑ k ∈ Ico 0 K, (Complex.log (1 + v k) - β k)
      = ∑ k ∈ Ico 0 K, (Complex.log (1 + v k) - v k) + ∑ k ∈ Ico 0 K, (v k - β k) := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [esplit]
  -- the logarithm
  have hlog : ‖∑ k ∈ Ico 0 K, (Complex.log (1 + v k) - v k)‖ ≤ (c + 2) * NV ε c ^ 2 + 1125000 / c := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun k _ => ?_).trans hsq0)
    have hk := S.small k
    have := Complex.norm_log_one_add_sub_self_le (z := v k) (by linarith)
    refine this.trans ?_
    have h1 : (1 - ‖v k‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have := sq_nonneg ‖v k‖
    calc ‖v k‖ ^ 2 * (1 - ‖v k‖)⁻¹ / 2 ≤ ‖v k‖ ^ 2 * 2 / 2 := by gcongr
      _ = ‖v k‖ ^ 2 := by ring
  -- the recursion part
  have hmain := Cvs.Upstream.RecursionFrozenForcingSum.norm_sum_sub_le (A := A) (β := β) (n := n) (v := v) (m := 0) (K := K)
    (by omega) (fun k _ _ => hAne k) (fun k _ _ => S.recur k)
  have hn : ∑ k ∈ Ico 0 K, ‖(1 + A k)⁻¹‖ * ‖n k‖
      ≤ 225 / (2 * Real.sqrt ε) * ((c + 2) * NV ε c ^ 2 + 1125000 / c) := by
    have hpt : ∀ k ∈ Ico 0 K, ‖(1 + A k)⁻¹‖ * ‖n k‖ ≤ 225 / (2 * Real.sqrt ε) * ‖v (k + 1)‖ ^ 2 := by
      intro k _
      have hv := S.small (k + 1)
      have h1v : 9 / 10 ≤ ‖1 + v (k + 1)‖ := by
        have := norm_sub_norm_le (1 : ℂ) (-v (k + 1))
        rw [norm_neg, sub_neg_eq_add, norm_one] at this; linarith
      have hAk := Cvs.Prolate.Mellin.PropagationFactorSizes.Hyp.norm_Af_le_const (Cvs.Prolate.Mellin.StepAmplification.hyp_line S.h k)
      have hnk : ‖n k‖ ≤ 135 / 16 * (10 / 9) * ‖v (k + 1)‖ ^ 2 := by
        simp only [n]; rw [norm_div, norm_mul, norm_pow, div_le_iff₀ (by linarith)]
        have := sq_nonneg ‖v (k + 1)‖
        calc ‖A k‖ * ‖v (k + 1)‖ ^ 2 ≤ 135 / 16 * ‖v (k + 1)‖ ^ 2 := by gcongr
          _ ≤ 135 / 16 * (10 / 9) * ‖v (k + 1)‖ ^ 2 * (9 / 10) := by nlinarith
          _ ≤ _ := by gcongr
      calc _ ≤ 12 / Real.sqrt ε * (135 / 16 * (10 / 9) * ‖v (k + 1)‖ ^ 2) :=
            mul_le_mul (ha k) hnk (norm_nonneg _) (by positivity)
        _ = _ := by field_simp; ring
    calc _ ≤ ∑ k ∈ Ico 0 K, 225 / (2 * Real.sqrt ε) * ‖v (k + 1)‖ ^ 2 := Finset.sum_le_sum hpt
      _ = 225 / (2 * Real.sqrt ε) * ∑ k ∈ Ico 0 K, ‖v (k + 1)‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ _ := by gcongr
  have hK1 : (1 + ‖(1 + A (K - 1))⁻¹‖) * ‖v K‖ ≤ (1 + 12 / Real.sqrt ε) * ‖v K‖ := by
    gcongr; exact ha _
  have h01 : (1 + ‖(1 + A 0)⁻¹‖) * ‖v 0‖ ≤ (1 + 12 / Real.sqrt ε) * NV ε c :=
    mul_le_mul (by linarith [ha 0]) (S.profile 0).2 (norm_nonneg _) (by positivity)
  have hdv := S.sum_dv_le K hK
  have hdv' : ∑ k ∈ Ico (0 + 1) K, ‖v k‖ * ‖(1 + A k)⁻¹ - (1 + A (k - 1))⁻¹‖ ≤ DV ε c := hdv
  have := norm_add_le (∑ k ∈ Ico 0 K, (Complex.log (1 + v k) - v k)) (∑ k ∈ Ico 0 K, (v k - β k))
  unfold E1
  nlinarith

end Cvs.Prolate.Mellin.GroundRatioStepErrors
