import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailFloorLimit
import Cvs.L2a.L1FullTailWinfBound
import Cvs.L2a.L1WindowFromFloor
import Cvs.Prolate.AngularBesselInequality
import Cvs.Prolate.RungTailMassLower

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The profile data of a rung span are powers of `c`

For a rung with `μ ≥ 1/c`: `|h(±1)| ≤ 2c`, `|h'(±1)| ≤ c³`, `∫|h''| ≤ 3c³` (Cvs.Prolate.RungTailMassLower), `∫₁^∞ψ² ≤ 1`. For a span with
`Σ|bᵢ| ≤ c`, `c ≥ 80`: `B_G ≤ c³`, `K₁ᵦ ≤ c⁷`, `α, β ≤ c³`, `N ≤ c⁶`, `D ≤ c⁸`, `P ≤ c²`, and `V ≥ κ/(64c⁴)` when
some `|bᵢ| ≥ 1`. So every level of L1 and of the frame is `O(c)` with an `O(log c)` remainder.
-/

noncomputable section

open Real Set MeasureTheory
open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.L2a.FullTailConvergence (fullTail BG K1b)

namespace Cvs.L2a.RungSpanProfilePowers

/-- **One rung's data in powers of `c`**, for `μ ≥ 1/c`, `0 ≤ χ < c²`, `c ≥ 4`. -/
theorem rung_data {g g₁ g₂ : ℝ → ℝ} {c χ μ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hnorm : ∫ s in (-1 : ℝ)..1, g s ^ 2 = 1)
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) (hc : 4 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2)
    (hμc : 1 / c ≤ μ) :
    (∫ s in (-1 : ℝ)..1, |g s|) ≤ 2 ∧ |g 1| ≤ 2 * c ∧ |g (-1)| ≤ 2 * c ∧ |g₁ 1| ≤ c ^ 3 ∧ |g₁ (-1)| ≤ c ^ 3
      ∧ (∫ s in (-1 : ℝ)..1, |g₂ s|) ≤ 3 * c ^ 3 ∧ (∫ ξ in Ioi 1, psi c g ξ ^ 2) ≤ 1 := by
  have hc0 : 0 < c := by linarith
  have hμ0 : 0 < μ := lt_of_lt_of_le (by positivity) hμc
  have hgc : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  have hgc' : ContinuousOn g (Icc (-1) 1) := by
    rw [← uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]; exact hgc
  have hI := Cvs.Prolate.RungTailMassLower.integral_abs_le_sqrt_two hgc' hnorm
  have hs2 : √2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  set I := ∫ s in (-1 : ℝ)..1, |g s|
  have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg (by norm_num) fun _ _ => abs_nonneg _
  have hinv : 1 / μ ≤ c := by
    rw [div_le_iff₀ hμ0]; have := mul_le_mul_of_nonneg_left hμc hc0.le
    rw [mul_one_div_cancel hc0.ne'] at this; linarith
  have hIμ : I / μ ≤ 2 * c := by
    rw [div_eq_mul_one_div]
    nlinarith [mul_le_mul hI hinv (by positivity) (by positivity)]
  have h1 : |g 1| ≤ 2 * c := by
    have := Cvs.Prolate.RungTailMassLower.abs_endpoint_le (c := c) hgc hμ0.ne' hμ
    rw [abs_of_pos hμ0] at this; linarith
  have hm1 : |g (-1)| ≤ 2 * c := by
    have := Cvs.Prolate.RungTailMassLower.abs_endpoint_neg_le (c := c) hgc hμ0.ne' hμ
    rw [abs_of_pos hμ0] at this; linarith
  obtain ⟨hd1, hdm1⟩ := Cvs.Prolate.RungTailMassLower.deriv_endpoints hang
  have hχc : |χ - c ^ 2| ≤ c ^ 2 := by rw [abs_le]; constructor <;> nlinarith
  have hχc' : |c ^ 2 - χ| ≤ c ^ 2 := by rw [abs_sub_comm]; exact hχc
  have hd1' : |g₁ 1| ≤ c ^ 3 := by
    rw [hd1, abs_div, abs_mul, abs_two]
    have := mul_le_mul hχc h1 (abs_nonneg _) (sq_nonneg c)
    nlinarith
  have hdm1' : |g₁ (-1)| ≤ c ^ 3 := by
    rw [hdm1, abs_div, abs_mul, abs_two]
    have := mul_le_mul hχc' hm1 (abs_nonneg _) (sq_nonneg c)
    nlinarith
  have h2 := Cvs.Prolate.RungTailMassLower.integral_abs_second_le hg hg₁ hg₂c hμ0.ne' hμ
  rw [abs_of_pos hμ0] at h2
  have h2' : (∫ s in (-1 : ℝ)..1, |g₂ s|) ≤ 3 * c ^ 3 := by
    have e : 2 * (c ^ 2 * I / μ) = 2 * c ^ 2 * (I / μ) := by ring
    rw [e] at h2
    have hIμ' : I / μ ≤ 3 / 2 * c := by
      rw [div_eq_mul_one_div]
      nlinarith [mul_le_mul (hI.trans hs2) hinv (by positivity) (by positivity)]
    nlinarith [sq_nonneg c]
  have hmass := Cvs.Prolate.AngularBesselInequality.mass_eq hc0 hgc' heven hμ hnorm
  have hM : (∫ ξ in Ioi 1, psi c g ξ ^ 2) ≤ 1 := by
    rw [hmass]
    have hpc : π / c ≤ 1 := by rw [div_le_one hc0]; linarith [Real.pi_lt_four]
    have h1l : 1 - (μ * √(c / (2 * π))) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (μ * √(c / (2 * π)))]
    have hpc0 : 0 ≤ π / c := by positivity
    by_cases hl : 0 ≤ 1 - (μ * √(c / (2 * π))) ^ 2
    · calc π / c * (1 - (μ * √(c / (2 * π))) ^ 2) ≤ 1 * 1 := mul_le_mul hpc h1l hl zero_le_one
        _ = 1 := one_mul 1
    · push Not at hl
      nlinarith
  exact ⟨hI.trans (hs2.trans (by norm_num)), h1, hm1, hd1', hdm1', h2', hM⟩

variable {ι : Type} [Fintype ι]

/-- Span data, under `Σ|bᵢ| ≤ c`, `μᵢ ≥ 1/c`, `c ≥ 80`. -/
structure SpanHyp (c : ℝ) (b : ι → ℝ) (h h₁ h₂ : ι → ℝ → ℝ) (χ μ : ι → ℝ) : Prop where
  hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (h i) (h₁ i s) s
  hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (h₁ i) (h₂ i s) s
  hg₂c : ∀ i, ContinuousOn (h₂ i) (uIcc (-1) 1)
  hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
    (1 - s ^ 2) * h₂ i s - 2 * s * h₁ i s - c ^ 2 * s ^ 2 * h i s + χ i * h i s = 0
  heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, h i (-s) = h i s
  hnorm : ∀ i, ∫ s in (-1 : ℝ)..1, h i s ^ 2 = 1
  hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (h i) s = μ i * h i s
  hc : 80 ≤ c
  hχ0 : ∀ i, 0 ≤ χ i
  hχc : ∀ i, χ i < c ^ 2
  hμc : ∀ i, 1 / c ≤ μ i
  hS : ∑ i, |b i| ≤ c

variable {c : ℝ} {b : ι → ℝ} {h h₁ h₂ : ι → ℝ → ℝ} {χ μ : ι → ℝ}

theorem SpanHyp.data (H : SpanHyp c b h h₁ h₂ χ μ) (i : ι) :
    (∫ s in (-1 : ℝ)..1, |h i s|) ≤ 2 ∧ |h i 1| ≤ 2 * c ∧ |h i (-1)| ≤ 2 * c ∧ |h₁ i 1| ≤ c ^ 3
      ∧ |h₁ i (-1)| ≤ c ^ 3 ∧ (∫ s in (-1 : ℝ)..1, |h₂ i s|) ≤ 3 * c ^ 3
      ∧ (∫ ξ in Ioi 1, psi c (h i) ξ ^ 2) ≤ 1 :=
  rung_data (H.hg i) (H.hg₁ i) (H.hg₂c i) (H.hang i) (H.heven i) (H.hnorm i) (H.hμ i) (by linarith [H.hc])
    (H.hχ0 i) (H.hχc i) (H.hμc i)

private theorem SpanHyp.sum_abs_mul_le (H : SpanHyp c b h h₁ h₂ χ μ) {f : ι → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ i, |f i| ≤ B) : |∑ i, b i * f i| ≤ c * B := by
  calc |∑ i, b i * f i| ≤ ∑ i, |b i| * B := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hf i) (abs_nonneg _)
    _ = (∑ i, |b i|) * B := by rw [Finset.sum_mul]
    _ ≤ c * B := mul_le_mul_of_nonneg_right H.hS hB

/-- `|A| ≤ 4c²`, `A = G(1) + G(−1)`. -/
theorem SpanHyp.abs_A_le (H : SpanHyp c b h h₁ h₂ χ μ) :
    |(fun t => ∑ i, b i * h i t) 1 + (fun t => ∑ i, b i * h i t) (-1)| ≤ 4 * c ^ 2 := by
  have hc0 : 0 ≤ c := by linarith [H.hc]
  have h1 := H.sum_abs_mul_le (f := fun i => h i 1) (by positivity) fun i => (H.data i).2.1
  have h2 := H.sum_abs_mul_le (f := fun i => h i (-1)) (by positivity) fun i => (H.data i).2.2.1
  simp only at h1 h2 ⊢
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ c * (2 * c) + c * (2 * c) := add_le_add h1 h2
    _ = 4 * c ^ 2 := by ring

/-- `C₁ ≤ 5c⁴`, `C₁ = |G'(1) − G'(−1)| + ∫|G''|`. -/
theorem SpanHyp.C1_le (H : SpanHyp c b h h₁ h₂ χ μ) :
    |(fun t => ∑ i, b i * h₁ i t) 1 - (fun t => ∑ i, b i * h₁ i t) (-1)|
      + ∫ s in (-1 : ℝ)..1, |(fun t => ∑ i, b i * h₂ i t) s| ≤ 5 * c ^ 4 := by
  have hc0 : 0 ≤ c := by linarith [H.hc]
  have h1 := H.sum_abs_mul_le (f := fun i => h₁ i 1) (by positivity) fun i => (H.data i).2.2.2.1
  have h2 := H.sum_abs_mul_le (f := fun i => h₁ i (-1)) (by positivity) fun i => (H.data i).2.2.2.2.1
  simp only at h1 h2 ⊢
  have hd : |∑ i, b i * h₁ i 1 - ∑ i, b i * h₁ i (-1)| ≤ 2 * c ^ 4 := by
    calc _ ≤ _ := abs_sub _ _
      _ ≤ c * c ^ 3 + c * c ^ 3 := add_le_add h1 h2
      _ = 2 * c ^ 4 := by ring
  have hint : ∀ i, IntervalIntegrable (fun s => |h₂ i s|) volume (-1) 1 := fun i =>
    ((H.hg₂c i).abs).intervalIntegrable
  have hI : (∫ s in (-1 : ℝ)..1, |∑ i, b i * h₂ i s|) ≤ 3 * c ^ 4 := by
    calc (∫ s in (-1 : ℝ)..1, |∑ i, b i * h₂ i s|)
        ≤ ∫ s in (-1 : ℝ)..1, ∑ i, |b i| * |h₂ i s| := by
          refine intervalIntegral.integral_mono_on (by norm_num)
            (((continuousOn_finsetSum _ fun i _ => continuousOn_const.mul (H.hg₂c i)).abs).intervalIntegrable)
            (by
              refine (continuousOn_finsetSum _ fun i _ => continuousOn_const.mul ((H.hg₂c i).abs)).intervalIntegrable)
            fun s _ => ?_
          refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
          exact Finset.sum_congr rfl fun i _ => abs_mul _ _
      _ = ∑ i, |b i| * ∫ s in (-1 : ℝ)..1, |h₂ i s| := by
          rw [intervalIntegral.integral_finsetSum fun i _ => (hint i).const_mul _]
          exact Finset.sum_congr rfl fun i _ => intervalIntegral.integral_const_mul _ _
      _ ≤ ∑ i, |b i| * (3 * c ^ 3) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (H.data i).2.2.2.2.2.1 (abs_nonneg _)
      _ = (∑ i, |b i|) * (3 * c ^ 3) := by rw [Finset.sum_mul]
      _ ≤ c * (3 * c ^ 3) := mul_le_mul_of_nonneg_right H.hS (by positivity)
      _ = 3 * c ^ 4 := by ring
  linarith

/-- `B_G ≤ c³`. -/
theorem SpanHyp.BG_le (H : SpanHyp c b h h₁ h₂ χ μ) :
    BG c ((fun t => ∑ i, b i * h i t) 1 + (fun t => ∑ i, b i * h i t) (-1))
      (|(fun t => ∑ i, b i * h₁ i t) 1 - (fun t => ∑ i, b i * h₁ i t) (-1)|
        + ∫ s in (-1 : ℝ)..1, |(fun t => ∑ i, b i * h₂ i t) s|) ≤ c ^ 3 := by
  have hc := H.hc
  have hc0 : 0 < c := by linarith
  have hA := H.abs_A_le
  have hC := H.C1_le
  unfold BG
  have hp4 := Real.pi_lt_four
  have hp0 := Real.pi_pos
  have e1 : (1 + π) * |(fun t => ∑ i, b i * h i t) 1 + (fun t => ∑ i, b i * h i t) (-1)| / c ≤ 20 * c := by
    rw [div_le_iff₀ hc0]
    nlinarith [abs_nonneg ((fun t => ∑ i, b i * h i t) 1 + (fun t => ∑ i, b i * h i t) (-1))]
  have e2 : π ^ 2 / 6 * (|(fun t => ∑ i, b i * h₁ i t) 1 - (fun t => ∑ i, b i * h₁ i t) (-1)|
        + ∫ s in (-1 : ℝ)..1, |(fun t => ∑ i, b i * h₂ i t) s|) / c ^ 2 ≤ 14 * c ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have hπ2 : π ^ 2 / 6 ≤ 16 / 6 := by nlinarith
    have hC0 : 0 ≤ |(fun t => ∑ i, b i * h₁ i t) 1 - (fun t => ∑ i, b i * h₁ i t) (-1)|
        + ∫ s in (-1 : ℝ)..1, |(fun t => ∑ i, b i * h₂ i t) s| :=
      Cvs.L2a.FullTailConvergence.C1_nonneg (fun t => ∑ i, b i * h₁ i t) (fun t => ∑ i, b i * h₂ i t)
    nlinarith [mul_le_mul hπ2 hC (by positivity) (by norm_num)]
  nlinarith

/-- `K₁ᵦ ≤ c⁷`. -/
theorem SpanHyp.K1bS_le (H : SpanHyp c b h h₁ h₂ χ μ) : Cvs.L2a.L1FullTailWinfBound.K1bS c b h h₁ h₂ ≤ c ^ 7 := by
  have hc := H.hc
  have hc0 : 0 < c := by linarith
  have hA := H.abs_A_le
  have hC := H.C1_le
  have hB := H.BG_le
  unfold Cvs.L2a.L1FullTailWinfBound.K1bS K1b
  set A := (fun t => ∑ i, b i * h i t) 1 + (fun t => ∑ i, b i * h i t) (-1)
  set C := |(fun t => ∑ i, b i * h₁ i t) 1 - (fun t => ∑ i, b i * h₁ i t) (-1)|
        + ∫ s in (-1 : ℝ)..1, |(fun t => ∑ i, b i * h₂ i t) s|
  have hC0 : 0 ≤ C := Cvs.L2a.FullTailConvergence.C1_nonneg (fun t => ∑ i, b i * h₁ i t) (fun t => ∑ i, b i * h₂ i t)
  have hB0 : 0 ≤ BG c A C := Cvs.L2a.FullTailConvergence.BG_nonneg hc0 A hC0
  have hp4 := Real.pi_lt_four
  have hp0 := Real.pi_pos
  have hA2 : A ^ 2 ≤ 16 * c ^ 4 := by
    rw [← sq_abs]; nlinarith [abs_nonneg A]
  have t1 : 16 * (1 + π) * A ^ 2 * (3 + 8 * π / c) / c ^ 2 ≤ 16 * 5 * (16 * c ^ 4) * 4 / c ^ 2 := by
    have h8 : 8 * π / c ≤ 1 := by rw [div_le_one hc0]; linarith
    gcongr
    · linarith
    · linarith
  have t1' : 16 * 5 * (16 * c ^ 4) * 4 / c ^ 2 = 5120 * c ^ 2 := by field_simp; ring
  have t2 : 8 * C ^ 2 / c ^ 4 ≤ 200 * c ^ 4 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [mul_le_mul hC hC hC0 (by positivity)]
  have t3 : BG c A C ^ 2 ≤ c ^ 6 := by nlinarith [mul_le_mul hB hB hB0 (by positivity)]
  have hc2 : 5120 * c ^ 2 ≤ c ^ 6 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 80) hc 4]
  have hc4 : 200 * c ^ 4 ≤ c ^ 6 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 80) hc 2]
  have hc6 : 3 * c ^ 6 ≤ c ^ 7 := by nlinarith [pow_pos hc0 6]
  linarith

/-- `α ≤ c³` and `β ≤ c³`. -/
theorem SpanHyp.alphaS_betaS_le (H : SpanHyp c b h h₁ h₂ χ μ) :
    Cvs.L2a.L1FullTailWinfBound.alphaS c b h ≤ c ^ 3 ∧ Cvs.L2a.L1FullTailWinfBound.betaS c b h ≤ c ^ 3 := by
  have hc := H.hc
  have hc0 : 0 < c := by linarith
  constructor
  · unfold Cvs.L2a.L1FullTailWinfBound.alphaS
    calc _ ≤ ∑ i, |b i| * (2 * (3 * 2 + 2 * (c * 2))) := Finset.sum_le_sum fun i _ => by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          have := (H.data i).1
          nlinarith
      _ = (∑ i, |b i|) * (2 * (3 * 2 + 2 * (c * 2))) := by rw [Finset.sum_mul]
      _ ≤ c * (2 * (3 * 2 + 2 * (c * 2))) := mul_le_mul_of_nonneg_right H.hS (by positivity)
      _ ≤ c ^ 3 := by nlinarith [mul_nonneg (mul_nonneg hc0.le hc0.le) (show 0 ≤ c - 80 by linarith)]
  · unfold Cvs.L2a.L1FullTailWinfBound.betaS
    have hs6 : √(6 : ℝ) ≤ 3 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    calc _ ≤ ∑ i, |b i| * (74 * 3) := Finset.sum_le_sum fun i _ => by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          have hM := (H.data i).2.2.2.2.2.2
          have : √(6 * ∫ t in Ioi 1, psi c (h i) t ^ 2) ≤ 3 :=
            (Real.sqrt_le_sqrt (by linarith)).trans hs6
          linarith
      _ = (∑ i, |b i|) * (74 * 3) := by rw [Finset.sum_mul]
      _ ≤ c * (74 * 3) := mul_le_mul_of_nonneg_right H.hS (by positivity)
      _ ≤ c ^ 3 := by
          have h1 := mul_nonneg (mul_nonneg hc0.le hc0.le) (show 0 ≤ c - 80 by linarith)
          have h2 := mul_nonneg hc0.le (show 0 ≤ c - 80 by linarith)
          nlinarith

/-- `N ≤ c⁶`. -/
theorem SpanHyp.tailN_le (H : SpanHyp c b h h₁ h₂ χ μ) : Cvs.L2a.L1WindowFromFloor.tailN c b h ≤ c ^ 6 := by
  have hc0 : 0 < c := by linarith [H.hc]
  have hG := Cvs.L2a.FullTailFloorLimit.hasDerivAt_span b H.hg
  have hG₁ := Cvs.L2a.FullTailFloorLimit.hasDerivAt_span b H.hg₁
  have hG₂ := Cvs.L2a.FullTailFloorLimit.continuousOn_span b H.hg₂c
  unfold Cvs.L2a.L1WindowFromFloor.tailN
  rw [Cvs.L2a.FullTailFloorLimit.span_eq b H.hg c]
  have hT := Cvs.L2a.FullTailConvergence.integral_sq_le_of_le (Cvs.L2a.FullTailConvergence.measurable_fullTail hG hG₁ hG₂ hc0)
    fun θ hθ => Cvs.L2a.FullTailConvergence.abs_fullTail_le hG hG₁ hG₂ hc0 hθ
  have hB := H.BG_le
  have hB0 := Cvs.L2a.FullTailConvergence.BG_nonneg hc0 ((fun t => ∑ i, b i * h i t) 1 + (fun t => ∑ i, b i * h i t) (-1))
    (Cvs.L2a.FullTailConvergence.C1_nonneg (fun t => ∑ i, b i * h₁ i t) (fun t => ∑ i, b i * h₂ i t))
  nlinarith [mul_le_mul hB hB hB0 (by positivity)]

/-- `D ≤ c⁸`. -/
theorem SpanHyp.levD_le (H : SpanHyp c b h h₁ h₂ χ μ) : Cvs.L2a.L1WindowFromFloor.levD c b h h₁ h₂ ≤ c ^ 8 := by
  have hc := H.hc
  have hc0 : 0 < c := by linarith
  obtain ⟨hα, hβ⟩ := H.alphaS_betaS_le
  have hα0 := Cvs.L2a.L1FullTailWinfBound.alphaS_nonneg hc0.le b h
  have hβ0 := Cvs.L2a.L1FullTailWinfBound.betaS_nonneg c b h
  have hK := H.K1bS_le
  have hN := H.tailN_le
  unfold Cvs.L2a.L1WindowFromFloor.levD
  have t1 : 2 * Cvs.L2a.L1FullTailWinfBound.alphaS c b h ^ 2 / (2 * c) ≤ c ^ 5 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [mul_le_mul hα hα hα0 (by positivity)]
  have t2 : 50 * Cvs.L2a.L1FullTailWinfBound.betaS c b h ^ 2 / (2 * c) ≤ 25 * c ^ 5 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [mul_le_mul hβ hβ hβ0 (by positivity)]
  have h5 : 51 * c ^ 5 ≤ c ^ 6 := by nlinarith [pow_pos hc0 5]
  have h6 : 2 * c ^ 6 ≤ c ^ 7 := by nlinarith [pow_pos hc0 6]
  have h7 : 4 * c ^ 7 ≤ c ^ 8 := by nlinarith [pow_pos hc0 7]
  linarith

/-- `P ≤ c²`. -/
theorem SpanHyp.P_le (H : SpanHyp c b h h₁ h₂ χ μ) : ∑ i, b i ^ 2 * (∫ t in Ioi 1, psi c (h i) t ^ 2) ≤ c ^ 2 := by
  have hc0 : 0 ≤ c := by linarith [H.hc]
  calc ∑ i, b i ^ 2 * (∫ t in Ioi 1, psi c (h i) t ^ 2) ≤ ∑ i, |b i| * |b i| := Finset.sum_le_sum fun i _ => by
        rw [← sq, sq_abs]
        have := (H.data i).2.2.2.2.2.2
        nlinarith [sq_nonneg (b i)]
    _ ≤ ∑ i, |b i| * c := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left ((Finset.single_le_sum (fun j _ => abs_nonneg (b j)) (Finset.mem_univ i)).trans H.hS)
          (abs_nonneg _)
    _ = (∑ i, |b i|) * c := by rw [Finset.sum_mul]
    _ ≤ c * c := mul_le_mul_of_nonneg_right H.hS hc0
    _ = c ^ 2 := by ring

/-- `V ≥ κ/(64c⁴)` when some `|bᵢ| ≥ 1`. -/
theorem SpanHyp.endV_ge (H : SpanHyp c b h h₁ h₂ χ μ) {κ : ℝ} (hκ : 0 ≤ κ) {i₀ : ι} (hb : 1 ≤ |b i₀|) :
    κ / (64 * c ^ 4) ≤ Cvs.L2a.L1WindowFromFloor.endV c κ b μ := by
  have hc0 : 0 < c := by linarith [H.hc]
  unfold Cvs.L2a.L1WindowFromFloor.endV
  have hμ0 : 0 < μ i₀ := lt_of_lt_of_le (by positivity) (H.hμc i₀)
  have hμ3 : 1 / c ^ 3 ≤ |μ i₀| ^ 3 := by
    rw [abs_of_pos hμ0, one_div, ← inv_pow, ← one_div]
    exact pow_le_pow_left₀ (by positivity) (H.hμc i₀) 3
  have hb2 : 1 ≤ b i₀ ^ 2 := by nlinarith [sq_abs (b i₀), abs_nonneg (b i₀)]
  have hsum : 1 / c ^ 3 ≤ ∑ i, b i ^ 2 * |μ i| ^ 3 :=
    calc 1 / c ^ 3 ≤ b i₀ ^ 2 * |μ i₀| ^ 3 := by nlinarith [pow_nonneg (abs_nonneg (μ i₀)) 3]
      _ ≤ _ := Finset.single_le_sum (f := fun i => b i ^ 2 * |μ i| ^ 3)
          (fun i _ => mul_nonneg (sq_nonneg _) (pow_nonneg (abs_nonneg _) 3)) (Finset.mem_univ i₀)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have := mul_le_mul_of_nonneg_left hsum hκ
  have e : κ * (1 / c ^ 3) * (64 * c ^ 4) = κ * (64 * c) := by field_simp
  nlinarith [mul_le_mul_of_nonneg_right this (by positivity : (0:ℝ) ≤ 64 * c ^ 4)]

end Cvs.L2a.RungSpanProfilePowers
