import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Harmonic.Bounds
import Cvs.L2a.NonresonantCrossIntegral
import Cvs.L2a.TelescopingIncreasingCoeff
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.Mellin.MellinKernelSturmLiouville
import Cvs.Prolate.Mellin.ModeMellinBelowGap
import Cvs.Prolate.Mellin.ModeMellinDyadicPiece
import Cvs.Prolate.Mellin.ModeMellinDyadicRange

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The first mode's Mellin transform below the gap, edge strip included

The Mellin kernels obey `|y| ≤ 1/√τ`, `|t²y'| ≤ (|ξ| + ½)√τ`. For the first mode on `[1, 2^{J+1}]`, split at
`1 + η`, `θ = √(1 + σ/c)` and `2` (`σ = √(c²−χ)`, `2w ≤ σ²`):
`|∫ ψ y| ≤ η|ψ(1)|Y + 8√2|ψ(1)|V/(cσ) + 32√2 √(cG) Y/σ² + 2P(2)`, with `P` from Cvs.Prolate.Mellin.ModeMellinDyadicRange.
-/

namespace Cvs.Prolate.Mellin.FirstModeMellinEdge

open Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.NonresonantCrossIntegral Cvs.Prolate.Mellin.MellinKernelSturmLiouville

theorem abs_ky_le {ξ t : ℝ} (ht : 0 < t) : |ky ξ t| ≤ 1 / √t := by
  unfold ky; rw [abs_div, abs_of_pos (sqrt_pos.mpr ht)]
  exact div_le_div_of_nonneg_right (abs_cos_le_one _) (sqrt_nonneg _)

theorem abs_ku_le {ξ t : ℝ} (ht : 0 < t) : |ku ξ t| ≤ (|ξ| + 1 / 2) * √t := by
  unfold ku
  rw [abs_neg, abs_mul, abs_of_nonneg (sqrt_nonneg t), mul_comm]
  apply mul_le_mul_of_nonneg_right _ (sqrt_nonneg t)
  calc |ξ * sin (ξ * log t) + cos (ξ * log t) / 2| ≤ |ξ * sin (ξ * log t)| + |cos (ξ * log t) / 2| :=
        abs_add_le _ _
    _ ≤ |ξ| * 1 + 1 / 2 := by
        rw [abs_mul, abs_div, abs_two]
        exact add_le_add (mul_le_mul_of_nonneg_left (abs_sin_le_one _) (abs_nonneg _))
          (div_le_div_of_nonneg_right (abs_cos_le_one _) (by norm_num))
    _ = |ξ| + 1 / 2 := by ring

theorem abs_kys_le {ξ t : ℝ} (ht : 0 < t) : |kys ξ t| ≤ 1 / √t := by
  unfold kys; rw [abs_div, abs_of_pos (sqrt_pos.mpr ht)]
  exact div_le_div_of_nonneg_right (abs_sin_le_one _) (sqrt_nonneg _)

theorem abs_kus_le {ξ t : ℝ} (ht : 0 < t) : |kus ξ t| ≤ (|ξ| + 1 / 2) * √t := by
  unfold kus
  rw [abs_mul, abs_of_nonneg (sqrt_nonneg t), mul_comm]
  apply mul_le_mul_of_nonneg_right _ (sqrt_nonneg t)
  calc |ξ * cos (ξ * log t) - sin (ξ * log t) / 2| ≤ |ξ * cos (ξ * log t)| + |sin (ξ * log t) / 2| :=
        abs_sub _ _
    _ ≤ |ξ| * 1 + 1 / 2 := by
        rw [abs_mul, abs_div, abs_two]
        exact add_le_add (mul_le_mul_of_nonneg_left (abs_cos_le_one _) (abs_nonneg _))
          (div_le_div_of_nonneg_right (abs_sin_le_one _) (by norm_num))
    _ = |ξ| + 1 / 2 := by ring

theorem pm_one (τ : ℝ) : pm 1 τ = pP τ := by unfold pm pP; ring
theorem qm_one (c χ τ : ℝ) : qm c χ 1 τ = qP c χ τ := by unfold qm qP; ring

/-- `D ≥ σ²/2` on `τ ≥ 1` when `2w ≤ c² − χ`. -/
theorem DE_one_ge {c χ w τ : ℝ} (hw : 0 ≤ w) (hgap : 2 * w ≤ c ^ 2 - χ) (hτ : 1 ≤ τ) :
    (c ^ 2 - χ) / 2 ≤ DE c χ 1 w τ := by
  unfold DE qm pm
  have h1 : 1 ≤ τ ^ 2 := by nlinarith
  have hc : 0 ≤ c ^ 2 := sq_nonneg c
  have hp : (1 ^ 2 * τ ^ 2 - 1) / 1 ^ 2 * w ≤ τ ^ 2 * w := by
    simp only [one_pow, one_mul, div_one]; nlinarith
  have : (c ^ 2 - χ) / 2 ≤ τ ^ 2 * (c ^ 2 * 1 ^ 2 * τ ^ 2 - χ) - τ ^ 2 * w := by
    have e : τ ^ 2 * (c ^ 2 * 1 ^ 2 * τ ^ 2 - χ) - τ ^ 2 * w = τ ^ 2 * (c ^ 2 * τ ^ 2 - χ - w) := by ring
    rw [e]
    have : (c ^ 2 - χ) / 2 ≤ c ^ 2 * τ ^ 2 - χ - w := by nlinarith
    have h0 : 0 ≤ (c ^ 2 - χ) / 2 := by linarith
    nlinarith
  linarith

set_option maxHeartbeats 1000000 in
/-- **The first mode on `[1, 2^{J+1}]`**, below the gap, in closed form. -/
theorem first_mode_le {c χ w G Y V η : ℝ} {ψ u y v : ℝ → ℝ} (J : ℕ)
    (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hw : 0 ≤ w) (hgap : 2 * w ≤ c ^ 2 - χ)
    (hG0 : 0 ≤ G) (hY : 0 ≤ Y) (hV : 0 ≤ V) (hη : 0 < η) (hηθ : 1 + η ≤ √(1 + √(c ^ 2 - χ) / c))
    (hψ : ∀ ξ ∈ Ioc 1 (2 ^ J * 2), HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Ioc 1 (2 ^ J * 2), HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hG : ∀ ξ ∈ Ioc 1 (2 ^ J * 2), energy (aP c χ) ψ u ξ ≤ G)
    (hcont : ContinuousOn ψ (Icc 1 (2 ^ J * 2))) (hedge : ∀ ξ ∈ Icc 1 2, |ψ ξ| ≤ |ψ 1|)
    (hy : ∀ τ ∈ Icc 1 (2 ^ J * 2), HasDerivAt y (v τ / τ ^ 2) τ)
    (hv : ∀ τ ∈ Icc 1 (2 ^ J * 2), HasDerivAt v (-(w * y τ)) τ)
    (hyb : ∀ τ ∈ Icc 1 (2 ^ J * 2), |y τ| ≤ Y / √τ) (hvb : ∀ τ ∈ Icc 1 (2 ^ J * 2), |v τ| ≤ V * √τ) :
    |∫ τ in (1 : ℝ)..2 ^ J * 2, ψ τ * y τ|
      ≤ η * |ψ 1| * Y + 8 * √2 * |ψ 1| * V / (c * √(c ^ 2 - χ)) + 32 * √2 * √(c * G) * Y / (c ^ 2 - χ)
        + 2 * Cvs.Prolate.Mellin.ModeMellinDyadicRange.P c χ 1 G Y V 2 := by
  set σ := √(c ^ 2 - χ) with hσ
  have hd : 0 < c ^ 2 - χ := by linarith
  have hσ0 : 0 < σ := sqrt_pos.mpr hd
  have hσ2 : σ ^ 2 = c ^ 2 - χ := sq_sqrt hd.le
  have hσc : σ ≤ c := by
    rw [hσ, sqrt_le_left hc.le]; linarith
  set θ := √(1 + σ / c) with hθ
  have hθ2 : θ ^ 2 = 1 + σ / c := sq_sqrt (by positivity)
  have hσc1 : σ / c ≤ 1 := by rw [div_le_one hc]; exact hσc
  have hσc0 : 0 < σ / c := by positivity
  have hθ1 : 1 < θ := by
    rw [hθ]; exact Real.lt_sqrt_of_sq_lt (by linarith)
  have hθ2' : θ ≤ 2 := by nlinarith
  set S := (2 : ℝ) ^ J * 2 with hS
  have hS2 : 2 ≤ S := by
    have : (1 : ℝ) ≤ 2 ^ J := one_le_pow₀ (by norm_num)
    rw [hS]; linarith
  set s₁ := 1 + η with hs₁
  have hs₁1 : 1 < s₁ := by linarith
  have hs₁θ : s₁ ≤ θ := hηθ
  -- continuity and the four intervals
  have hycont : ContinuousOn y (Icc 1 S) := fun τ hτ => (hy τ hτ).continuousAt.continuousWithinAt
  have hint : ∀ a b, 1 ≤ a → a ≤ b → b ≤ S →
      IntervalIntegrable (fun τ => ψ τ * y τ) MeasureTheory.volume a b := fun a b ha hab hb =>
    ((hcont.mul hycont).mono (Icc_subset_Icc ha hb)).intervalIntegrable_of_Icc hab
  have e1 := intervalIntegral.integral_add_adjacent_intervals (hint 1 s₁ le_rfl hs₁1.le (by linarith))
    (hint s₁ θ hs₁1.le hs₁θ (by linarith))
  have e2 := intervalIntegral.integral_add_adjacent_intervals (hint 1 θ le_rfl hθ1.le (by linarith))
    (hint θ 2 hθ1.le hθ2' hS2)
  have e3 := intervalIntegral.integral_add_adjacent_intervals (hint 1 2 le_rfl (by norm_num) hS2)
    (hint 2 S (by norm_num) hS2 le_rfl)
  have inS : ∀ τ, 1 < τ → τ ≤ S → τ ∈ Ioc 1 S := fun τ h1 h2 => ⟨h1, h2⟩
  have inSc : ∀ τ, 1 ≤ τ → τ ≤ S → τ ∈ Icc 1 S := fun τ h1 h2 => ⟨h1, h2⟩
  -- piece 0: [1, 1 + η]
  have p0 : |∫ τ in (1 : ℝ)..s₁, ψ τ * y τ| ≤ η * |ψ 1| * Y := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 1) (b := s₁) (C := |ψ 1| * Y)
      (f := fun τ => ψ τ * y τ) (fun τ hτ => by
        rw [uIoc_of_le hs₁1.le] at hτ
        have h1 : 1 ≤ τ := hτ.1.le
        have hτS : τ ≤ S := by linarith [hτ.2]
        rw [Real.norm_eq_abs, abs_mul]
        have hy1 : |y τ| ≤ Y := by
          have := hyb τ (inSc τ h1 hτS)
          have hs : 1 ≤ √τ := Real.one_le_sqrt.mpr h1
          exact this.trans (div_le_self hY hs)
        exact mul_le_mul (hedge τ ⟨h1, by linarith [hτ.2]⟩) hy1 (abs_nonneg _) (abs_nonneg _))
    rw [Real.norm_eq_abs, abs_of_pos (by linarith : 0 < s₁ - 1)] at this
    rw [show s₁ - 1 = η by rw [hs₁]; ring] at this
    linarith
  -- the envelopes on [1, 2]
  have hZb : ∀ τ ∈ Icc s₁ 2, |ψ τ * v τ| ≤ |ψ 1| * (V * √2) := fun τ hτ => by
    have h1 : 1 ≤ τ := by linarith [hτ.1]
    rw [abs_mul]
    apply mul_le_mul (hedge τ ⟨h1, hτ.2⟩) _ (abs_nonneg _) (abs_nonneg _)
    exact (hvb τ (inSc τ h1 (by linarith [hτ.2]))).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hτ.2) hV)
  have hVb : ∀ τ ∈ Icc s₁ 2, |u τ * y τ| ≤ √(c * G) * √2 * Y := fun τ hτ => by
    have h1 : 1 < τ := by linarith [hτ.1]
    have hτ0 : 0 < τ := by linarith
    have hu' := Cvs.Prolate.Mellin.ModeMellinDyadicPiece.abs_u_le hc hχ0 hχ h1 (hG τ (inS τ h1 (by linarith [hτ.2])))
    have hy' := hyb τ (inSc τ h1.le (by linarith [hτ.2]))
    have hsq : 0 < √τ := sqrt_pos.mpr hτ0
    rw [abs_mul]
    calc |u τ| * |y τ| ≤ τ * √(c * G) * (Y / √τ) := mul_le_mul hu' hy' (abs_nonneg _) (by positivity)
      _ = √τ * √(c * G) * Y := by
          have hq := mul_self_sqrt hτ0.le
          field_simp
          linear_combination (-(√(c * G) * Y)) * hq
      _ ≤ √2 * √(c * G) * Y := by
          apply mul_le_mul_of_nonneg_right _ hY
          exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hτ.2) (sqrt_nonneg _)
      _ = √(c * G) * √2 * Y := by ring
  have hDpos : ∀ τ, 1 ≤ τ → 0 < DE c χ 1 w τ := fun τ h =>
    lt_of_lt_of_le (by positivity) (DE_one_ge hw hgap h)
  have hsysψ : ∀ τ, 1 < τ → τ ≤ S → HasDerivAt ψ (u τ / pm 1 τ) τ := fun τ h1 h2 => by
    rw [pm_one]; exact hψ τ (inS τ h1 h2)
  have hsysu : ∀ τ, 1 < τ → τ ≤ S → HasDerivAt u (-(qm c χ 1 τ * ψ τ)) τ := fun τ h1 h2 => by
    rw [qm_one]; exact hu τ (inS τ h1 h2)
  have hB' : ∀ τ, 1 ≤ τ → w ≤ c ^ 2 * 1 ^ 4 * τ ^ 4 := fun τ h => by
    have : 1 ≤ τ ^ 4 := one_le_pow₀ h
    nlinarith [sq_nonneg c]
  -- piece 1: [1 + η, θ]
  have p1 := Cvs.L2a.TelescopingIncreasingCoeff.euler_cross_le_inc (c := c) (χ := χ) (m := 1) (w := w) (f := ψ) (u := u)
    (y := y) (v := v) hs₁θ one_pos (by linarith) (fun τ hτ => hDpos τ (by linarith [hτ.1]))
    (fun τ hτ => by
      have h1 : 1 ≤ τ := by linarith [hτ.1]
      have a0 : 0 ≤ 1 ^ 2 * τ ^ 2 - 1 := by nlinarith
      have a1 : 1 ^ 2 * τ ^ 2 - 1 ≤ σ / c := by nlinarith [hτ.2]
      have a2 : (1 ^ 2 * τ ^ 2 - 1) ^ 2 ≤ (σ / c) ^ 2 := pow_le_pow_left₀ a0 a1 2
      calc c ^ 2 * (1 ^ 2 * τ ^ 2 - 1) ^ 2 ≤ c ^ 2 * (σ / c) ^ 2 := mul_le_mul_of_nonneg_left a2 (sq_nonneg c)
        _ = c ^ 2 - χ := by rw [div_pow, ← hσ2]; field_simp)
    (fun τ hτ => hB' τ (by linarith [hτ.1]))
    (fun τ hτ => hsysψ τ (by linarith [hτ.1]) (by linarith [hτ.2]))
    (fun τ hτ => hsysu τ (by linarith [hτ.1]) (by linarith [hτ.2]))
    (fun τ hτ => hy τ (inSc τ (by linarith [hτ.1]) (by linarith [hτ.2])))
    (fun τ hτ => hv τ (inSc τ (by linarith [hτ.1]) (by linarith [hτ.2])))
    (fun τ hτ => hZb τ ⟨hτ.1, by linarith [hτ.2]⟩) (fun τ hτ => hVb τ ⟨hτ.1, by linarith [hτ.2]⟩)
  -- piece 2: [θ, 2]
  have p2 := Cvs.Prolate.Mellin.ModeMellinBelowGap.euler_cross_le (c := c) (χ := χ) (m := 1) (w := w) (f := ψ) (u := u)
    (y := y) (v := v) hθ2' one_pos (by linarith) (fun τ hτ => hDpos τ (by linarith [hτ.1]))
    (fun τ hτ => by
      have a0 : σ / c ≤ 1 ^ 2 * τ ^ 2 - 1 := by nlinarith [hτ.1]
      have a2 : (σ / c) ^ 2 ≤ (1 ^ 2 * τ ^ 2 - 1) ^ 2 := pow_le_pow_left₀ (by positivity) a0 2
      calc c ^ 2 - χ = c ^ 2 * (σ / c) ^ 2 := by rw [div_pow, ← hσ2]; field_simp
        _ ≤ c ^ 2 * (1 ^ 2 * τ ^ 2 - 1) ^ 2 := mul_le_mul_of_nonneg_left a2 (sq_nonneg c))
    (fun τ hτ => hB' τ (by linarith [hτ.1]))
    (fun τ hτ => hsysψ τ (by linarith [hτ.1]) (by linarith [hτ.2]))
    (fun τ hτ => hsysu τ (by linarith [hτ.1]) (by linarith [hτ.2]))
    (fun τ hτ => hy τ (inSc τ (by linarith [hτ.1]) (by linarith [hτ.2])))
    (fun τ hτ => hv τ (inSc τ (by linarith [hτ.1]) (by linarith [hτ.2])))
    (fun τ hτ => hZb τ ⟨by linarith [hτ.1], hτ.2⟩) (fun τ hτ => hVb τ ⟨by linarith [hτ.1], hτ.2⟩)
  -- piece 3: [2, S]
  have p3 := Cvs.Prolate.Mellin.ModeMellinDyadicRange.mode_le (c := c) (χ := χ) (m := 1) (w := w) (s₀ := 2) (G := G) (Y := Y)
    (V := V) (ψ := ψ) (u := u) (y := y) (v := v) J hc hχ0 hχ one_pos (by norm_num) hw (by linarith) hG0 hY hV
    (fun ξ hξ => hψ ξ (inS ξ (by linarith [hξ.1]) (by rw [hS]; linarith [hξ.2])))
    (fun ξ hξ => hu ξ (inS ξ (by linarith [hξ.1]) (by rw [hS]; linarith [hξ.2])))
    (fun ξ hξ => hG ξ (inS ξ (by linarith [hξ.1]) (by rw [hS]; linarith [hξ.2])))
    (fun τ hτ => hy τ (inSc τ (by linarith [hτ.1]) (by rw [hS]; linarith [hτ.2])))
    (fun τ hτ => hv τ (inSc τ (by linarith [hτ.1]) (by rw [hS]; linarith [hτ.2])))
    (fun τ hτ => hyb τ (inSc τ (by linarith [hτ.1]) (by rw [hS]; linarith [hτ.2])))
    (fun τ hτ => hvb τ (inSc τ (by linarith [hτ.1]) (by rw [hS]; linarith [hτ.2])))
  simp only [one_mul] at p3
  -- the coefficients
  have hpmθ : pm 1 θ = σ / c := by rw [pm_one]; unfold pP; rw [hθ2]; ring
  have hDθ := DE_one_ge (c := c) (χ := χ) hw hgap hθ1.le
  have hDs := DE_one_ge (c := c) (χ := χ) hw hgap hs₁1.le
  have hMz : 0 ≤ |ψ 1| * (V * √2) := by positivity
  have hMv : 0 ≤ √(c * G) * √2 * Y := by positivity
  have hσh : 0 < (c ^ 2 - χ) / 2 := by positivity
  have cA : pm 1 θ / DE c χ 1 w θ ≤ 2 / (c * σ) := by
    rw [hpmθ]
    calc σ / c / DE c χ 1 w θ ≤ σ / c / (σ ^ 2 / 2) := by
          rw [hσ2]; exact div_le_div_of_nonneg_left (by positivity) hσh hDθ
      _ = 2 / (c * σ) := by field_simp
  have cB : ∀ r, 1 ≤ r → r ≤ 2 → r ^ 2 / DE c χ 1 w r ≤ 8 / (c ^ 2 - χ) := fun r h1 h2 => by
    have := DE_one_ge (c := c) (χ := χ) hw hgap h1
    calc r ^ 2 / DE c χ 1 w r ≤ 4 / ((c ^ 2 - χ) / 2) := by
          apply div_le_div₀ (by norm_num) (by nlinarith) hσh this
      _ = 8 / (c ^ 2 - χ) := by field_simp; ring
  have q1 : |∫ τ in s₁..θ, ψ τ * y τ| ≤ 2 * (2 / (c * σ) * (|ψ 1| * (V * √2))
      + 8 / (c ^ 2 - χ) * (√(c * G) * √2 * Y)) := by
    refine p1.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact add_le_add (mul_le_mul_of_nonneg_right cA hMz)
      (mul_le_mul_of_nonneg_right (cB s₁ hs₁1.le (by linarith)) hMv)
  have q2 : |∫ τ in θ..2, ψ τ * y τ| ≤ 2 * (2 / (c * σ) * (|ψ 1| * (V * √2))
      + 8 / (c ^ 2 - χ) * (√(c * G) * √2 * Y)) := by
    refine p2.trans ?_
    have hθD : 0 < DE c χ 1 w θ := hDpos θ hθ1.le
    have e : 2 * (pm 1 θ * (|ψ 1| * (V * √2)) + θ ^ 2 * (√(c * G) * √2 * Y)) / DE c χ 1 w θ
        = 2 * (pm 1 θ / DE c χ 1 w θ * (|ψ 1| * (V * √2)) + θ ^ 2 / DE c χ 1 w θ * (√(c * G) * √2 * Y)) := by
      field_simp
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact add_le_add (mul_le_mul_of_nonneg_right cA hMz)
      (mul_le_mul_of_nonneg_right (cB θ hθ1.le hθ2') hMv)
  have fin : 2 * (2 * (2 / (c * σ) * (|ψ 1| * (V * √2)) + 8 / (c ^ 2 - χ) * (√(c * G) * √2 * Y)))
      = 8 * √2 * |ψ 1| * V / (c * σ) + 32 * √2 * √(c * G) * Y / (c ^ 2 - χ) := by
    field_simp; ring
  rw [← e3, ← e2, ← e1]
  have t1 := abs_add_le (∫ τ in (1 : ℝ)..s₁, ψ τ * y τ) (∫ τ in s₁..θ, ψ τ * y τ)
  have t2 := abs_add_le ((∫ τ in (1 : ℝ)..s₁, ψ τ * y τ) + ∫ τ in s₁..θ, ψ τ * y τ) (∫ τ in θ..2, ψ τ * y τ)
  have t3 := abs_add_le ((∫ τ in (1 : ℝ)..s₁, ψ τ * y τ) + (∫ τ in s₁..θ, ψ τ * y τ) + ∫ τ in θ..2, ψ τ * y τ)
    (∫ τ in (2 : ℝ)..S, ψ τ * y τ)
  linarith

end Cvs.Prolate.Mellin.FirstModeMellinEdge
