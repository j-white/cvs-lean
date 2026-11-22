import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.CornerSuprema
import Cvs.L2a.CutKernelSimplified
import Cvs.L2a.CutKernels
import Cvs.L2a.FarFarBound
import Cvs.L2a.FarIntegrationByParts
import Cvs.L2a.LocalisedBottomCorners
import Cvs.L2a.LocalisedConstants
import Cvs.L2a.OrbitGapIntegerM
import Cvs.L2a.TopCornerSum
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The `m = 2` shells

On `(1, 2 − s]` the shell `(2 − e_{k+1}, 2 − e_k]` carries the collar `δ_k = min(δ, e_k/4)`, so `LocalisedBottomCorners`'s simplified
kernel is bounded by `π⁻²(f₂ − cos(2ct)g₂)W + 4/(2 − t)²(A_kW + B_kP)` and the correction by Lemma K at `y₀ = t/2`;
one weighted Cauchy–Schwarz against the shell majorant gives `ShellM2 c d δ s`, in particular at `S*`.
-/

noncomputable section

namespace Cvs.L2a.SecondModeShells

open Real Set MeasureTheory
open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.AngularProlateTailPositive Cvs.L2a.FarIntegrationByParts Cvs.L2a.OrbitGapIntegerM Cvs.Prolate.RungCauchySplit Cvs.L2a.BandTransferBandForm Cvs.L2a.LocalisedBottomCorners
open Cvs.L2a.CornerSuprema (fm Lnear)
open Cvs.L2a.CutKernelSimplified (kNear kCmp_le_near)

/-! ### The shells -/

/-- `e₀ = s`, `e_N = 1` with `N = ⌈log₂(1/s)⌉`, `e` monotone and `0 < e_k ≤ 1`, for `0 < s ≤ 1`. -/
theorem eSh_facts {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    eSh s 0 = s ∧ eSh s (nSh s) = 1 ∧ Monotone (eSh s) ∧ ∀ k, 0 < eSh s k ∧ eSh s k ≤ 1 := by
  refine ⟨?_, ?_, fun k l hkl => ?_, fun k => ⟨lt_min one_pos (by positivity), min_le_left _ _⟩⟩
  · unfold eSh; rw [pow_zero, mul_one]; exact min_eq_right hs1
  · unfold eSh
    refine min_eq_left ?_
    have hK : Real.logb 2 (1 / s) ≤ (nSh s : ℝ) := Nat.le_ceil _
    have h2 : 1 / s ≤ (2 : ℝ) ^ (nSh s) := by
      rw [← Real.rpow_natCast]
      calc 1 / s = (2 : ℝ) ^ Real.logb 2 (1 / s) :=
            (Real.rpow_logb (by norm_num) (by norm_num) (by positivity)).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hK
    rw [div_le_iff₀ hs] at h2
    linarith
  · exact min_le_min le_rfl (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hkl) hs.le)

/-- Every `t ∈ (1, 2 − s]` lies in a shell `(2 − e_{k+1}, 2 − e_k]` with `k < N`. -/
theorem exists_shell_mem {s t : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (ht : t ∈ Ioc 1 (2 - s)) :
    ∃ k < nSh s, t ∈ Ioc (2 - eSh s (k + 1)) (2 - eSh s k) := by
  obtain ⟨he0, heN, -, -⟩ := eSh_facts hs hs1
  obtain ⟨k, hk, h1, h2⟩ := Cvs.L2a.TopCornerSum.exists_shell (u := eSh s) heN (v := 2 - t)
    (by rw [he0]; linarith [ht.2]) (by linarith [ht.1])
  exact ⟨k, hk, by linarith, by linarith⟩

theorem shell_sub {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (k : ℕ) :
    Ioc (2 - eSh s (k + 1)) (2 - eSh s k) ⊆ Ioc 1 (2 - s) := fun t ht => by
  obtain ⟨he0, -, hmono, hb⟩ := eSh_facts hs hs1
  have h1 := (hb (k + 1)).2
  have h2 := hmono (Nat.zero_le k)
  rw [he0] at h2
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- With `a = 2(1 − δ)`, `δ ≤ e/4` and `e ≤ 2 − t`: `a²/(a² − t²)² ≤ 4/(2 − t)²` and `1/(a − t)² ≤ 4/(2 − t)²`. -/
theorem shell_kernel_le {δ e t : ℝ} (hδ : 0 < δ) (hδe : δ ≤ e / 4) (ht : 0 < t)
    (hte : e ≤ 2 - t) :
    (2 * (1 - δ)) ^ 2 / ((2 * (1 - δ)) ^ 2 - t ^ 2) ^ 2 ≤ 4 / (2 - t) ^ 2
      ∧ 1 / (2 * (1 - δ) - t) ^ 2 ≤ 4 / (2 - t) ^ 2 := by
  have hu : 0 < (2 - t) / 2 := by linarith
  have hat : (2 - t) / 2 ≤ 2 * (1 - δ) - t := by linarith
  have hat0 : 0 < 2 * (1 - δ) - t := by linarith
  have hinv : 1 / (2 * (1 - δ) - t) ^ 2 ≤ 4 / (2 - t) ^ 2 := by
    rw [div_le_div_iff₀ (pow_pos hat0 2) (pow_pos (by linarith : (0 : ℝ) < 2 - t) 2)]
    nlinarith [pow_le_pow_left₀ hu.le hat 2]
  refine ⟨le_trans ?_ hinv, hinv⟩
  have hq : 0 < (2 * (1 - δ)) ^ 2 - t ^ 2 := by
    have : (2 * (1 - δ)) ^ 2 - t ^ 2 = (2 * (1 - δ) - t) * (2 * (1 - δ) + t) := by ring
    rw [this]; exact mul_pos hat0 (by linarith)
  rw [div_le_div_iff₀ (pow_pos hq 2) (pow_pos hat0 2), one_mul,
    show ((2 * (1 - δ)) ^ 2 - t ^ 2) ^ 2 = (2 * (1 - δ) + t) ^ 2 * (2 * (1 - δ) - t) ^ 2 by ring]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) (by linarith) 2) (sq_nonneg _)

variable {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ}

/-! ### The two kernels on a shell -/

/-- **The simplified kernel on the shell `k`**: `𝔅₂^si(t)² ≤ π⁻²(f₂ − cos(2ct)g₂)W + 4/(2 − t)²(A_kW + B_kP)`,
`A_k = (4κ_S/π²)δ_k`, `B_k = (2/π)T(c, 2, d, δ_k, e_k/4)`. -/
theorem bSi_sq_le_shell (a : ι → ℝ) {M : ℕ} {d δ s t : ℝ} {k : ℕ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχi : Function.Injective χ)
    (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..M, psi c (g i) t ^ 2) (hM2 : 2 ≤ M)
    (hd : 0 < d) (hd1 : d < 1) (hδ : 0 < δ) (hs : 0 < s) (hs1 : s ≤ 1)
    (ht : t ∈ Ioc (2 - eSh s (k + 1)) (2 - eSh s k)) :
    bSi c χ g a 2 t ^ 2
      ≤ (π ^ 2)⁻¹ * (fm 2 t - Real.cos (2 * c * t) * gT 2 t)
          * (∫ x in (2 - d)..(2 + d), (∑ i, a i * psi c (g i) x) ^ 2)
        + 4 / (2 - t) ^ 2 * (4 * (181 / 462) / π ^ 2 * dSh δ s k
            * (∫ x in (2 - d)..(2 + d), (∑ i, a i * psi c (g i) x) ^ 2)
          + 2 / π * tT c 2 d (dSh δ s k) (eSh s k / 4) (Fintype.card ι)
            * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨-, -, -, hb⟩ := eSh_facts hs hs1
  have he := (hb k).1
  have he1 := (hb k).2
  have he2 := (hb (k + 1)).2
  have hδk : 0 < dSh δ s k := lt_min hδ (by linarith)
  have hδe : dSh δ s k ≤ eSh s k / 4 := min_le_right _ _
  have ht0 : 0 < t := by linarith [ht.1]
  have hte : eSh s k ≤ 2 - t := by linarith [ht.2]
  have h2r : ((2 : ℕ) : ℝ) = 2 := by norm_num
  have h := bSi_sq_le_near a (M := M) (m := 2) (d := d) (δ := dSh δ s k) (t := t) (r₀ := eSh s k / 4)
    hg hg₁ hg₂c hang hc hχ0 hχc hχi hM le_rfl hM2 hd (by rw [h2r]; linarith) hδk (by linarith) ht0
    (by rw [h2r]; linarith) (by linarith) (by rw [h2r]; linarith)
  rw [h2r] at h
  obtain ⟨k1, k2⟩ := shell_kernel_le hδk hδe ht0 hte
  have hW0 : 0 ≤ ∫ x in (2 - d)..(2 + d), (∑ i, a i * psi c (g i) x) ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) fun x _ => sq_nonneg _
  have hP0 : 0 ≤ ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi fun x _ => sq_nonneg _
  have hA : 0 ≤ 4 * (181 / 462) / π ^ 2 * dSh δ s k := mul_nonneg (by positivity) hδk.le
  have hB : 0 ≤ 2 / π * tT c 2 d (dSh δ s k) (eSh s k / 4) (Fintype.card ι) :=
    mul_nonneg (by positivity) (tT_nonneg hc0 hd.le (by linarith) hδk.le (Nat.cast_nonneg _) (by positivity))
  have hcoll : 4 * (181 / 462) / π ^ 2 * dSh δ s k * (2 * (1 - dSh δ s k)) ^ 2
        / ((2 * (1 - dSh δ s k)) ^ 2 - t ^ 2) ^ 2
      ≤ 4 * (181 / 462) / π ^ 2 * dSh δ s k * (4 / (2 - t) ^ 2) :=
    Eq.trans_le (by ring) (mul_le_mul_of_nonneg_left k1 hA)
  have hch : 2 / π * tT c 2 d (dSh δ s k) (eSh s k / 4) (Fintype.card ι) / (2 * (1 - dSh δ s k) - t) ^ 2
      ≤ 2 / π * tT c 2 d (dSh δ s k) (eSh s k / 4) (Fintype.card ι) * (4 / (2 - t) ^ 2) :=
    Eq.trans_le (by ring) (mul_le_mul_of_nonneg_left k2 hB)
  refine h.trans (le_of_le_of_eq (add_le_add (mul_le_mul_of_nonneg_right (add_le_add le_rfl hcoll) hW0)
    (mul_le_mul_of_nonneg_right hch hP0)) (by ring))

/-- **The correction on `[1, 2)`**: Lemma K at `y₀ = t/2` gives
`𝔅₂^co(t)² ≤ (κ_ι/c²)K_near(c, 2, t/2, Y₂)²·env_n(t)·P`. -/
theorem bCo_sq_le_shell (a : ι → ℝ) {M : ℕ} {t : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχi : Function.Injective χ)
    (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..M, psi c (g i) t ^ 2) (hM2 : 2 ≤ M) (ht1 : 1 ≤ t) (ht2 : t < 2) :
    bCo c χ g a 2 t ^ 2
      ≤ kapI c (Fintype.card ι) / c ^ 2 * kNear c 2 (t / 2) (Ymax 2) ^ 2 * envN 2 t
        * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := by
  have hc0 : 0 < c := by linarith
  have h2r : ((2 : ℕ) : ℝ) = 2 := by norm_num
  have ht0 : 0 < t := by linarith
  have h := (t0_frakB a (M := M) (m := 2) (t := t)
    (K := kNear c ((2 : ℕ) : ℝ) (t / ((2 : ℕ) : ℝ)) (Ymax ((2 : ℕ) : ℝ)))
    (S := √((t / 2) ^ 2 + 1) / (1 - (t / 2) ^ 2)) hg hg₁ hg₂c hang hc hχ0 hχc hχi hM le_rfl hM2 ht0
    (off_near (by norm_num) (by rw [h2r]; exact ht2))
    (fun η h1 h2 => kCmp_le_near hc0 (by norm_num) (by positivity) le_rfl (by rw [h2r]; linarith) h1 h2)
    (fun v hv => by rw [h2r]; exact env_near (by positivity) (by linarith) hv.1)).2
  rw [h2r] at h
  rw [envN, ← env_sq_div (by norm_num : (0 : ℝ) < 2) ht2 ht0.le]
  calc _ ≤ _ := h
    _ = _ := by ring

/-! ### The shells by one weighted Cauchy–Schwarz -/

/-- **The `m = 2` shells**: for `0 < d < 1`, `δ > 0` and `0 < s ≤ 1`, `ShellM2 c d δ s χ g a` holds. -/
theorem shellM2 (a : ι → ℝ) {M : ℕ} {d δ s : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχi : Function.Injective χ)
    (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..M, psi c (g i) t ^ 2) (hM2 : 2 ≤ M)
    (hd : 0 < d) (hd1 : d < 1) (hδ : 0 < δ) (hs : 0 < s) (hs1 : s ≤ 1) :
    ShellM2 c d δ s χ g a := by
  have hc0 : 0 < c := by linarith
  obtain ⟨-, -, hmono, hb⟩ := eSh_facts hs hs1
  unfold ShellM2
  set W := ∫ x in (2 - d)..(2 + d), (∑ i, a i * psi c (g i) x) ^ 2 with hW
  set P := ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 with hP
  have hW0 : 0 ≤ W := intervalIntegral.integral_nonneg (by linarith) fun x _ => sq_nonneg _
  have hP0 : 0 ≤ P := setIntegral_nonneg measurableSet_Ioi fun x _ => sq_nonneg _
  have hw0 : ∀ t, 0 ≤ 1 - wF t := fun t => by linarith [(Cvs.L2a.FarFarBound.wF_bounds t).2.1]
  have hcw := Cvs.L2a.CornerSuprema.continuous_one_sub_wF
  have hΦc := continuous_Phi a hg hg₁ hg₂c hang
  have h1s : (1 : ℝ) ≤ 2 - s := by linarith
  have hs2 : 2 - s < 2 := by linarith
  have hdk : ∀ k, 0 ≤ dSh δ s k := fun k => le_min hδ.le (by linarith [(hb k).1])
  have hA : ∀ k, 0 ≤ 4 * (181 / 462) / π ^ 2 * dSh δ s k := fun k => mul_nonneg (by positivity) (hdk k)
  have hB : ∀ k, 0 ≤ 2 / π * tT c 2 d (dSh δ s k) (eSh s k / 4) (Fintype.card ι) := fun k =>
    mul_nonneg (by positivity)
      (tT_nonneg hc0 hd.le (by linarith) (hdk k) (Nat.cast_nonneg _) (by linarith [(hb k).1]))
  -- the majorants
  set fsh : ℕ → ℝ → ℝ := fun k t => 4 * (1 - wF t) / (2 - t) ^ 2
      * (4 * (181 / 462) / π ^ 2 * dSh δ s k * W
        + 2 / π * tT c 2 d (dSh δ s k) (eSh s k / 4) (Fintype.card ι) * P) with hfsh
  set fmain : ℝ → ℝ := fun t => W * (π ^ 2)⁻¹
      * ((1 - wF t) * fm 2 t - (1 - wF t) * gT 2 t * Real.cos (2 * c * t)) with hfmain
  set q₁ : ℝ → ℝ := fun t => fmain t
      + ∑ k ∈ Finset.range (nSh s), (Ioc (2 - eSh s (k + 1)) (2 - eSh s k)).indicator (fsh k) t with hq₁
  set q₂ : ℝ → ℝ := fun t => kapI c (Fintype.card ι) / c ^ 2 * P
      * ((1 - wF t) * kNear c 2 (t / 2) (Ymax 2) ^ 2 * envN 2 t) with hq₂
  have hfsh0 : ∀ k t, 0 ≤ fsh k t := fun k t => by
    simp only [hfsh]
    exact mul_nonneg (div_nonneg (mul_nonneg (by norm_num) (hw0 t)) (sq_nonneg _))
      (add_nonneg (mul_nonneg (hA k) hW0) (mul_nonneg (hB k) hP0))
  -- pointwise
  have hS1 : ∀ t ∈ Ioc 1 (2 - s), (1 - wF t) * bSi c χ g a 2 t ^ 2 ≤ q₁ t := fun t ht => by
    obtain ⟨k, hk, htk⟩ := exists_shell_mem hs hs1 ht
    have h := bSi_sq_le_shell a hg hg₁ hg₂c hang hc hχ0 hχc hχi hM hM2 hd hd1 hδ hs hs1 htk
    rw [← hW, ← hP] at h
    have hle : (Ioc (2 - eSh s (k + 1)) (2 - eSh s k)).indicator (fsh k) t
        ≤ ∑ j ∈ Finset.range (nSh s), (Ioc (2 - eSh s (j + 1)) (2 - eSh s j)).indicator (fsh j) t :=
      Finset.single_le_sum (f := fun j => (Ioc (2 - eSh s (j + 1)) (2 - eSh s j)).indicator (fsh j) t)
        (fun j _ => indicator_nonneg (fun x _ => hfsh0 j x) t) (Finset.mem_range.2 hk)
    have hin : (Ioc (2 - eSh s (k + 1)) (2 - eSh s k)).indicator (fsh k) t = fsh k t := indicator_of_mem htk _
    calc (1 - wF t) * bSi c χ g a 2 t ^ 2
        ≤ (1 - wF t) * ((π ^ 2)⁻¹ * (fm 2 t - Real.cos (2 * c * t) * gT 2 t) * W
          + 4 / (2 - t) ^ 2 * (4 * (181 / 462) / π ^ 2 * dSh δ s k * W
            + 2 / π * tT c 2 d (dSh δ s k) (eSh s k / 4) (Fintype.card ι) * P)) :=
          mul_le_mul_of_nonneg_left h (hw0 t)
      _ = fmain t + fsh k t := by simp only [hfmain, hfsh]; ring
      _ ≤ q₁ t := by simp only [hq₁]; linarith [hle, hin]
  have hS2 : ∀ t ∈ Ioc 1 (2 - s), (1 - wF t) * bCo c χ g a 2 t ^ 2 ≤ q₂ t := fun t ht => by
    have h := bCo_sq_le_shell a hg hg₁ hg₂c hang hc hχ0 hχc hχi hM hM2 ht.1.le (by linarith [ht.2])
    rw [← hP] at h
    calc _ ≤ (1 - wF t) * _ := mul_le_mul_of_nonneg_left h (hw0 t)
      _ = q₂ t := by simp only [hq₂]; ring
  -- integrability
  have hfm := (continuousOn_fm_near (m := 2) (by norm_num) hs2).mono
    (Icc_subset_Icc (by norm_num : (0 : ℝ) ≤ 1) le_rfl)
  have hgT := continuousOn_gT_near (m := 2) (by norm_num) hs2
  have hcos : Continuous fun t => Real.cos (2 * c * t) := by fun_prop
  have i1 : IntervalIntegrable (fun t => (1 - wF t) * fm 2 t) volume 1 (2 - s) :=
    Cvs.L2a.LocalisedConstants.intervalIntegrable_nearInt le_rfl h1s hs2.le
  have i2 : IntervalIntegrable (fun t => (1 - wF t) * gT 2 t * Real.cos (2 * c * t)) volume 1 (2 - s) :=
    ((hcw.continuousOn.mul hgT).mul hcos.continuousOn).intervalIntegrable_of_Icc h1s
  have imain : IntegrableOn fmain (Ioc 1 (2 - s)) := by
    rw [hfmain]
    exact (continuousOn_const.mul ((hcw.continuousOn.mul hfm).sub
      ((hcw.continuousOn.mul hgT).mul hcos.continuousOn))).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have ishk : ∀ k, IntegrableOn (fsh k) (Ioc (2 - eSh s (k + 1)) (2 - eSh s k)) := fun k => by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
    have hden : ContinuousOn (fun t : ℝ => (2 - t) ^ 2) (Icc (2 - eSh s (k + 1)) (2 - eSh s k)) := by
      fun_prop
    have hnum : ContinuousOn (fun t => 4 * (1 - wF t)) (Icc (2 - eSh s (k + 1)) (2 - eSh s k)) :=
      (continuous_const.mul hcw).continuousOn
    have hne : ∀ t ∈ Icc (2 - eSh s (k + 1)) (2 - eSh s k), (2 - t) ^ 2 ≠ 0 := fun t ht => by
      have : 0 < 2 - t := by linarith [ht.2, (hb k).1]
      exact (pow_pos this 2).ne'
    have hq := (hnum.div₀ hden hne).mul (continuousOn_const (c := 4 * (181 / 462) / π ^ 2 * dSh δ s k * W
        + 2 / π * tT c 2 d (dSh δ s k) (eSh s k / 4) (Fintype.card ι) * P))
    exact hq
  have ishI : ∀ k, IntegrableOn ((Ioc (2 - eSh s (k + 1)) (2 - eSh s k)).indicator (fsh k)) (Ioc 1 (2 - s)) :=
    fun k => ((ishk k).integrable_indicator measurableSet_Ioc).integrableOn
  have isum : IntegrableOn (fun t => ∑ k ∈ Finset.range (nSh s),
      (Ioc (2 - eSh s (k + 1)) (2 - eSh s k)).indicator (fsh k) t) (Ioc 1 (2 - s)) :=
    integrable_finsetSum _ fun k _ => ishI k
  have hq1i : IntegrableOn q₁ (Ioc 1 (2 - s)) := by rw [hq₁]; exact imain.add isum
  have hkN : ContinuousOn (fun t => kNear c 2 (t / 2) (Ymax 2)) (Icc 1 (2 - s)) := by
    unfold kNear
    have hq : ∀ t ∈ Icc (1 : ℝ) (2 - s), 0 < 1 - (t / 2) ^ 2 := fun t ht => by nlinarith [ht.1, ht.2]
    have hp := pP_pos (ξ := (2 : ℝ)) (by norm_num)
    have h1 : ContinuousOn (fun t : ℝ => 2 * 2 * (t / 2)) (Icc 1 (2 - s)) := by fun_prop
    have hu : Continuous fun t : ℝ => 1 - (t / 2) ^ 2 := by fun_prop
    have h2 : ContinuousOn (fun t : ℝ => pP (2 : ℝ) * (1 - (t / 2) ^ 2)) (Icc 1 (2 - s)) :=
      (continuous_const.mul hu).continuousOn
    have h3 : ContinuousOn (fun t : ℝ => 2 * (2 + t / 2 / c) * (t / 2 + Ymax 2)) (Icc 1 (2 - s)) := by
      fun_prop
    have h4 : ContinuousOn (fun t : ℝ => pP (2 : ℝ) * (1 - (t / 2) ^ 2) ^ 2) (Icc 1 (2 - s)) :=
      (continuous_const.mul (hu.pow 2)).continuousOn
    exact (h1.div₀ h2 fun t ht => (mul_pos hp (hq t ht)).ne').add
      (h3.div₀ h4 fun t ht => (mul_pos hp (pow_pos (hq t ht) 2)).ne')
  have hen : ContinuousOn (fun t => envN 2 t) (Icc 1 (2 - s)) := by
    unfold envN
    have h1' : Continuous fun t : ℝ => t ^ 2 + (2 : ℝ) ^ 2 := by fun_prop
    have h2' : Continuous fun t : ℝ => ((2 : ℝ) ^ 2 - t ^ 2) ^ 2 := by fun_prop
    have h1 : ContinuousOn (fun t : ℝ => t ^ 2 + (2 : ℝ) ^ 2) (Icc 1 (2 - s)) := h1'.continuousOn
    have h2 : ContinuousOn (fun t : ℝ => ((2 : ℝ) ^ 2 - t ^ 2) ^ 2) (Icc 1 (2 - s)) := h2'.continuousOn
    refine ContinuousOn.div_const (h1.div₀ h2 fun t ht => ?_) _
    have : 0 < (2 : ℝ) ^ 2 - t ^ 2 := by nlinarith [ht.1, ht.2]
    exact (pow_pos this 2).ne'
  have hq2c : ContinuousOn (fun t => (1 - wF t) * kNear c 2 (t / 2) (Ymax 2) ^ 2 * envN 2 t) (Icc 1 (2 - s)) :=
    (hcw.continuousOn.mul (hkN.pow 2)).mul hen
  have hq2i : IntegrableOn q₂ (Ioc 1 (2 - s)) := by
    rw [hq₂]
    exact (continuousOn_const.mul hq2c).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hpi : IntegrableOn (fun t => (1 - wF t) * (∑ i, a i * psi c (g i) t) ^ 2) (Ioc 1 (2 - s)) :=
    ((hcw.mul (hΦc.pow 2)).continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  -- Cauchy–Schwarz
  have key := abs_integral_le_sqrt (S := Ioc 1 (2 - s))
    (h := fun t => (1 - wF t) * (∑ i, a i * psi c (g i) t) * Cvs.L2a.CutKernels.frakB c χ g a 2 t)
    (p := fun t => (1 - wF t) * (∑ i, a i * psi c (g i) t) ^ 2) (q₁ := q₁) (q₂ := q₂)
    measurableSet_Ioc hpi hq1i hq2i (fun t _ => mul_nonneg (hw0 t) (sq_nonneg _))
    (fun t ht => (mul_nonneg (hw0 t) (sq_nonneg _)).trans (hS1 t ht))
    (fun t ht => (mul_nonneg (hw0 t) (sq_nonneg _)).trans (hS2 t ht))
    (fun t ht => abs_wPhi_frakB_le (hw0 t) (by unfold bCo; ring) (hS1 t ht) (hS2 t ht))
  refine key.trans (mul_le_mul_of_nonneg_left (add_le_add (Real.sqrt_le_sqrt ?_) (Real.sqrt_le_sqrt ?_))
    (Real.sqrt_nonneg _))
  · -- the integral of `q₁`
    have hmainI : ∫ t in Ioc 1 (2 - s), fmain t = W * (π ^ 2)⁻¹ * ((∫ t in (1 : ℝ)..(2 - s), (1 - wF t) * fm 2 t)
        - ∫ t in (1 : ℝ)..(2 - s), (1 - wF t) * gT 2 t * Real.cos (2 * c * t)) := by
      rw [← intervalIntegral.integral_of_le h1s]
      simp only [hfmain]
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub i1 i2]
    have hshI : ∀ k ∈ Finset.range (nSh s),
        ∫ t in Ioc 1 (2 - s), (Ioc (2 - eSh s (k + 1)) (2 - eSh s k)).indicator (fsh k) t
          = W * (4 * (181 / 462) / π ^ 2 * dSh δ s k * iSh s k)
            + P * (2 / π * tT c 2 d (dSh δ s k) (eSh s k / 4) (Fintype.card ι) * iSh s k) := fun k _ => by
      rw [setIntegral_indicator measurableSet_Ioc, inter_eq_right.2 (shell_sub hs hs1 k)]
      simp only [hfsh]
      rw [integral_mul_const, iSh,
        intervalIntegral.integral_of_le (by linarith [hmono (Nat.le_succ k)])]
      ring
    simp only [hq₁]
    rw [integral_add imain isum, integral_finsetSum _ fun k _ => ishI k, hmainI, Finset.sum_congr rfl hshI,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have i1' : IntervalIntegrable (fun t => (1 - wF t) * fm 2 t) volume (2 - s) 2 :=
      Cvs.L2a.LocalisedConstants.intervalIntegrable_nearInt h1s hs2.le le_rfl
    have hadd := intervalIntegral.integral_add_adjacent_intervals i1 i1'
    have hnn : 0 ≤ ∫ t in (2 - s)..2, (1 - wF t) * fm 2 t :=
      intervalIntegral.integral_nonneg hs2.le fun t ht =>
        Cvs.L2a.LocalisedConstants.nearInt_nonneg (by linarith [ht.1]) ht.2
    have hosc := osc_gT_near (m := 2) (by norm_num) h1s hs2 hc0
    have hX : (π ^ 2)⁻¹ * ((∫ t in (1 : ℝ)..(2 - s), (1 - wF t) * fm 2 t)
          - ∫ t in (1 : ℝ)..(2 - s), (1 - wF t) * gT 2 t * Real.cos (2 * c * t))
        ≤ Lnear 2 + |gT 2 (2 - s)| / (π ^ 2 * c) := by
      have h3 : (∫ t in (1 : ℝ)..(2 - s), (1 - wF t) * fm 2 t)
            - ∫ t in (1 : ℝ)..(2 - s), (1 - wF t) * gT 2 t * Real.cos (2 * c * t)
          ≤ (∫ t in (1 : ℝ)..2, (1 - wF t) * fm 2 t) + |gT 2 (2 - s)| / c := by
        linarith [neg_le_abs (∫ t in (1 : ℝ)..(2 - s), (1 - wF t) * gT 2 t * Real.cos (2 * c * t))]
      calc _ ≤ (π ^ 2)⁻¹ * ((∫ t in (1 : ℝ)..2, (1 - wF t) * fm 2 t) + |gT 2 (2 - s)| / c) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = _ := by unfold Lnear; ring
    unfold lam2 e2
    nlinarith [mul_le_mul_of_nonneg_left hX hW0]
  · -- the integral of `q₂`
    simp only [hq₂]
    rw [integral_const_mul, ← intervalIntegral.integral_of_le h1s]
    unfold k2
    exact le_of_eq (by ring)

/-- **The shells at `S*`**: for `c ≥ 4096` and `∫₁³ ψᵢ² > 0`, `ShellM2 c δ* δ* s* χ g a`. -/
theorem shellM2_S (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 4096 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχi : Function.Injective χ)
    (hmass : ∀ i, 0 < ∫ t in (1 : ℝ)..3, psi c (g i) t ^ 2) :
    ShellM2 c (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.sS c)
      χ g a := by
  have hc0 : 0 < c := by linarith
  have hδ := Cvs.L2a.TopCornerSum.deltaS_pos hc0
  have hδ8 := Cvs.L2a.TopCornerSum.deltaS_le hc
  exact shellM2 a (M := 3) hg hg₁ hg₂c hang (by linarith) hχ0 hχc hχi (fun i => by exact_mod_cast hmass i)
    (by norm_num) hδ (by linarith) hδ (Cvs.L2a.TopCornerSum.sS_pos hc0) (Cvs.L2a.TopCornerSum.sS_le hc)

/-- **The shells on the deep span**: under `FullTailDeepSpan`'s hypotheses (`c ≥ 10¹⁶`, `σᵢ² ≥ 5c`, `∫₁³ ψᵢ² > 0`),
`ShellM2 c δ* δ* s* χ g a` holds. -/
theorem shellM2_star (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 10 ^ 16 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hσ : ∀ i, 5 * c ≤ c ^ 2 - χ i) (hχi : Function.Injective χ)
    (hmass : ∀ i, 0 < ∫ t in (1 : ℝ)..3, psi c (g i) t ^ 2) :
    ShellM2 c (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.sS c)
      χ g a := by
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le (by norm_num) hc
  exact shellM2_S a hg hg₁ hg₂c hang (le_trans (by norm_num) hc) hχ0
    (fun i => by have := hσ i; linarith) hχi hmass

end Cvs.L2a.SecondModeShells
