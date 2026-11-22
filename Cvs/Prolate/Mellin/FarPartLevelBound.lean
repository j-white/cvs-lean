import Mathlib
import Cvs.L2a.FarPartDirichletSplit
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.TailLogScaleTest
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.Mellin.GreenBoundaryBound
import Cvs.Prolate.Mellin.GreenBulkBound
import Cvs.Prolate.Mellin.OrbitGapGreenIdentity
import Cvs.WeilForm.SelfConvolutionTransform

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The level bound on the far-part transform

`FarPartDirichletSplit`'s Dirichlet split with Lemma G at each cut `s ∈ {k} ∪ (⌊k⌋, ⌊X⌋]`: for `|t| ≤ kT`, `T² + 1/16 ≤ r c²`,
`r < 1` and `E ≤ Ē` on `[k, X]`, `‖𝓕(posTail ψ X − posTail ψ k)(t)‖ ≤ C̄√(Ē/c³)/k`, `C̄ = (11/2)β + (7/3)ρ`.
-/

namespace Cvs.Prolate.Mellin.FarPartLevelBound

open Real Set intervalIntegral Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.Mellin.MellinKernelSturmLiouville Cvs.L2a.TailLogScaleTest Cvs.L2a.PositionTruncatedTail Cvs.L2a.FarPartDirichletSplit Cvs.Prolate.Mellin.OrbitGapGreenIdentity Cvs.Prolate.Mellin.GreenBoundaryBound Cvs.Prolate.Mellin.GreenBulkBound
open scoped FourierTransform

/-- The level constant `C̄ = (11/2)β + (7/3)ρ`. -/
noncomputable def Cbar (c r : ℝ) : ℝ := 11 / 2 * √(betaSq c r) + 7 / 3 * √(rhoSq c r)

/-- Lemma B as a norm bound: `‖B(ξ)‖ ≤ β√(Ē/c³)/(ξ√ξ)` when `E(ξ) ≤ Ē`. -/
theorem norm_bdryC_le {c χ r t ξ Ebar : ℝ} (ψ u : ℝ → ℝ) (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ ≤ c ^ 2)
    (hξ : 2 ≤ ξ) (hr : r < 1) (hw : t ^ 2 + 1 / 4 ≤ r * (c ^ 2 * ξ ^ 2))
    (hE : energy (aP c χ) ψ u ξ ≤ Ebar) :
    ‖bdryC c χ t ψ u ξ‖ ≤ √(betaSq c r) * √(Ebar / c ^ 3) / (ξ * √ξ) := by
  have hξ0 : 0 < ξ := by linarith
  have hr0 : 0 ≤ r := by
    by_contra h; push Not at h
    have : r * (c ^ 2 * ξ ^ 2) < 0 := mul_neg_of_neg_of_pos h (by positivity)
    nlinarith
  have hb0 : 0 ≤ betaSq c r := by unfold betaSq; positivity
  have hEξ : 0 ≤ energy (aP c χ) ψ u ξ := by unfold energy aP; positivity
  have hEb : 0 ≤ Ebar := le_trans hEξ hE
  have h := green_boundary_le ψ u hc hχ0 hχ hξ hr hw
  have h2 : betaSq c r * energy (aP c χ) ψ u ξ / (c ^ 3 * ξ ^ 3) ≤ betaSq c r * Ebar / (c ^ 3 * ξ ^ 3) := by
    gcongr
  have e : betaSq c r * Ebar / (c ^ 3 * ξ ^ 3) = (√(betaSq c r) * √(Ebar / c ^ 3) / (ξ * √ξ)) ^ 2 := by
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hb0, Real.sq_sqrt (by positivity), Real.sq_sqrt hξ0.le]
    field_simp
  have hsq : ‖bdryC c χ t ψ u ξ‖ ^ 2 ≤ (√(betaSq c r) * √(Ebar / c ^ 3) / (ξ * √ξ)) ^ 2 := by linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-- `Σ_{1≤m≤⌊k⌋} + Σ_{⌊k⌋<m≤⌊X⌋} = Σ_{1≤m≤⌊X⌋}` for `k ≤ X`. -/
theorem sum_Icc_add_sum_Ioc {k X : ℝ} (hkX : k ≤ X) (f : ℕ → ℂ) :
    ∑ m ∈ Finset.Icc 1 ⌊k⌋₊, f m + ∑ m ∈ Finset.Ioc ⌊k⌋₊ ⌊X⌋₊, f m = ∑ m ∈ Finset.Icc 1 ⌊X⌋₊, f m := by
  have e : ∀ n : ℕ, Finset.Icc 1 n = Finset.Ioc 0 n := fun n => by
    ext m; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [e, e, Finset.sum_Ioc_consecutive _ (Nat.zero_le _) (Nat.floor_le_floor hkX)]

/-- `‖Σ_{1≤m≤⌊k⌋} m^{−1/2+it}‖ ≤ 2√k`. -/
theorem norm_sum_dch_le {k : ℝ} (hk : 0 ≤ k) (t : ℝ) : ‖∑ m ∈ Finset.Icc 1 ⌊k⌋₊, dch m t‖ ≤ 2 * √k := by
  refine (norm_sum_le _ _).trans ?_
  simp_rw [norm_dch]
  exact sum_inv_sqrt_le hk

/-- **The level bound**: for a rung pair on `[k, X]`, `2 ≤ k`, with `E ≤ Ē` there, `T² + 1/16 ≤ r c²`, `r < 1` and
`|t| ≤ kT`, the far-part transform `‖𝓕(posTail ψ X − posTail ψ k)(t)‖ ≤ C̄·√(Ē/c³)/k`. -/
theorem mellin_level_le {c χ r T k X t Ebar : ℝ} {ψ u : ℝ → ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ ≤ c ^ 2)
    (hk : 2 ≤ k) (hkX : k ≤ X) (hTr : T ^ 2 + 1 / 16 ≤ r * c ^ 2) (hr : r < 1) (ht : |t| ≤ k * T)
    (hψc : ContinuousOn ψ (Icc 1 X))
    (hψ : ∀ ξ ∈ Icc k X, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Icc k X, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hE : ∀ ξ ∈ Icc k X, energy (aP c χ) ψ u ξ ≤ Ebar) :
    ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf (logScale (posTail ψ X - posTail ψ k))) (t / (2 * π))‖
      ≤ Cbar c r * √(Ebar / c ^ 3) / k := by
  have hk0 : 0 < k := by linarith
  have hT0 : 0 ≤ T := by
    by_contra h; push Not at h
    have : k * T < 0 := mul_neg_of_pos_of_neg hk0 h
    linarith [abs_nonneg t]
  have hwξ : ∀ ξ, k ≤ ξ → t ^ 2 + 1 / 4 ≤ r * (c ^ 2 * ξ ^ 2) := by
    intro ξ hξ
    have h1 : t ^ 2 ≤ (ξ * T) ^ 2 := by
      have : |t| ≤ ξ * T := le_trans ht (mul_le_mul_of_nonneg_right hξ hT0)
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
    have h2 : (1 : ℝ) / 4 ≤ ξ ^ 2 / 16 := by nlinarith
    have h3 : ξ ^ 2 * (T ^ 2 + 1 / 16) ≤ ξ ^ 2 * (r * c ^ 2) := mul_le_mul_of_nonneg_left hTr (sq_nonneg ξ)
    nlinarith
  have hDpos : ∀ s, k ≤ s → ∀ ξ ∈ Icc s X, 0 < DM c χ (t ^ 2 + 1 / 4) ξ := by
    intro s hs ξ hξ
    have hξk : k ≤ ξ := le_trans hs hξ.1
    have hξ0 : 0 < ξ := by linarith
    refine DM_pos hχ (by linarith) ?_
    have h1 := hwξ ξ hξk
    have h2 : 0 < c ^ 2 * ξ ^ 2 := by positivity
    nlinarith
  have hG : ∀ s, k ≤ s → s ≤ X → mellinI ψ s X t
      = bdryC c χ t ψ u X - bdryC c χ t ψ u s - ∫ ξ in s..X, remDens c χ t ψ u ξ := fun s hs hsX =>
    mellinI_eq_green (by linarith) hsX (hDpos s hs) (fun ξ hξ => hψ ξ ⟨le_trans hs hξ.1, hξ.2⟩)
      (fun ξ hξ => hu ξ ⟨le_trans hs hξ.1, hξ.2⟩)
  set S := √(Ebar / c ^ 3) with hS
  set bβ := √(betaSq c r) with hbβ
  set bρ := √(rhoSq c r) with hbρ
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hbβ0 : 0 ≤ bβ := Real.sqrt_nonneg _
  have hbρ0 : 0 ≤ bρ := Real.sqrt_nonneg _
  have hB : ∀ ξ, k ≤ ξ → ξ ≤ X → ‖bdryC c χ t ψ u ξ‖ ≤ bβ * S / (ξ * √ξ) := fun ξ hξ hξX =>
    norm_bdryC_le ψ u hc hχ0 hχ (le_trans hk hξ) hr (hwξ ξ hξ) (hE ξ ⟨hξ, hξX⟩)
  have hR : ∀ s, k ≤ s → s ≤ X → ‖∫ ξ in s..X, remDens c χ t ψ u ξ‖ ≤ 2 / 3 * (bρ * S) / (s * √s) := by
    intro s hs hsX
    have h := green_rem_le (ψ := ψ) (u := u) hc hχ0 hχ (le_trans hk hs) hsX hr (hwξ s hs)
      (fun ξ hξ => hE ξ ⟨le_trans hs hξ.1, hξ.2⟩)
    have hr0 : 0 ≤ r := by
      have h1 := hwξ s hs
      by_contra h'; push Not at h'
      have hs0 : 0 < s := by linarith
      have : r * (c ^ 2 * s ^ 2) < 0 := mul_neg_of_neg_of_pos h' (by positivity)
      nlinarith
    rwa [mul_div_assoc (rhoSq c r), Real.sqrt_mul (rhoSq_nonneg hc hr0)] at h
  rw [fourier_far_eq ψ (by linarith) hkX hψc t]
  set Z := ∑ m ∈ Finset.Icc 1 ⌊k⌋₊, dch m t with hZ
  set F := Finset.Ioc ⌊k⌋₊ ⌊X⌋₊ with hF
  have hmF : ∀ m ∈ F, k ≤ (m : ℝ) ∧ (m : ℝ) ≤ X := by
    intro m hm
    rw [hF, Finset.mem_Ioc] at hm
    refine ⟨?_, ?_⟩
    · have := (Nat.lt_floor_add_one k).le
      have h2 : ((⌊k⌋₊ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm.1
      push_cast at h2; linarith
    · exact (Nat.cast_le.mpr hm.2).trans (Nat.floor_le (by linarith))
  -- rewrite every mode through Green
  have hsplit : Z * mellinI ψ k X t + ∑ m ∈ F, dch m t * mellinI ψ m X t
      = (∑ m ∈ Finset.Icc 1 ⌊X⌋₊, dch m t) * bdryC c χ t ψ u X
        - Z * bdryC c χ t ψ u k - Z * (∫ ξ in k..X, remDens c χ t ψ u ξ)
        - ∑ m ∈ F, dch m t * bdryC c χ t ψ u m
        - ∑ m ∈ F, dch m t * (∫ ξ in (m : ℝ)..X, remDens c χ t ψ u ξ) := by
    rw [hG k le_rfl hkX, ← sum_Icc_add_sum_Ioc hkX]
    have : ∀ m ∈ F, dch m t * mellinI ψ m X t = dch m t * bdryC c χ t ψ u X - dch m t * bdryC c χ t ψ u m
        - dch m t * (∫ ξ in (m : ℝ)..X, remDens c χ t ψ u ξ) := fun m hm => by
      rw [hG m (hmF m hm).1 (hmF m hm).2]; ring
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul]
    ring
  rw [hsplit]
  -- the five norms
  have hZ0 : ‖Z‖ ≤ 2 * √k := norm_sum_dch_le hk0.le t
  have hX0 : 0 < X := by linarith
  have n1 : ‖(∑ m ∈ Finset.Icc 1 ⌊X⌋₊, dch m t) * bdryC c χ t ψ u X‖ ≤ 2 * bβ * S / k := by
    rw [norm_mul]
    have h1 := norm_sum_dch_le hX0.le t
    have h2 := hB X hkX le_rfl
    have hsX : 0 < √X := Real.sqrt_pos.mpr hX0
    calc _ ≤ 2 * √X * (bβ * S / (X * √X)) := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = 2 * bβ * S / X := by field_simp
      _ ≤ 2 * bβ * S / k := div_le_div_of_nonneg_left (by positivity) hk0 hkX
  have n2 : ‖Z * bdryC c χ t ψ u k‖ ≤ 2 * bβ * S / k := by
    rw [norm_mul]
    have hsk : 0 < √k := Real.sqrt_pos.mpr hk0
    calc _ ≤ 2 * √k * (bβ * S / (k * √k)) := mul_le_mul hZ0 (hB k le_rfl hkX) (norm_nonneg _) (by positivity)
      _ = 2 * bβ * S / k := by field_simp
  have n3 : ‖Z * (∫ ξ in k..X, remDens c χ t ψ u ξ)‖ ≤ 4 / 3 * bρ * S / k := by
    rw [norm_mul]
    have hsk : 0 < √k := Real.sqrt_pos.mpr hk0
    calc _ ≤ 2 * √k * (2 / 3 * (bρ * S) / (k * √k)) :=
          mul_le_mul hZ0 (hR k le_rfl hkX) (norm_nonneg _) (by positivity)
      _ = 4 / 3 * bρ * S / k := by field_simp; ring
  have hinvsq : ∀ m ∈ F, ‖dch m t‖ * (1 / ((m : ℝ) * √(m : ℝ))) = ((m : ℝ) ^ 2)⁻¹ := by
    intro m hm
    have hm0 : (0 : ℝ) < m := by linarith [(hmF m hm).1]
    have hs := Real.sqrt_pos.mpr hm0
    have hss : √(m : ℝ) * √(m : ℝ) = m := Real.mul_self_sqrt hm0.le
    rw [norm_dch]; field_simp; nlinarith [hss]
  have hsum2 : ∑ m ∈ F, ((m : ℝ) ^ 2)⁻¹ ≤ 3 / (2 * k) := sum_inv_sq_far_le hk ⌊X⌋₊
  have n4 : ‖∑ m ∈ F, dch m t * bdryC c χ t ψ u m‖ ≤ 3 / 2 * bβ * S / k := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ m ∈ F, ‖dch m t * bdryC c χ t ψ u m‖ ≤ ∑ m ∈ F, bβ * S * ((m : ℝ) ^ 2)⁻¹ := by
          refine Finset.sum_le_sum fun m hm => ?_
          rw [norm_mul, ← hinvsq m hm]
          have h := hB m (hmF m hm).1 (hmF m hm).2
          calc ‖dch m t‖ * ‖bdryC c χ t ψ u m‖ ≤ ‖dch m t‖ * (bβ * S / (m * √(m : ℝ))) :=
                mul_le_mul_of_nonneg_left h (norm_nonneg _)
            _ = bβ * S * (‖dch m t‖ * (1 / ((m : ℝ) * √(m : ℝ)))) := by ring
      _ = bβ * S * ∑ m ∈ F, ((m : ℝ) ^ 2)⁻¹ := by rw [Finset.mul_sum]
      _ ≤ bβ * S * (3 / (2 * k)) := mul_le_mul_of_nonneg_left hsum2 (by positivity)
      _ = 3 / 2 * bβ * S / k := by field_simp
  have n5 : ‖∑ m ∈ F, dch m t * (∫ ξ in (m : ℝ)..X, remDens c χ t ψ u ξ)‖ ≤ bρ * S / k := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ m ∈ F, ‖dch m t * (∫ ξ in (m : ℝ)..X, remDens c χ t ψ u ξ)‖
        ≤ ∑ m ∈ F, 2 / 3 * (bρ * S) * ((m : ℝ) ^ 2)⁻¹ := by
          refine Finset.sum_le_sum fun m hm => ?_
          rw [norm_mul, ← hinvsq m hm]
          have h := hR m (hmF m hm).1 (hmF m hm).2
          calc ‖dch m t‖ * ‖∫ ξ in (m : ℝ)..X, remDens c χ t ψ u ξ‖
              ≤ ‖dch m t‖ * (2 / 3 * (bρ * S) / (m * √(m : ℝ))) := mul_le_mul_of_nonneg_left h (norm_nonneg _)
            _ = 2 / 3 * (bρ * S) * (‖dch m t‖ * (1 / ((m : ℝ) * √(m : ℝ)))) := by ring
      _ = 2 / 3 * (bρ * S) * ∑ m ∈ F, ((m : ℝ) ^ 2)⁻¹ := by rw [Finset.mul_sum]
      _ ≤ 2 / 3 * (bρ * S) * (3 / (2 * k)) := mul_le_mul_of_nonneg_left hsum2 (by positivity)
      _ = bρ * S / k := by field_simp
  calc _ ≤ ‖(∑ m ∈ Finset.Icc 1 ⌊X⌋₊, dch m t) * bdryC c χ t ψ u X‖ + ‖Z * bdryC c χ t ψ u k‖
        + ‖Z * (∫ ξ in k..X, remDens c χ t ψ u ξ)‖ + ‖∑ m ∈ F, dch m t * bdryC c χ t ψ u m‖
        + ‖∑ m ∈ F, dch m t * (∫ ξ in (m : ℝ)..X, remDens c χ t ψ u ξ)‖ := by
        refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
        exact norm_sub_le _ _
    _ ≤ 2 * bβ * S / k + 2 * bβ * S / k + 4 / 3 * bρ * S / k + 3 / 2 * bβ * S / k + bρ * S / k := by
        linarith
    _ = Cbar c r * S / k := by rw [Cbar]; ring

end Cvs.Prolate.Mellin.FarPartLevelBound
