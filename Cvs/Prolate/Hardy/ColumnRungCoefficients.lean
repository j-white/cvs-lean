import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.CellGramTraceComparison
import Cvs.Prolate.Gram.CentralResolventTrace
import Cvs.Prolate.Hardy.CentralRungExpansion
import Cvs.Prolate.Hardy.FourierDefectColumns
import Cvs.Prolate.SincTopIsRung

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The rung coefficients of the exterior columns are the band functions of the rungs

For `u > 1` the column `e_u` is even and continuous on `[−1, 1]` with `|e_u| ≤ (2c + 2)/(πu)`; its rung coefficients
are `⟨e_u, h_k⟩ = B_{h_k}(u)` and those of `Fe_u` are `σ_k B_{h_k}(u)`, since `F` is symmetric with `Fh_k = σ_k h_k`;
and `2∫_{u>1} B_{h_k}B_{h_j} = (σ_k² − σ_k⁴)δ_kj`.
-/

noncomputable section

open Real Set MeasureTheory Filter intervalIntegral

namespace Cvs.Prolate.Hardy.ColumnRungCoefficients
open Cvs.ZeroCounting

open Cvs.Prolate.EvenRungsByIndex (rung IsLevelIdx rung_spec continuousOn_rung muR psi_rung)
open Cvs.Prolate.SincTopIsRung (clampExt clampExt_of_mem continuous_clampExt clampExt_neg)
open Cvs.Prolate.Hardy.FourierDefectColumns (Fop cosT bandB evenCol)
open Cvs.Prolate.Hardy.CentralRungExpansion (hk coef continuous_hk hk_eq)
open Cvs.Prolate.Gram.CentralResolventTrace (sigma)

/-! ### The exterior columns -/

theorem continuousOn_evenCol (c : ℝ) {u : ℝ} (hu : 1 < u) : ContinuousOn (evenCol c u) (Icc (-1) 1) := by
  have hπ := Real.pi_pos
  unfold evenCol
  refine ContinuousOn.div_const (ContinuousOn.add ?_ ?_) 2
  · refine (by fun_prop : Continuous fun t => sin (c * (t - u))).continuousOn.div
      (by fun_prop : Continuous fun t => π * (t - u)).continuousOn fun t ht => ?_
    exact mul_ne_zero hπ.ne' (show t - u < 0 by linarith [ht.2]).ne
  · refine (by fun_prop : Continuous fun t => sin (c * (-t - u))).continuousOn.div
      (by fun_prop : Continuous fun t => π * (-t - u)).continuousOn fun t ht => ?_
    exact mul_ne_zero hπ.ne' (show -t - u < 0 by linarith [ht.1]).ne

theorem evenCol_neg (c u t : ℝ) : evenCol c u (-t) = evenCol c u t := by
  unfold evenCol; rw [neg_neg, add_comm]

/-- The column `e_u` as a continuous function on `ℝ` (clamped outside `[−1, 1]`). -/
def eC (c u : ℝ) : ℝ → ℝ := clampExt (evenCol c u)

theorem continuous_eC (c : ℝ) {u : ℝ} (hu : 1 < u) : Continuous (eC c u) :=
  continuous_clampExt (continuousOn_evenCol c hu)

theorem eC_neg (c u t : ℝ) : eC c u (-t) = eC c u t :=
  clampExt_neg (fun s _ => evenCol_neg c u s) t

theorem abs_sinc_le {c u d : ℝ} (hc : 0 ≤ c) (hu : 1 < u) (hd : u - 1 ≤ |d|) :
    |sin (c * d) / (π * d)| ≤ (2 * c + 2) / (π * u) := by
  have hπ := Real.pi_pos
  have hd0 : 0 < |d| := by linarith
  rw [abs_div, abs_mul, abs_of_pos hπ, div_le_div_iff₀ (by positivity) (by positivity)]
  have hs0 := abs_nonneg (sin (c * d))
  rcases le_or_gt u 2 with h2 | h2
  · have h1 : |sin (c * d)| ≤ c * |d| := by
      have := Real.abs_sin_le_abs (x := c * d); rwa [abs_mul, abs_of_nonneg hc] at this
    calc |sin (c * d)| * (π * u) ≤ c * |d| * (π * u) := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ c * |d| * (π * 2) := mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
      _ ≤ (2 * c + 2) * (π * |d|) := by nlinarith [mul_nonneg hπ.le (abs_nonneg d)]
  · have h1 := Real.abs_sin_le_one (c * d)
    calc |sin (c * d)| * (π * u) ≤ 1 * (π * u) := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ (2 * c + 2) * (π * |d|) := by nlinarith [mul_nonneg hπ.le (abs_nonneg d), mul_nonneg hc hπ.le]

/-- **The column bound** `|e_u(t)| ≤ (2c + 2)/(πu)` on `[−1, 1]` for `u > 1`. -/
theorem abs_evenCol_le {c u t : ℝ} (hc : 0 ≤ c) (hu : 1 < u) (ht : t ∈ Icc (-1 : ℝ) 1) :
    |evenCol c u t| ≤ (2 * c + 2) / (π * u) := by
  have h1 := abs_sinc_le (d := t - u) hc hu (by rw [abs_of_neg (by linarith [ht.2])]; linarith [ht.2])
  have h2 := abs_sinc_le (d := -t - u) hc hu (by rw [abs_of_neg (by linarith [ht.1])]; linarith [ht.1])
  unfold evenCol
  rw [abs_div, abs_two]
  have := abs_add_le (sin (c * (t - u)) / (π * (t - u))) (sin (c * (-t - u)) / (π * (-t - u)))
  linarith

theorem integral_eC_sq_le {c u : ℝ} (hc : 0 ≤ c) (hu : 1 < u) :
    ∫ t in (-1 : ℝ)..1, eC c u t ^ 2 ≤ 2 * ((2 * c + 2) / (π * u)) ^ 2 := by
  have hb : ∀ t ∈ Icc (-1 : ℝ) 1, eC c u t ^ 2 ≤ ((2 * c + 2) / (π * u)) ^ 2 := by
    intro t ht
    rw [eC, clampExt_of_mem ht, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_evenCol_le hc hu ht) 2
  calc ∫ t in (-1 : ℝ)..1, eC c u t ^ 2 ≤ ∫ t in (-1 : ℝ)..1, ((2 * c + 2) / (π * u)) ^ 2 :=
        integral_mono_on (by norm_num) (((continuous_eC c hu).pow 2).intervalIntegrable _ _)
          intervalIntegrable_const hb
    _ = 2 * ((2 * c + 2) / (π * u)) ^ 2 := by rw [intervalIntegral.integral_const, smul_eq_mul]; norm_num

/-! ### Symmetry and eigenvectors of `F` -/

/-- **`F` is symmetric on `[−1, 1]`**: `∫ (Fy) z = ∫ y (Fz)`. -/
theorem integral_Fop_mul (c : ℝ) {y z : ℝ → ℝ} (hy : Continuous y) (hz : Continuous z) :
    ∫ t in (-1 : ℝ)..1, Fop c y t * z t = ∫ t in (-1 : ℝ)..1, y t * Fop c z t := by
  have hint : IntegrableOn (Function.uncurry fun t s => y s * cos (c * t * s) * z t)
      (uIoc (-1 : ℝ) 1 ×ˢ uIoc (-1 : ℝ) 1) :=
    ((by fun_prop : Continuous (Function.uncurry fun t s => y s * cos (c * t * s) * z t)).continuousOn
      |>.integrableOn_compact
      (isCompact_uIcc.prod isCompact_uIcc)).mono_set (prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  have e1 : ∫ t in (-1 : ℝ)..1, Fop c y t * z t =
      √(c / (2 * π)) * ∫ t in (-1 : ℝ)..1, ∫ s in (-1 : ℝ)..1, y s * cos (c * t * s) * z t := by
    rw [← intervalIntegral.integral_const_mul]
    refine integral_congr fun t _ => ?_
    simp only [Fop, cosT]
    rw [mul_assoc, ← intervalIntegral.integral_mul_const]
  have e2 : ∫ t in (-1 : ℝ)..1, y t * Fop c z t =
      √(c / (2 * π)) * ∫ s in (-1 : ℝ)..1, ∫ t in (-1 : ℝ)..1, y s * cos (c * t * s) * z t := by
    rw [← intervalIntegral.integral_const_mul]
    refine integral_congr fun s _ => ?_
    simp only [Fop, cosT]
    rw [mul_left_comm, ← intervalIntegral.integral_const_mul]
    congr 1; refine integral_congr fun t _ => ?_
    ring_nf
  rw [e1, e2, intervalIntegral_intervalIntegral_swap hint]

/-- `Fh_k = σ_k h_k` on `[−1, 1]`. -/
theorem Fop_hk {c : ℝ} {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    Fop c (hk c k) t = sigma c k * hk c k t := by
  have e : cosT (hk c k) (c * t) = Cvs.L2a.AngularProlateTailPositive.psi c (rung c k) t := by
    show ∫ s in (-1 : ℝ)..1, hk c k s * cos (c * t * s) = ∫ s in (-1 : ℝ)..1, rung c k s * cos (c * t * s)
    refine integral_congr fun s hs => ?_
    rw [uIcc_of_le (by norm_num)] at hs
    simp only [hk_eq h hs]
  rw [Fop, e, psi_rung h t ht, hk_eq h ht, sigma]
  ring

/-- `F²h_k = σ_k² h_k` on `[−1, 1]`. -/
theorem Fop_Fop_hk {c : ℝ} {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    Fop c (Fop c (hk c k)) t = sigma c k ^ 2 * hk c k t := by
  have e : cosT (Fop c (hk c k)) (c * t) = sigma c k * cosT (hk c k) (c * t) := by
    unfold cosT
    rw [← intervalIntegral.integral_const_mul]
    refine integral_congr fun s hs => ?_
    rw [uIcc_of_le (by norm_num)] at hs
    simp only [Fop_hk h hs]; ring
  have e2 : Fop c (Fop c (hk c k)) t = sigma c k * Fop c (hk c k) t := by
    rw [Fop, e, Fop]; ring
  rw [e2, Fop_hk h ht]; ring

/-- The rung coefficients of `Fy` are `σ_k⟨y, h_k⟩`. -/
theorem coef_Fop {c : ℝ} {y : ℝ → ℝ} (hy : Continuous y) (k : ℕ) :
    coef c (Fop c y) k = sigma c k * coef c y k := by
  unfold coef
  split_ifs with h
  · rw [integral_Fop_mul c hy (continuous_hk c k), ← intervalIntegral.integral_const_mul]
    refine integral_congr fun t ht => ?_
    rw [uIcc_of_le (by norm_num)] at ht
    simp only [Fop_hk h ht]; ring
  · ring

/-! ### The band functions of the rungs -/

theorem bandB_zero (c u : ℝ) : bandB c 0 u = 0 := by
  simp [bandB, cosT]

/-- `⟨e_u, h_k⟩ = B_{h_k}(u)` for `u > 1`. -/
theorem coef_eC {c u : ℝ} (hu : 1 < u) (k : ℕ) : coef c (eC c u) k = bandB c (hk c k) u := by
  unfold coef
  split_ifs with h
  · rw [Cvs.Prolate.Hardy.FourierDefectColumns.bandB_eq (continuous_hk c k) (by rw [abs_of_pos (by linarith)]; exact hu)]
    refine integral_congr fun t ht => ?_
    rw [uIcc_of_le (by norm_num)] at ht
    simp only [eC, clampExt_of_mem ht]
  · rw [Cvs.Prolate.Hardy.CentralRungExpansion.hk_of_not h, bandB_zero]

/-- **Double orthogonality**: `2∫_{u>1} B_{h_k}B_{h_j} = (σ_k² − σ_k⁴)δ_kj`. -/
theorem integral_bandB_mul {c : ℝ} (hc : 0 < c) {k j : ℕ} (hk' : ∃ χ, IsLevelIdx c k χ)
    (hj : ∃ χ, IsLevelIdx c j χ) :
    2 * ∫ u in Ioi 1, bandB c (hk c k) u * bandB c (hk c j) u =
      if k = j then sigma c k ^ 2 - sigma c k ^ 4 else 0 := by
  rw [← Cvs.Prolate.Hardy.FourierDefectColumns.defect hc (continuous_hk c k) (continuous_hk c j)]
  have e1 : ∫ s in (-1 : ℝ)..1, Fop c (hk c k) s * Fop c (hk c j) s =
      sigma c k * sigma c j * ∫ s in (-1 : ℝ)..1, hk c k s * hk c j s := by
    rw [← intervalIntegral.integral_const_mul]
    refine integral_congr fun s hs => ?_
    rw [uIcc_of_le (by norm_num)] at hs
    simp only [Fop_hk hk' hs, Fop_hk hj hs]; ring
  have e2 : ∫ s in (-1 : ℝ)..1, Fop c (Fop c (hk c k)) s * Fop c (Fop c (hk c j)) s =
      sigma c k ^ 2 * sigma c j ^ 2 * ∫ s in (-1 : ℝ)..1, hk c k s * hk c j s := by
    rw [← intervalIntegral.integral_const_mul]
    refine integral_congr fun s hs => ?_
    rw [uIcc_of_le (by norm_num)] at hs
    simp only [Fop_Fop_hk hk' hs, Fop_Fop_hk hj hs]; ring
  rw [e1, e2, Cvs.Prolate.Hardy.CentralRungExpansion.integral_hk_mul_hk hk' hj]
  split_ifs with hkj
  · subst hkj; ring
  · ring

end Cvs.Prolate.Hardy.ColumnRungCoefficients

end
