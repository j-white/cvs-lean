import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Harmonic.Bounds
import Cvs.L2a.NonresonantCrossIntegral
import Cvs.L2a.StationaryMismatchExactRoots
import Cvs.L2a.StationaryPairElementarySizes
import Cvs.L2a.StationaryPairMismatchSign

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The right and left pieces of a stationary pair with `σ`-free envelopes, for every `χ ≤ c²`

With the window at `√T₊`, `|D| ≥ (9/8)m²c²k³δ` on either side (Cvs.L2a.StationaryMismatchExactRoots), and the envelopes of Cvs.L2a.SigmaFreeStationaryEdgePairs: the right piece is
at most `(16/9)G(8k²/(√3m) + 2√3 k^{5/2}√(t_r − k))/(m²c²k³δ)`, and the left piece, from `a = k(1 + 1/c)`, at most
`(16/9)G(t_l²(2/√3)/m + (T₊ − k²)√2 k√c)/(m²c²k³δ)`; neither involves `σ`.
-/

namespace Cvs.L2a.SigmaFreePairPieces

open Real Set Cvs.L2a.NonresonantCrossIntegral Cvs.Prolate.Envelope.ProlateWeightToEdge Cvs.L2a.StationaryPairElementarySizes Cvs.L2a.StationaryMismatchExactRoots

set_option maxHeartbeats 2000000 in
/-- **The right piece, `σ`-free**, `t_r = √T₊ + δ`. -/
theorem right_le {c χ k m δ G tr : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ ≤ c ^ 2) (hk1 : 1 ≤ k)
    (hkm2 : 2 ≤ k * m) (hm : 1 ≤ m) (hδ : 0 < δ) (hδk : δ ≤ k / 2) (hG : 0 ≤ G)
    (htrdef : tr = √(Tp c χ k m) + δ) :
    2 * (pm m tr * (2 / √3 * G / m) + pm (1 / k) tr * (G * k * tr / √(tr ^ 2 - k ^ 2))) / Dmr c χ m (1 / k) tr
      ≤ 16 / 9 * G * (8 * k ^ 2 / (√3 * m) + 2 * √3 * k ^ 2 * √k * √(tr - k)) / (m ^ 2 * c ^ 2 * k ^ 3 * δ) := by
  have hk0 : 0 < k := by linarith
  have hm0 : 0 < m := by linarith
  set S := k ^ 2 + 1 / m ^ 2 with hSdef
  have hkm1' : 1 ≤ m * k := by nlinarith
  have hTp := Tp_ge hc hk0 hm0 hkm1' hχ0 hχc
  have hTpS := Tp_le (k := k) hc hm0 hχ0
  have hT0 : 0 ≤ (c ^ 2 - χ) / (c ^ 2 * m ^ 2) := div_nonneg (by linarith) (by positivity)
  have hkS : k ≤ √(Tp c χ k m) := Real.le_sqrt_of_sq_le (by linarith)
  have hTS : √(Tp c χ k m) ≤ √S := sqrt_le_sqrt hTpS
  have hgap := sqrtS_sub_le hk0 hm0
  have hkm1 : 1 ≤ k * m := by nlinarith
  have hgap1 : 1 / (2 * k * m ^ 2) ≤ k / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_le_mul hkm1 hkm1 zero_le_one (by linarith), mul_le_mul hk1 hkm1 zero_le_one (by linarith)]
  have htrk : δ ≤ tr - k := by rw [htrdef]; linarith
  have htr2 : tr ≤ 2 * k := by rw [htrdef]; linarith
  have htr0 : 0 < tr := by linarith
  have hmk : 3 / 4 * m ^ 2 ≤ m ^ 2 - 1 / k ^ 2 := by
    have : 1 / k ^ 2 ≤ m ^ 2 / 4 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    nlinarith
  have hE := Est_right (t := tr) hc hk0 hm0 hkm1' hχ0 hχc hδ (le_of_eq htrdef.symm)
  have hk2 : 3 / 4 * k ^ 2 ≤ k ^ 2 - 1 / m ^ 2 := by
    have : 1 / m ^ 2 ≤ k ^ 2 / 4 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have hD : (m ^ 2 - 1 / k ^ 2) * (3 / 2 * c ^ 2 * k ^ 3 * δ) ≤ Dmr c χ m (1 / k) tr := by
    rw [Cvs.L2a.StationaryPairMismatchSign.Dmr_eq_Est hk0.ne' hm0.ne']
    apply mul_le_mul_of_nonneg_left _ (by nlinarith [hmk, sq_nonneg m])
    refine le_trans ?_ hE
    calc 3 / 2 * c ^ 2 * k ^ 3 * δ = 2 * c ^ 2 * k * δ * (3 / 4 * k ^ 2) := by ring
      _ ≤ 2 * c ^ 2 * √(Tp c χ k m) * δ * (k ^ 2 - 1 / m ^ 2) := by
          apply mul_le_mul _ hk2 (by positivity) (by positivity)
          apply mul_le_mul_of_nonneg_right _ hδ.le
          exact mul_le_mul_of_nonneg_left hkS (by positivity)
  have hD' : 9 / 8 * (m ^ 2 * c ^ 2 * k ^ 3 * δ) ≤ Dmr c χ m (1 / k) tr := by
    refine le_trans ?_ hD
    have := mul_le_mul_of_nonneg_right hmk (by positivity : (0 : ℝ) ≤ 3 / 2 * c ^ 2 * k ^ 3 * δ)
    nlinarith
  have hDpos : 0 < 9 / 8 * (m ^ 2 * c ^ 2 * k ^ 3 * δ) := by positivity
  -- the numerator
  have hpm : pm m tr ≤ 4 * k ^ 2 := (pm_le hm0.ne').trans (by nlinarith)
  have hq : 0 < tr ^ 2 - k ^ 2 := by nlinarith
  have hsq : √(tr ^ 2 - k ^ 2) ≤ √3 * √k * √(tr - k) := by
    rw [← sqrt_mul (by norm_num), ← sqrt_mul (by positivity)]
    apply sqrt_le_sqrt; nlinarith
  have hs0 : 0 < √(tr ^ 2 - k ^ 2) := sqrt_pos.mpr hq
  have hpr : pm (1 / k) tr * (G * k * tr / √(tr ^ 2 - k ^ 2)) ≤ 2 * √3 * G * k ^ 2 * √k * √(tr - k) := by
    rw [pm_inv hk0.ne']
    have hdiv : (tr ^ 2 - k ^ 2) / √(tr ^ 2 - k ^ 2) = √(tr ^ 2 - k ^ 2) := by
      rw [div_eq_iff hs0.ne', mul_self_sqrt hq.le]
    have e : (tr ^ 2 - k ^ 2) * (G * k * tr / √(tr ^ 2 - k ^ 2)) = G * k * tr * √(tr ^ 2 - k ^ 2) := by
      calc (tr ^ 2 - k ^ 2) * (G * k * tr / √(tr ^ 2 - k ^ 2))
          = G * k * tr * ((tr ^ 2 - k ^ 2) / √(tr ^ 2 - k ^ 2)) := by ring
        _ = G * k * tr * √(tr ^ 2 - k ^ 2) := by rw [hdiv]
    rw [e]
    calc G * k * tr * √(tr ^ 2 - k ^ 2) ≤ G * k * (2 * k) * (√3 * √k * √(tr - k)) := by gcongr
      _ = 2 * √3 * G * k ^ 2 * √k * √(tr - k) := by ring
  have hnum : 2 * (pm m tr * (2 / √3 * G / m) + pm (1 / k) tr * (G * k * tr / √(tr ^ 2 - k ^ 2)))
      ≤ 2 * (4 * k ^ 2 * (2 / √3 * G / m) + 2 * √3 * G * k ^ 2 * √k * √(tr - k)) := by
    have := mul_le_mul_of_nonneg_right hpm (by positivity : (0 : ℝ) ≤ 2 / √3 * G / m)
    linarith
  calc _ ≤ 2 * (4 * k ^ 2 * (2 / √3 * G / m) + 2 * √3 * G * k ^ 2 * √k * √(tr - k))
        / (9 / 8 * (m ^ 2 * c ^ 2 * k ^ 3 * δ)) := div_le_div₀ (by positivity) hnum hDpos hD'
    _ = 16 / 9 * G * (8 * k ^ 2 / (√3 * m) + 2 * √3 * k ^ 2 * √k * √(tr - k)) / (m ^ 2 * c ^ 2 * k ^ 3 * δ) := by
        field_simp; ring

set_option maxHeartbeats 2000000 in
/-- **The left piece, `σ`-free**, from `a = k(1 + 1/c)` to `t_l ≤ √T₊ − δ`. -/
theorem left_le {c χ k m δ G tl : ℝ} (hc : 1 ≤ c) (hχ0 : 0 ≤ χ) (hχc : χ ≤ c ^ 2) (hk1 : 1 ≤ k)
    (hkm2 : 2 ≤ k * m) (hm : 1 ≤ m) (hδ : 0 < δ) (hG : 0 ≤ G)
    (hktl : k * (1 + 1 / c) ≤ tl) (htl : tl ≤ √(Tp c χ k m) - δ) :
    2 * (-(pm m tl / Dmr c χ m (1 / k) tl) * (2 / √3 * G / m)
          + -(pm (1 / k) tl / Dmr c χ m (1 / k) tl) * (G * k * (k * (1 + 1 / c)) / √((k * (1 + 1 / c)) ^ 2 - k ^ 2)))
      ≤ 16 / 9 * G * (tl ^ 2 * (2 / √3) / m + (Tp c χ k m - k ^ 2) * (√2 * k * √c)) / (m ^ 2 * c ^ 2 * k ^ 3 * δ) := by
  have hk0 : 0 < k := by linarith
  have hm0 : 0 < m := by linarith
  have hc0 : 0 < c := by linarith
  set a := k * (1 + 1 / c) with ha
  have hic : 0 < 1 / c := by positivity
  have hka : k < a := by rw [ha]; nlinarith
  have hktl' : k ≤ tl := hka.le.trans hktl
  have htl0 : 0 < tl := by linarith
  have hkm1' : 1 ≤ m * k := by nlinarith
  have hTp := Tp_ge hc0 hk0 hm0 hkm1' hχ0 hχc
  have hE := Est_left (t := tl) hc0 hk0 hm0 hkm1' hχ0 hχc hδ hktl' htl
  have hmk : 3 / 4 * m ^ 2 ≤ m ^ 2 - 1 / k ^ 2 := by
    have : 1 / k ^ 2 ≤ m ^ 2 / 4 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    nlinarith
  have hmk0 : 0 < m ^ 2 - 1 / k ^ 2 := by nlinarith
  have hk2 : 3 / 4 * k ^ 2 ≤ k ^ 2 - 1 / m ^ 2 := by
    have : 1 / m ^ 2 ≤ k ^ 2 / 4 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have hD : 9 / 8 * (m ^ 2 * c ^ 2 * k ^ 3 * δ) ≤ -Dmr c χ m (1 / k) tl := by
    rw [Cvs.L2a.StationaryPairMismatchSign.Dmr_eq_Est hk0.ne' hm0.ne']
    have h1 : 3 / 2 * c ^ 2 * k ^ 3 * δ ≤ 2 * c ^ 2 * k * δ * (k ^ 2 - 1 / m ^ 2) := by
      have := mul_le_mul_of_nonneg_left hk2 (by positivity : (0 : ℝ) ≤ 2 * c ^ 2 * k * δ)
      linarith
    have h2 := mul_le_mul_of_nonneg_right hmk (by positivity : (0 : ℝ) ≤ 3 / 2 * c ^ 2 * k ^ 3 * δ)
    nlinarith [mul_le_mul_of_nonneg_left hE hmk0.le, mul_le_mul_of_nonneg_left h1 hmk0.le]
  have hDpos : 0 < 9 / 8 * (m ^ 2 * c ^ 2 * k ^ 3 * δ) := by positivity
  have hDneg : Dmr c χ m (1 / k) tl < 0 := by linarith
  -- numerators
  have hpm : pm m tl ≤ tl ^ 2 := pm_le hm0.ne'
  have hmt : 1 ≤ m * tl := by nlinarith
  have hpm0 : 0 ≤ pm m tl := by
    unfold pm; apply div_nonneg _ (by positivity); nlinarith [hmt]
  have hpr : pm (1 / k) tl ≤ Tp c χ k m - k ^ 2 := by
    rw [pm_inv hk0.ne']
    have hT0' : 0 ≤ (c ^ 2 - χ) / (c ^ 2 * m ^ 2) := div_nonneg (by linarith) (by positivity)
    have hT0 : 0 ≤ Tp c χ k m := by nlinarith [sq_nonneg k]
    have hsq : √(Tp c χ k m) ^ 2 = Tp c χ k m := sq_sqrt hT0
    have hle : tl ≤ √(Tp c χ k m) := by linarith [htl, hδ]
    have : tl ^ 2 ≤ √(Tp c χ k m) ^ 2 := pow_le_pow_left₀ htl0.le hle 2
    linarith
  have hpr0 : 0 ≤ pm (1 / k) tl := by rw [pm_inv hk0.ne']; nlinarith
  -- the flux-value factor at `a`: `k a/√(a² − k²) ≤ √2 k √c`
  have hfac : G * k * a / √(a ^ 2 - k ^ 2) ≤ G * (√2 * k * √c) := by
    have ha2 : 2 * k ^ 2 / c ≤ a ^ 2 - k ^ 2 := by
      rw [ha]; have : 0 ≤ k ^ 2 / c ^ 2 := by positivity
      have e : (k * (1 + 1 / c)) ^ 2 - k ^ 2 = 2 * k ^ 2 / c + k ^ 2 / c ^ 2 := by field_simp; ring
      rw [e]; linarith
    have ha2' : a ≤ 2 * k := by
      rw [ha]; have : 1 / c ≤ 1 := by rw [div_le_one hc0]; exact hc
      nlinarith
    have hs : √(2 * k ^ 2 / c) ≤ √(a ^ 2 - k ^ 2) := sqrt_le_sqrt ha2
    have hs0 : 0 < √(2 * k ^ 2 / c) := sqrt_pos.mpr (by positivity)
    have hsv : √(2 * k ^ 2 / c) = √2 * k / √c := by
      rw [sqrt_div' _ hc0.le, sqrt_mul (by norm_num), sqrt_sq hk0.le]
    have hsc : 0 < √c := sqrt_pos.mpr hc0
    calc G * k * a / √(a ^ 2 - k ^ 2) ≤ G * k * a / √(2 * k ^ 2 / c) :=
          div_le_div_of_nonneg_left (by positivity) hs0 hs
      _ ≤ G * k * (2 * k) / √(2 * k ^ 2 / c) := by gcongr
      _ = G * (√2 * k * √c) := by
          rw [hsv, div_div_eq_mul_div]
          have h22 : √2 * √2 = 2 := mul_self_sqrt (by norm_num)
          rw [div_eq_iff (by positivity)]
          linear_combination (-(G * k ^ 2 * √c)) * h22
  have e : 2 * (-(pm m tl / Dmr c χ m (1 / k) tl) * (2 / √3 * G / m)
          + -(pm (1 / k) tl / Dmr c χ m (1 / k) tl) * (G * k * a / √(a ^ 2 - k ^ 2)))
      = 2 * (pm m tl * (2 / √3 * G / m) + pm (1 / k) tl * (G * k * a / √(a ^ 2 - k ^ 2)))
        / (-Dmr c χ m (1 / k) tl) := by
    have hDne := hDneg.ne
    field_simp
    ring
  rw [e]
  have hnum : 2 * (pm m tl * (2 / √3 * G / m) + pm (1 / k) tl * (G * k * a / √(a ^ 2 - k ^ 2)))
      ≤ 2 * G * (tl ^ 2 * (2 / √3) / m + (Tp c χ k m - k ^ 2) * (√2 * k * √c)) := by
    have h1 := mul_le_mul_of_nonneg_right hpm (by positivity : (0 : ℝ) ≤ 2 / √3 * G / m)
    have h2 := mul_le_mul hpr hfac (by positivity) (le_trans hpr0 hpr)
    have e1 : tl ^ 2 * (2 / √3 * G / m) = G * (tl ^ 2 * (2 / √3) / m) := by ring
    have e2 : (Tp c χ k m - k ^ 2) * (G * (√2 * k * √c)) = G * ((Tp c χ k m - k ^ 2) * (√2 * k * √c)) := by ring
    nlinarith
  calc _ ≤ 2 * G * (tl ^ 2 * (2 / √3) / m + (Tp c χ k m - k ^ 2) * (√2 * k * √c))
        / (9 / 8 * (m ^ 2 * c ^ 2 * k ^ 3 * δ)) := by
          have hTk : 0 ≤ Tp c χ k m - k ^ 2 := le_trans hpr0 hpr
          exact div_le_div₀ (mul_nonneg (by positivity) (add_nonneg (by positivity)
            (mul_nonneg hTk (by positivity)))) hnum hDpos hD
    _ = 16 / 9 * G * (tl ^ 2 * (2 / √3) / m + (Tp c χ k m - k ^ 2) * (√2 * k * √c))
        / (m ^ 2 * c ^ 2 * k ^ 3 * δ) := by field_simp; ring

end Cvs.L2a.SigmaFreePairPieces
