import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Harmonic.Bounds
import Cvs.L2a.NonresonantCrossIntegral
import Cvs.L2a.StationaryPairElementarySizes
import Cvs.L2a.StationaryPairMismatchSign
import Cvs.Prolate.Envelope.ProlateWeightToEdge

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The edge-window stationary pair as a monomial in `k`, `m`, `c`

With `t_r = √(k² + 1/m²) + δ`, the right piece of Cvs.L2a.EdgeStationaryPairWindow has `D(t_r) ≥ (m² − 1/k²) 2c²k³δ`, `p_m(t_r) ≤ 4k²`,
`p_{1/k}(t_r) ≤ 3k(t_r − k)` and `R(t_r) ≤ 4m²k³/(t_r − k)`, so it is at most
`G√κ₀ (16k²/(3m) + 8k^{5/2}√(t_r − k))/(c² m² k³ δ)`, the window `(t_r − k)√(2K/(√3 σ)) G/(mk)`.
-/

namespace Cvs.L2a.EdgeWindowPairMonomial

open Real Set Cvs.L2a.NonresonantCrossIntegral Cvs.Prolate.Envelope.ProlateWeightToEdge Cvs.L2a.StationaryPairElementarySizes

set_option maxHeartbeats 1000000 in
/-- **The right piece, bounded.** For `k ≥ 1`, `km ≥ 2`, `0 < δ ≤ k/2`, `0 ≤ χ < c²`, `t_r = √S + δ`, `G, κ ≥ 0`:
`2(p_m(t_r) G√κ/m + p_{1/k}(t_r)(G/m)√(κ R(t_r)))/D(t_r) ≤ G√κ (16k²/(3m) + 8k²√k √(t_r − k))/(c² m² k³ δ)`. -/
theorem right_le {c χ k m δ G κ tr : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hk1 : 1 ≤ k) (hkm2 : 2 ≤ k * m) (hm : 1 ≤ m)
    (hδ : 0 < δ) (hδk : δ ≤ k / 2) (hG : 0 ≤ G) (hκ : 0 ≤ κ) (htrdef : tr = √(k ^ 2 + 1 / m ^ 2) + δ) :
    2 * (pm m tr * (G * √κ / m) + pm (1 / k) tr * (G / m * √(κ * (ew (m * tr) / ew (tr / k)))))
        / Dmr c χ m (1 / k) tr
      ≤ G * √κ * (16 * k ^ 2 / (3 * m) + 8 * k ^ 2 * √k * √(tr - k)) / (c ^ 2 * m ^ 2 * k ^ 3 * δ) := by
  have hk : 1 ≤ k := by linarith
  have hk0 : 0 < k := by linarith
  have hm0 : 0 < m := by linarith
  set S := k ^ 2 + 1 / m ^ 2 with hSdef
  have hS0 : 0 ≤ S := by positivity
  have hkS : k ≤ √S := Real.le_sqrt_of_sq_le (by have : 0 ≤ 1 / m ^ 2 := by positivity
                                                 linarith)
  have hgap := sqrtS_sub_le hk0 hm0
  have hkm1 : 1 ≤ k * m := by nlinarith
  have hgap1 : 1 / (2 * k * m ^ 2) ≤ k / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_le_mul hkm1 hkm1 zero_le_one (by linarith), mul_le_mul hk hkm1 zero_le_one (by linarith)]
  have htrk : δ ≤ tr - k := by rw [htrdef]; linarith
  have htr2 : tr ≤ 2 * k := by rw [htrdef]; linarith
  have htr0 : 0 < tr := by linarith
  -- D(t_r) ≥ (m² − 1/k²) 2c²k³δ
  have hmk : 3 / 4 * m ^ 2 ≤ m ^ 2 - 1 / k ^ 2 := by
    have : 1 / k ^ 2 ≤ m ^ 2 / 4 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    nlinarith
  have hE := Cvs.L2a.StationaryPairMismatchSign.Est_right (c := c) (χ := χ) (k := k) (m := m) (t := tr) hχ0 hδ hm0.ne' (le_of_eq htrdef.symm)
  have hD : (m ^ 2 - 1 / k ^ 2) * (2 * c ^ 2 * k ^ 3 * δ) ≤ Dmr c χ m (1 / k) tr := by
    rw [Cvs.L2a.StationaryPairMismatchSign.Dmr_eq_Est hk0.ne' hm0.ne']
    apply mul_le_mul_of_nonneg_left _ (by nlinarith [hmk, sq_nonneg m])
    refine le_trans ?_ hE
    have : k ^ 2 ≤ tr ^ 2 := by nlinarith
    have hk3 : k ^ 3 = k ^ 2 * k := by ring
    calc 2 * c ^ 2 * k ^ 3 * δ = 2 * c ^ 2 * k ^ 2 * k * δ := by ring
      _ ≤ 2 * c ^ 2 * tr ^ 2 * √S * δ := by
          apply mul_le_mul_of_nonneg_right _ hδ.le
          apply mul_le_mul (mul_le_mul_of_nonneg_left this (by positivity)) hkS hk0.le (by positivity)
  have hDpos : 0 < (m ^ 2 - 1 / k ^ 2) * (2 * c ^ 2 * k ^ 3 * δ) := by
    have : 0 < m ^ 2 - 1 / k ^ 2 := by nlinarith
    positivity
  -- the numerator
  have hpm : pm m tr ≤ 4 * k ^ 2 := (pm_le hm0.ne').trans (by nlinarith)
  have hpr : pm (1 / k) tr ≤ 3 * k * (tr - k) := by
    rw [pm_inv hk0.ne']; nlinarith
  have hpr0 : 0 ≤ pm (1 / k) tr := by rw [pm_inv hk0.ne']; nlinarith
  have hR : ew (m * tr) / ew (tr / k) ≤ 4 * m ^ 2 * k ^ 3 / (tr - k) := by
    have h1 : 1 ≤ tr / k := by rw [le_div_iff₀ hk0]; linarith
    have h2 : (tr - k) / k ≤ ew (tr / k) := by
      have := ew_ge_sub h1; rw [show tr / k - 1 = (tr - k) / k by field_simp] at this; exact this
    have hew1 : ew (m * tr) ≤ (m * tr) ^ 2 := by
      unfold ew
      have : √((m * tr) ^ 2 - 1) ≤ m * tr := Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
      calc m * tr * √((m * tr) ^ 2 - 1) ≤ m * tr * (m * tr) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = (m * tr) ^ 2 := by ring
    have hpos : 0 < (tr - k) / k := by apply div_pos (by linarith) hk0
    rw [div_le_div_iff₀ (lt_of_lt_of_le hpos h2) (by linarith)]
    calc ew (m * tr) * (tr - k) ≤ (m * tr) ^ 2 * (tr - k) :=
          mul_le_mul_of_nonneg_right hew1 (by linarith)
      _ ≤ (m * (2 * k)) ^ 2 * (tr - k) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left htr2 hm0.le) 2
      _ = 4 * m ^ 2 * k ^ 3 * ((tr - k) / k) := by field_simp; ring
      _ ≤ 4 * m ^ 2 * k ^ 3 * ew (tr / k) := mul_le_mul_of_nonneg_left h2 (by positivity)
  have hflux : pm (1 / k) tr * √(κ * (ew (m * tr) / ew (tr / k))) ≤ √κ * (6 * m * k ^ 2 * √k * √(tr - k)) := by
    have hq : 0 < tr - k := by linarith
    have hR' : √(κ * (ew (m * tr) / ew (tr / k))) ≤ √κ * (2 * m * k * √k / √(tr - k)) := by
      rw [sqrt_mul hκ]
      apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
      calc √(ew (m * tr) / ew (tr / k)) ≤ √(4 * m ^ 2 * k ^ 3 / (tr - k)) := sqrt_le_sqrt hR
        _ = 2 * m * k * √k / √(tr - k) := by
            rw [sqrt_div' _ hq.le, show 4 * m ^ 2 * k ^ 3 = (2 * m * k) ^ 2 * k by ring,
              sqrt_mul (by positivity), sqrt_sq (by positivity)]
    have hsq : √(tr - k) * √(tr - k) = tr - k := mul_self_sqrt hq.le
    have hs : 0 < √(tr - k) := sqrt_pos.mpr hq
    calc pm (1 / k) tr * √(κ * (ew (m * tr) / ew (tr / k)))
        ≤ 3 * k * (tr - k) * (√κ * (2 * m * k * √k / √(tr - k))) :=
          mul_le_mul hpr hR' (sqrt_nonneg _) (mul_nonneg (by linarith) hq.le)
      _ = √κ * (6 * m * k ^ 2 * √k * ((tr - k) / √(tr - k))) := by ring
      _ = √κ * (6 * m * k ^ 2 * √k * √(tr - k)) := by
          have hdv : (tr - k) / √(tr - k) = √(tr - k) := by
            rw [div_eq_iff hs.ne', hsq]
          rw [hdv]
  -- combine
  have hnum : 2 * (pm m tr * (G * √κ / m) + pm (1 / k) tr * (G / m * √(κ * (ew (m * tr) / ew (tr / k)))))
      ≤ 2 * (4 * k ^ 2 * (G * √κ / m) + G / m * (√κ * (6 * m * k ^ 2 * √k * √(tr - k)))) := by
    have e1 : pm m tr * (G * √κ / m) ≤ 4 * k ^ 2 * (G * √κ / m) :=
      mul_le_mul_of_nonneg_right hpm (by positivity)
    have e2 : pm (1 / k) tr * (G / m * √(κ * (ew (m * tr) / ew (tr / k))))
        ≤ G / m * (√κ * (6 * m * k ^ 2 * √k * √(tr - k))) := by
      rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left hflux (by positivity)
    exact mul_le_mul_of_nonneg_left (add_le_add e1 e2) (by norm_num)
  calc _ ≤ 2 * (4 * k ^ 2 * (G * √κ / m) + G / m * (√κ * (6 * m * k ^ 2 * √k * √(tr - k))))
        / ((m ^ 2 - 1 / k ^ 2) * (2 * c ^ 2 * k ^ 3 * δ)) := by
        apply div_le_div₀ (by positivity) hnum hDpos hD
    _ ≤ 2 * (4 * k ^ 2 * (G * √κ / m) + G / m * (√κ * (6 * m * k ^ 2 * √k * √(tr - k))))
        / (3 / 4 * m ^ 2 * (2 * c ^ 2 * k ^ 3 * δ)) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right hmk (by positivity)
    _ = G * √κ * (16 * k ^ 2 / (3 * m) + 8 * k ^ 2 * √k * √(tr - k)) / (c ^ 2 * m ^ 2 * k ^ 3 * δ) := by
        field_simp; ring

/-- **The window's value factor**: with `ψ(1)² ≤ K G`, `σ > 0`, `m k ≥ 2`,
`√(G/(σ ew(mk))) |ψ(1)| ≤ √(2K/(√3 σ)) G/(mk)`. -/
theorem window_factor_le {σ G K m k ψ1 : ℝ} (hσ : 0 < σ) (hG : 0 ≤ G) (hK : 0 ≤ K) (hmk : 2 ≤ m * k)
    (hm : 0 < m) (hk : 0 < k) (hedge : ψ1 ^ 2 ≤ K * G) :
    √(G / (σ * ew (m * k))) * |ψ1| ≤ √(2 * K / (√3 * σ)) * G / (m * k) := by
  have hew := ew_ge_sq hmk
  have hew0 : 0 < ew (m * k) := lt_of_lt_of_le (by positivity) hew
  have hs3 : 0 < √3 := by positivity
  have h1 : √(G / (σ * ew (m * k))) ≤ √(G / (σ * (√3 / 2 * (m * k) ^ 2))) :=
    sqrt_le_sqrt (div_le_div_of_nonneg_left hG (by positivity) (mul_le_mul_of_nonneg_left hew hσ.le))
  have h2 : |ψ1| ≤ √(K * G) := by rw [← sqrt_sq_eq_abs]; exact sqrt_le_sqrt hedge
  calc √(G / (σ * ew (m * k))) * |ψ1| ≤ √(G / (σ * (√3 / 2 * (m * k) ^ 2))) * √(K * G) :=
        mul_le_mul h1 h2 (abs_nonneg _) (sqrt_nonneg _)
    _ = √(G / (σ * (√3 / 2 * (m * k) ^ 2)) * (K * G)) := (sqrt_mul (by positivity) _).symm
    _ = √((2 * K / (√3 * σ)) * (G / (m * k)) ^ 2) := by congr 1; field_simp
    _ = √(2 * K / (√3 * σ)) * G / (m * k) := by
        rw [sqrt_mul (by positivity), sqrt_sq (by positivity)]; ring

end Cvs.L2a.EdgeWindowPairMonomial
