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
# The near-edge stationary pair's left piece and window as monomials

With `t_l = √(k² + 1/m²) − δ ≥ a = k(1 + 1/c)`, `k ≥ 1`, `km ≥ 2`, `m ≥ 1`: the left piece of Cvs.L2a.StationaryEnvelopeMonotone is at most
`8G√κ (1/m + 2k√c/(m² t_l²))/(3c² k δ m²)`, and the window `2δ √(G/(σ ew(m t_l))) √(G/(σ ew(t_l/k)))` is at most
`2δ G √(4√3)/σ` once `t_l − k ≥ 1/(6km²)`.
-/

namespace Cvs.L2a.NearEdgePairLeftPiece

open Real Set Cvs.L2a.NonresonantCrossIntegral Cvs.Prolate.Envelope.ProlateWeightToEdge Cvs.L2a.StationaryPairElementarySizes

/-- **The left piece, bounded.** -/
theorem left_le {c χ k m δ G κ tl : ℝ} (hc : 1 ≤ c) (hχ0 : 0 ≤ χ) (hk1 : 1 ≤ k) (hkm2 : 2 ≤ k * m) (hm : 1 ≤ m)
    (hδ : 0 < δ) (hδχ : χ / (c ^ 2 * m ^ 2 * k) ≤ δ) (hG : 0 ≤ G) (hκ : 0 ≤ κ)
    (hktl : k * (1 + 1 / c) ≤ tl) (htl : tl ≤ √(k ^ 2 + 1 / m ^ 2) - δ) :
    2 * (-(pm m tl / Dmr c χ m (1 / k) tl) * (G * √κ / m)
          + -(pm (1 / k) tl / Dmr c χ m (1 / k) tl)
            * (G / m * √(κ * (ew (m * (k * (1 + 1 / c))) / ew (k * (1 + 1 / c) / k)))))
      ≤ 8 * G * √κ * (1 / m + 2 * k * √c / (m ^ 2 * tl ^ 2)) / (3 * c ^ 2 * k * δ * m ^ 2) := by
  have hk0 : 0 < k := by linarith
  have hm0 : 0 < m := by linarith
  have hc0 : 0 < c := by linarith
  set a := k * (1 + 1 / c) with ha
  have hka : k ≤ a := by rw [ha]; nlinarith [show 0 < 1 / c by positivity]
  have hktl' : k ≤ tl := hka.trans hktl
  have htl0 : 0 < tl := by linarith
  -- −D(t_l) ≥ (m² − 1/k²) c² t_l² k δ
  have hE := Cvs.L2a.StationaryPairMismatchSign.Est_left (c := c) (χ := χ) (k := k) (m := m) (t := tl) hc0 hk0 hm0.ne'
    hδ hδχ hktl' htl
  have hmk : 3 / 4 * m ^ 2 ≤ m ^ 2 - 1 / k ^ 2 := by
    have : 1 / k ^ 2 ≤ m ^ 2 / 4 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    nlinarith
  have hmk0 : 0 < m ^ 2 - 1 / k ^ 2 := by nlinarith
  have hD : (m ^ 2 - 1 / k ^ 2) * (c ^ 2 * tl ^ 2 * k * δ) ≤ -Dmr c χ m (1 / k) tl := by
    rw [Cvs.L2a.StationaryPairMismatchSign.Dmr_eq_Est hk0.ne' hm0.ne']
    nlinarith [mul_le_mul_of_nonneg_left hE hmk0.le]
  have hDpos : 0 < (m ^ 2 - 1 / k ^ 2) * (c ^ 2 * tl ^ 2 * k * δ) := by positivity
  have hDneg : Dmr c χ m (1 / k) tl < 0 := by linarith
  -- numerators
  have hpm : pm m tl ≤ tl ^ 2 := pm_le hm0.ne'
  have hmt : 1 ≤ m * tl := by nlinarith
  have hpm0 : 0 ≤ pm m tl := by
    unfold pm; apply div_nonneg _ (by positivity); nlinarith [hmt]
  have hpr : pm (1 / k) tl ≤ 1 / m ^ 2 := by
    rw [pm_inv hk0.ne']
    have hS : 0 ≤ √(k ^ 2 + 1 / m ^ 2) := sqrt_nonneg _
    have hsq : √(k ^ 2 + 1 / m ^ 2) ^ 2 = k ^ 2 + 1 / m ^ 2 := sq_sqrt (by positivity)
    have hle : tl ≤ √(k ^ 2 + 1 / m ^ 2) := by linarith [htl, hδ]
    have : tl ^ 2 ≤ √(k ^ 2 + 1 / m ^ 2) ^ 2 := pow_le_pow_left₀ htl0.le hle 2
    linarith
  have hpr0 : 0 ≤ pm (1 / k) tl := by rw [pm_inv hk0.ne']; nlinarith
  -- R(a) ≤ 4 m² k² c
  have hR : ew (m * a) / ew (a / k) ≤ 4 * m ^ 2 * k ^ 2 * c := by
    have hak : a / k = 1 + 1 / c := by rw [ha]; field_simp
    rw [hak]
    have hc1 : (1 : ℝ) ≤ 1 + 1 / c := by
      have : 0 ≤ 1 / c := by positivity
      linarith
    have h1 : 1 / c ≤ ew (1 + 1 / c) := by
      have := ew_ge_sub hc1
      linarith
    have hew1 : ew (m * a) ≤ (m * a) ^ 2 := by
      unfold ew
      have hma : 1 ≤ m * a := by nlinarith
      have : √((m * a) ^ 2 - 1) ≤ m * a := Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
      calc m * a * √((m * a) ^ 2 - 1) ≤ m * a * (m * a) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = (m * a) ^ 2 := by ring
    have hc1' : 1 / c ≤ 1 := by rw [div_le_one hc0]; exact hc
    have ha2 : a ≤ 2 * k := by
      rw [ha]
      calc k * (1 + 1 / c) ≤ k * (1 + 1) := mul_le_mul_of_nonneg_left (by linarith) hk0.le
        _ = 2 * k := by ring
    rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) h1)]
    calc ew (m * a) ≤ (m * a) ^ 2 := hew1
      _ ≤ (m * (2 * k)) ^ 2 := pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left ha2 hm0.le) 2
      _ = 4 * m ^ 2 * k ^ 2 * c * (1 / c) := by field_simp; ring
      _ ≤ 4 * m ^ 2 * k ^ 2 * c * ew (1 + 1 / c) := mul_le_mul_of_nonneg_left h1 (by positivity)
  have hsR : √(κ * (ew (m * a) / ew (a / k))) ≤ √κ * (2 * m * k * √c) := by
    rw [sqrt_mul hκ]
    apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
    calc √(ew (m * a) / ew (a / k)) ≤ √(4 * m ^ 2 * k ^ 2 * c) := sqrt_le_sqrt hR
      _ = 2 * m * k * √c := by
          rw [show 4 * m ^ 2 * k ^ 2 * c = (2 * m * k) ^ 2 * c by ring, sqrt_mul (by positivity),
            sqrt_sq (by positivity)]
  -- assemble
  have e : 2 * (-(pm m tl / Dmr c χ m (1 / k) tl) * (G * √κ / m)
          + -(pm (1 / k) tl / Dmr c χ m (1 / k) tl) * (G / m * √(κ * (ew (m * a) / ew (a / k)))))
      = 2 * (pm m tl * (G * √κ / m) + pm (1 / k) tl * (G / m * √(κ * (ew (m * a) / ew (a / k)))))
        / (-Dmr c χ m (1 / k) tl) := by
    have hDne := hDneg.ne
    field_simp
    ring
  rw [e]
  have hnum : 2 * (pm m tl * (G * √κ / m) + pm (1 / k) tl * (G / m * √(κ * (ew (m * a) / ew (a / k)))))
      ≤ 2 * (tl ^ 2 * (G * √κ / m) + 1 / m ^ 2 * (G / m * (√κ * (2 * m * k * √c)))) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply add_le_add (mul_le_mul_of_nonneg_right hpm (by positivity))
    exact mul_le_mul hpr (mul_le_mul_of_nonneg_left hsR (by positivity)) (by positivity) (by positivity)
  calc _ ≤ 2 * (tl ^ 2 * (G * √κ / m) + 1 / m ^ 2 * (G / m * (√κ * (2 * m * k * √c))))
        / ((m ^ 2 - 1 / k ^ 2) * (c ^ 2 * tl ^ 2 * k * δ)) := div_le_div₀ (by positivity) hnum hDpos hD
    _ ≤ 2 * (tl ^ 2 * (G * √κ / m) + 1 / m ^ 2 * (G / m * (√κ * (2 * m * k * √c))))
        / (3 / 4 * m ^ 2 * (c ^ 2 * tl ^ 2 * k * δ)) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right hmk (by positivity)
    _ = 8 * G * √κ * (1 / m + 2 * k * √c / (m ^ 2 * tl ^ 2)) / (3 * c ^ 2 * k * δ * m ^ 2) := by
        field_simp; ring

/-- **The window, bounded.** With `t_l − k ≥ 1/(6km²)`, `m k ≥ 2`, `σ > 0`:
`2δ √(G/(σ ew(m t_l))) √(G/(σ ew(t_l/k))) ≤ 2δ G √(4√3)/σ`. -/
theorem window_le' {σ G k m tl δ : ℝ} (hσ : 0 < σ) (hG : 0 ≤ G) (hk : 0 < k) (hm : 0 < m) (hδ : 0 ≤ δ)
    (hmk : 2 ≤ m * k) (hgap : 1 / (6 * k * m ^ 2) ≤ tl - k) :
    2 * δ * (√(G / (σ * ew (m * tl))) * √(G / (σ * ew (tl / k)))) ≤ 2 * δ * (G * √(4 * √3) / σ) := by
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h6 : 0 < 1 / (6 * k * m ^ 2) := by positivity
  have htl : k < tl := by linarith
  have hmtl : 2 ≤ m * tl := le_trans hmk (by nlinarith)
  have h1 := ew_ge_sq hmtl
  have h2 : 1 / (6 * k ^ 2 * m ^ 2) ≤ ew (tl / k) := by
    have h := ew_ge_sub (show (1 : ℝ) ≤ tl / k by rw [le_div_iff₀ hk]; linarith)
    have e : tl / k - 1 = (tl - k) / k := by field_simp
    rw [e] at h
    calc 1 / (6 * k ^ 2 * m ^ 2) = (1 / (6 * k * m ^ 2)) / k := by field_simp
      _ ≤ (tl - k) / k := div_le_div_of_nonneg_right hgap hk.le
      _ ≤ ew (tl / k) := h
  have hmk2 : m ^ 2 * k ^ 2 ≤ m ^ 2 * tl ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hk.le htl.le 2) (sq_nonneg m)
  have h1' : √3 / 2 * (m ^ 2 * k ^ 2) ≤ ew (m * tl) := by
    refine le_trans ?_ h1
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hmk2 (by positivity)
  have hs3 : 0 < √3 := by positivity
  calc √(G / (σ * ew (m * tl))) * √(G / (σ * ew (tl / k)))
      ≤ √(G / (σ * (√3 / 2 * (m ^ 2 * k ^ 2)))) * √(G / (σ * (1 / (6 * k ^ 2 * m ^ 2)))) := by
        apply mul_le_mul (sqrt_le_sqrt (div_le_div_of_nonneg_left hG (by positivity)
          (mul_le_mul_of_nonneg_left h1' hσ.le)))
          (sqrt_le_sqrt (div_le_div_of_nonneg_left hG (by positivity) (mul_le_mul_of_nonneg_left h2 hσ.le)))
          (sqrt_nonneg _) (sqrt_nonneg _)
    _ = √(G / (σ * (√3 / 2 * (m ^ 2 * k ^ 2))) * (G / (σ * (1 / (6 * k ^ 2 * m ^ 2))))) :=
        (sqrt_mul (by positivity) _).symm
    _ = √((G / σ) ^ 2 * (4 * √3)) := by
        congr 1
        have h33 : √3 * √3 = 3 := mul_self_sqrt (by norm_num)
        field_simp; nlinarith [h33]
    _ = G * √(4 * √3) / σ := by
        rw [sqrt_mul (by positivity), sqrt_sq (by positivity)]; ring

end Cvs.L2a.NearEdgePairLeftPiece
