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
import Cvs.L2a.StationaryMismatchExactRoots
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
# The right and left pieces of a stationary pair at the exact root, for every `χ ≤ c²`

With the window centred at `√T₊` (Cvs.L2a.StationaryMismatchExactRoots), `|D| ≥ (m² − 1/k²)(3/2)c²k³δ` on either side, with no condition on `χ`:
the right piece is at most `G√κ(64k²/(9m) + 32k^{5/2}√(t_r − k)/3)/(c²m²k³δ)` and the left piece at most
`16G√κ(t_l²/m + 2k√c/m²)/(9c²k³δm²)`; the window with a gap `g ≤ t_l − k` is at most
`2δ(G/σ)√(2/(√3m²kg))`.
-/

namespace Cvs.L2a.ExactRootPairPieces

open Real Set Cvs.L2a.NonresonantCrossIntegral Cvs.Prolate.Envelope.ProlateWeightToEdge Cvs.L2a.StationaryPairElementarySizes Cvs.L2a.StationaryMismatchExactRoots

set_option maxHeartbeats 2000000 in
/-- **The right piece at the exact root**, `t_r = √T₊ + δ`, any `0 ≤ χ ≤ c²`. -/
theorem right_le {c χ k m δ G κ tr : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ ≤ c ^ 2) (hk1 : 1 ≤ k)
    (hkm2 : 2 ≤ k * m) (hm : 1 ≤ m)
    (hδ : 0 < δ) (hδk : δ ≤ k / 2) (hG : 0 ≤ G) (hκ : 0 ≤ κ) (htrdef : tr = √(Tp c χ k m) + δ) :
    2 * (pm m tr * (G * √κ / m) + pm (1 / k) tr * (G / m * √(κ * (ew (m * tr) / ew (tr / k)))))
        / Dmr c χ m (1 / k) tr
      ≤ G * √κ * (64 * k ^ 2 / (9 * m) + 32 * k ^ 2 * √k * √(tr - k) / 3) / (c ^ 2 * m ^ 2 * k ^ 3 * δ) := by
  have hk : 1 ≤ k := by linarith
  have hk0 : 0 < k := by linarith
  have hm0 : 0 < m := by linarith
  set S := k ^ 2 + 1 / m ^ 2 with hSdef
  have hS0 : 0 ≤ S := by positivity
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
    nlinarith [mul_le_mul hkm1 hkm1 zero_le_one (by linarith), mul_le_mul hk hkm1 zero_le_one (by linarith)]
  have htrk : δ ≤ tr - k := by rw [htrdef]; linarith
  have htr2 : tr ≤ 2 * k := by rw [htrdef]; linarith
  have htr0 : 0 < tr := by linarith
  -- D(t_r) ≥ (m² − 1/k²) 2c²k³δ
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
  have hDpos : 0 < (m ^ 2 - 1 / k ^ 2) * (3 / 2 * c ^ 2 * k ^ 3 * δ) := by
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
        / ((m ^ 2 - 1 / k ^ 2) * (3 / 2 * c ^ 2 * k ^ 3 * δ)) := by
        apply div_le_div₀ (by positivity) hnum hDpos hD
    _ ≤ 2 * (4 * k ^ 2 * (G * √κ / m) + G / m * (√κ * (6 * m * k ^ 2 * √k * √(tr - k))))
        / (3 / 4 * m ^ 2 * (3 / 2 * c ^ 2 * k ^ 3 * δ)) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right hmk (by positivity)
    _ = G * √κ * (64 * k ^ 2 / (9 * m) + 32 * k ^ 2 * √k * √(tr - k) / 3) / (c ^ 2 * m ^ 2 * k ^ 3 * δ) := by
        field_simp; ring

set_option maxHeartbeats 2000000 in
/-- **The left piece at the exact root**, `t_l ≤ √T₊ − δ`, any `0 ≤ χ ≤ c²`. -/
theorem left_le {c χ k m δ G κ tl : ℝ} (hc : 1 ≤ c) (hχ0 : 0 ≤ χ) (hχc : χ ≤ c ^ 2) (hk1 : 1 ≤ k)
    (hkm2 : 2 ≤ k * m) (hm : 1 ≤ m)
    (hδ : 0 < δ) (hG : 0 ≤ G) (hκ : 0 ≤ κ)
    (hktl : k * (1 + 1 / c) ≤ tl) (htl : tl ≤ √(Tp c χ k m) - δ) :
    2 * (-(pm m tl / Dmr c χ m (1 / k) tl) * (G * √κ / m)
          + -(pm (1 / k) tl / Dmr c χ m (1 / k) tl)
            * (G / m * √(κ * (ew (m * (k * (1 + 1 / c))) / ew (k * (1 + 1 / c) / k)))))
      ≤ 16 * G * √κ * (tl ^ 2 / m + 2 * k * √c / m ^ 2) / (9 * c ^ 2 * k ^ 3 * δ * m ^ 2) := by
  have hk0 : 0 < k := by linarith
  have hm0 : 0 < m := by linarith
  have hc0 : 0 < c := by linarith
  set a := k * (1 + 1 / c) with ha
  have hka : k ≤ a := by rw [ha]; nlinarith [show 0 < 1 / c by positivity]
  have hktl' : k ≤ tl := hka.trans hktl
  have htl0 : 0 < tl := by linarith
  have hkm1' : 1 ≤ m * k := by nlinarith
  have hTp := Tp_ge hc0 hk0 hm0 hkm1' hχ0 hχc
  have hTpS := Tp_le (k := k) hc0 hm0 hχ0
  have hE := Est_left (t := tl) hc0 hk0 hm0 hkm1' hχ0 hχc hδ hktl' htl
  have hmk : 3 / 4 * m ^ 2 ≤ m ^ 2 - 1 / k ^ 2 := by
    have : 1 / k ^ 2 ≤ m ^ 2 / 4 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    nlinarith
  have hmk0 : 0 < m ^ 2 - 1 / k ^ 2 := by nlinarith
  have hk2 : 3 / 4 * k ^ 2 ≤ k ^ 2 - 1 / m ^ 2 := by
    have : 1 / m ^ 2 ≤ k ^ 2 / 4 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have hD : (m ^ 2 - 1 / k ^ 2) * (3 / 2 * c ^ 2 * k ^ 3 * δ) ≤ -Dmr c χ m (1 / k) tl := by
    rw [Cvs.L2a.StationaryPairMismatchSign.Dmr_eq_Est hk0.ne' hm0.ne']
    have h1 : 3 / 2 * c ^ 2 * k ^ 3 * δ ≤ 2 * c ^ 2 * k * δ * (k ^ 2 - 1 / m ^ 2) := by
      have := mul_le_mul_of_nonneg_left hk2 (by positivity : (0 : ℝ) ≤ 2 * c ^ 2 * k * δ)
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hE hmk0.le, mul_le_mul_of_nonneg_left h1 hmk0.le]
  have hDpos : 0 < (m ^ 2 - 1 / k ^ 2) * (3 / 2 * c ^ 2 * k ^ 3 * δ) := by positivity
  have hDneg : Dmr c χ m (1 / k) tl < 0 := by linarith
  -- numerators
  have hpm : pm m tl ≤ tl ^ 2 := pm_le hm0.ne'
  have hmt : 1 ≤ m * tl := by nlinarith
  have hpm0 : 0 ≤ pm m tl := by
    unfold pm; apply div_nonneg _ (by positivity); nlinarith [hmt]
  have hpr : pm (1 / k) tl ≤ 1 / m ^ 2 := by
    rw [pm_inv hk0.ne']
    have hT0 : 0 ≤ Tp c χ k m := le_trans (by positivity) hTp
    have hsq : √(Tp c χ k m) ^ 2 = Tp c χ k m := sq_sqrt hT0
    have hle : tl ≤ √(Tp c χ k m) := by linarith [htl, hδ]
    have : tl ^ 2 ≤ √(Tp c χ k m) ^ 2 := pow_le_pow_left₀ htl0.le hle 2
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
        / ((m ^ 2 - 1 / k ^ 2) * (3 / 2 * c ^ 2 * k ^ 3 * δ)) := div_le_div₀ (by positivity) hnum hDpos hD
    _ ≤ 2 * (tl ^ 2 * (G * √κ / m) + 1 / m ^ 2 * (G / m * (√κ * (2 * m * k * √c))))
        / (3 / 4 * m ^ 2 * (3 / 2 * c ^ 2 * k ^ 3 * δ)) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right hmk (by positivity)
    _ = 16 * G * √κ * (tl ^ 2 / m + 2 * k * √c / m ^ 2) / (9 * c ^ 2 * k ^ 3 * δ * m ^ 2) := by
        field_simp; ring
/-- **The window with a general gap** `g ≤ t_l − k`:
`2δ √(G/(σ ew(m t_l))) √(G/(σ ew(t_l/k))) ≤ 2δ (G/σ) √(2/(√3 m² k g))`. -/
theorem window_gap_le {σ G k m tl δ g : ℝ} (hσ : 0 < σ) (hG : 0 ≤ G) (hk : 0 < k) (hm : 0 < m) (hδ : 0 ≤ δ)
    (hmk : 2 ≤ m * k) (hg : 0 < g) (hgap : g ≤ tl - k) :
    2 * δ * (√(G / (σ * ew (m * tl))) * √(G / (σ * ew (tl / k))))
      ≤ 2 * δ * (G / σ * √(2 / (√3 * (m ^ 2 * k * g)))) := by
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have htl : k < tl := by linarith
  have hmtl : 2 ≤ m * tl := le_trans hmk (by nlinarith)
  have h1 := ew_ge_sq hmtl
  have h2 : g / k ≤ ew (tl / k) := by
    have h := ew_ge_sub (show (1 : ℝ) ≤ tl / k by rw [le_div_iff₀ hk]; linarith)
    have e : tl / k - 1 = (tl - k) / k := by field_simp
    rw [e] at h
    exact (div_le_div_of_nonneg_right hgap hk.le).trans h
  have hmk2 : m ^ 2 * k ^ 2 ≤ m ^ 2 * tl ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hk.le htl.le 2) (sq_nonneg m)
  have h1' : √3 / 2 * (m ^ 2 * k ^ 2) ≤ ew (m * tl) := by
    refine le_trans ?_ h1
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hmk2 (by positivity)
  have hs3 : 0 < √3 := by positivity
  calc √(G / (σ * ew (m * tl))) * √(G / (σ * ew (tl / k)))
      ≤ √(G / (σ * (√3 / 2 * (m ^ 2 * k ^ 2)))) * √(G / (σ * (g / k))) := by
        apply mul_le_mul (sqrt_le_sqrt (div_le_div_of_nonneg_left hG (by positivity)
          (mul_le_mul_of_nonneg_left h1' hσ.le)))
          (sqrt_le_sqrt (div_le_div_of_nonneg_left hG (by positivity) (mul_le_mul_of_nonneg_left h2 hσ.le)))
          (sqrt_nonneg _) (sqrt_nonneg _)
    _ = √(G / (σ * (√3 / 2 * (m ^ 2 * k ^ 2))) * (G / (σ * (g / k)))) :=
        (sqrt_mul (by positivity) _).symm
    _ = √((G / σ) ^ 2 * (2 / (√3 * (m ^ 2 * k * g)))) := by
        congr 1; field_simp
    _ = G / σ * √(2 / (√3 * (m ^ 2 * k * g))) := by
        rw [sqrt_mul (by positivity), sqrt_sq (by positivity)]

end Cvs.L2a.ExactRootPairPieces
