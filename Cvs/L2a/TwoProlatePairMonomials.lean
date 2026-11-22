import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.Bounds
import Cvs.L2a.StationaryPairAtDelta
import Cvs.L2a.StationaryPairElementarySizes
import Cvs.L2a.TwoProlateStripPair
import Cvs.L2a.TwoProlateWindowPieceMonomials
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Each stationary pair of two prolates at `δ = 1/(s m)`, as monomials in `k` and `m`

For the mode `m` of `ψ_a` and `1/k` of `ψ_b`, with `σ = √(c² − χ_m)`, `χ_m ≥ χ_a, χ_b`, `κ₀ = c/σ`, `A = √(2K/(√3σ))`,
`Q = √(4√3)/σ`, and `|χ_b − χ_a| ≤ (3/4)c²/s`: an edge pair (`s < 6km`) is at most
`G(4A/(s km²) + √κ₀(32s/(3c²km²) + 32√s/(c²√k m√m)))`; a strip pair (`6km ≤ s`, `s² ≤ c`, `χ_a ≤ c√c`) is at most
`G(A/(cm) + 2Q/(s m) + √κ₀(32s√c/(3c²k²m³) + 32s/(c²km²) + 16√s/(c²√k m√m)))`.
-/

namespace Cvs.L2a.TwoProlatePairMonomials

open Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.NonresonantCrossIntegral

/-- **An edge pair of two prolates** (`s < 6km`), at `δ = 1/(s m)`. -/
theorem edge2_mono {c χa χb χm G K Ξ k m b s : ℝ} {ψa ua ψb ub : ℝ → ℝ}
    (hc : 1 ≤ c) (hχa0 : 0 ≤ χa) (hχam : χa ≤ χm) (hχb0 : 0 ≤ χb) (hχbm : χb ≤ χm) (hχm : χm < c ^ 2)
    (hΔ : |χb - χa| ≤ 3 / 4 * c ^ 2 / s) (hk1 : 1 ≤ k) (hkm2 : 2 ≤ k * m) (hm : 1 ≤ m) (hs1 : 1 ≤ s) (hreg : s < 6 * (k * m))
    (hrb : k + 2 ≤ b) (hhi : m * b ≤ Ξ)
    (hψa : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψa (ua ξ / pP ξ) ξ)
    (hua : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ua (-(qP c χa ξ * ψa ξ)) ξ)
    (hψb : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψb (ub ξ / pP ξ) ξ)
    (hub : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ub (-(qP c χb ξ * ψb ξ)) ξ)
    (hGa : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χa) ψa ua ξ ≤ G) (hGb : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χb) ψb ub ξ ≤ G)
    (hG0 : 0 ≤ G) (hK : 0 ≤ K)
    (hcontb : ContinuousOn ψb (Icc 1 Ξ)) (hedgeb : ∀ ξ ∈ Icc 1 Ξ, |ψb ξ| ≤ |ψb 1|) (hedge1 : ψb 1 ^ 2 ≤ K * G) :
    |∫ t in k..b, ψa (m * t) * ψb (1 / k * t)|
      ≤ G * (4 * √(2 * K / (√3 * √(c ^ 2 - χm))) / (s * k * m ^ 2)
        + √(c / √(c ^ 2 - χm)) * (32 * s / (3 * c ^ 2 * k * m ^ 2)
          + 32 * √s / (c ^ 2 * √k * (m * √m)))) := by
  have hc0 : 0 < c := by linarith
  have hk0 : 0 < k := by linarith
  have hm0 : 0 < m := by linarith
  have hs0 : 0 < s := by linarith
  set tr := √(k ^ 2 + 1 / m ^ 2) + 1 / (s * m) with htr
  have hkS : k ≤ √(k ^ 2 + 1 / m ^ 2) :=
    Real.le_sqrt_of_sq_le (by have : 0 ≤ 1 / m ^ 2 := by positivity
                              linarith)
  have him : 0 < 1 / (s * m) := by positivity
  have hktr : k < tr := by rw [htr]; linarith
  -- the window: t_r − k ≤ 1/(2km²) + 1/(sm) ≤ 4/(sm), since s < 6km
  have hS := Cvs.L2a.StationaryPairElementarySizes.sqrtS_sub_le hk0 hm0
  have h1 : 1 / (2 * k * m ^ 2) ≤ 3 / (s * m) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hlen : tr - k ≤ 4 / (s * m) := by
    have : 4 / (s * m) = 3 / (s * m) + 1 / (s * m) := by ring
    rw [htr]; linarith
  have hsm1 : 1 ≤ s * m := by nlinarith
  have hlen2 : tr - k ≤ 2 := by
    have a1 : 1 / (2 * k * m ^ 2) ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
    have a2 : 1 / (s * m) ≤ 1 := by rw [div_le_one (by positivity)]; exact hsm1
    rw [htr]; linarith
  have hb0 : 0 ≤ b := by linarith
  have hξ₀ : 1 < tr / k := by rw [one_lt_div hk0]; exact hktr
  have hmk : 2 ≤ m * k := by linarith [mul_comm m k]
  have hξ₁ : 1 < min (tr / k) 2 := lt_min hξ₀ (by norm_num)
  have htrk : min (tr / k) 2 ≤ m * k := (min_le_right _ _).trans hmk
  have hsub : Icc (min (tr / k) 2) Ξ ⊆ Ioc 1 Ξ := fun ξ hξ => ⟨lt_of_lt_of_le hξ₁ hξ.1, hξ.2⟩
  have hbk : b / k ≤ Ξ := by
    have : b / k ≤ b := div_le_self hb0 (by linarith)
    nlinarith
  have hδk : 1 / (s * m) ≤ k / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hΔ' : |χb - χa| ≤ 3 / 4 * m ^ 2 * c ^ 2 * k * (1 / (s * m)) := by
    have e : 3 / 4 * m ^ 2 * c ^ 2 * k * (1 / (s * m)) = 3 / 4 * (k * m) * c ^ 2 / s := by field_simp
    rw [e]; refine hΔ.trans (div_le_div_of_nonneg_right ?_ hs0.le)
    nlinarith [sq_nonneg c]
  have key := Cvs.L2a.TwoProlateWindowPieceMonomials.pairB2_le (δ := 1 / (s * m)) (tr := tr) (b := b) (ξ₁ := min (tr / k) 2)
    hc0 hχa0 hχam hχb0 hχbm hχm hk1 hkm2 hm him hδk hΔ' htr (by linarith) hξ₁ (min_le_left _ _) htrk
    hhi hbk (fun ξ hξ => hψa ξ (hsub hξ)) (fun ξ hξ => hua ξ (hsub hξ))
    (fun ξ hξ => hψb ξ (hsub hξ)) (fun ξ hξ => hub ξ (hsub hξ)) (fun ξ hξ => hGa ξ (hsub hξ))
    (fun ξ hξ => hGb ξ (hsub hξ)) hG0 hK hcontb hedgeb hedge1
  -- √(t_r − k) ≤ 2/(√s √m)
  have hsq : √(tr - k) ≤ 2 / (√s * √m) := by
    have : 2 / (√s * √m) = √(4 / (s * m)) := by
      rw [sqrt_div' 4 (by positivity : 0 ≤ s * m), sqrt_mul hs0.le]
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]
    rw [this]; exact Real.sqrt_le_sqrt hlen
  have hr := Cvs.L2a.StationaryPairAtDelta.right_le (G := 2 * G) (κ := c / √(c ^ 2 - χm)) hc0 (by positivity) hk0 hm0 hs0 hsq
  have ek : G * √(c / √(c ^ 2 - χm)) * (32 * k ^ 2 / (3 * m) + 16 * k ^ 2 * √k * √(tr - k))
        / (c ^ 2 * m ^ 2 * k ^ 3 * (1 / (s * m)))
      = 2 * G * √(c / √(c ^ 2 - χm)) * (16 * k ^ 2 / (3 * m) + 8 * k ^ 2 * √k * √(tr - k))
        / (c ^ 2 * m ^ 2 * k ^ 3 * (1 / (s * m))) := by ring
  have hA : 0 ≤ √(2 * K / (√3 * √(c ^ 2 - χm))) * G / (m * k) := by positivity
  have hw : (tr - k) * (√(2 * K / (√3 * √(c ^ 2 - χm))) * G / (m * k))
      ≤ 4 / (s * m) * (√(2 * K / (√3 * √(c ^ 2 - χm))) * G / (m * k)) :=
    mul_le_mul_of_nonneg_right hlen hA
  have hsm : 0 < √m := sqrt_pos.mpr hm0
  have hsk : 0 < √k := sqrt_pos.mpr hk0
  have hss : 0 < √s := sqrt_pos.mpr hs0
  have e1 : 4 / (s * m) * (√(2 * K / (√3 * √(c ^ 2 - χm))) * G / (m * k))
      = G * (4 * √(2 * K / (√3 * √(c ^ 2 - χm))) / (s * k * m ^ 2)) := by field_simp
  have e2 : 2 * G * √(c / √(c ^ 2 - χm)) * (16 * s / (3 * c ^ 2 * k * m ^ 2) + 8 * s * (2 / (√s * √m)) / (c ^ 2 * √k * m))
      = G * √(c / √(c ^ 2 - χm)) * (32 * s / (3 * c ^ 2 * k * m ^ 2) + 32 * √s / (c ^ 2 * √k * (m * √m))) := by
    obtain ⟨p, hp, hkp⟩ : ∃ p, 0 < p ∧ k = p ^ 2 := ⟨√k, hsk, (sq_sqrt hk0.le).symm⟩
    obtain ⟨q, hq, hmq⟩ : ∃ q, 0 < q ∧ m = q ^ 2 := ⟨√m, hsm, (sq_sqrt hm0.le).symm⟩
    obtain ⟨r, hr, hsr⟩ : ∃ r, 0 < r ∧ s = r ^ 2 := ⟨√s, hss, (sq_sqrt hs0.le).symm⟩
    rw [show √k = p by rw [hkp, sqrt_sq hp.le], show √m = q by rw [hmq, sqrt_sq hq.le],
      show √s = r by rw [hsr, sqrt_sq hr.le], hkp, hmq, hsr]
    field_simp; ring
  have e3 : G * (4 * √(2 * K / (√3 * √(c ^ 2 - χm))) / (s * k * m ^ 2)
        + √(c / √(c ^ 2 - χm)) * (32 * s / (3 * c ^ 2 * k * m ^ 2) + 32 * √s / (c ^ 2 * √k * (m * √m))))
      = G * (4 * √(2 * K / (√3 * √(c ^ 2 - χm))) / (s * k * m ^ 2))
        + G * √(c / √(c ^ 2 - χm)) * (32 * s / (3 * c ^ 2 * k * m ^ 2) + 32 * √s / (c ^ 2 * √k * (m * √m))) := by
    ring
  rw [e3]; rw [ek] at key; linarith

set_option maxHeartbeats 1000000 in
/-- **A strip pair of two prolates** (`6km ≤ s`, `s² ≤ c`), at `δ = 1/(s m)`, given `χ_a ≤ c√c`. -/
theorem strip2_mono {c χa χb χm G K Ξ k m b s : ℝ} {ψa ua ψb ub : ℝ → ℝ}
    (hc : 1 ≤ c) (hχa0 : 0 ≤ χa) (hχam : χa ≤ χm) (hχb0 : 0 ≤ χb) (hχbm : χb ≤ χm) (hχm : χm < c ^ 2)
    (hχs : χa ≤ c * √c) (hΔ : |χb - χa| ≤ 3 / 4 * c ^ 2 / s) (hk1 : 1 ≤ k) (hkm2 : 2 ≤ k * m) (hm : 1 ≤ m)
    (hs1 : 1 ≤ s) (hsc : s ^ 2 ≤ c) (hreg : 6 * (k * m) ≤ s) (hrb : k + 2 ≤ b) (hhi : m * b ≤ Ξ)
    (hψa : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψa (ua ξ / pP ξ) ξ)
    (hua : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ua (-(qP c χa ξ * ψa ξ)) ξ)
    (hψb : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψb (ub ξ / pP ξ) ξ)
    (hub : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ub (-(qP c χb ξ * ψb ξ)) ξ)
    (hGa : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χa) ψa ua ξ ≤ G) (hGb : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χb) ψb ub ξ ≤ G)
    (hG0 : 0 ≤ G) (hK : 0 ≤ K)
    (hcontb : ContinuousOn ψb (Icc 1 Ξ)) (hedgeb : ∀ ξ ∈ Icc 1 Ξ, |ψb ξ| ≤ |ψb 1|) (hedge1 : ψb 1 ^ 2 ≤ K * G) :
    |∫ t in k..b, ψa (m * t) * ψb (1 / k * t)|
      ≤ G * (√(2 * K / (√3 * √(c ^ 2 - χm))) / (c * m) + 2 * (√(4 * √3) / √(c ^ 2 - χm)) / (s * m)
        + √(c / √(c ^ 2 - χm)) * (32 * s * √c / (3 * c ^ 2 * k ^ 2 * m ^ 3) + 32 * s / (c ^ 2 * k * m ^ 2)
          + 16 * √s / (c ^ 2 * √k * (m * √m)))) := by
  have hc0 : 0 < c := by linarith
  have hk0 : 0 < k := by linarith
  have hm0 : 0 < m := by linarith
  have hs0 : 0 < s := by linarith
  have hss : s * s ≤ c := by nlinarith
  have hsqc : s ≤ √c := Real.le_sqrt_of_sq_le hsc
  have hkm : 2 ≤ k * m := by nlinarith
  have hup := Cvs.L2a.StationaryPairElementarySizes.sqrtS_sub_le hk0 hm0
  have hlow := Cvs.L2a.StationaryPairElementarySizes.le_sqrtS_sub (by linarith : (1 : ℝ) ≤ k) hm
  set S := √(k ^ 2 + 1 / m ^ 2) with hSdef
  set tl := S - 1 / (s * m) with htl
  set tr := S + 1 / (s * m) with htr
  have hkS : k ≤ S := by linarith [(by positivity : (0 : ℝ) < 1 / (3 * k * m ^ 2))]
  have him : 0 < 1 / (s * m) := by positivity
  -- the regime's two sizes
  have r1 : k / c ≤ 1 / (36 * k * m ^ 2) := by
    rw [div_le_div_iff₀ hc0 (by positivity)]
    have h6 : 36 * (k * m) ^ 2 ≤ s ^ 2 := by nlinarith
    nlinarith
  have r2 : 1 / (s * m) ≤ 1 / (6 * k * m ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have e36 : 1 / (3 * k * m ^ 2) = 1 / (36 * k * m ^ 2) + 1 / (6 * k * m ^ 2) + 5 / (36 * k * m ^ 2) := by
    field_simp; ring
  have e6 : 1 / (3 * k * m ^ 2) = 1 / (6 * k * m ^ 2) + 1 / (6 * k * m ^ 2) := by field_simp; ring
  have h5 : 0 ≤ 5 / (36 * k * m ^ 2) := by positivity
  have hatl : k * (1 + 1 / c) ≤ tl := by
    have : k * (1 + 1 / c) = k + k / c := by ring
    rw [this, htl]; linarith
  have hgap : 1 / (6 * k * m ^ 2) ≤ tl - k := by rw [htl]; linarith
  have hδχ : χa / (c ^ 2 * m ^ 2 * k) ≤ 1 / (s * m) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hsc0 : 0 ≤ √c := sqrt_nonneg c
    have h1 : χa * (s * m) ≤ c * √c * (√c * m) :=
      mul_le_mul hχs (mul_le_mul_of_nonneg_right hsqc hm0.le) (by positivity) (by positivity)
    have h2 : c * √c * (√c * m) = c ^ 2 * m := by
      rw [show c * √c * (√c * m) = c * (√c * √c) * m by ring, mul_self_sqrt hc0.le]; ring
    have hmk1 : (1 : ℝ) ≤ m * k := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hmk1 (by positivity : (0 : ℝ) ≤ c ^ 2 * m)
    nlinarith
  have hδk : 1 / (s * m) ≤ k / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hlen2 : tr - k ≤ 2 := by
    have a1 : 1 / (2 * k * m ^ 2) ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
    have a2 : 1 / (s * m) ≤ 1 := by rw [div_le_one (by positivity)]; exact one_le_mul_of_one_le_of_one_le hs1 hm
    rw [htr]; linarith
  have hb0 : 0 ≤ b := by linarith
  have hbk : b / k ≤ Ξ :=
    (div_le_self hb0 (by linarith)).trans ((le_mul_of_one_le_left hb0 hm).trans hhi)
  have hic0 : 0 < 1 / c := by positivity
  have hξ₁ : (1 : ℝ) < 1 + 1 / c := by linarith
  have hic : 1 / c ≤ 1 := by rw [div_le_one hc0]; exact hc
  have hsub : Icc (1 + 1 / c) Ξ ⊆ Ioc 1 Ξ := fun ξ hξ => ⟨lt_of_lt_of_le hξ₁ hξ.1, hξ.2⟩
  have hΔ' : |χb - χa| ≤ 3 / 8 * m ^ 2 * c ^ 2 * k * (1 / (s * m)) := by
    have e : 3 / 8 * m ^ 2 * c ^ 2 * k * (1 / (s * m)) = 3 / 8 * (k * m) * c ^ 2 / s := by field_simp
    rw [e]; refine hΔ.trans (div_le_div_of_nonneg_right ?_ hs0.le)
    nlinarith [sq_nonneg c]
  have key := Cvs.L2a.TwoProlateStripPair.pairA2_le (δ := 1 / (s * m)) (tl := tl) (tr := tr) (b := b)
    (ξ₁ := 1 + 1 / c) (K := K) hc hχa0 hχam hχb0 hχbm hχm hk1 hkm2 hm him hδk hδχ hΔ' htl htr (by linarith) hatl
    hgap hξ₁ le_rfl (by rw [mul_comm]; linarith) hhi hbk (fun ξ hξ => hψa ξ (hsub hξ)) (fun ξ hξ => hua ξ (hsub hξ))
    (fun ξ hξ => hψb ξ (hsub hξ)) (fun ξ hξ => hub ξ (hsub hξ)) (fun ξ hξ => hGa ξ (hsub hξ))
    (fun ξ hξ => hGb ξ (hsub hξ)) hG0 hK hcontb hedgeb hedge1
  set A := √(2 * K / (√3 * √(c ^ 2 - χm))) with hA
  set Q := √(4 * √3) / √(c ^ 2 - χm) with hQ
  set κ := √(c / √(c ^ 2 - χm)) with hκ
  have hA0 : 0 ≤ A := sqrt_nonneg _
  have hQ0 : 0 ≤ Q := by positivity
  have hκ0 : 0 ≤ κ := sqrt_nonneg _
  have hsk : 0 < √k := sqrt_pos.mpr hk0
  have hsm : 0 < √m := sqrt_pos.mpr hm0
  have hsss : 0 < √s := sqrt_pos.mpr hs0
  have hkk : √k * √k = k := mul_self_sqrt hk0.le
  have hmm : √m * √m = m := mul_self_sqrt hm0.le
  have hs2 : √s * √s = s := mul_self_sqrt hs0.le
  -- the strip piece
  have x1 : k / c * (A * G / (m * k)) = G * (A / (c * m)) := by field_simp
  -- the left piece, with `t_l ≥ k`
  have htlk : k ≤ tl := by linarith
  have x2 : 16 * G * κ * (1 / m + 2 * k * √c / (m ^ 2 * tl ^ 2)) / (3 * c ^ 2 * k * (1 / (s * m)) * m ^ 2)
      ≤ G * κ * (32 * s * √c / (3 * c ^ 2 * k ^ 2 * m ^ 3) + 16 * s / (3 * c ^ 2 * k * m ^ 2)) := by
    have ht : 2 * k * √c / (m ^ 2 * tl ^ 2) ≤ 2 * √c / (m ^ 2 * k) := by
      rw [div_le_div_iff₀ (mul_pos (by positivity) (pow_pos (hk0.trans_le htlk) 2)) (by positivity)]
      have : k ^ 2 ≤ tl ^ 2 := pow_le_pow_left₀ hk0.le htlk 2
      have hp : 0 ≤ 2 * √c * m ^ 2 := by positivity
      linear_combination (2 * √c * m ^ 2) * this
    calc 16 * G * κ * (1 / m + 2 * k * √c / (m ^ 2 * tl ^ 2)) / (3 * c ^ 2 * k * (1 / (s * m)) * m ^ 2)
        ≤ 16 * G * κ * (1 / m + 2 * √c / (m ^ 2 * k)) / (3 * c ^ 2 * k * (1 / (s * m)) * m ^ 2) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
      _ = G * κ * (32 * s * √c / (3 * c ^ 2 * k ^ 2 * m ^ 3) + 16 * s / (3 * c ^ 2 * k * m ^ 2)) := by
          field_simp; ring
  -- the window
  have x3 : 2 * (1 / (s * m)) * (G * √(4 * √3) / √(c ^ 2 - χm)) = G * (2 * Q / (s * m)) := by
    rw [hQ]; field_simp
  -- the right piece: √(t_r − k) ≤ 1/(m√k) + 1/(√s√m)
  have he : √(tr - k) ≤ 1 / (m * √k) + 1 / (√s * √m) := by
    have hsq : tr - k ≤ (1 / (m * √k) + 1 / (√s * √m)) ^ 2 := by
      have e : (1 / (m * √k) + 1 / (√s * √m)) ^ 2
          = 1 / (m ^ 2 * k) + 2 / (m * √k * (√s * √m)) + 1 / (s * m) := by
        obtain ⟨p, hp, hkp⟩ : ∃ p, 0 < p ∧ k = p ^ 2 := ⟨√k, hsk, (sq_sqrt hk0.le).symm⟩
        obtain ⟨q, hq, hmq⟩ : ∃ q, 0 < q ∧ m = q ^ 2 := ⟨√m, hsm, (sq_sqrt hm0.le).symm⟩
        obtain ⟨r, hr, hsr⟩ : ∃ r, 0 < r ∧ s = r ^ 2 := ⟨√s, hsss, (sq_sqrt hs0.le).symm⟩
        rw [show √k = p by rw [hkp, sqrt_sq hp.le], show √m = q by rw [hmq, sqrt_sq hq.le],
          show √s = r by rw [hsr, sqrt_sq hr.le], hkp, hmq, hsr]
        field_simp; ring
      have : 1 / (2 * k * m ^ 2) ≤ 1 / (m ^ 2 * k) := by
        apply one_div_le_one_div_of_le (by positivity)
        have : 0 < m ^ 2 * k := by positivity
        linarith [show 2 * k * m ^ 2 = 2 * (m ^ 2 * k) by ring]
      have : 0 ≤ 2 / (m * √k * (√s * √m)) := by positivity
      rw [e, htr]; linarith
    calc √(tr - k) ≤ √((1 / (m * √k) + 1 / (√s * √m)) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = _ := sqrt_sq (by positivity)
  have x4 := Cvs.L2a.StationaryPairAtDelta.right_le (G := 2 * G) (κ := c / √(c ^ 2 - χm)) hc0 (by positivity) hk0 hm0 hs0 he
  have x4e : 2 * G * κ * (16 * s / (3 * c ^ 2 * k * m ^ 2) + 8 * s * (1 / (m * √k) + 1 / (√s * √m)) / (c ^ 2 * √k * m))
      = G * κ * (32 * s / (3 * c ^ 2 * k * m ^ 2) + 16 * s / (c ^ 2 * k * m ^ 2)
          + 16 * √s / (c ^ 2 * √k * (m * √m))) := by
    obtain ⟨p, hp, hkp⟩ : ∃ p, 0 < p ∧ k = p ^ 2 := ⟨√k, hsk, (sq_sqrt hk0.le).symm⟩
    obtain ⟨q, hq, hmq⟩ : ∃ q, 0 < q ∧ m = q ^ 2 := ⟨√m, hsm, (sq_sqrt hm0.le).symm⟩
    obtain ⟨r, hr, hsr⟩ : ∃ r, 0 < r ∧ s = r ^ 2 := ⟨√s, hsss, (sq_sqrt hs0.le).symm⟩
    rw [show √k = p by rw [hkp, sqrt_sq hp.le], show √m = q by rw [hmq, sqrt_sq hq.le],
      show √s = r by rw [hsr, sqrt_sq hr.le], hkp, hmq, hsr]
    field_simp; ring
  have fin : G * (A / (c * m) + 2 * Q / (s * m)
        + κ * (32 * s * √c / (3 * c ^ 2 * k ^ 2 * m ^ 3) + 32 * s / (c ^ 2 * k * m ^ 2) + 16 * √s / (c ^ 2 * √k * (m * √m))))
      = G * (A / (c * m)) + G * (2 * Q / (s * m))
        + G * κ * (32 * s * √c / (3 * c ^ 2 * k ^ 2 * m ^ 3) + 16 * s / (3 * c ^ 2 * k * m ^ 2))
        + G * κ * (32 * s / (3 * c ^ 2 * k * m ^ 2) + 16 * s / (c ^ 2 * k * m ^ 2)
          + 16 * √s / (c ^ 2 * √k * (m * √m))) := by ring
  rw [fin]
  rw [x1, x3] at key
  have x4' : G * κ * (32 * k ^ 2 / (3 * m) + 16 * k ^ 2 * √k * √(tr - k)) / (c ^ 2 * m ^ 2 * k ^ 3 * (1 / (s * m)))
      ≤ G * κ * (32 * s / (3 * c ^ 2 * k * m ^ 2) + 16 * s / (c ^ 2 * k * m ^ 2)
          + 16 * √s / (c ^ 2 * √k * (m * √m))) := by
    rw [← x4e]
    calc _ = 2 * G * κ * (16 * k ^ 2 / (3 * m) + 8 * k ^ 2 * √k * √(tr - k))
          / (c ^ 2 * m ^ 2 * k ^ 3 * (1 / (s * m))) := by ring
      _ ≤ _ := x4
  linarith

end Cvs.L2a.TwoProlatePairMonomials
