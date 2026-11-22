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
import Cvs.L2a.ExactRootEdgeWindowPair
import Cvs.L2a.ExactRootNearEdgePair
import Cvs.L2a.StationaryMismatchExactRoots
import Cvs.L2a.StationaryPairElementarySizes
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
# Each stationary pair at the exact root and `δ = 1/(sm)`, for every `χ < c²`, as monomials

With `ℓ ≤ (c² − χ)/c²`, `√T₊ − k ≥ (2/5)ℓ/(km²)`. An edge pair (`s < (10/ℓ)km`) is at most
`G((5/ℓ + 1)A/(skm²) + √κ₀(64s/(9c²km²) + 32√(5/ℓ + 1)√s/(3c²√k m√m)))`; a strip pair (`(10/ℓ)km ≤ s`, `s² ≤ c`) at most
`G(A/(cm) + 2√(10/(√3ℓ))/(σsm) + √κ₀(32s√c/(9c²k²m³) + 20s/(c²km²) + 32√s/(3c²√k m√m)))`.
-/

namespace Cvs.L2a.ExactRootPairMonomials

open Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.NonresonantCrossIntegral Cvs.Prolate.Envelope.ProlateWeightToEdge Cvs.L2a.StationaryPairElementarySizes Cvs.L2a.StationaryMismatchExactRoots

/-- **The stationary point's distance from the edge**: `√T₊ − k ≥ (2/5)ℓ/(km²)`, `ℓ ≤ (c² − χ)/c²`. -/
theorem sqrtTp_sub_ge {c χ k m ℓ : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ ≤ c ^ 2) (hk : 0 < k) (hm : 0 < m)
    (hkm : 1 ≤ m * k) (hℓ : ℓ ≤ (c ^ 2 - χ) / c ^ 2) :
    2 / 5 * ℓ / (k * m ^ 2) ≤ √(Tp c χ k m) - k := by
  have hTp := Tp_ge hc hk hm hkm hχ0 hχc
  have hTpS := Tp_le (k := k) hc hm hχ0
  have hT0 : 0 ≤ (c ^ 2 - χ) / (c ^ 2 * m ^ 2) := div_nonneg (by linarith) (by positivity)
  have hTp0 : 0 ≤ Tp c χ k m := le_trans (by positivity) hTp
  have hsq : √(Tp c χ k m) ^ 2 = Tp c χ k m := sq_sqrt hTp0
  have hkT : k ≤ √(Tp c χ k m) := Real.le_sqrt_of_sq_le (by linarith)
  have hS := sqrtS_sub_le hk hm
  have hTS : √(Tp c χ k m) ≤ √(k ^ 2 + 1 / m ^ 2) := sqrt_le_sqrt hTpS
  have hsmall : 1 / (2 * k * m ^ 2) ≤ k / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hsum : √(Tp c χ k m) + k ≤ 5 / 2 * k := by linarith
  have hdiff : ℓ / m ^ 2 ≤ Tp c χ k m - k ^ 2 := by
    have : ℓ / m ^ 2 ≤ (c ^ 2 - χ) / (c ^ 2 * m ^ 2) := by
      rw [show (c ^ 2 - χ) / (c ^ 2 * m ^ 2) = (c ^ 2 - χ) / c ^ 2 / m ^ 2 by field_simp]
      exact div_le_div_of_nonneg_right hℓ (by positivity)
    linarith
  have hfac : Tp c χ k m - k ^ 2 = (√(Tp c χ k m) - k) * (√(Tp c χ k m) + k) := by
    linear_combination -hsq
  have hpos : 0 < √(Tp c χ k m) + k := by linarith
  rw [div_le_iff₀ (by positivity)]
  have h1 : ℓ / m ^ 2 ≤ (√(Tp c χ k m) - k) * (5 / 2 * k) := by
    rw [hfac] at hdiff
    exact hdiff.trans (mul_le_mul_of_nonneg_left hsum (by linarith))
  have e : 2 / 5 * ℓ = 2 / 5 * (ℓ / m ^ 2) * m ^ 2 := by field_simp
  rw [e]
  have := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 2 / 5)
  nlinarith [sq_nonneg m]

/-- The right piece of Cvs.L2a.ExactRootPairPieces at `δ = 1/(s m)`, given `√(t_r − k) ≤ e`. -/
theorem right_s_le {c G κ k m s e tr : ℝ} (hc : 0 < c) (hG : 0 ≤ G) (hk : 0 < k) (hm : 0 < m) (hs : 0 < s)
    (he : √(tr - k) ≤ e) :
    G * √κ * (64 * k ^ 2 / (9 * m) + 32 * k ^ 2 * √k * √(tr - k) / 3) / (c ^ 2 * m ^ 2 * k ^ 3 * (1 / (s * m)))
      ≤ G * √κ * (64 * s / (9 * c ^ 2 * k * m ^ 2) + 32 * s * e / (3 * c ^ 2 * √k * m)) := by
  have hsk : 0 < √k := sqrt_pos.mpr hk
  have hkk : √k * √k = k := mul_self_sqrt hk.le
  have e1 : G * √κ * (64 * k ^ 2 / (9 * m) + 32 * k ^ 2 * √k * √(tr - k) / 3)
        / (c ^ 2 * m ^ 2 * k ^ 3 * (1 / (s * m)))
      = G * √κ * (64 * s / (9 * c ^ 2 * k * m ^ 2) + 32 * s * √(tr - k) / (3 * c ^ 2 * √k * m)) := by
    obtain ⟨p, hp, hkp⟩ : ∃ p, 0 < p ∧ k = p ^ 2 := ⟨√k, hsk, (sq_sqrt hk.le).symm⟩
    rw [show √k = p by rw [hkp, sqrt_sq hp.le], hkp]
    field_simp
  rw [e1]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add_right
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left he (by positivity)

set_option maxHeartbeats 1000000 in
/-- **An edge pair at the exact root** (`sℓ < 10km`), at `δ = 1/(s m)`. -/
theorem edge_mono {c χ G K Ξ k m b s ℓ : ℝ} {ψ u : ℝ → ℝ}
    (hc : 1 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hℓ0 : 0 < ℓ)
    (hk1 : 1 ≤ k) (hkm2 : 2 ≤ k * m) (hm : 1 ≤ m) (hs1 : 1 ≤ s) (hreg : s * ℓ < 10 * (k * m))
    (hrb : k + 2 ≤ b) (hhi : m * b ≤ Ξ)
    (hψ : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hG : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χ) ψ u ξ ≤ G) (hG0 : 0 ≤ G) (hK : 0 ≤ K)
    (hcont : ContinuousOn ψ (Icc 1 Ξ)) (hedge : ∀ ξ ∈ Icc 1 Ξ, |ψ ξ| ≤ |ψ 1|) (hedge1 : ψ 1 ^ 2 ≤ K * G) :
    |∫ t in k..b, ψ (m * t) * ψ (1 / k * t)|
      ≤ G * ((5 / ℓ + 1) * √(2 * K / (√3 * √(c ^ 2 - χ))) / (s * k * m ^ 2)
        + √(c / √(c ^ 2 - χ)) * (64 * s / (9 * c ^ 2 * k * m ^ 2)
          + 32 * √(5 / ℓ + 1) * √s / (3 * c ^ 2 * √k * (m * √m)))) := by
  have hc0 : 0 < c := by linarith
  have hk0 : 0 < k := by linarith
  have hm0 : 0 < m := by linarith
  have hs0 : 0 < s := by linarith
  have hkm1' : 1 ≤ m * k := by nlinarith
  set tr := √(Tp c χ k m) + 1 / (s * m) with htr
  have hTp := Tp_ge hc0 hk0 hm0 hkm1' hχ0 hχ.le
  have hTpS := Tp_le (k := k) hc0 hm0 hχ0
  have hT0 : 0 ≤ (c ^ 2 - χ) / (c ^ 2 * m ^ 2) := div_nonneg (by linarith) (by positivity)
  have hkS : k ≤ √(Tp c χ k m) := Real.le_sqrt_of_sq_le (by linarith)
  have hTS : √(Tp c χ k m) ≤ √(k ^ 2 + 1 / m ^ 2) := sqrt_le_sqrt hTpS
  have him : 0 < 1 / (s * m) := by positivity
  have hktr : k < tr := by rw [htr]; linarith
  have hS := sqrtS_sub_le hk0 hm0
  have h1 : 1 / (2 * k * m ^ 2) ≤ 5 / ℓ / (s * m) := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hlen : tr - k ≤ (5 / ℓ + 1) / (s * m) := by
    have : (5 / ℓ + 1) / (s * m) = 5 / ℓ / (s * m) + 1 / (s * m) := by ring
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
  have key := Cvs.L2a.ExactRootEdgeWindowPair.pairB_le (δ := 1 / (s * m)) (tr := tr) (b := b) (ξ₁ := min (tr / k) 2)
    hc0 hχ0 hχ hk1 hkm2 hm him hδk htr (by linarith) hξ₁ (min_le_left _ _) htrk
    hhi hbk (fun ξ hξ => hψ ξ (hsub hξ)) (fun ξ hξ => hu ξ (hsub hξ)) (fun ξ hξ => hG ξ (hsub hξ))
    hG0 hK hcont hedge hedge1
  set L := 5 / ℓ + 1 with hL
  have hL0 : 0 < L := by positivity
  have hsq : √(tr - k) ≤ √L / (√s * √m) := by
    have : √L / (√s * √m) = √(L / (s * m)) := by
      rw [sqrt_div' L (by positivity : 0 ≤ s * m), sqrt_mul hs0.le]
    rw [this]; exact Real.sqrt_le_sqrt hlen
  have hr := Cvs.L2a.ExactRootPairMonomials.right_s_le (κ := c / √(c ^ 2 - χ)) hc0 hG0 hk0 hm0 hs0 hsq
  have hA : 0 ≤ √(2 * K / (√3 * √(c ^ 2 - χ))) * G / (m * k) := by positivity
  have hw : (tr - k) * (√(2 * K / (√3 * √(c ^ 2 - χ))) * G / (m * k))
      ≤ L / (s * m) * (√(2 * K / (√3 * √(c ^ 2 - χ))) * G / (m * k)) :=
    mul_le_mul_of_nonneg_right hlen hA
  have hsm : 0 < √m := sqrt_pos.mpr hm0
  have hsk : 0 < √k := sqrt_pos.mpr hk0
  have hss : 0 < √s := sqrt_pos.mpr hs0
  have e1 : L / (s * m) * (√(2 * K / (√3 * √(c ^ 2 - χ))) * G / (m * k))
      = G * (L * √(2 * K / (√3 * √(c ^ 2 - χ))) / (s * k * m ^ 2)) := by field_simp
  have e2 : G * √(c / √(c ^ 2 - χ)) * (64 * s / (9 * c ^ 2 * k * m ^ 2) + 32 * s * (√L / (√s * √m)) / (3 * c ^ 2 * √k * m))
      = G * √(c / √(c ^ 2 - χ)) * (64 * s / (9 * c ^ 2 * k * m ^ 2) + 32 * √L * √s / (3 * c ^ 2 * √k * (m * √m))) := by
    obtain ⟨r, hr0, hsr⟩ : ∃ r, 0 < r ∧ s = r ^ 2 := ⟨√s, hss, (sq_sqrt hs0.le).symm⟩
    rw [show √s = r by rw [hsr, sqrt_sq hr0.le], hsr]
    field_simp
  have e3 : G * (L * √(2 * K / (√3 * √(c ^ 2 - χ))) / (s * k * m ^ 2)
        + √(c / √(c ^ 2 - χ)) * (64 * s / (9 * c ^ 2 * k * m ^ 2) + 32 * √L * √s / (3 * c ^ 2 * √k * (m * √m))))
      = G * (L * √(2 * K / (√3 * √(c ^ 2 - χ))) / (s * k * m ^ 2))
        + G * √(c / √(c ^ 2 - χ)) * (64 * s / (9 * c ^ 2 * k * m ^ 2) + 32 * √L * √s / (3 * c ^ 2 * √k * (m * √m))) := by
    ring
  rw [e3]; linarith

set_option maxHeartbeats 2000000 in
/-- **A strip pair at the exact root** (`10km ≤ sℓ`, `s² ≤ c`), at `δ = 1/(s m)`. -/
theorem strip_mono {c χ G K Ξ k m b s ℓ : ℝ} {ψ u : ℝ → ℝ}
    (hc : 1 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hℓ0 : 0 < ℓ) (hℓ : ℓ ≤ (c ^ 2 - χ) / c ^ 2)
    (hk1 : 1 ≤ k) (hkm2 : 2 ≤ k * m) (hm : 1 ≤ m)
    (hs1 : 1 ≤ s) (hsc : s ^ 2 ≤ c) (hreg : 10 * (k * m) ≤ s * ℓ) (hrb : k + 2 ≤ b) (hhi : m * b ≤ Ξ)
    (hψ : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hG : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χ) ψ u ξ ≤ G) (hG0 : 0 ≤ G) (hK : 0 ≤ K)
    (hcont : ContinuousOn ψ (Icc 1 Ξ)) (hedge : ∀ ξ ∈ Icc 1 Ξ, |ψ ξ| ≤ |ψ 1|) (hedge1 : ψ 1 ^ 2 ≤ K * G) :
    |∫ t in k..b, ψ (m * t) * ψ (1 / k * t)|
      ≤ G * (√(2 * K / (√3 * √(c ^ 2 - χ))) / (c * m) + 2 * √(10 / (√3 * ℓ)) / √(c ^ 2 - χ) / (s * m)
        + √(c / √(c ^ 2 - χ)) * (32 * s * √c / (9 * c ^ 2 * k ^ 2 * m ^ 3) + 20 * s / (c ^ 2 * k * m ^ 2)
          + 32 * √s / (3 * c ^ 2 * √k * (m * √m)))) := by
  have hc0 : 0 < c := by linarith
  have hk0 : 0 < k := by linarith
  have hm0 : 0 < m := by linarith
  have hs0 : 0 < s := by linarith
  have hkm1' : 1 ≤ m * k := by nlinarith
  have hd : 0 < c ^ 2 - χ := by linarith
  have hsd : 0 < √(c ^ 2 - χ) := sqrt_pos.mpr hd
  have hℓ1 : ℓ ≤ 1 := by
    refine hℓ.trans ?_; rw [div_le_one (by positivity)]; linarith
  have hTp := Tp_ge hc0 hk0 hm0 hkm1' hχ0 hχ.le
  have hTpS := Tp_le (k := k) hc0 hm0 hχ0
  have hT0 : 0 ≤ (c ^ 2 - χ) / (c ^ 2 * m ^ 2) := div_nonneg (by linarith) (by positivity)
  have hTS : √(Tp c χ k m) ≤ √(k ^ 2 + 1 / m ^ 2) := sqrt_le_sqrt hTpS
  have hgap0 := sqrtTp_sub_ge hc0 hχ0 hχ.le hk0 hm0 hkm1' hℓ
  have hup := sqrtS_sub_le hk0 hm0
  set tl := √(Tp c χ k m) - 1 / (s * m) with htl
  set tr := √(Tp c χ k m) + 1 / (s * m) with htr
  have him : 0 < 1 / (s * m) := by positivity
  -- the regime's two sizes
  have r2 : 1 / (s * m) ≤ ℓ / (10 * k * m ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have r1 : k / c ≤ ℓ / (10 * k * m ^ 2) := by
    rw [div_le_div_iff₀ hc0 (by positivity)]
    have h1 : 100 * (k * m) ^ 2 ≤ (s * ℓ) ^ 2 := by nlinarith
    have h2 : (s * ℓ) ^ 2 ≤ s ^ 2 * ℓ := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg s)
    have h3 : s ^ 2 * ℓ ≤ c * ℓ := mul_le_mul_of_nonneg_right hsc hℓ0.le
    nlinarith
  have e5 : 2 / 5 * ℓ / (k * m ^ 2) = ℓ / (10 * k * m ^ 2) + ℓ / (10 * k * m ^ 2) + ℓ / (5 * k * m ^ 2) := by
    field_simp; ring
  have hg0 : 0 < ℓ / (5 * k * m ^ 2) := by positivity
  have hatl : k * (1 + 1 / c) ≤ tl := by
    have : k * (1 + 1 / c) = k + k / c := by ring
    rw [this, htl]; linarith
  have hgap : ℓ / (5 * k * m ^ 2) ≤ tl - k := by rw [htl]; linarith
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
  have key := Cvs.L2a.ExactRootNearEdgePair.pairA_le (δ := 1 / (s * m)) (tl := tl) (tr := tr) (b := b)
    (ξ₁ := 1 + 1 / c) (K := K) hc hχ0 hχ hk1 hkm2 hm him hδk htl htr (by linarith) hatl hg0 hgap hξ₁ le_rfl
    (by rw [mul_comm]; linarith) hhi hbk (fun ξ hξ => hψ ξ (hsub hξ)) (fun ξ hξ => hu ξ (hsub hξ))
    (fun ξ hξ => hG ξ (hsub hξ)) hG0 hK hcont hedge hedge1
  set A := √(2 * K / (√3 * √(c ^ 2 - χ))) with hA
  set κ := √(c / √(c ^ 2 - χ)) with hκ
  have hA0 : 0 ≤ A := sqrt_nonneg _
  have hκ0 : 0 ≤ κ := sqrt_nonneg _
  have hsk : 0 < √k := sqrt_pos.mpr hk0
  have hsm : 0 < √m := sqrt_pos.mpr hm0
  have hsss : 0 < √s := sqrt_pos.mpr hs0
  -- the strip piece
  have x1 : k / c * (A * G / (m * k)) = G * (A / (c * m)) := by field_simp
  -- the left piece, with `t_l² ≤ (5/4)k²`
  have htl0 : 0 < tl := by linarith
  have htl2 : tl ^ 2 ≤ 5 / 4 * k ^ 2 := by
    have hle : tl ≤ √(k ^ 2 + 1 / m ^ 2) := by rw [htl]; linarith
    have hsq : √(k ^ 2 + 1 / m ^ 2) ^ 2 = k ^ 2 + 1 / m ^ 2 := sq_sqrt (by positivity)
    have : 1 / m ^ 2 ≤ k ^ 2 / 4 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    nlinarith [pow_le_pow_left₀ htl0.le hle 2]
  have x2 : 16 * G * κ * (tl ^ 2 / m + 2 * k * √c / m ^ 2) / (9 * c ^ 2 * k ^ 3 * (1 / (s * m)) * m ^ 2)
      ≤ G * κ * (32 * s * √c / (9 * c ^ 2 * k ^ 2 * m ^ 3) + 20 * s / (9 * c ^ 2 * k * m ^ 2)) := by
    calc 16 * G * κ * (tl ^ 2 / m + 2 * k * √c / m ^ 2) / (9 * c ^ 2 * k ^ 3 * (1 / (s * m)) * m ^ 2)
        ≤ 16 * G * κ * (5 / 4 * k ^ 2 / m + 2 * k * √c / m ^ 2) / (9 * c ^ 2 * k ^ 3 * (1 / (s * m)) * m ^ 2) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have := div_le_div_of_nonneg_right htl2 hm0.le
          linarith
      _ = G * κ * (32 * s * √c / (9 * c ^ 2 * k ^ 2 * m ^ 3) + 20 * s / (9 * c ^ 2 * k * m ^ 2)) := by
          field_simp; ring
  -- the window
  have x3 : 2 * (1 / (s * m)) * (G / √(c ^ 2 - χ) * √(2 / (√3 * (m ^ 2 * k * (ℓ / (5 * k * m ^ 2))))))
      = G * (2 * √(10 / (√3 * ℓ)) / √(c ^ 2 - χ) / (s * m)) := by
    have e : 2 / (√3 * (m ^ 2 * k * (ℓ / (5 * k * m ^ 2)))) = 10 / (√3 * ℓ) := by field_simp; ring
    rw [e]; field_simp
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
  have x4 := right_s_le (κ := c / √(c ^ 2 - χ)) hc0 hG0 hk0 hm0 hs0 he
  have x4e : G * κ * (64 * s / (9 * c ^ 2 * k * m ^ 2) + 32 * s * (1 / (m * √k) + 1 / (√s * √m)) / (3 * c ^ 2 * √k * m))
      = G * κ * (64 * s / (9 * c ^ 2 * k * m ^ 2) + 32 * s / (3 * c ^ 2 * k * m ^ 2)
          + 32 * √s / (3 * c ^ 2 * √k * (m * √m))) := by
    obtain ⟨p, hp, hkp⟩ : ∃ p, 0 < p ∧ k = p ^ 2 := ⟨√k, hsk, (sq_sqrt hk0.le).symm⟩
    obtain ⟨q, hq, hmq⟩ : ∃ q, 0 < q ∧ m = q ^ 2 := ⟨√m, hsm, (sq_sqrt hm0.le).symm⟩
    obtain ⟨r, hr, hsr⟩ : ∃ r, 0 < r ∧ s = r ^ 2 := ⟨√s, hsss, (sq_sqrt hs0.le).symm⟩
    rw [show √k = p by rw [hkp, sqrt_sq hp.le], show √m = q by rw [hmq, sqrt_sq hq.le],
      show √s = r by rw [hsr, sqrt_sq hr.le], hkp, hmq, hsr]
    field_simp; ring
  have fin : G * (A / (c * m) + 2 * √(10 / (√3 * ℓ)) / √(c ^ 2 - χ) / (s * m)
        + κ * (32 * s * √c / (9 * c ^ 2 * k ^ 2 * m ^ 3) + 20 * s / (c ^ 2 * k * m ^ 2)
          + 32 * √s / (3 * c ^ 2 * √k * (m * √m))))
      = G * (A / (c * m)) + G * (2 * √(10 / (√3 * ℓ)) / √(c ^ 2 - χ) / (s * m))
        + G * κ * (32 * s * √c / (9 * c ^ 2 * k ^ 2 * m ^ 3) + 20 * s / (9 * c ^ 2 * k * m ^ 2))
        + G * κ * (64 * s / (9 * c ^ 2 * k * m ^ 2) + 32 * s / (3 * c ^ 2 * k * m ^ 2)
          + 32 * √s / (3 * c ^ 2 * √k * (m * √m))) := by ring
  rw [fin]
  rw [x1, x3] at key
  have x4' : G * κ * (64 * k ^ 2 / (9 * m) + 32 * k ^ 2 * √k * √(tr - k) / 3)
        / (c ^ 2 * m ^ 2 * k ^ 3 * (1 / (s * m)))
      ≤ G * κ * (64 * s / (9 * c ^ 2 * k * m ^ 2) + 32 * s / (3 * c ^ 2 * k * m ^ 2)
          + 32 * √s / (3 * c ^ 2 * √k * (m * √m))) := by
    rw [← x4e]; exact x4
  linarith

end Cvs.L2a.ExactRootPairMonomials
