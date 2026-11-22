import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.Bounds
import Cvs.L2a.ExactRootPairMonomials
import Cvs.L2a.SigmaFreeEdgePairMonomials
import Cvs.L2a.SigmaFreeNearEdgePair
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
# A strip stationary pair with `σ`-free envelopes, as monomials

With `L = (c² − χ)/c²`, a strip pair (`10km ≤ sL`, `s²L ≤ c`) at `δ = 1/(sm)`, gap `L/(5km²)`, is at most
`G(√(4K/(3c))/(cm) + 2√(10/(3L))/(csm) + (40/(9√3) + (16/9)(8/√3 + 2√3√L))s/(c²km²) + (64√2/27)Ls√c/(c²k²m³))`:
the only negative power of `L` is the window's `L^{−1/2}`.
-/

namespace Cvs.L2a.SigmaFreeStripPairMonomials

open Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.NonresonantCrossIntegral Cvs.Prolate.Envelope.ProlateWeightToEdge Cvs.L2a.StationaryPairElementarySizes Cvs.L2a.StationaryMismatchExactRoots

set_option maxHeartbeats 4000000 in
/-- **A strip pair with `σ`-free envelopes** (`10km ≤ sL`, `s²L ≤ c`), at `δ = 1/(s m)`. -/
theorem strip_mono {c χ G K Ξ k m b s : ℝ} {ψ u : ℝ → ℝ}
    (hc : 1 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hk1 : 1 ≤ k) (hkm2 : 2 ≤ k * m) (hm : 1 ≤ m)
    (hs1 : 1 ≤ s) (hsc : s ^ 2 * ((c ^ 2 - χ) / c ^ 2) ≤ c) (hreg : 10 * (k * m) ≤ s * ((c ^ 2 - χ) / c ^ 2))
    (hrb : k + 2 ≤ b) (hhi : m * b ≤ Ξ)
    (hψ : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hG : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χ) ψ u ξ ≤ G) (hG0 : 0 ≤ G)
    (hcont : ContinuousOn ψ (Icc 1 Ξ)) (hedge : ∀ ξ ∈ Icc 1 Ξ, |ψ ξ| ≤ |ψ 1|) (hedge1 : ψ 1 ^ 2 ≤ K * G) :
    |∫ t in k..b, ψ (m * t) * ψ (1 / k * t)|
      ≤ G * (√(4 * K / (3 * c)) / (c * m) + 2 * √(10 / (3 * ((c ^ 2 - χ) / c ^ 2))) / (c * s * m)
        + (40 / (9 * √3) + 16 / 9 * (8 / √3 + 2 * √3 * √((c ^ 2 - χ) / c ^ 2))) * s / (c ^ 2 * k * m ^ 2)
        + 64 * √2 / 27 * ((c ^ 2 - χ) / c ^ 2) * s * √c / (c ^ 2 * k ^ 2 * m ^ 3)) := by
  have hc0 : 0 < c := by linarith
  have hk0 : 0 < k := by linarith
  have hm0 : 0 < m := by linarith
  have hs0 : 0 < s := by linarith
  have hkm1' : 1 ≤ m * k := by nlinarith
  set L := (c ^ 2 - χ) / c ^ 2 with hLdef
  have hL0 : 0 < L := by
    by_contra h; push Not at h
    have : s * L ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs0.le h
    nlinarith
  have hL1 : L ≤ 1 := by rw [hLdef, div_le_one (by positivity)]; linarith
  have hTp := Tp_ge hc0 hk0 hm0 hkm1' hχ0 hχ.le
  have hTpS := Tp_le (k := k) hc0 hm0 hχ0
  have hT0 : 0 ≤ (c ^ 2 - χ) / (c ^ 2 * m ^ 2) := div_nonneg (by linarith) (by positivity)
  have hTS : √(Tp c χ k m) ≤ √(k ^ 2 + 1 / m ^ 2) := sqrt_le_sqrt hTpS
  have hgap0 := Cvs.L2a.ExactRootPairMonomials.sqrtTp_sub_ge hc0 hχ0 hχ.le hk0 hm0 hkm1' (le_refl L)
  have hoff := Cvs.L2a.SigmaFreeEdgePairMonomials.sqrtTp_sub_le hc0 hk0 hm0 hkm2 hχ0 hχ.le
  have hToff := Cvs.L2a.SigmaFreeEdgePairMonomials.Tp_sub_le hc0 hk0 hm0 hkm2 hχ0 hχ.le
  rw [← hLdef] at hoff hToff
  set tl := √(Tp c χ k m) - 1 / (s * m) with htl
  set tr := √(Tp c χ k m) + 1 / (s * m) with htr
  have him : 0 < 1 / (s * m) := by positivity
  have r2 : 1 / (s * m) ≤ L / (10 * k * m ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have r1 : k / c ≤ L / (10 * k * m ^ 2) := by
    rw [div_le_div_iff₀ hc0 (by positivity)]
    have h1 : 100 * (k * m) ^ 2 ≤ (s * L) ^ 2 := by nlinarith
    have h2 : (s * L) ^ 2 ≤ c * L := by
      calc (s * L) ^ 2 = s ^ 2 * L * L := by ring
        _ ≤ c * L := mul_le_mul_of_nonneg_right hsc hL0.le
    nlinarith
  have e5 : 2 / 5 * L / (k * m ^ 2) = L / (10 * k * m ^ 2) + L / (10 * k * m ^ 2) + L / (5 * k * m ^ 2) := by
    field_simp; ring
  have hg0 : 0 < L / (5 * k * m ^ 2) := by positivity
  have hatl : k * (1 + 1 / c) ≤ tl := by
    have : k * (1 + 1 / c) = k + k / c := by ring
    rw [this, htl]; linarith
  have hgap : L / (5 * k * m ^ 2) ≤ tl - k := by rw [htl]; linarith
  have hδk : 1 / (s * m) ≤ k / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hup := sqrtS_sub_le hk0 hm0
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
  have key := Cvs.L2a.SigmaFreeNearEdgePair.pairA_le (δ := 1 / (s * m)) (tl := tl) (tr := tr) (b := b)
    (ξ₁ := 1 + 1 / c) (K := K) hc hχ0 hχ hk1 hkm2 hm him hδk htl htr (by linarith) hatl hg0 hgap hξ₁ le_rfl
    (by rw [mul_comm]; linarith) hhi hbk (fun ξ hξ => hψ ξ (hsub hξ)) (fun ξ hξ => hu ξ (hsub hξ))
    (fun ξ hξ => hG ξ (hsub hξ)) hG0 hcont hedge hedge1
  set Ac := √(4 * K / (3 * c)) with hAc
  have hAc0 : 0 ≤ Ac := sqrt_nonneg _
  have hsk : 0 < √k := sqrt_pos.mpr hk0
  have hsm : 0 < √m := sqrt_pos.mpr hm0
  have hsc0 : 0 ≤ √c := sqrt_nonneg _
  -- the strip piece
  have x1 : k / c * (G * Ac / (m * k)) = G * (Ac / (c * m)) := by field_simp
  -- the left piece
  have htl0 : 0 < tl := by linarith
  have htl2 : tl ^ 2 ≤ 5 / 4 * k ^ 2 := by
    have hle : tl ≤ √(k ^ 2 + 1 / m ^ 2) := by rw [htl]; linarith
    have hsq : √(k ^ 2 + 1 / m ^ 2) ^ 2 = k ^ 2 + 1 / m ^ 2 := sq_sqrt (by positivity)
    have : 1 / m ^ 2 ≤ k ^ 2 / 4 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    nlinarith [pow_le_pow_left₀ htl0.le hle 2]
  have hTk0 : 0 ≤ Tp c χ k m - k ^ 2 := by nlinarith
  have x2 : 16 / 9 * G * (tl ^ 2 * (2 / √3) / m + (Tp c χ k m - k ^ 2) * (√2 * k * √c))
        / (m ^ 2 * c ^ 2 * k ^ 3 * (1 / (s * m)))
      ≤ G * (40 / (9 * √3) * s / (c ^ 2 * k * m ^ 2) + 64 * √2 / 27 * L * s * √c / (c ^ 2 * k ^ 2 * m ^ 3)) := by
    calc 16 / 9 * G * (tl ^ 2 * (2 / √3) / m + (Tp c χ k m - k ^ 2) * (√2 * k * √c))
          / (m ^ 2 * c ^ 2 * k ^ 3 * (1 / (s * m)))
        ≤ 16 / 9 * G * (5 / 4 * k ^ 2 * (2 / √3) / m + 4 / 3 * L / m ^ 2 * (√2 * k * √c))
          / (m ^ 2 * c ^ 2 * k ^ 3 * (1 / (s * m))) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have a1 : tl ^ 2 * (2 / √3) / m ≤ 5 / 4 * k ^ 2 * (2 / √3) / m := by gcongr
          have a2 : (Tp c χ k m - k ^ 2) * (√2 * k * √c) ≤ 4 / 3 * L / m ^ 2 * (√2 * k * √c) :=
            mul_le_mul_of_nonneg_right hToff (by positivity)
          linarith
      _ = G * (40 / (9 * √3) * s / (c ^ 2 * k * m ^ 2) + 64 * √2 / 27 * L * s * √c / (c ^ 2 * k ^ 2 * m ^ 3)) := by
          field_simp; ring
  -- the window
  have x3 : 2 * (1 / (s * m)) * (G / c * √(2 / (3 * (m ^ 2 * k * (L / (5 * k * m ^ 2))))))
      = G * (2 * √(10 / (3 * L)) / (c * s * m)) := by
    have e : 2 / (3 * (m ^ 2 * k * (L / (5 * k * m ^ 2)))) = 10 / (3 * L) := by field_simp; ring
    rw [e]; field_simp
  -- the right piece: `t_r − k ≤ L/(km²)`
  have htrk : tr - k ≤ L / (k * m ^ 2) := by
    have e : L / (k * m ^ 2) = 2 / 3 * L / (k * m ^ 2) + L / (10 * k * m ^ 2) + 7 / 30 * L / (k * m ^ 2) := by
      field_simp; ring
    have : 0 ≤ 7 / 30 * L / (k * m ^ 2) := by positivity
    rw [htr]; linarith
  have he : √(tr - k) ≤ √L / (√k * m) := by
    have : √L / (√k * m) = √(L / (k * m ^ 2)) := by
      rw [sqrt_div' L (by positivity : (0 : ℝ) ≤ k * m ^ 2), sqrt_mul hk0.le, sqrt_sq hm0.le]
    rw [this]; exact sqrt_le_sqrt htrk
  have x4 : 16 / 9 * G * (8 * k ^ 2 / (√3 * m) + 2 * √3 * k ^ 2 * √k * √(tr - k))
        / (m ^ 2 * c ^ 2 * k ^ 3 * (1 / (s * m)))
      ≤ G * (16 / 9 * (8 / √3 + 2 * √3 * √L) * s / (c ^ 2 * k * m ^ 2)) := by
    calc 16 / 9 * G * (8 * k ^ 2 / (√3 * m) + 2 * √3 * k ^ 2 * √k * √(tr - k))
          / (m ^ 2 * c ^ 2 * k ^ 3 * (1 / (s * m)))
        ≤ 16 / 9 * G * (8 * k ^ 2 / (√3 * m) + 2 * √3 * k ^ 2 * √k * (√L / (√k * m)))
          / (m ^ 2 * c ^ 2 * k ^ 3 * (1 / (s * m))) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have := mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ 2 * √3 * k ^ 2 * √k)
          linarith
      _ = G * (16 / 9 * (8 / √3 + 2 * √3 * √L) * s / (c ^ 2 * k * m ^ 2)) := by
          field_simp
  rw [x1, x3] at key
  have fin : G * (Ac / (c * m) + 2 * √(10 / (3 * L)) / (c * s * m)
        + (40 / (9 * √3) + 16 / 9 * (8 / √3 + 2 * √3 * √L)) * s / (c ^ 2 * k * m ^ 2)
        + 64 * √2 / 27 * L * s * √c / (c ^ 2 * k ^ 2 * m ^ 3))
      = G * (Ac / (c * m)) + G * (2 * √(10 / (3 * L)) / (c * s * m))
        + G * (40 / (9 * √3) * s / (c ^ 2 * k * m ^ 2) + 64 * √2 / 27 * L * s * √c / (c ^ 2 * k ^ 2 * m ^ 3))
        + G * (16 / 9 * (8 / √3 + 2 * √3 * √L) * s / (c ^ 2 * k * m ^ 2)) := by ring
  rw [fin]
  linarith

end Cvs.L2a.SigmaFreeStripPairMonomials
