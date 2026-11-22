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
import Cvs.L2a.NonresonantCrossIntegral
import Cvs.L2a.SigmaFreePairPieces
import Cvs.L2a.SigmaFreeStationaryEdgePairs
import Cvs.L2a.StationaryMismatchExactRoots
import Cvs.L2a.StationaryPairElementarySizes
import Cvs.L2a.StationaryPairMismatchSign
import Cvs.Prolate.Envelope.EdgeEnvelopeSigmaFreeOffset
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
# The edge-window stationary pair with `σ`-free envelopes, as monomials

With `L = (c² − χ)/c²` and `km ≥ 2`: `T₊ − k² ≤ (4/3)L/m²` and `√T₊ − k ≤ (2/3)L/(km²)` (Cvs.Prolate.Envelope.EdgeEnvelopeSigmaFreeOffset), so an edge pair
(`sL < 10km`) at `δ = 1/(sm)` has `t_r − k ≤ (23/3)/(sm)` and is at most
`G((23/3)√(4K/(3c))/(skm²) + (128/(9√3))s/(c²km²) + (32√3/9)√(23/3)√s/(c²√k m√m))`, with no negative power of `L`.
-/

namespace Cvs.L2a.SigmaFreeEdgePairMonomials

open Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.NonresonantCrossIntegral Cvs.Prolate.Envelope.ProlateWeightToEdge Cvs.L2a.StationaryPairElementarySizes Cvs.L2a.StationaryMismatchExactRoots

/-- `T₊ − k² ≤ (4/3)L/m²` for `km ≥ 2`, `L = (c² − χ)/c²`. -/
theorem Tp_sub_le {c χ k m : ℝ} (hc : 0 < c) (hk : 0 < k) (hm : 0 < m) (hkm2 : 2 ≤ k * m) (hχ0 : 0 ≤ χ)
    (hχc : χ ≤ c ^ 2) : Tp c χ k m - k ^ 2 ≤ 4 / 3 * ((c ^ 2 - χ) / c ^ 2) / m ^ 2 := by
  have h := Cvs.Prolate.Envelope.EdgeEnvelopeSigmaFreeOffset.Tp_sub_le hc hk hm (by nlinarith) hχ0 hχc
  refine h.trans ?_
  have hL : 0 ≤ (c ^ 2 - χ) / c ^ 2 := div_nonneg (by linarith) (by positivity)
  have hkm : 3 / 4 * (k ^ 2 * m ^ 2) ≤ k ^ 2 * m ^ 2 - 1 := by nlinarith
  rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
  have := mul_le_mul_of_nonneg_left hkm (by positivity : (0 : ℝ) ≤ 4 / 3 * ((c ^ 2 - χ) / c ^ 2))
  nlinarith [mul_nonneg hL (sq_nonneg k), mul_nonneg hL (sq_nonneg m)]

/-- `√T₊ − k ≤ (2/3)L/(km²)`. -/
theorem sqrtTp_sub_le {c χ k m : ℝ} (hc : 0 < c) (hk : 0 < k) (hm : 0 < m) (hkm2 : 2 ≤ k * m) (hχ0 : 0 ≤ χ)
    (hχc : χ ≤ c ^ 2) : √(Tp c χ k m) - k ≤ 2 / 3 * ((c ^ 2 - χ) / c ^ 2) / (k * m ^ 2) := by
  have h := Tp_sub_le hc hk hm hkm2 hχ0 hχc
  have hTp := Tp_ge hc hk hm (by nlinarith) hχ0 hχc
  have hT0' : 0 ≤ (c ^ 2 - χ) / (c ^ 2 * m ^ 2) := div_nonneg (by linarith) (by positivity)
  have hT0 : 0 ≤ Tp c χ k m := by nlinarith [sq_nonneg k]
  have hsq : √(Tp c χ k m) ^ 2 = Tp c χ k m := sq_sqrt hT0
  have hkT : k ≤ √(Tp c χ k m) := Real.le_sqrt_of_sq_le (by linarith)
  have hfac : Tp c χ k m - k ^ 2 = (√(Tp c χ k m) - k) * (√(Tp c χ k m) + k) := by linear_combination -hsq
  have h2 : (√(Tp c χ k m) - k) * (2 * k) ≤ Tp c χ k m - k ^ 2 := by
    rw [hfac]; exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  rw [le_div_iff₀ (by positivity)]
  have e : 2 / 3 * ((c ^ 2 - χ) / c ^ 2) = 4 / 3 * ((c ^ 2 - χ) / c ^ 2) / m ^ 2 * m ^ 2 / 2 := by field_simp; ring
  nlinarith [mul_le_mul_of_nonneg_right (h2.trans h) (by positivity : (0 : ℝ) ≤ m ^ 2)]

/-- **The edge-window pair with `σ`-free envelopes.** -/
theorem pairB_le {c χ G K ξ₁ Ξ k m δ tr b : ℝ} {ψ u : ℝ → ℝ}
    (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hk1 : 1 ≤ k) (hkm2 : 2 ≤ k * m) (hm : 1 ≤ m) (hδ : 0 < δ) (hδk : δ ≤ k / 2)
    (htrdef : tr = √(Tp c χ k m) + δ) (hrb : tr ≤ b)
    (hξ₁ : 1 < ξ₁) (hlo : ξ₁ ≤ tr / k) (hlo' : ξ₁ ≤ m * k) (hhi : m * b ≤ Ξ) (hhi' : b / k ≤ Ξ)
    (hψ : ∀ ξ ∈ Icc ξ₁ Ξ, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Icc ξ₁ Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hG : ∀ ξ ∈ Icc ξ₁ Ξ, energy (aP c χ) ψ u ξ ≤ G) (hG0 : 0 ≤ G)
    (hcont : ContinuousOn ψ (Icc 1 Ξ)) (hedge : ∀ ξ ∈ Icc 1 Ξ, |ψ ξ| ≤ |ψ 1|) (hedge1 : ψ 1 ^ 2 ≤ K * G) :
    |∫ t in k..b, ψ (m * t) * ψ (1 / k * t)|
      ≤ (tr - k) * (G * √(4 * K / (3 * c)) / (m * k))
        + 16 / 9 * G * (8 * k ^ 2 / (√3 * m) + 2 * √3 * k ^ 2 * √k * √(tr - k)) / (m ^ 2 * c ^ 2 * k ^ 3 * δ) := by
  have hk0 : 0 < k := by linarith
  have hm0 : 0 < m := by linarith
  have hkm : 1 < k * m := by nlinarith
  have hkm1' : 1 ≤ m * k := by nlinarith
  have hTp := Tp_ge hc hk0 hm0 hkm1' hχ0 hχ.le
  have hT0 : 0 ≤ (c ^ 2 - χ) / (c ^ 2 * m ^ 2) := div_nonneg (by linarith) (by positivity)
  have hkS : k ≤ √(Tp c χ k m) := Real.le_sqrt_of_sq_le (by linarith)
  have hktr : k < tr := by rw [htrdef]; linarith
  have hDR : ∀ τ ∈ Icc tr b, 0 < Dmr c χ m (1 / k) τ := fun τ hτ => by
    rw [Cvs.L2a.StationaryPairMismatchSign.Dmr_eq_Est hk0.ne' hm0.ne']
    have hE := Est_right (t := τ) hc hk0 hm0 hkm1' hχ0 hχ.le hδ (by rw [← htrdef]; exact hτ.1)
    have hk2 : 0 < k ^ 2 - 1 / m ^ 2 := by
      rw [sub_pos, div_lt_iff₀ (by positivity)]; nlinarith
    have : 0 < 2 * c ^ 2 * √(Tp c χ k m) * δ * (k ^ 2 - 1 / m ^ 2) := by
      have : 0 < √(Tp c χ k m) := lt_of_lt_of_le hk0 hkS
      positivity
    have hmk : 0 < m ^ 2 - 1 / k ^ 2 := by
      have : 1 / k ^ 2 < m ^ 2 := by rw [div_lt_iff₀ (by positivity)]; nlinarith
      nlinarith
    exact mul_pos hmk (lt_of_lt_of_le this hE)
  have key := Cvs.L2a.SigmaFreeStationaryEdgePairs.edge_pair_le hc hχ0 hχ hk0 hm0 hkm2 hktr hrb hξ₁ hlo hlo' hhi hhi'
    hψ hu hG hcont hedge hDR
  have hw : √(G / (3 / 4 * c * (m * k) ^ 2)) * |ψ 1| ≤ G * √(4 * K / (3 * c)) / (m * k) := by
    have hp1 : |ψ 1| ≤ √(K * G) := Real.abs_le_sqrt hedge1
    calc √(G / (3 / 4 * c * (m * k) ^ 2)) * |ψ 1| ≤ √(G / (3 / 4 * c * (m * k) ^ 2)) * √(K * G) :=
          mul_le_mul_of_nonneg_left hp1 (sqrt_nonneg _)
      _ = G * √(4 * K / (3 * c)) / (m * k) := by
          rw [← sqrt_mul (by positivity), show G / (3 / 4 * c * (m * k) ^ 2) * (K * G)
            = (G / (m * k)) ^ 2 * (4 * K / (3 * c)) by field_simp, sqrt_mul (sq_nonneg _),
            sqrt_sq (by positivity)]
          ring
  have hr := Cvs.L2a.SigmaFreePairPieces.right_le (c := c) (χ := χ) (k := k) (m := m) (δ := δ) (G := G)
    (tr := tr) hc hχ0 hχ.le hk1 hkm2 hm hδ hδk hG0 htrdef
  have hwin : (tr - k) * (√(G / (3 / 4 * c * (m * k) ^ 2)) * |ψ 1|)
      ≤ (tr - k) * (G * √(4 * K / (3 * c)) / (m * k)) :=
    mul_le_mul_of_nonneg_left hw (by linarith)
  linarith

set_option maxHeartbeats 1000000 in
/-- **An edge pair with `σ`-free envelopes** (`sL < 10km`, `L = (c² − χ)/c²`), at `δ = 1/(s m)`. -/
theorem edge_mono {c χ G K Ξ k m b s : ℝ} {ψ u : ℝ → ℝ}
    (hc : 1 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2)
    (hk1 : 1 ≤ k) (hkm2 : 2 ≤ k * m) (hm : 1 ≤ m) (hs1 : 1 ≤ s) (hreg : s * ((c ^ 2 - χ) / c ^ 2) < 10 * (k * m))
    (hrb : k + 2 ≤ b) (hhi : m * b ≤ Ξ)
    (hψ : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hG : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χ) ψ u ξ ≤ G) (hG0 : 0 ≤ G)
    (hcont : ContinuousOn ψ (Icc 1 Ξ)) (hedge : ∀ ξ ∈ Icc 1 Ξ, |ψ ξ| ≤ |ψ 1|) (hedge1 : ψ 1 ^ 2 ≤ K * G) :
    |∫ t in k..b, ψ (m * t) * ψ (1 / k * t)|
      ≤ G * (23 / 3 * √(4 * K / (3 * c)) / (s * k * m ^ 2) + 128 / (9 * √3) * s / (c ^ 2 * k * m ^ 2)
        + 32 * √3 / 9 * √(23 / 3) * √s / (c ^ 2 * √k * (m * √m))) := by
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
  set L := (c ^ 2 - χ) / c ^ 2 with hL
  have hL0 : 0 ≤ L := div_nonneg (by linarith) (by positivity)
  have hoff := sqrtTp_sub_le hc0 hk0 hm0 hkm2 hχ0 hχ.le
  rw [← hL] at hoff
  have h1 : 2 / 3 * L / (k * m ^ 2) ≤ 20 / 3 / (s * m) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hlen : tr - k ≤ 23 / 3 / (s * m) := by
    have : 23 / 3 / (s * m) = 20 / 3 / (s * m) + 1 / (s * m) := by ring
    rw [htr]; linarith
  have hsm1 : 1 ≤ s * m := by nlinarith
  have hS := sqrtS_sub_le hk0 hm0
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
  have key := pairB_le (δ := 1 / (s * m)) (tr := tr) (b := b) (ξ₁ := min (tr / k) 2) (K := K)
    hc0 hχ0 hχ hk1 hkm2 hm him hδk htr (by linarith) hξ₁ (min_le_left _ _) htrk
    hhi hbk (fun ξ hξ => hψ ξ (hsub hξ)) (fun ξ hξ => hu ξ (hsub hξ)) (fun ξ hξ => hG ξ (hsub hξ))
    hG0 hcont hedge hedge1
  have hsm : 0 < √m := sqrt_pos.mpr hm0
  have hsk : 0 < √k := sqrt_pos.mpr hk0
  have hss : 0 < √s := sqrt_pos.mpr hs0
  have hsq : √(tr - k) ≤ √(23 / 3) / (√s * √m) := by
    have : √(23 / 3) / (√s * √m) = √(23 / 3 / (s * m)) := by
      rw [sqrt_div' _ (by positivity : 0 ≤ s * m), sqrt_mul hs0.le]
    rw [this]; exact Real.sqrt_le_sqrt hlen
  set Ac := √(4 * K / (3 * c)) with hAc
  have hAc0 : 0 ≤ Ac := sqrt_nonneg _
  have hw : (tr - k) * (G * Ac / (m * k)) ≤ 23 / 3 / (s * m) * (G * Ac / (m * k)) :=
    mul_le_mul_of_nonneg_right hlen (by positivity)
  have hr : 16 / 9 * G * (8 * k ^ 2 / (√3 * m) + 2 * √3 * k ^ 2 * √k * √(tr - k))
        / (m ^ 2 * c ^ 2 * k ^ 3 * (1 / (s * m)))
      ≤ 16 / 9 * G * (8 * k ^ 2 / (√3 * m) + 2 * √3 * k ^ 2 * √k * (√(23 / 3) / (√s * √m)))
        / (m ^ 2 * c ^ 2 * k ^ 3 * (1 / (s * m))) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 2 * √3 * k ^ 2 * √k)
    linarith
  have e1 : 23 / 3 / (s * m) * (G * Ac / (m * k)) = G * (23 / 3 * Ac / (s * k * m ^ 2)) := by field_simp
  have e2 : 16 / 9 * G * (8 * k ^ 2 / (√3 * m) + 2 * √3 * k ^ 2 * √k * (√(23 / 3) / (√s * √m)))
        / (m ^ 2 * c ^ 2 * k ^ 3 * (1 / (s * m)))
      = G * (128 / (9 * √3) * s / (c ^ 2 * k * m ^ 2) + 32 * √3 / 9 * √(23 / 3) * √s / (c ^ 2 * √k * (m * √m))) := by
    obtain ⟨p, hp, hkp⟩ : ∃ p, 0 < p ∧ k = p ^ 2 := ⟨√k, hsk, (sq_sqrt hk0.le).symm⟩
    obtain ⟨q, hq, hmq⟩ : ∃ q, 0 < q ∧ m = q ^ 2 := ⟨√m, hsm, (sq_sqrt hm0.le).symm⟩
    obtain ⟨r, hr0, hsr⟩ : ∃ r, 0 < r ∧ s = r ^ 2 := ⟨√s, hss, (sq_sqrt hs0.le).symm⟩
    rw [show √k = p by rw [hkp, sqrt_sq hp.le], show √m = q by rw [hmq, sqrt_sq hq.le],
      show √s = r by rw [hsr, sqrt_sq hr0.le], hkp, hmq, hsr]
    field_simp; ring
  have e3 : G * (23 / 3 * Ac / (s * k * m ^ 2) + 128 / (9 * √3) * s / (c ^ 2 * k * m ^ 2)
        + 32 * √3 / 9 * √(23 / 3) * √s / (c ^ 2 * √k * (m * √m)))
      = G * (23 / 3 * Ac / (s * k * m ^ 2))
        + G * (128 / (9 * √3) * s / (c ^ 2 * k * m ^ 2) + 32 * √3 / 9 * √(23 / 3) * √s / (c ^ 2 * √k * (m * √m))) := by
    ring
  rw [e3]; linarith

end Cvs.L2a.SigmaFreeEdgePairMonomials
