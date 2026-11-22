import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BandTransferBandForm
import Cvs.L2a.BandTransferKernelForm
import Cvs.L2a.OrbitGapIntegerM
import Cvs.L2a.QIdentityCutPoint
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RungExactOrthogonality

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The r-scaled band transfer

`σ_j` is linear and monotone in `N ≥ 0`, and `τ̂` is monotone and 1-homogeneous, so `N_j ≤ N̄·j!/r^j` gives
`τ̂(N) ≤ N̄·τ̂_r`. A pole `A/(p + qv)` at distance `≥ D` from the band has `N_j = ‖A‖j!|q|^j/D^{j+1}`. Folded into
`BandTransferBandForm`'s band form: `‖Σa S‖² ≤ ((2π)⁻¹∫_B|μ|² + c(2κ_S/π)δN₀²)W + cN̄²(2τ̂_r√((ΔY + 2κ_Sδ)G/π) + τ̂_r²G)∫₁^∞Φ²`.
-/

namespace Cvs.L2a.ScaledBandTransfer

open Complex Set MeasureTheory Cvs.L2a.AngularProlateTailPositive Cvs.L2a.OrbitGapIntegerM Cvs.L2a.BandTransferKernelForm Cvs.L2a.BandTransferBandForm
open scoped Real ComplexConjugate

/-! ### `σ_j` and `τ̂` in the multiplier norms -/

theorem varsig_nonneg (i : ℕ) : 0 ≤ varsig i := by
  unfold varsig; split <;> exact Real.sqrt_nonneg _

/-- `σ_j` is monotone in `N`, given `δ ≥ 0`. -/
theorem sigmaB_mono {dY δ : ℝ} (hδ : 0 ≤ δ) {N N' : ℕ → ℝ} {j : ℕ} (h : ∀ i ≤ j, N i ≤ N' i) :
    sigmaB dY δ N j ≤ sigmaB dY δ N' j := by
  unfold sigmaB
  refine add_le_add (mul_le_mul_of_nonneg_left (h j le_rfl) (Real.sqrt_nonneg _))
    (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) zero_le_two)
  have := varsig_nonneg i
  exact mul_le_mul_of_nonneg_left (h _ (Nat.sub_le _ _)) (by positivity)

/-- `σ_j` is linear in `N`; this generalises `Cvs.L2a.BandTransferBandForm.sigmaB_const`. -/
theorem sigmaB_smul (dY δ a : ℝ) (N : ℕ → ℝ) (j : ℕ) :
    sigmaB dY δ (fun i => a * N i) j = a * sigmaB dY δ N j := by
  have h : ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * varsig i * (√δ / δ ^ i) * (a * N (j - i))
      = a * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * varsig i * (√δ / δ ^ i) * N (j - i) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  unfold sigmaB
  rw [h]; ring

theorem sigmaB_nonneg {dY δ : ℝ} (hδ : 0 ≤ δ) {N : ℕ → ℝ} {j : ℕ} (h : ∀ i ≤ j, 0 ≤ N i) :
    0 ≤ sigmaB dY δ N j := by
  unfold sigmaB
  refine add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (h j le_rfl))
    (mul_nonneg zero_le_two (Finset.sum_nonneg fun i _ => ?_))
  have := varsig_nonneg i
  have := h _ (Nat.sub_le j i)
  positivity

/-- `τ̂ ≥ 0` for `N ≥ 0`. -/
theorem tauHat_nonneg {c x₀ d δ : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (hxd : 1 < x₀ - d) (hδ : 0 ≤ δ)
    {N : ℕ → ℝ} (h0 : ∀ j ≤ 3, 0 ≤ N j) : 0 ≤ tauHat c x₀ d δ N := by
  have := betaW_nonneg hxd
  have := chirpW_nonneg hd hxd
  have := sigmaB_nonneg (dY := Ymax x₀ - 1) hδ (j := 3) h0
  unfold tauHat
  positivity

/-- `τ̂` is monotone in `0 ≤ N`. -/
theorem tauHat_mono {c x₀ d δ : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (hxd : 1 < x₀ - d) (hδ : 0 ≤ δ)
    {N N' : ℕ → ℝ} (h0 : ∀ j ≤ 3, 0 ≤ N j) (h : ∀ j ≤ 3, N j ≤ N' j) :
    tauHat c x₀ d δ N ≤ tauHat c x₀ d δ N' := by
  have := betaW_nonneg hxd
  have := chirpW_nonneg hd hxd
  have hk : ∀ k ≤ 3, 0 ≤ sigmaB (Ymax x₀ - 1) δ N k ∧
      sigmaB (Ymax x₀ - 1) δ N k ≤ sigmaB (Ymax x₀ - 1) δ N' k := fun k hk =>
    ⟨sigmaB_nonneg hδ fun i hi => h0 i (hi.trans hk), sigmaB_mono hδ fun i hi => h i (hi.trans hk)⟩
  obtain ⟨a1, b1⟩ := hk 1 (by norm_num)
  obtain ⟨a2, b2⟩ := hk 2 (by norm_num)
  obtain ⟨a3, b3⟩ := hk 3 le_rfl
  have := a1.trans b1
  have := a2.trans b2
  have := a3.trans b3
  unfold tauHat
  gcongr

/-- `τ̂` is 1-homogeneous in `N`; this generalises `Cvs.L2a.BandTransferBandForm.tauHat_const`. -/
theorem tauHat_smul {c x₀ d δ a : ℝ} (ha : 0 ≤ a) (N : ℕ → ℝ) :
    tauHat c x₀ d δ (fun j => a * N j) = a * tauHat c x₀ d δ N := by
  unfold tauHat
  simp only [sigmaB_smul]
  have e : ∀ x y : ℝ, √(a * x * (a * y)) = a * √(x * y) := fun x y => by
    rw [show a * x * (a * y) = a ^ 2 * (x * y) by ring, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq ha]
  rw [e, e]; ring

/-- **The r-scaled fold**: `0 ≤ N_j ≤ N̄·j!/r^j` for `j ≤ 3` gives `τ̂(N) ≤ N̄·τ̂(j ↦ j!/r^j)`. -/
theorem tauHat_le_scaled {c x₀ d δ r Nb : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (hxd : 1 < x₀ - d) (hδ : 0 ≤ δ)
    {N : ℕ → ℝ} (h0 : ∀ j ≤ 3, 0 ≤ N j) (h : ∀ j ≤ 3, N j ≤ Nb * ((j.factorial : ℝ) / r ^ j)) :
    tauHat c x₀ d δ N ≤ Nb * tauHat c x₀ d δ (fun j => (j.factorial : ℝ) / r ^ j) := by
  have hNb : 0 ≤ Nb := by
    have := (h0 0 (by norm_num)).trans (h 0 (by norm_num))
    simpa using this
  rw [← tauHat_smul hNb]
  exact tauHat_mono hc hd hxd hδ h0 h

/-! ### Band multipliers: poles and sums -/

/-- The `j`-th derivative `A·(−q)^j j!/(p + qv)^{j+1}` of `A/(p + qv)`. -/
noncomputable def poleD (A : ℂ) (p q : ℝ) (j : ℕ) (v : ℝ) : ℂ :=
  A * (((-q) ^ j * (j.factorial : ℝ) / (p + q * v) ^ (j + 1) : ℝ) : ℂ)

theorem poleD_zero (A : ℂ) (p q v : ℝ) : poleD A p q 0 v = A / ((p + q * v : ℝ) : ℂ) := by
  simp [poleD, div_eq_mul_inv]

theorem hasDerivAt_poleD (A : ℂ) (p q : ℝ) (j : ℕ) {v : ℝ} (hv : p + q * v ≠ 0) :
    HasDerivAt (poleD A p q j) (poleD A p q (j + 1) v) v := by
  have h1 := (((hasDerivAt_id v).const_mul q).const_add p).pow (j + 1)
  have h2 := (h1.inv (by simp [hv])).const_mul ((-q) ^ j * (j.factorial : ℝ))
  have h3 := (h2.ofReal_comp).const_mul A
  refine (h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by
    simp [poleD, div_eq_mul_inv])).congr_deriv ?_
  simp only [poleD, id, Nat.add_sub_cancel, Pi.pow_apply, mul_one]
  congr 2
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem norm_poleD_le (A : ℂ) (p q : ℝ) (j : ℕ) {v D : ℝ} (hD : 0 < D) (h : D ≤ |p + q * v|) :
    ‖poleD A p q j v‖ ≤ ‖A‖ * j.factorial * |q| ^ j / D ^ (j + 1) := by
  rw [poleD, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_pow, abs_neg,
    Nat.abs_cast]
  have hp : 0 < |p + q * v| := hD.trans_le h
  have : |q| ^ j * (j.factorial : ℝ) / |p + q * v| ^ (j + 1) ≤ |q| ^ j * j.factorial / D ^ (j + 1) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ hD.le h _)
  calc ‖A‖ * (|q| ^ j * (j.factorial : ℝ) / |p + q * v| ^ (j + 1))
      ≤ ‖A‖ * (|q| ^ j * j.factorial / D ^ (j + 1)) := mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = _ := by ring

/-- **A pole off the band**: `A/(p + qv)` with `|p + qv| ≥ D > 0` on the band region is a band multiplier with
`N_j = ‖A‖j!|q|^j/D^{j+1}`. -/
theorem isBandMult_pole {A : ℂ} {p q D δ Y : ℝ} (hD : 0 < D) (hpq : ∀ v ∈ bandRg δ Y, D ≤ |p + q * v|) :
    IsBandMult (fun v => A / ((p + q * v : ℝ) : ℂ)) (poleD A p q 1) (poleD A p q 2) (poleD A p q 3) δ Y
      (fun j => ‖A‖ * j.factorial * |q| ^ j / D ^ (j + 1)) := by
  have hne : ∀ v ∈ bandRg δ Y, p + q * v ≠ 0 := fun v hv h0 => by
    have := hpq v hv; rw [h0, abs_zero] at this; linarith
  have e0 : (fun v => A / ((p + q * v : ℝ) : ℂ)) = poleD A p q 0 := funext fun v => (poleD_zero A p q v).symm
  rw [e0]
  exact
    { d0 := fun v hv => hasDerivAt_poleD A p q 0 (hne v hv)
      d1 := fun v hv => hasDerivAt_poleD A p q 1 (hne v hv)
      d2 := fun v hv => hasDerivAt_poleD A p q 2 (hne v hv)
      c3 := fun v hv => (hasDerivAt_poleD A p q 3 (hne v hv)).continuousAt.continuousWithinAt
      bd := fun v hv => ⟨norm_poleD_le A p q 0 hD (hpq v hv), norm_poleD_le A p q 1 hD (hpq v hv),
        norm_poleD_le A p q 2 hD (hpq v hv), norm_poleD_le A p q 3 hD (hpq v hv)⟩ }

/-- **Sums of band multipliers** add their bounds. -/
theorem IsBandMult.add {μ μ₁ μ₂ μ₃ ν ν₁ ν₂ ν₃ : ℝ → ℂ} {δ Y : ℝ} {N N' : ℕ → ℝ}
    (hμ : IsBandMult μ μ₁ μ₂ μ₃ δ Y N) (hν : IsBandMult ν ν₁ ν₂ ν₃ δ Y N') :
    IsBandMult (fun v => μ v + ν v) (fun v => μ₁ v + ν₁ v) (fun v => μ₂ v + ν₂ v) (fun v => μ₃ v + ν₃ v) δ Y
      (fun j => N j + N' j) where
  d0 v hv := (hμ.d0 v hv).add (hν.d0 v hv)
  d1 v hv := (hμ.d1 v hv).add (hν.d1 v hv)
  d2 v hv := (hμ.d2 v hv).add (hν.d2 v hv)
  c3 := hμ.c3.add hν.c3
  bd v hv := by
    obtain ⟨a0, a1, a2, a3⟩ := hμ.bd v hv
    obtain ⟨b0, b1, b2, b3⟩ := hν.bd v hv
    exact ⟨(norm_add_le _ _).trans (add_le_add a0 b0), (norm_add_le _ _).trans (add_le_add a1 b1),
      (norm_add_le _ _).trans (add_le_add a2 b2), (norm_add_le _ _).trans (add_le_add a3 b3)⟩

/-- A band multiplier's bounds may be raised. -/
theorem IsBandMult.mono {μ μ₁ μ₂ μ₃ : ℝ → ℂ} {δ Y : ℝ} {N N' : ℕ → ℝ} (hμ : IsBandMult μ μ₁ μ₂ μ₃ δ Y N)
    (h : ∀ j ≤ 3, N j ≤ N' j) : IsBandMult μ μ₁ μ₂ μ₃ δ Y N' where
  d0 := hμ.d0
  d1 := hμ.d1
  d2 := hμ.d2
  c3 := hμ.c3
  bd v hv := by
    obtain ⟨a0, a1, a2, a3⟩ := hμ.bd v hv
    exact ⟨a0.trans (h 0 (by norm_num)), a1.trans (h 1 (by norm_num)), a2.trans (h 2 (by norm_num)),
      a3.trans (h 3 le_rfl)⟩

/-! ### The real part of a band sum -/

/-- **`Re Σaₙ Sₙ[μ] = Σaₙ Sₙ[μ_s]`** for `μ(ξ) = μ̃(ξ/c)`, with `μ_s = Cvs.L2a.QIdentityCutPoint.muSym`. -/
theorem smp_sPart {ι : Type} [Fintype ι] (a : ι → ℝ) (μ : ℝ → ℂ) (c : ℝ) (χ : ι → ℝ) (g : ι → ℝ → ℝ)
    (x₀ : ℝ) :
    (((∑ i, (a i : ℂ) * smp (fun ξ => μ (ξ / c)) c (χ i) (g i) x₀).re : ℝ) : ℂ)
      = ∑ i, (a i : ℂ) * smp (fun ξ => Cvs.L2a.QIdentityCutPoint.muSym μ (ξ / c)) c (χ i) (g i) x₀ := by
  have hs : Cvs.L2a.QIdentityCutPoint.muSym (fun ξ => μ (ξ / c))
      = fun ξ => Cvs.L2a.QIdentityCutPoint.muSym μ (ξ / c) := by
    funext ξ; simp [Cvs.L2a.QIdentityCutPoint.muSym, neg_div]
  rw [Complex.re_sum, ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_ofReal_mul, ofReal_mul, Cvs.L2a.QIdentityCutPoint.re_smp, hs]

/-! ### LBT-h (B), r-scaled -/

/-- **LBT-h (B), r-scaled**: if `N_j ≤ N̄·j!/r^j` for `j ≤ 3`, then `‖Σaₙ Sₙ[μ]‖² ≤ ((2π)⁻¹∫_B|μ|² + c(2κ_S/π)δN₀²)·W
+ c·N̄²·(2τ̂_r√((ΔY + 2κ_Sδ)G/π) + τ̂_r²·G)·∫₁^∞Φ²` with `τ̂_r = τ̂(j ↦ j!/r^j)`, `G = 6#ι/(c(x₀²−1))`. -/
theorem lbt_band_scaled {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    {X x₀ d δ r Nb : ℝ} {μ μ₁ μ₂ μ₃ : ℝ → ℂ} {N : ℕ → ℝ} {B : Set ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχi : Function.Injective χ)
    (hX : 2 ≤ X) (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2) (hx₀ : x₀ ∈ Icc (6 / 5 : ℝ) X)
    (hd : 0 < d) (hxd : 1 < x₀ - d) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hμ : IsBandMult μ μ₁ μ₂ μ₃ δ (Ymax x₀) N) (hNb : ∀ j ≤ 3, N j ≤ Nb * ((j.factorial : ℝ) / r ^ j))
    (hB : MeasurableSet B) (hBc : ∀ ξ, |ξ| ∈ Icc c (c * Ymax x₀) → ξ ∈ B)
    (hBi : IntegrableOn (fun ξ => ‖μ (ξ / c)‖ ^ 2) B) :
    ‖∑ i, (a i : ℂ) * smp (fun ξ => μ (ξ / c)) c (χ i) (g i) x₀‖ ^ 2
      ≤ ((2 * π)⁻¹ * (∫ ξ in B, ‖μ (ξ / c)‖ ^ 2) + c * (2 * (181 / 462) / π * δ * N 0 ^ 2))
          * (∫ x in (x₀ - d)..(x₀ + d), (∑ i, a i * psi c (g i) x) ^ 2)
        + c * Nb ^ 2 * (2 * tauHat c x₀ d δ (fun j => (j.factorial : ℝ) / r ^ j)
            * √((Ymax x₀ - 1 + 2 * (181 / 462) * δ) * (6 * (Fintype.card ι : ℝ) / (c * (x₀ ^ 2 - 1))) / π)
          + tauHat c x₀ d δ (fun j => (j.factorial : ℝ) / r ^ j) ^ 2
            * (6 * (Fintype.card ι : ℝ) / (c * (x₀ ^ 2 - 1))))
          * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hx1 : 1 < x₀ := by linarith
  have hgen := lbt_band_gen a hg hg₁ hg₂c hang hc hχ0 hχc hX hM hx₀ hd hxd hδ hδ1 hμ hB hBc hBi
  obtain ⟨n0, n1, n2, n3⟩ := N_nonneg hδ (one_le_Ymax hx1) hμ
  have h0 : ∀ j ≤ 3, 0 ≤ N j := fun j hj => by
    interval_cases j
    exacts [n0, n1, n2, n3]
  have hN0 : N 0 ≤ Nb := by simpa using hNb 0 (by norm_num)
  set W := ∫ x in (x₀ - d)..(x₀ + d), (∑ i, a i * psi c (g i) x) ^ 2 with hWdef
  set P := ∑ i, a i ^ 2 * (∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2) with hPdef
  set Q := ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 with hQdef
  set G := 6 * (Fintype.card ι : ℝ) / (c * (x₀ ^ 2 - 1)) with hGdef
  set S := √((Ymax x₀ - 1 + 2 * (181 / 462) * δ) * G / π) with hSdef
  set τ := tauHat c x₀ d δ N with hτdef
  set τr := tauHat c x₀ d δ (fun j => (j.factorial : ℝ) / r ^ j) with hτrdef
  have hτ0 : 0 ≤ τ := tauHat_nonneg hc0.le hd.le hxd hδ.le h0
  have hττ : τ ≤ Nb * τr := tauHat_le_scaled hc0.le hd.le hxd hδ.le h0 hNb
  have hG : 0 ≤ G := by have : 0 < x₀ ^ 2 - 1 := by nlinarith
                        positivity
  have hW : 0 ≤ W := intervalIntegral.integral_nonneg (by linarith) fun x _ => sq_nonneg _
  have hP : 0 ≤ P := Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _)
    (intervalIntegral.integral_nonneg (by linarith) fun x _ => sq_nonneg _)
  -- `W ≤ Q` and `P ≤ Q` by the window's position and by orthogonality on `(1, ∞)`
  have hψ2 : ∀ i, IntegrableOn (fun x => psi c (g i) x ^ 2) (Ioi 1) := fun i =>
    (memLp_two_iff_integrable_sq ((Cvs.Prolate.Gram.RungGramFloorAtInfinity.rung_system (hg i) (hg₁ i) (hg₂c i)
      (hang i)).2.2.1.aestronglyMeasurable)).mp (Cvs.Prolate.RungExactOrthogonality.memLp_psi (hg i) (hg₁ i) (hg₂c i)
      (hang i) hc0)
  have hΦ2 : IntegrableOn (fun x => (∑ i, a i * psi c (g i) x) ^ 2) (Ioi 1) := by
    have hm : MemLp (fun x => ∑ i, a i * psi c (g i) x) 2 (volume.restrict (Ioi 1)) := by
      have := memLp_finsetSum' Finset.univ fun i _ =>
        (Cvs.Prolate.RungExactOrthogonality.memLp_psi (hg i) (hg₁ i) (hg₂c i) (hang i) hc0).const_mul (a i)
      refine this.ae_eq (ae_of_all _ fun x => ?_)
      simp [Finset.sum_apply]
    exact (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mp hm
  have hWQ : W ≤ Q := by
    rw [hWdef, intervalIntegral.integral_of_le (by linarith)]
    exact setIntegral_mono_set hΦ2 (ae_of_all _ fun x => sq_nonneg _)
      (ae_of_all _ fun x hx => show 1 < x by linarith [hx.1])
  have hPQ : P ≤ Q := by
    rw [hQdef, Cvs.Prolate.RungExactOrthogonality.integral_span_sq a hg hg₁ hg₂c hang hc0 hχi]
    refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    rw [intervalIntegral.integral_of_le (by linarith)]
    exact setIntegral_mono_set (hψ2 i) (ae_of_all _ fun x => sq_nonneg _)
      (ae_of_all _ fun x hx => show 1 < x from hx.1)
  have hWP : √(W * P) ≤ Q := by
    calc √(W * P) ≤ √(Q * Q) := Real.sqrt_le_sqrt (mul_le_mul hWQ hPQ hP (hW.trans hWQ))
      _ = Q := Real.sqrt_mul_self (hW.trans hWQ)
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hQ : 0 ≤ Q := hW.trans hWQ
  have hNbτ : 0 ≤ Nb * τr := hτ0.trans hττ
  have hNb0 : 0 ≤ Nb := n0.trans hN0
  -- the cross term and the square term
  have k1 : 2 * N 0 * τ * S * √(W * P) ≤ 2 * Nb * (Nb * τr) * S * Q := by
    have a1 : N 0 * τ ≤ Nb * (Nb * τr) := mul_le_mul hN0 hττ hτ0 hNb0
    have a2 : N 0 * τ * S ≤ Nb * (Nb * τr) * S := mul_le_mul_of_nonneg_right a1 hS
    have a3 : N 0 * τ * S * √(W * P) ≤ Nb * (Nb * τr) * S * Q :=
      mul_le_mul a2 hWP (Real.sqrt_nonneg _) (by positivity)
    nlinarith
  have k2 : τ ^ 2 * G * P ≤ (Nb * τr) ^ 2 * G * Q := by
    have a1 : τ ^ 2 ≤ (Nb * τr) ^ 2 := pow_le_pow_left₀ hτ0 hττ 2
    exact mul_le_mul (mul_le_mul_of_nonneg_right a1 hG) hPQ hP (by positivity)
  refine hgen.trans ?_
  have : c * (2 * (181 / 462) / π * δ * N 0 ^ 2 * W + 2 * N 0 * τ * S * √(W * P) + τ ^ 2 * G * P)
      ≤ c * (2 * (181 / 462) / π * δ * N 0 ^ 2 * W + 2 * Nb * (Nb * τr) * S * Q + (Nb * τr) ^ 2 * G * Q) :=
    mul_le_mul_of_nonneg_left (by linarith) hc0.le
  refine (add_le_add le_rfl this).trans (le_of_eq ?_)
  ring

end Cvs.L2a.ScaledBandTransfer
