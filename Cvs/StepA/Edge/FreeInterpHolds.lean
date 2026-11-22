import Mathlib
import Cvs.StepA.Edge.CaseInfinityJointRates
import Cvs.StepA.Edge.DbarTransplantHolds
import Cvs.StepA.Edge.DeepPointBlaschkeCount
import Cvs.StepA.Edge.DeepSetZeroSums
import Cvs.StepA.Edge.ExpSumWindowTransplant
import Cvs.StepA.Edge.OtherDeepPointsBlaschke
import Cvs.StepA.Edge.WindowCoshTransformDuality
import Cvs.StepA.LowEigenvalueCountZeros
import Cvs.Upstream.ExpSumBlaschkeProduct
import Cvs.Upstream.ExpSumContourInterpolation
import Cvs.Upstream.ExpSumTwoEndedError
import Cvs.Upstream.HardyCorrectedInterpolation
import Cvs.Upstream.PointInterpolationHardyDatum
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `FreeInterp` holds

For a deep `σ` below the cutoff, the Hardy datum `F = B_{others}(A/(z + w̄) + Ā/(z + w))` with `F(w) = ie^{−wT}`
is corrected on the deep points (Cvs.Upstream.HardyCorrectedInterpolation) and turned into a window class (Cvs.StepA.Edge.ExpSumWindowTransplant): `F_v` vanishes on the other deep
points, `F_v(w) = i`, and `‖v‖² ≤ 64δx^{−δ}/((1 − g)²β_σ²)` with `OtherDeepPointsBlaschke`'s `β_σ`. This is `CaseInfinityJointRates`'s `FreeInterp` with
`α = bexp + 1` and `β = β_σ/2^{1/2}` (caseinf-W Theorem F).
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology Finset
open scoped Interval ComplexConjugate
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.Upstream.ExpSumBlaschkeProduct (lap gram)
open Cvs.Upstream.ExpSumTwoEndedError (err)
open Cvs.StepA.Edge.WindowCoshTransformDuality (wR PointInterp)
open Cvs.StepA.Edge.DeepSetZeroSums (deepSet mem_deepSet)
open Cvs.StepA.Edge.DeepPointBlaschkeCount (deepPts bexp)
open Cvs.StepA.Edge.DbarTransplantHolds (qq kc zc wc)
open Cvs.Upstream.PointInterpolationHardyDatum (bS datum solveA)
open Cvs.StepA.Edge.OtherDeepPointsBlaschke (others kS)

namespace Cvs.StepA.Edge.FreeInterpHolds
open Cvs.ZeroCounting

/-- **The good `x`**: for a cutoff at `ε₂` with `(bexp + 1)ε₂ < δ_D/8`, eventually `x ≥ 1`, `H(x) ≥ M₀`,
`H(x) > 0` and `0 ≤ q ≤ ½`. -/
theorem eventually_good {δD ε₂ : ℝ} (hδ : 0 < δD) (hδ' : δD < 1 / 2) (hε₂ : 0 < ε₂)
    (hαε : ((bexp : ℝ) + 1) * ε₂ < δD / 8) {H : ℕ → ℝ} (hH : Cvs.StepA.Edge.CaseInfinityJointRates.Cutoff ε₂ H) (M₀ : ℝ) :
    ∀ᶠ x : ℕ in atTop, 1 ≤ x ∧ M₀ ≤ H x ∧ 0 < H x ∧ qq x δD (H x) ≤ 1 / 2 ∧ 0 ≤ qq x δD (H x) := by
  have hpi := Real.pi_pos
  have hs : 0 < √(δD / 2) := Real.sqrt_pos.2 (by linarith)
  set C₀ := 24 * 17 ^ bexp / (2 * Real.pi * √(δD / 2)) with hC₀
  have hneg : 0 < δD / 8 - ((bexp : ℝ) + 1) * ε₂ := by linarith
  have hev : ∀ᶠ x : ℕ in atTop,
      2 * C₀ / √(δD / 2) * (x : ℝ) ^ (-(δD / 8 - ((bexp : ℝ) + 1) * ε₂)) ≤ 1 / 2 := by
    have h1 : Tendsto (fun x : ℕ => (x : ℝ) ^ (-(δD / 8 - ((bexp : ℝ) + 1) * ε₂))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hneg).comp tendsto_natCast_atTop_atTop
    have h2 := h1.const_mul (2 * C₀ / √(δD / 2))
    rw [mul_zero] at h2
    exact (h2.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono fun x h => h.le
  have hbig : ∀ᶠ x : ℕ in atTop, M₀ ≤ (x : ℝ) ^ ε₂ :=
    ((tendsto_rpow_atTop hε₂).comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop M₀)
  filter_upwards [hH, hev, hbig, eventually_ge_atTop 1] with x hHx hq hbx hx
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  set X := (x : ℝ) ^ ε₂ with hXdef
  have hX : 1 ≤ X := Real.one_le_rpow hx1 hε₂.le
  have hkc := Cvs.StepA.Edge.DbarTransplantHolds.kc_le hδ hδ' hX hHx.1 hHx.2
  have hXα : X ^ (bexp + 1) = (x : ℝ) ^ (((bexp : ℝ) + 1) * ε₂) := by
    rw [hXdef, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; push_cast; ring_nf
  have hkc' : kc δD (H x) ≤ C₀ * (x : ℝ) ^ (((bexp : ℝ) + 1) * ε₂) := by rw [← hXα]; exact hkc
  have hkc0 : 0 ≤ kc δD (H x) := by
    unfold kc; rw [Cvs.StepA.Edge.DbarTransplantHolds.zc_re, Cvs.StepA.Edge.DbarTransplantHolds.zc_im, Cvs.StepA.Edge.DbarTransplantHolds.wc_re, Cvs.StepA.Edge.DbarTransplantHolds.wc_im]
    refine div_nonneg (by nlinarith [hHx.1]) ?_
    have : 0 ≤ √(2 * (δD / 4)) := Real.sqrt_nonneg _
    positivity
  refine ⟨hx, hbx.trans hHx.1, by linarith [hHx.1], ?_, ?_⟩
  · unfold qq
    rw [Cvs.StepA.Edge.DbarTransplantHolds.zc_re]
    have he : Real.exp (-(δD / 4 * (Real.log x / 2))) = (x : ℝ) ^ (-(δD / 8)) := by
      rw [Real.rpow_def_of_pos hx0]; congr 1; ring
    have hz : √(2 * (δD / 4)) = √(δD / 2) := by congr 1; ring
    rw [he, hz]
    refine le_trans ?_ hq
    have e : 2 * C₀ / √(δD / 2) * (x : ℝ) ^ (-(δD / 8 - ((bexp : ℝ) + 1) * ε₂))
        = C₀ * (x : ℝ) ^ (((bexp : ℝ) + 1) * ε₂) * (2 * (x : ℝ) ^ (-(δD / 8)) / √(δD / 2)) := by
      rw [show -(δD / 8 - ((bexp : ℝ) + 1) * ε₂) = ((bexp : ℝ) + 1) * ε₂ + -(δD / 8) by ring,
        Real.rpow_add hx0]
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right hkc' (by positivity)
  · unfold qq; rw [Cvs.StepA.Edge.DbarTransplantHolds.zc_re]
    have : 0 ≤ √(2 * (δD / 4)) := Real.sqrt_nonneg _
    exact mul_nonneg hkc0 (by positivity)

/-- **Point interpolation at one `x`** (caseinf-W Theorem F (ii)–(v)): for a deep `σ` below `H` and `q ≤ ½`,
`PointInterp` holds at `w_σ` for the deep points with bound `64δx^{−δ}/((1 − δ/|w_σ|)²β_σ²)`. -/
theorem pointInterp_at {x : ℕ} (hx : 1 ≤ x) {δD H : ℝ} (hδ : 0 < δD) (hδ' : δD < 1 / 2) (hH : 0 < H)
    (hq : qq x δD H ≤ 1 / 2) {σ : nonTrivialZeroSet} (hσD : δD ≤ |Cvs.GaussKernel.del σ|)
    (hσH : |(σ : ℂ).im| ≤ H) :
    PointInterp x (wR '' (deepSet δD H : Set nonTrivialZeroSet)) (wR σ)
      (64 * |Cvs.GaussKernel.del σ| * (x : ℝ) ^ (-|Cvs.GaussKernel.del σ|)
        / ((1 - |Cvs.GaussKernel.del σ| / ‖wR σ‖) ^ 2 * Real.exp (-(kS σ / 2)) ^ 2)) := by
  classical
  set w := wR σ with hwdef
  set δ := |Cvs.GaussKernel.del σ| with hδdef
  set T : ℝ := Real.log x / 2 with hTdef
  have hT0 : 0 ≤ T := by have := Real.log_natCast_nonneg x; positivity
  set Λ := deepPts δD H with hΛ
  set S := others δD H σ with hS
  have hwre : w.re = δ := Cvs.StepA.Edge.WindowCoshTransformDuality.wR_re σ
  have hw0 : 0 < w.re := by rw [hwre]; linarith
  have him : w.im ≠ 0 := by
    have h := Cvs.StepA.Edge.WindowCoshTransformDuality.abs_wR_im σ
    intro h0; rw [← hwdef, h0, abs_zero] at h
    exact Cvs.StepA.LowEigenvalueCountZeros.im_ne_zero σ (abs_eq_zero.1 h.symm)
  have hwΛ : w ∈ Λ := Finset.mem_image.2 ⟨σ, mem_deepSet.2 ⟨hσH, hσD⟩, rfl⟩
  have hwbΛ : conj w ∈ Λ := Cvs.StepA.Edge.DeepPointBlaschkeCount.conj_mem_deepPts hwΛ
  have hSmem : ∀ ζ, ζ ∈ S ↔ ζ ∈ Λ ∧ ζ ≠ w ∧ ζ ≠ conj w := by
    intro ζ
    simp only [hS, Cvs.StepA.Edge.OtherDeepPointsBlaschke.others, Finset.mem_erase]
    tauto
  have hSconj : ∀ ζ ∈ S, conj ζ ∈ S := by
    intro ζ hζ
    obtain ⟨h1, h2, h3⟩ := (hSmem ζ).1 hζ
    refine (hSmem _).2 ⟨Cvs.StepA.Edge.DeepPointBlaschkeCount.conj_mem_deepPts h1, fun h => h3 ?_, fun h => h2 ?_⟩
    · rw [← h, Complex.conj_conj]
    · rw [← Complex.conj_conj ζ, h, Complex.conj_conj]
  have hSre : ∀ ζ ∈ S, δD ≤ ζ.re := fun ζ hζ => by
    obtain ⟨_, _, _, h1, _, _⟩ := Cvs.StepA.Edge.DeepPointBlaschkeCount.deepPts_facts ((hSmem ζ).1 hζ).1; exact h1
  have hS0 : ∀ ζ ∈ S, 0 < ζ.re := fun ζ hζ => hδ.trans_le (hSre ζ hζ)
  have hβ := Cvs.StepA.Edge.OtherDeepPointsBlaschke.exp_le_norm_bS_others σ hδ H
  have hβ0 : 0 < Real.exp (-(kS σ / 2)) := Real.exp_pos _
  have hbne : bS S w ≠ 0 := norm_pos_iff.1 (hβ0.trans_le hβ)
  set c : ℂ := I * cexp (-(w * (T : ℂ))) / bS S w with hc
  set A := solveA (1 / (2 * w.re)) (1 / (2 * w)) c with hA
  set F := datum S w A with hF
  have hFw : F w = I * cexp (-(w * (T : ℂ))) := by
    rw [hF, hA, Cvs.Upstream.PointInterpolationHardyDatum.datum_at hw0 him, hc]; field_simp
  have hFwb : F (conj w) = conj (F w) := Cvs.Upstream.PointInterpolationHardyDatum.datum_conj hSconj w A w
  -- the corrected interpolation
  set p : Λ → ℂ := fun ζ => (ζ : ℂ) with hp
  have hqq : (2 * ((wc H).re - (zc δD H).re) + 2 * ((wc H).im - (zc δD H).im))
      / (2 * Real.pi * Real.exp (-((bexp : ℝ) * Real.log (5 * H + 7))) * √(2 * (zc δD H).re))
      * (2 * Real.exp (-((zc δD H).re * T)) / √(2 * (zc δD H).re)) < 1 := by
    have : qq x δD H < 1 := by linarith
    exact this
  obtain ⟨a, ha, hb⟩ := Cvs.Upstream.HardyCorrectedInterpolation.exists_solution_h2 (p := p) Subtype.val_injective (z := zc δD H) (w := wc H)
    (by simp; linarith) (by simp; linarith) (by simp; linarith)
    (fun k => Cvs.StepA.Edge.DbarTransplantHolds.inside_of_mem hδ hH.le k.2) (Real.exp_pos _)
    (fun u hu => Cvs.StepA.Edge.DeepPointBlaschkeCount.norm_blaschke_ge_onBd hδ hδ' hH.le hu) hT0 hqq hδ
    (Cvs.Upstream.PointInterpolationHardyDatum.differentiableOn_datum hSre (by rw [hwre]; exact hσD) A) (Cvs.Upstream.PointInterpolationHardyDatum.datum_dec hS0 w A)
  have hpre : ∀ i, 0 < (p i).re := fun i => by
    obtain ⟨_, _, _, h1, _, _⟩ := Cvs.StepA.Edge.DeepPointBlaschkeCount.deepPts_facts i.2; exact hδ.trans_le h1
  have hcosh : ∀ ζ ∈ Λ, Cvs.StepA.Edge.WindowCoshTransformDuality.coshT x (Cvs.StepA.Edge.ExpSumWindowTransplant.winVec x p a) ζ
      = (cexp (ζ * (T : ℂ)) * F ζ + conj (cexp (conj ζ * (T : ℂ)) * F (conj ζ))) / 2 := by
    intro ζ hζ
    obtain ⟨_, _, _, h1, _, _⟩ := Cvs.StepA.Edge.DeepPointBlaschkeCount.deepPts_facts hζ
    have hζ0 : 0 < ζ.re := hδ.trans_le h1
    rw [Cvs.StepA.Edge.ExpSumWindowTransplant.coshT_winVec x p a (fun i => Cvs.Upstream.ExpSumBlaschkeProduct.add_conj_ne_zero (hpre i) hζ0.le)
      (fun i => Cvs.Upstream.ExpSumBlaschkeProduct.add_conj_ne_zero (hpre i) (by rw [Complex.conj_re]; exact hζ0.le))]
    have e1 : lap p a ζ + err p T a ζ = F ζ := ha ⟨ζ, hζ⟩
    have e2 : lap p a (conj ζ) + err p T a (conj ζ) = F (conj ζ) :=
      ha ⟨conj ζ, Cvs.StepA.Edge.DeepPointBlaschkeCount.conj_mem_deepPts hζ⟩
    rw [e1, e2]
  refine ⟨Cvs.StepA.Edge.ExpSumWindowTransplant.winVec x p a, fun ζ hζ hne1 hne2 => ?_, ?_, ?_⟩
  · rw [← Cvs.StepA.Edge.DeepPointBlaschkeCount.coe_deepPts] at hζ
    have hζS : ζ ∈ S := (hSmem ζ).2 ⟨hζ, hne1, hne2⟩
    rw [hcosh ζ hζ, hF, Cvs.Upstream.PointInterpolationHardyDatum.datum_self hζS, Cvs.Upstream.PointInterpolationHardyDatum.datum_self (hSconj ζ hζS)]
    simp
  · rw [hcosh w hwΛ, hFwb, hFw]
    have h1 : cexp (w * (T : ℂ)) * cexp (-(w * (T : ℂ))) = 1 := by rw [← Complex.exp_add]; simp
    have h2 : conj (cexp (conj w * (T : ℂ))) = cexp (w * (T : ℂ)) := by
      rw [← Complex.exp_conj, map_mul, Complex.conj_conj, Complex.conj_ofReal]
    simp only [map_mul, Complex.conj_conj, h2]
    linear_combination (I / 2 + I / 2) * h1
  · have hv := Cvs.StepA.Edge.ExpSumWindowTransplant.norm_sq_winVec_le (ε := δD) hδ
      (fun i => by obtain ⟨_, _, _, h1, _, _⟩ := Cvs.StepA.Edge.DeepPointBlaschkeCount.deepPts_facts i.2; exact h1) x a
    have hG := Cvs.Upstream.ExpSumBlaschkeProduct.gram_re_nonneg (ε := δD) hδ
      (fun i => by obtain ⟨_, _, _, h1, _, _⟩ := Cvs.StepA.Edge.DeepPointBlaschkeCount.deepPts_facts i.2; exact h1) a
    set G := (gram p a).re
    set Iint := ∫ y : ℝ, ‖F (y * I)‖ ^ 2 with hIint
    have hb' : (1 - qq x δD H) * √G ≤ √Iint / √(2 * Real.pi) := hb
    have hI0 : 0 ≤ Iint := integral_nonneg fun y => sq_nonneg _
    have hIle : Iint ≤ 4 * Real.pi * ‖A‖ ^ 2 / δ := by
      have := Cvs.Upstream.PointInterpolationHardyDatum.integral_norm_sq_datum_le hδ hSre (by rw [hwre]; exact hσD) A
      rwa [hwre] at this
    have hpi := Real.pi_pos
    have hδ0 : 0 < δ := by linarith
    -- `G ≤ 8|A|²/δ`
    have hsG : √G ≤ 2 * (√Iint / √(2 * Real.pi)) := by
      have : (1 / 2) * √G ≤ (1 - qq x δD H) * √G :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
      linarith
    have hG8 : G ≤ 8 * ‖A‖ ^ 2 / δ := by
      have h1 : G ≤ (2 * (√Iint / √(2 * Real.pi))) ^ 2 := by
        rw [← Real.sq_sqrt hG]; exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hsG 2
      have h2 : (2 * (√Iint / √(2 * Real.pi))) ^ 2 = 4 * Iint / (2 * Real.pi) := by
        rw [mul_pow, div_pow, Real.sq_sqrt hI0, Real.sq_sqrt (by positivity)]; ring
      rw [h2] at h1
      calc G ≤ 4 * Iint / (2 * Real.pi) := h1
        _ ≤ 4 * (4 * Real.pi * ‖A‖ ^ 2 / δ) / (2 * Real.pi) := by gcongr
        _ = 8 * ‖A‖ ^ 2 / δ := by field_simp; ring
    -- `|A| ≤ |c|·2δ/(1 − g)`
    have hwn : δ < ‖w‖ := by rw [← hwre]; exact (Complex.abs_re_lt_norm.2 him).trans_le' (le_abs_self _)
    have hg1 : 0 < 1 - δ / ‖w‖ := by rw [sub_pos, div_lt_one (by linarith)]; exact hwn
    have hAle := Cvs.Upstream.PointInterpolationHardyDatum.norm_solveA_le (Cvs.Upstream.PointInterpolationHardyDatum.norm_t_lt_u hw0 him) c
    have hut : 1 / (2 * w.re) - ‖1 / (2 * w)‖ = (1 - δ / ‖w‖) / (2 * δ) := by
      rw [hwre, norm_div, norm_one, norm_mul, Complex.norm_two]; field_simp
    rw [hut, ← hA] at hAle
    have hcn : ‖c‖ ≤ Real.exp (-(δ * T)) / Real.exp (-(kS σ / 2)) := by
      rw [hc, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_exp]
      have he : (-(w * (T : ℂ))).re = -(δ * T) := by simp [hwre]
      rw [he]
      exact div_le_div_of_nonneg_left (Real.exp_pos _).le hβ0 hβ
    have hA2 : ‖A‖ ≤ Real.exp (-(δ * T)) / Real.exp (-(kS σ / 2)) / ((1 - δ / ‖w‖) / (2 * δ)) :=
      hAle.trans (div_le_div_of_nonneg_right hcn (by positivity))
    have hxT : Real.exp (-(δ * T)) ^ 2 = (x : ℝ) ^ (-δ) := by
      have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
      rw [← Real.exp_nat_mul, Real.rpow_def_of_pos hx0, hTdef]; push_cast; ring_nf
    have hAsq : ‖A‖ ^ 2 ≤ (x : ℝ) ^ (-δ) * (4 * δ ^ 2) / ((1 - δ / ‖w‖) ^ 2 * Real.exp (-(kS σ / 2)) ^ 2) := by
      refine (pow_le_pow_left₀ (norm_nonneg _) hA2 2).trans_eq ?_
      rw [← hxT]; field_simp; ring
    calc ‖Cvs.StepA.Edge.ExpSumWindowTransplant.winVec x p a‖ ^ 2 ≤ 2 * G := hv
      _ ≤ 2 * (8 * ‖A‖ ^ 2 / δ) := by linarith
      _ ≤ 2 * (8 * ((x : ℝ) ^ (-δ) * (4 * δ ^ 2) / ((1 - δ / ‖w‖) ^ 2 * Real.exp (-(kS σ / 2)) ^ 2)) / δ) := by
          gcongr
      _ = 64 * δ * (x : ℝ) ^ (-δ) / ((1 - δ / ‖w‖) ^ 2 * Real.exp (-(kS σ / 2)) ^ 2) := by
          field_simp; ring

/-- **`FreeInterp` holds** (caseinf-W Theorem F), with `α = bexp + 1` and `β = β_σ/2^{1/2}`. -/
theorem freeInterp : Cvs.StepA.Edge.CaseInfinityJointRates.FreeInterp := by
  refine ⟨(bexp : ℝ) + 1, by positivity, fun δD hδ hδ' ε₂ hε₂ hαε H hH σ hσ => ?_⟩
  refine ⟨Real.exp (-(kS σ / 2)) / √2, by positivity, ?_⟩
  filter_upwards [eventually_good hδ hδ' hε₂ hαε hH |(σ : ℂ).im|] with x hgood
  obtain ⟨hx, hM, hH0, hq, _⟩ := hgood
  have h := pointInterp_at hx hδ hδ' hH0 hq hσ hM
  have e : 32 * |Cvs.GaussKernel.del σ| * (x : ℝ) ^ (-|Cvs.GaussKernel.del σ|)
      / ((1 - |Cvs.GaussKernel.del σ| / ‖wR σ‖) ^ 2 * (Real.exp (-(kS σ / 2)) / √2) ^ 2)
      = 64 * |Cvs.GaussKernel.del σ| * (x : ℝ) ^ (-|Cvs.GaussKernel.del σ|)
        / ((1 - |Cvs.GaussKernel.del σ| / ‖wR σ‖) ^ 2 * Real.exp (-(kS σ / 2)) ^ 2) := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp
    ring
  rw [e]
  exact h

end Cvs.StepA.Edge.FreeInterpHolds

end
