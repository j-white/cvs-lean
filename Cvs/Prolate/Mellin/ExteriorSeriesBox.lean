import Mathlib
import Cvs.Prolate.Mellin.ModeExteriorTerms
import Cvs.StepA.Edge.TransplantAngleHighZeros
import Cvs.Upstream.HolomorphicParamIntegralSine

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The exterior series `Σ_k M_k` on the box of height `x`

For `ψ` bounded and `C¹` with `ψ, ψ′ ∈ L²(1, ∞)`, `x ≥ 14` and `c = 2πx`, the series `F = Σ_{k≥1} M_k` converges
uniformly on the box `−2 < Re s < 3`, `|Im s| < x`, is holomorphic there, equals `Σ_k −2∫₁^∞ ψ(t)C(kct, s) dt` on
`Re s < 0`, and satisfies `‖F(s)‖ ≤ (2P/c)(3 + log(1 + B/(2cP)))`, `B = 2(|ψ(1)| + D + P/√3)`.
-/

noncomputable section

open MeasureTheory Set Real Filter Topology Complex
open Cvs.Upstream.TrigMellinIntegralsContinuation (cosM)
open Cvs.Prolate.Mellin.ModeExteriorTerms (aCoef wInt mTerm)
open Cvs.StepA.Edge.TransplantAngleHighZeros (sbox)

namespace Cvs.Prolate.Mellin.ExteriorSeriesBox
open Cvs.ZeroCounting

variable {ψ ψ' : ℝ → ℝ}

/-- The exterior series `F(s) = Σ_{k≥1} M_k(s)`. -/
def extSeries (ψ : ℝ → ℝ) (c : ℝ) (s : ℂ) : ℂ := ∑' n : ℕ, mTerm ψ c (n + 1) s

/-- The `L²(1, ∞)` norm `P`. -/
def pNorm (ψ : ℝ → ℝ) : ℝ := √(∫ t in Ioi (1 : ℝ), ψ t ^ 2)

/-- The constant `B = 2(|ψ(1)| + D + P/√3)` of one integration by parts. -/
def bConst (ψ ψ' : ℝ → ℝ) : ℝ := 2 * (|ψ 1| + √(∫ t in Ioi (1 : ℝ), ψ' t ^ 2) + pNorm ψ / √3)

theorem pNorm_nonneg (ψ : ℝ → ℝ) : 0 ≤ pNorm ψ := Real.sqrt_nonneg _

theorem bConst_nonneg (ψ ψ' : ℝ → ℝ) : 0 ≤ bConst ψ ψ' := by
  unfold bConst; have := pNorm_nonneg ψ; positivity

/-- The box sits inside every `J`-region `Re s < 3`, `|Im s| < kc − 2`. -/
theorem sbox_subset_jRegion {x : ℕ} (hx : 1 ≤ x) {k : ℕ} (hk : 1 ≤ k) :
    sbox x ⊆ Cvs.Upstream.HolomorphicParamIntegralSine.jRegion (k * (2 * π * x)) := fun s hs => by
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  refine ⟨hs.2.1, hs.2.2.trans_le ?_⟩
  have : (2 * π * x : ℝ) ≤ k * (2 * π * x) := le_mul_of_one_le_left (by positivity) hk1
  nlinarith [Real.pi_gt_three]

/-- **The per-mode bound on the box**: `‖M_k(s)‖ ≤ min(2P, B/(kc))/(kc) + 2(x + 3)P/(√3(kc)·k(c − x − 1))`. -/
theorem norm_mTerm_le (hψ : ∀ t, HasDerivAt ψ (ψ' t) t) (hψ'c : Continuous ψ') {Mψ : ℝ}
    (hψb : ∀ t, |ψ t| ≤ Mψ) (hψ2 : IntegrableOn (fun t => ψ t ^ 2) (Ioi 1))
    (hψ'2 : IntegrableOn (fun t => ψ' t ^ 2) (Ioi 1)) {x : ℕ} (hx : 1 ≤ x) {s : ℂ} (hs : s ∈ sbox x) (n : ℕ) :
    ‖mTerm ψ (2 * π * x) (n + 1) s‖
      ≤ min (2 * pNorm ψ) (bConst ψ ψ' / (((n : ℝ) + 1) * (2 * π * x))) / (((n : ℝ) + 1) * (2 * π * x))
        + 2 * ((x : ℝ) + 3) / (((n : ℝ) + 1) * (2 * π * x))
          * (pNorm ψ / √3 / (((n : ℝ) + 1) * (2 * π * x - x - 1))) := by
  have hψm : Measurable ψ := (continuous_iff_continuousAt.2 fun t => (hψ t).continuousAt).measurable
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  set c := 2 * π * (x : ℝ) with hc
  have hc0 : 0 < c := by positivity
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hkc : 0 < ((n : ℝ) + 1) * c := by positivity
  have hcx : 0 < c - x - 1 := by rw [hc]; nlinarith [Real.pi_gt_three]
  obtain ⟨hre1, hre2, him⟩ := hs
  -- the coefficient
  have hA : |aCoef ψ (((n : ℝ) + 1) * c)| ≤ min (2 * pNorm ψ) (bConst ψ ψ' / (((n : ℝ) + 1) * c)) := by
    refine le_min (Cvs.Prolate.Mellin.ModeExteriorTerms.abs_aCoef_le hψm hψ2 _) ?_
    have := Cvs.Prolate.Mellin.ModeExteriorTerms.abs_aCoef_le_div hψ hψ'c hψb hψ2 hψ'2 hkc
    unfold bConst pNorm
    exact this
  -- the remainder
  have hW : ‖wInt ψ (((n : ℝ) + 1) * c) s‖ ≤ pNorm ψ / √3 / (((n : ℝ) + 1) * (c - x - 1)) := by
    have h := Cvs.Prolate.Mellin.ModeExteriorTerms.norm_wInt_le hψm hψ2 (y₀ := ((n : ℝ) + 1) * c) (s := s) hre2.le (by
      have : (x : ℝ) + 1 < ((n : ℝ) + 1) * c := by
        have : c ≤ ((n : ℝ) + 1) * c := le_mul_of_one_le_left hc0.le hn1
        rw [hc] at this ⊢; nlinarith [Real.pi_gt_three]
      linarith)
    refine h.trans ?_
    unfold pNorm
    have hP0 : 0 ≤ √(∫ t in Ioi (1 : ℝ), ψ t ^ 2) / √3 := by positivity
    refine div_le_div_of_nonneg_left hP0 (by positivity) ?_
    nlinarith [abs_nonneg s.im]
  have hs1 : ‖s - 1‖ ≤ (x : ℝ) + 3 := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
    have : |s.re - 1| ≤ 3 := abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  have hk : ‖((n : ℂ) + 1) * (c : ℂ)‖ = ((n : ℝ) + 1) * c := by
    rw [show ((n : ℂ) + 1) * (c : ℂ) = (((n : ℝ) + 1) * c : ℝ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hkc]
  unfold mTerm
  push_cast
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, hk]
    exact div_le_div_of_nonneg_right hA hkc.le
  · rw [norm_mul, norm_div, norm_mul, Complex.norm_ofNat, hk]
    gcongr

/-- `(x + 3)π²/(6√3(2πx − x − 1)) ≤ 1` for `x ≥ 1`. -/
theorem tail_const_le {x : ℝ} (hx : 1 ≤ x) : (x + 3) * (π ^ 2 / 6) / (√3 * (2 * π * x - x - 1)) ≤ 1 := by
  have hπ := Real.pi_gt_d2
  have hπ' := Real.pi_lt_d2
  have h3 : (1.7 : ℝ) ≤ √3 := by
    rw [show (1.7 : ℝ) = √(1.7 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hd : 0 < 2 * π * x - x - 1 := by nlinarith
  rw [div_le_one (by positivity)]
  have hπ2 : π ^ 2 ≤ 10 := by nlinarith
  calc (x + 3) * (π ^ 2 / 6) ≤ (x + 3) * (10 / 6) := by gcongr
    _ ≤ 1.7 * (2 * π * x - x - 1) := by nlinarith
    _ ≤ √3 * (2 * π * x - x - 1) := by gcongr

/-- **The exterior series on the box**: summable, holomorphic, and `‖F(s)‖ ≤ (2P/c)(3 + log(1 + B/(2cP)))`. -/
theorem extSeries_spec (hψ : ∀ t, HasDerivAt ψ (ψ' t) t) (hψ'c : Continuous ψ') {Mψ : ℝ}
    (hψb : ∀ t, |ψ t| ≤ Mψ) (hψ2 : IntegrableOn (fun t => ψ t ^ 2) (Ioi 1))
    (hψ'2 : IntegrableOn (fun t => ψ' t ^ 2) (Ioi 1)) {x : ℕ} (hx : 1 ≤ x) :
    DifferentiableOn ℂ (extSeries ψ (2 * π * x)) (sbox x)
      ∧ (∀ s ∈ sbox x, Summable fun n : ℕ => mTerm ψ (2 * π * x) (n + 1) s)
      ∧ ∀ s ∈ sbox x, ‖extSeries ψ (2 * π * x) s‖
          ≤ 2 * pNorm ψ / (2 * π * x) * (3 + Real.log (1 + bConst ψ ψ' / (2 * (2 * π * x) * pNorm ψ))) := by
  have hψm : Measurable ψ := (continuous_iff_continuousAt.2 fun t => (hψ t).continuousAt).measurable
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  set c := 2 * π * (x : ℝ) with hc
  have hc0 : 0 < c := by positivity
  have hcx : 0 < c - x - 1 := by rw [hc]; nlinarith [Real.pi_gt_three]
  set P := pNorm ψ with hP
  set B := bConst ψ ψ' with hB
  have hP0 : 0 ≤ P := pNorm_nonneg ψ
  have hB0 : 0 ≤ B := bConst_nonneg ψ ψ'
  set f : ℕ → ℝ := fun n => min (2 * P) (B / (((n : ℝ) + 1) * c)) / (((n : ℝ) + 1) * c) with hf
  set G : ℝ := 2 * ((x : ℝ) + 3) * P / (√3 * c * (c - x - 1)) with hG
  set g : ℕ → ℝ := fun n => G * (1 / ((n : ℝ) + 1) ^ 2) with hg
  have hterm : ∀ s ∈ sbox x, ∀ n : ℕ, ‖mTerm ψ c (n + 1) s‖ ≤ f n + g n := fun s hs n => by
    have h := norm_mTerm_le hψ hψ'c hψb hψ2 hψ'2 hx hs n
    refine h.trans (le_of_eq ?_)
    simp only [hf, hg, hG, hP, hB, hc]
    have : 0 < (n : ℝ) + 1 := by positivity
    have h2 : 0 < 2 * π * (x : ℝ) - x - 1 := by nlinarith [Real.pi_gt_three]
    field_simp
  have hf0 : ∀ n, 0 ≤ f n := fun n => div_nonneg (le_min (by positivity) (by positivity)) (by positivity)
  have hfB : ∀ n, f n ≤ B / c ^ 2 * (1 / ((n : ℝ) + 1) ^ 2) := fun n => by
    simp only [hf]
    calc min (2 * P) (B / (((n : ℝ) + 1) * c)) / (((n : ℝ) + 1) * c)
        ≤ B / (((n : ℝ) + 1) * c) / (((n : ℝ) + 1) * c) := by gcongr; exact min_le_right _ _
      _ = B / c ^ 2 * (1 / ((n : ℝ) + 1) ^ 2) := by field_simp
  have hz : Summable fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2 := by
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
    exact this.congr fun n => by push_cast; ring
  have hfs : Summable f := (hz.mul_left (B / c ^ 2)).of_nonneg_of_le hf0 hfB
  have hgs : Summable g := hz.mul_left G
  have hsum : ∀ s ∈ sbox x, Summable fun n : ℕ => mTerm ψ c (n + 1) s := fun s hs =>
    Summable.of_norm_bounded (hfs.add hgs) (hterm s hs)
  refine ⟨?_, hsum, fun s hs => ?_⟩
  · refine differentiableOn_tsum_of_summable_norm (hfs.add hgs) (fun n => ?_) (Cvs.StepA.Edge.TransplantAngleHighZeros.isOpen_sbox _)
      (fun n s hs => hterm s hs n)
    have hd := (Cvs.Prolate.Mellin.ModeExteriorTerms.differentiableOn_wInt hψm hψb (y₀ := ((n + 1 : ℕ) : ℝ) * c) (by positivity)).mono
      (sbox_subset_jRegion hx (k := n + 1) (by omega))
    unfold mTerm
    exact differentiableOn_const _ |>.add (((differentiableOn_id.sub_const 1).const_mul 2).div_const _ |>.mul hd)
  -- the bound
  have hnorm : ‖extSeries ψ c s‖ ≤ ∑' n, f n + ∑' n, g n := by
    unfold extSeries
    have hns : Summable fun n : ℕ => ‖mTerm ψ c (n + 1) s‖ := (hsum s hs).norm
    refine (norm_tsum_le_tsum_norm hns).trans ?_
    rw [← hfs.tsum_add hgs]
    exact hns.tsum_le_tsum (hterm s hs) (hfs.add hgs)
  have hgsum : ∑' n, g n = G * (π ^ 2 / 6) := by
    simp only [hg]
    rw [tsum_mul_left]
    congr 1
    have h : HasSum (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
      have := (hasSum_nat_add_iff' 1).2 hasSum_zeta_two
      simpa [Finset.sum_range_one] using this
    exact h.tsum_eq
  have hGle : G * (π ^ 2 / 6) ≤ 2 * P / c * 1 := by
    have ht := tail_const_le hx1
    rw [← hc] at ht
    have e : G * (π ^ 2 / 6) = 2 * P / c * ((x + 3) * (π ^ 2 / 6) / (√3 * (c - x - 1))) := by
      rw [hG]; field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left ht (by positivity)
  rcases hP0.eq_or_lt with hP00 | hPpos
  · -- `P = 0`: every term vanishes
    have hf00 : ∀ n, f n = 0 := fun n => by
      show min (2 * P) (B / (((n : ℝ) + 1) * c)) / (((n : ℝ) + 1) * c) = 0
      rw [← hP00, mul_zero, min_eq_left (by positivity), zero_div]
    rw [show f = fun _ => 0 from funext hf00, tsum_zero, hgsum, hG, ← hP00] at hnorm
    simp only [mul_zero, zero_mul, zero_div, add_zero] at hnorm
    rw [← hP00]
    simpa using hnorm
  · have hfsum := (Cvs.Prolate.Mellin.ModeExteriorTerms.tsum_min_le hPpos hB0 hc0).2
    rw [hgsum] at hnorm
    calc ‖extSeries ψ c s‖ ≤ ∑' n, f n + G * (π ^ 2 / 6) := hnorm
      _ ≤ 2 * P / c * (2 + Real.log (1 + B / (2 * c * P))) + 2 * P / c * 1 := add_le_add hfsum hGle
      _ = 2 * P / c * (3 + Real.log (1 + B / (2 * c * P))) := by ring

end Cvs.Prolate.Mellin.ExteriorSeriesBox

end
