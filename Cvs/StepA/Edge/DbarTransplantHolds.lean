import Mathlib
import Cvs.StepA.Edge.CaseInfinityJointRates
import Cvs.StepA.Edge.DeepPointBlaschkeCount
import Cvs.StepA.Edge.DeepSetZeroSums
import Cvs.StepA.Edge.ExpSumWindowTransplant
import Cvs.StepA.Edge.TransplantAngleHighZeros
import Cvs.StepA.Edge.WindowCoshTransformDuality
import Cvs.Upstream.ExpSumContourInterpolation
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.RectArgument

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `DbarTransplant` holds

On the rectangle `[δ_D/4, 2] × [−(2H + 1), 2H + 1]`, `DeepPointBlaschkeCount`'s Blaschke bounds and `ExpSumWindowTransplant`'s transplant give
`Transplant` for `deepSet δ_D H` on `rect (δ_D/4) (4H + 1)` with `K ≤ 2^{1/2}K_c/(1 − q)`,
`K_c ≤ (8H + 8)(5H + 7)^{33792}/(2π(δ_D/2)^{1/2})` and `K_p ≤ 2^{1/2}e^{Z}/(1 − q)`. For a cutoff `H ≍ x^{ε₂}` this
is `K ≤ Cx^{αε₂}`, `K_p ≤ C`, and `q → 0` once `αε₂ < δ_D/8`: `CaseInfinityJointRates`'s `DbarTransplant` with `α = 33793`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology Finset
open scoped Interval ComplexConjugate
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.StepA.Edge.WindowCoshTransformDuality (wR Transplant)
open Cvs.StepA.Edge.DeepSetZeroSums (deepSet)
open Cvs.StepA.Edge.TransplantAngleHighZeros (rect)
open Cvs.StepA.Edge.DeepPointBlaschkeCount (deepPts bexp)
open Cvs.Zeta (closedRect)

namespace Cvs.StepA.Edge.DbarTransplantHolds
open Cvs.ZeroCounting

/-! ### The rectangle -/

theorem isOpen_rect (s Y : ℝ) : IsOpen (rect s Y) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const))

/-- The lower-left corner `δ_D/4 − (2H + 1)i`. -/
def zc (δD H : ℝ) : ℂ := ((δD / 4 : ℝ) : ℂ) - ((2 * H + 1 : ℝ) : ℂ) * I

/-- The upper-right corner `2 + (2H + 1)i`. -/
def wc (H : ℝ) : ℂ := ((2 : ℝ) : ℂ) + ((2 * H + 1 : ℝ) : ℂ) * I

@[simp] theorem zc_re (δD H : ℝ) : (zc δD H).re = δD / 4 := by simp [zc]
@[simp] theorem zc_im (δD H : ℝ) : (zc δD H).im = -(2 * H + 1) := by simp [zc]
@[simp] theorem wc_re (H : ℝ) : (wc H).re = 2 := by simp [wc]
@[simp] theorem wc_im (H : ℝ) : (wc H).im = 2 * H + 1 := by simp [wc]

theorem closedRect_subset_rect {δD H : ℝ} (hδ : 0 < δD) (hδ' : δD < 1 / 2) (hH : 0 < H) :
    closedRect (zc δD H) (wc H) ⊆ rect (δD / 4) (4 * H + 1) := by
  intro u hu
  obtain ⟨hre, him⟩ := hu
  rw [Set.mem_preimage, zc_re, wc_re, Set.uIcc_of_le (by linarith)] at hre
  rw [Set.mem_preimage, zc_im, wc_im, Set.uIcc_of_le (by linarith)] at him
  refine ⟨by linarith [hre.1], by linarith [hre.2], ?_⟩
  rw [abs_lt]; constructor <;> linarith [him.1, him.2]

theorem inside_of_mem {δD H : ℝ} (hδ : 0 < δD) (hH : 0 ≤ H) {ζ : ℂ} (hζ : ζ ∈ deepPts δD H) :
    Cvs.Upstream.ExpSumContourInterpolation.Inside (zc δD H) (wc H) ζ := by
  obtain ⟨_, _, _, h1, h2, h3⟩ := Cvs.StepA.Edge.DeepPointBlaschkeCount.deepPts_facts hζ
  rw [abs_le] at h3
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith [h3.1, h3.2]

/-- `Transplant` is monotone in its constants. -/
theorem transplant_mono {x : ℕ} {Λ Ω T : Set ℂ} {K Kp K' Kp' : ℝ} (h : Transplant x Λ Ω T K Kp)
    (hT : T.Nonempty) (hK : K ≤ K') (hKp : Kp ≤ Kp') : Transplant x Λ Ω T K' Kp' := by
  intro d M c hd hs hM
  obtain ⟨v, hv, hn⟩ := h d M c hd hs hM
  obtain ⟨t, ht⟩ := hT
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM t ht)
  exact ⟨v, hv, hn.trans (add_le_add (mul_le_mul_of_nonneg_right hK hM0)
    (mul_le_mul_of_nonneg_right hKp (abs_nonneg c)))⟩

/-! ### The transplant at one `x` -/

/-- The contour constant `K_c = (2(2 − δ_D/4) + 4(2H + 1))(5H + 7)^{33792}/(2π(δ_D/2)^{1/2})`. -/
def kc (δD H : ℝ) : ℝ :=
  (2 * ((wc H).re - (zc δD H).re) + 2 * ((wc H).im - (zc δD H).im))
    / (2 * Real.pi * Real.exp (-((bexp : ℝ) * Real.log (5 * H + 7))) * √(2 * (zc δD H).re))

/-- The contraction constant `q = K_c·2x^{−δ_D/8}/(δ_D/2)^{1/2}`. -/
def qq (x : ℕ) (δD H : ℝ) : ℝ :=
  kc δD H * (2 * Real.exp (-((zc δD H).re * (Real.log x / 2))) / √(2 * (zc δD H).re))

/-- **The transplant for the deep set at one `x`**. -/
theorem transplant_deep {x : ℕ} (hx : 1 ≤ x) {δD H : ℝ} (hδ : 0 < δD) (hδ' : δD < 1 / 2) (hH : 0 < H)
    (hq : qq x δD H < 1) :
    Transplant x (wR '' (deepSet δD H : Set nonTrivialZeroSet)) (rect (δD / 4) (4 * H + 1))
      (rect (δD / 4) (4 * H + 1)) (√2 * kc δD H / (1 - qq x δD H))
      (√2 / (Real.exp (-Cvs.StepA.Edge.DeepSetZeroSums.invSqSum) * (1 - qq x δD H))) := by
  rw [← Cvs.StepA.Edge.DeepPointBlaschkeCount.coe_deepPts]
  have hsub := closedRect_subset_rect hδ hδ' hH
  exact Cvs.StepA.Edge.ExpSumWindowTransplant.transplant_of_rect hx (fun ζ hζ => Cvs.StepA.Edge.DeepPointBlaschkeCount.conj_mem_deepPts hζ)
    (by simp; linarith) (by simp; linarith) (by simp; linarith)
    (fun ζ hζ => inside_of_mem hδ hH.le hζ) (Real.exp_pos _)
    (fun u hu => Cvs.StepA.Edge.DeepPointBlaschkeCount.norm_blaschke_ge_onBd hδ hδ' hH.le hu) (Real.exp_pos _)
    (Cvs.StepA.Edge.DeepPointBlaschkeCount.norm_blaschke_half_ge hδ H)
    (fun h => by obtain ⟨_, _, _, _, h2, _⟩ := Cvs.StepA.Edge.DeepPointBlaschkeCount.deepPts_facts h; norm_num at h2)
    (isOpen_rect _ _) hsub (fun u hu => hsub hu.1) hq

/-! ### Growth in `x` -/

/-- `K_c ≤ C₀X^{bexp + 1}` for `X ≤ H ≤ 2X`, `X ≥ 1`, `C₀ = 24·17^{bexp}/(2π(δ_D/2)^{1/2})`. -/
theorem kc_le {δD H X : ℝ} (hδ : 0 < δD) (hδ' : δD < 1 / 2) (hX : 1 ≤ X) (hH1 : X ≤ H) (hH2 : H ≤ 2 * X) :
    kc δD H ≤ 24 * 17 ^ bexp / (2 * Real.pi * √(δD / 2)) * X ^ (bexp + 1) := by
  have hpi := Real.pi_pos
  have hs : 0 < √(δD / 2) := Real.sqrt_pos.2 (by linarith)
  have h57 : 0 < 5 * H + 7 := by linarith
  have hexp : (Real.exp (-((bexp : ℝ) * Real.log (5 * H + 7))))⁻¹ = (5 * H + 7) ^ bexp := by
    rw [← Real.exp_neg, neg_neg, Real.exp_nat_mul, Real.exp_log h57]
  have hz : √(2 * (zc δD H).re) = √(δD / 2) := by rw [zc_re]; congr 1; ring
  unfold kc
  rw [hz, zc_re, zc_im, wc_re, wc_im]
  have hnum : 2 * (2 - δD / 4) + 2 * (2 * H + 1 - -(2 * H + 1)) ≤ 24 * X := by nlinarith
  have hpow : (5 * H + 7) ^ bexp ≤ (17 * X) ^ bexp :=
    pow_le_pow_left₀ h57.le (by linarith) _
  have hE : 0 < Real.exp (-((bexp : ℝ) * Real.log (5 * H + 7))) := Real.exp_pos _
  rw [div_le_iff₀ (by positivity)]
  have e1 : 24 * 17 ^ bexp / (2 * Real.pi * √(δD / 2)) * X ^ (bexp + 1)
      * (2 * Real.pi * Real.exp (-((bexp : ℝ) * Real.log (5 * H + 7))) * √(δD / 2))
      = 24 * X * (17 * X) ^ bexp * Real.exp (-((bexp : ℝ) * Real.log (5 * H + 7))) := by
    field_simp; ring
  rw [e1]
  have e2 : (5 * H + 7) ^ bexp * Real.exp (-((bexp : ℝ) * Real.log (5 * H + 7))) = 1 := by
    rw [← hexp, inv_mul_cancel₀ hE.ne']
  have hn0 : 0 ≤ 2 * (2 - δD / 4) + 2 * (2 * H + 1 - -(2 * H + 1)) := by nlinarith
  calc 2 * (2 - δD / 4) + 2 * (2 * H + 1 - -(2 * H + 1))
      = (2 * (2 - δD / 4) + 2 * (2 * H + 1 - -(2 * H + 1)))
        * ((5 * H + 7) ^ bexp * Real.exp (-((bexp : ℝ) * Real.log (5 * H + 7)))) := by rw [e2, mul_one]
    _ ≤ 24 * X * ((17 * X) ^ bexp * Real.exp (-((bexp : ℝ) * Real.log (5 * H + 7)))) := by
        refine mul_le_mul hnum (mul_le_mul_of_nonneg_right hpow hE.le) (by positivity) (by positivity)
    _ = _ := by ring

/-- **`DbarTransplant` holds** (caseinf-attack Theorem 4 (a), (d), (e), Lemma 3, Corollary 5, by contour
interpolation), with `α = bexp + 1 = 33793`. -/
theorem dbarTransplant : Cvs.StepA.Edge.CaseInfinityJointRates.DbarTransplant := by
  refine ⟨(bexp : ℝ) + 1, by positivity, fun δD hδ hδ' ε₂ hε₂ hαε H hH => ?_⟩
  have hpi := Real.pi_pos
  have hs : 0 < √(δD / 2) := Real.sqrt_pos.2 (by linarith)
  set C₀ := 24 * 17 ^ bexp / (2 * Real.pi * √(δD / 2)) with hC₀
  have hC₀0 : 0 < C₀ := by positivity
  set Z := Cvs.StepA.Edge.DeepSetZeroSums.invSqSum
  set C := max (2 * √2 * C₀) (2 * √2 * Real.exp Z) with hC
  refine ⟨C, lt_max_of_lt_left (by positivity), ?_⟩
  have hneg : 0 < δD / 8 - ((bexp : ℝ) + 1) * ε₂ := by linarith
  have hev : ∀ᶠ x : ℕ in atTop, 2 * C₀ / √(δD / 2) * (x : ℝ) ^ (-(δD / 8 - ((bexp : ℝ) + 1) * ε₂)) ≤ 1 / 2 := by
    have h1 : Tendsto (fun x : ℕ => (x : ℝ) ^ (-(δD / 8 - ((bexp : ℝ) + 1) * ε₂))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hneg).comp tendsto_natCast_atTop_atTop
    have h2 := h1.const_mul (2 * C₀ / √(δD / 2))
    rw [mul_zero] at h2
    exact (h2.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono fun x h => h.le
  filter_upwards [hH, hev, eventually_ge_atTop 1] with x hHx hq hx
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  set X := (x : ℝ) ^ ε₂ with hXdef
  have hX : 1 ≤ X := Real.one_le_rpow hx1 hε₂.le
  have hH0 : 0 < H x := by linarith [hHx.1]
  have hkc := kc_le hδ hδ' hX hHx.1 hHx.2
  have hXα : X ^ (bexp + 1) = (x : ℝ) ^ (((bexp : ℝ) + 1) * ε₂) := by
    rw [hXdef, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; push_cast; ring_nf
  have hkc' : kc δD (H x) ≤ C₀ * (x : ℝ) ^ (((bexp : ℝ) + 1) * ε₂) := by rw [← hXα]; exact hkc
  have hkc0 : 0 ≤ kc δD (H x) := by
    unfold kc; rw [zc_re, zc_im, wc_re, wc_im]
    refine div_nonneg (by nlinarith) ?_
    have : 0 ≤ √(2 * (δD / 4)) := Real.sqrt_nonneg _
    positivity
  have hqq : qq x δD (H x) ≤ 1 / 2 := by
    unfold qq
    rw [zc_re]
    have he : Real.exp (-(δD / 4 * (Real.log x / 2))) = (x : ℝ) ^ (-(δD / 8)) := by
      rw [Real.rpow_def_of_pos hx0]; congr 1; ring
    have hz : √(2 * (δD / 4)) = √(δD / 2) := by congr 1; ring
    rw [he, hz]
    refine le_trans ?_ hq
    have e : 2 * C₀ / √(δD / 2) * (x : ℝ) ^ (-(δD / 8 - ((bexp : ℝ) + 1) * ε₂))
        = C₀ * (x : ℝ) ^ (((bexp : ℝ) + 1) * ε₂) * (2 * (x : ℝ) ^ (-(δD / 8)) / √(δD / 2)) := by
      rw [show -(δD / 8 - ((bexp : ℝ) + 1) * ε₂) = ((bexp : ℝ) + 1) * ε₂ + -(δD / 8) by ring, Real.rpow_add hx0]
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right hkc' (by positivity)
  have hqq0 : 0 ≤ qq x δD (H x) := by
    unfold qq; rw [zc_re]
    have : 0 ≤ √(2 * (δD / 4)) := Real.sqrt_nonneg _
    exact mul_nonneg hkc0 (by positivity)
  have h1q : 1 / 2 ≤ 1 - qq x δD (H x) := by linarith
  have ht := transplant_deep hx hδ hδ' hH0 (by linarith)
  refine transplant_mono ht ⟨1, by refine ⟨?_, ?_, ?_⟩ <;> simp <;> linarith⟩ ?_ ?_
  · calc √2 * kc δD (H x) / (1 - qq x δD (H x)) ≤ √2 * kc δD (H x) / (1 / 2) :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) h1q
      _ = 2 * √2 * kc δD (H x) := by ring
      _ ≤ 2 * √2 * (C₀ * (x : ℝ) ^ (((bexp : ℝ) + 1) * ε₂)) := mul_le_mul_of_nonneg_left hkc' (by positivity)
      _ = 2 * √2 * C₀ * (x : ℝ) ^ (((bexp : ℝ) + 1) * ε₂) := by ring
      _ ≤ C * (x : ℝ) ^ (((bexp : ℝ) + 1) * ε₂) := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · calc √2 / (Real.exp (-Z) * (1 - qq x δD (H x))) ≤ √2 / (Real.exp (-Z) * (1 / 2)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            (mul_le_mul_of_nonneg_left h1q (Real.exp_pos _).le)
      _ = 2 * √2 * Real.exp Z := by rw [Real.exp_neg]; field_simp
      _ ≤ C := le_max_right _ _

end Cvs.StepA.Edge.DbarTransplantHolds

end
