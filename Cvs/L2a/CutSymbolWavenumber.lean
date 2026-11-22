import Mathlib
import Cvs.L2a.FarIntegrationByParts
import Cvs.L2a.QIdentityCutPoint
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The cut symbol in the wavenumber variable

`μ = μ_si + e^{icxy}(2cxy/(Q(cy + ξ)) + pQ′/Q²)` wherever `Q(ξ) ≠ 0`, for every real `y`. In `ζ = ξ/c`
the phase-free symbol `μ̃` is holomorphic on `Ω = {9/16 < |Re ζ|, |Im ζ| < 3/16}` for `|y| ≤ ½`, and the
co-symbol `h = μ̃ + i/(c(y + ζ))` is `O(1/c²)`: `c²|h| ≤ 192x/(x² − 1) + 64/(c(x² − 1))` on the strip
`{5/8 ≤ |Re ζ|, |Im ζ| ≤ 1/8}`, and `c²|h| ≤ 34x/(x² − 1) + 11/(c(x² − 1))` at real `|ζ| ≥ 3/4`.
-/

noncomputable section

namespace Cvs.L2a.CutSymbolWavenumber

open Real Set Complex Metric
open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.FarIntegrationByParts

/-! ### The split for every real `y` -/

/-! ### The symbol in `ζ = ξ/c` -/

/-- `Q` at complex `ζ = ξ/c`: `p(c²y² − c²ζ²) − 2icxy`. -/
def qQξC (c y x : ℝ) (ζ : ℂ) : ℂ :=
  ((pP x : ℝ) : ℂ) * ((c : ℂ) ^ 2 * (y : ℂ) ^ 2 - (c : ℂ) ^ 2 * ζ ^ 2) - 2 * I * (c : ℂ) * (x : ℂ) * (y : ℂ)

/-- The phase-free cut symbol at complex `ζ = ξ/c`: `p[i(cζ − cy)/Q + Q′/Q²]`. -/
def muQξC (c y x : ℝ) (ζ : ℂ) : ℂ :=
  ((pP x : ℝ) : ℂ) * (I * ((c : ℂ) * ζ - (c : ℂ) * (y : ℂ)) / qQξC c y x ζ + qQ₁ c y x / qQξC c y x ζ ^ 2)

/-- The co-symbol `h = μ̃ − (−i/(c(y + ζ)))`. -/
def hcoC (c y x : ℝ) (ζ : ℂ) : ℂ := muQξC c y x ζ - (-I / ((c : ℂ) * ((y : ℂ) + ζ)))

/-- The region `Ω = {9/16 < |Re ζ|, |Im ζ| < 3/16}`. -/
def omegaC : Set ℂ := {ζ | 9 / 16 < |ζ.re| ∧ |ζ.im| < 3 / 16}

/-- The closed strip `{5/8 ≤ |Re ζ|, |Im ζ| ≤ 1/8}`. -/
def stripC : Set ℂ := {ζ | 5 / 8 ≤ |ζ.re| ∧ |ζ.im| ≤ 1 / 8}

theorem qQξC_ofReal (c y x η : ℝ) : qQξC c y x (η : ℂ) = Cvs.L2a.QIdentityCutPoint.qQk c y x (c * η) := by
  unfold qQξC Cvs.L2a.QIdentityCutPoint.qQk; push_cast; ring

/-- `μ̃(c·η)` is the real trace of `muQξC`. -/
theorem muQξC_ofReal (c y x η : ℝ) : muQξC c y x (η : ℂ) = Cvs.L2a.QIdentityCutPoint.muQ c y x (c * η) := by
  unfold muQξC Cvs.L2a.QIdentityCutPoint.muQ
  rw [qQξC_ofReal]
  push_cast
  ring

theorem re_qQξC (c y x : ℝ) (ζ : ℂ) :
    (qQξC c y x ζ).re = pP x * c ^ 2 * (y ^ 2 - ζ.re ^ 2 + ζ.im ^ 2) := by
  simp only [qQξC, sq, Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
  ring

/-- `|Q| ≥ pc²(Re ζ² − Im ζ² − y²)`. -/
theorem le_norm_qQξC (c y x : ℝ) (ζ : ℂ) :
    pP x * c ^ 2 * (ζ.re ^ 2 - ζ.im ^ 2 - y ^ 2) ≤ ‖qQξC c y x ζ‖ := by
  refine le_trans ?_ ((neg_le_abs _).trans (Complex.abs_re_le_norm _))
  rw [re_qQξC]
  linarith

/-- `‖Q′‖ ≤ 2c²x + c` for `|y| ≤ ½`, `x ≥ 0`. -/
theorem norm_qQ₁_le_half {c y x : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) (hy : |y| ≤ 1 / 2) :
    ‖qQ₁ c y x‖ ≤ 2 * c ^ 2 * x + c := by
  unfold qQ₁
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]
  have hy2 : y ^ 2 ≤ 1 / 4 := by
    have := sq_abs y ▸ pow_le_pow_left₀ (abs_nonneg y) hy 2
    nlinarith
  have h1 : |2 * c ^ 2 * x * (y ^ 2 - 1)| ≤ 2 * c ^ 2 * x := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * c ^ 2 * x), abs_of_nonpos (by nlinarith)]
    have : 0 ≤ 2 * c ^ 2 * x := by positivity
    nlinarith [sq_nonneg y]
  have h2 : |2 * c * y| ≤ c := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * c)]
    nlinarith
  linarith

/-! ### Holomorphy on `Ω` -/

theorem isOpen_omegaC : IsOpen omegaC := by
  change IsOpen ({ζ : ℂ | 9 / 16 < |ζ.re|} ∩ {ζ : ℂ | |ζ.im| < 3 / 16})
  exact (isOpen_lt continuous_const (continuous_abs.comp Complex.continuous_re)).inter
    (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)

theorem stripC_subset_omegaC : stripC ⊆ omegaC := fun _ hz => ⟨by linarith [hz.1], by linarith [hz.2]⟩

/-- The closed disc of radius `1/8` about a real `η` with `|η| ≥ 3/4` lies in the strip. -/
theorem closedBall_subset_stripC {η : ℝ} (hη : 3 / 4 ≤ |η|) : closedBall (η : ℂ) (1 / 8) ⊆ stripC := by
  intro z hz
  rw [mem_closedBall, dist_eq_norm] at hz
  have h1 : |z.re - η| ≤ 1 / 8 := by
    have := Complex.abs_re_le_norm (z - η); simp only [Complex.sub_re, Complex.ofReal_re] at this; linarith
  have h2 : |z.im| ≤ 1 / 8 := by
    have := Complex.abs_im_le_norm (z - η); simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
    linarith
  refine ⟨?_, h2⟩
  have := abs_sub_abs_le_abs_sub η z.re
  rw [abs_sub_comm] at this
  linarith

/-- On `Ω`, `Re Q < 0`. -/
theorem re_qQξC_neg {c y x : ℝ} (hc : 0 < c) (hx : 1 < x) (hy : |y| ≤ 1 / 2) {ζ : ℂ} (hζ : ζ ∈ omegaC) :
    (qQξC c y x ζ).re < 0 := by
  rw [re_qQξC]
  have hy2 : y ^ 2 ≤ 64 / 256 := by
    have := sq_abs y ▸ pow_le_pow_left₀ (abs_nonneg y) hy 2
    nlinarith
  have hre : 81 / 256 < ζ.re ^ 2 := by
    have := sq_abs ζ.re ▸ pow_lt_pow_left₀ hζ.1 (by norm_num) (by norm_num : (2 : ℕ) ≠ 0)
    nlinarith
  have him : ζ.im ^ 2 < 9 / 256 := by
    have := sq_abs ζ.im ▸ pow_lt_pow_left₀ hζ.2 (abs_nonneg _) (by norm_num : (2 : ℕ) ≠ 0)
    nlinarith
  have hp : 0 < pP x * c ^ 2 := mul_pos (pP_pos hx) (by positivity)
  nlinarith

theorem qQξC_ne_zero {c y x : ℝ} (hc : 0 < c) (hx : 1 < x) (hy : |y| ≤ 1 / 2) {ζ : ℂ} (hζ : ζ ∈ omegaC) :
    qQξC c y x ζ ≠ 0 := fun h => by
  have := re_qQξC_neg hc hx hy hζ
  rw [h, Complex.zero_re] at this
  exact lt_irrefl _ this

/-- On `Ω`, `y + ζ ≠ 0`. -/
theorem add_ne_zero_of_mem_omegaC {y : ℝ} (hy : |y| ≤ 1 / 2) {ζ : ℂ} (hζ : ζ ∈ omegaC) :
    (y : ℂ) + ζ ≠ 0 := fun h => by
  have h1 : y + ζ.re = 0 := by have := congrArg Complex.re h; simpa using this
  have : |ζ.re| = |y| := by rw [show ζ.re = -y by linarith, abs_neg]
  linarith [hζ.1]

/-! ### The co-symbol is `O(1/c²)` -/

/-- **The co-symbol identity**: `h = 2cxy/(Q·c(y + ζ)) + pQ′/Q²`. -/
theorem hcoC_eq {c y x : ℝ} {ζ : ℂ} (hc : c ≠ 0) (hQ : qQξC c y x ζ ≠ 0) (hs : (y : ℂ) + ζ ≠ 0) :
    hcoC c y x ζ = ((2 * c * x * y : ℝ) : ℂ) / (qQξC c y x ζ * ((c : ℂ) * ((y : ℂ) + ζ)))
      + ((pP x : ℝ) : ℂ) * qQ₁ c y x / qQξC c y x ζ ^ 2 := by
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc
  have hcs : (c : ℂ) * ((y : ℂ) + ζ) ≠ 0 := mul_ne_zero hc' hs
  have key : ((pP x : ℝ) : ℂ) * (I * ((c : ℂ) * ζ - (c : ℂ) * (y : ℂ))) * ((c : ℂ) * ((y : ℂ) + ζ))
      = -I * qQξC c y x ζ + ((2 * c * x * y : ℝ) : ℂ) := by
    unfold qQξC
    push_cast
    linear_combination (-(2 * (c : ℂ) * x * y)) * I_sq
  have h1 : ((pP x : ℝ) : ℂ) * (I * ((c : ℂ) * ζ - (c : ℂ) * (y : ℂ)) / qQξC c y x ζ)
      = -I / ((c : ℂ) * ((y : ℂ) + ζ))
        + ((2 * c * x * y : ℝ) : ℂ) / (qQξC c y x ζ * ((c : ℂ) * ((y : ℂ) + ζ))) := by
    rw [div_add_div _ _ hcs (mul_ne_zero hQ hcs), ← mul_div_assoc,
      div_eq_div_iff hQ (mul_ne_zero hcs (mul_ne_zero hQ hcs))]
    linear_combination (((c : ℂ) * ((y : ℂ) + ζ)) * qQξC c y x ζ) * key
  unfold hcoC muQξC
  rw [mul_add, h1]
  ring

/-- **The co-symbol bound from `|Q| ≥ A` and `|y + ζ| ≥ B`**. -/
theorem norm_hcoC_le_of {c y x : ℝ} {ζ : ℂ} {A B : ℝ} (hc : 0 < c) (hx : 1 < x) (hy : |y| ≤ 1 / 2)
    (hA : 0 < A) (hB : 0 < B) (hQ : A ≤ ‖qQξC c y x ζ‖) (hs : B ≤ ‖(y : ℂ) + ζ‖) :
    ‖hcoC c y x ζ‖ ≤ c * x / (A * (c * B)) + pP x * (2 * c ^ 2 * x + c) / A ^ 2 := by
  have hQ0 : qQξC c y x ζ ≠ 0 := norm_pos_iff.1 (hA.trans_le hQ)
  have hs0 : (y : ℂ) + ζ ≠ 0 := norm_pos_iff.1 (hB.trans_le hs)
  have hp : 0 < pP x := pP_pos hx
  have hx0 : 0 < x := by linarith
  rw [hcoC_eq hc.ne' hQ0 hs0]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hc]
    have h1 : |2 * c * x * y| ≤ c * x := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * c * x)]
      nlinarith [mul_pos hc hx0]
    gcongr
  · rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
    have h2 := norm_qQ₁_le_half hc.le hx0.le hy
    gcongr

/-- **The co-symbol on the strip**: `c²‖h‖ ≤ 192x/(x² − 1) + 64/(c(x² − 1))`. -/
theorem norm_hcoC_le_strip {c y x : ℝ} {ζ : ℂ} (hc : 0 < c) (hx : 1 < x) (hy : |y| ≤ 1 / 2)
    (hζ : ζ ∈ stripC) :
    ‖hcoC c y x ζ‖ ≤ (192 * x / (x ^ 2 - 1) + 64 / (c * (x ^ 2 - 1))) / c ^ 2 := by
  have hp : 0 < pP x := pP_pos hx
  have hy2 : y ^ 2 ≤ 16 / 64 := by
    have := sq_abs y ▸ pow_le_pow_left₀ (abs_nonneg y) hy 2
    nlinarith
  have hre : 25 / 64 ≤ ζ.re ^ 2 := by
    have := sq_abs ζ.re ▸ pow_le_pow_left₀ (by norm_num) hζ.1 2
    nlinarith
  have him : ζ.im ^ 2 ≤ 1 / 64 := by
    have := sq_abs ζ.im ▸ pow_le_pow_left₀ (abs_nonneg _) hζ.2 2
    nlinarith
  have hQ : pP x * c ^ 2 / 8 ≤ ‖qQξC c y x ζ‖ := by
    refine le_trans ?_ (le_norm_qQξC c y x ζ)
    have : 1 / 8 ≤ ζ.re ^ 2 - ζ.im ^ 2 - y ^ 2 := by linarith
    have h0 : 0 ≤ pP x * c ^ 2 := by positivity
    nlinarith
  have hs : 1 / 8 ≤ ‖(y : ℂ) + ζ‖ := by
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    simp only [Complex.add_re, Complex.ofReal_re]
    have := abs_sub_abs_le_abs_sub ζ.re (-y)
    rw [abs_neg, sub_neg_eq_add, add_comm] at this
    linarith [hζ.1]
  refine (norm_hcoC_le_of hc hx hy (by positivity) (by norm_num) hQ hs).trans (le_of_eq ?_)
  unfold pP at hp ⊢
  field_simp
  ring

/-- **The co-symbol at real `|η| ≥ 3/4`**: `c²‖h‖ ≤ 34x/(x² − 1) + 11/(c(x² − 1))`. -/
theorem norm_hcoC_le_real {c y x η : ℝ} (hc : 0 < c) (hx : 1 < x) (hy : |y| ≤ 1 / 2) (hη : 3 / 4 ≤ |η|) :
    ‖hcoC c y x (η : ℂ)‖ ≤ (34 * x / (x ^ 2 - 1) + 11 / (c * (x ^ 2 - 1))) / c ^ 2 := by
  have hp : 0 < pP x := pP_pos hx
  have hx0 : 0 < x := by linarith
  have hy2 : y ^ 2 ≤ 1 / 4 := by
    have := sq_abs y ▸ pow_le_pow_left₀ (abs_nonneg y) hy 2
    nlinarith
  have hη2 : 9 / 16 ≤ η ^ 2 := by
    have := sq_abs η ▸ pow_le_pow_left₀ (by norm_num) hη 2
    nlinarith
  have hQ : 5 * (pP x * c ^ 2) / 16 ≤ ‖qQξC c y x (η : ℂ)‖ := by
    refine le_trans ?_ (le_norm_qQξC c y x (η : ℂ))
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    have h0 : 0 ≤ pP x * c ^ 2 := by positivity
    nlinarith
  have hs : 1 / 4 ≤ ‖(y : ℂ) + (η : ℂ)‖ := by
    rw [← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]
    have := abs_sub_abs_le_abs_sub η (-y)
    rw [abs_neg, sub_neg_eq_add, add_comm] at this
    linarith
  refine (norm_hcoC_le_of hc hx hy (by positivity) (by norm_num) hQ hs).trans ?_
  have e : c * x / (5 * (pP x * c ^ 2) / 16 * (c * (1 / 4))) + pP x * (2 * c ^ 2 * x + c) / (5 * (pP x * c ^ 2) / 16) ^ 2
      = (832 * x / pP x + 256 / (c * pP x)) / (25 * c ^ 2) := by
    field_simp
    ring
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  unfold pP at hp ⊢
  have h1 : 832 * x / (x ^ 2 - 1) ≤ 25 * (34 * x / (x ^ 2 - 1)) := by
    rw [mul_div_assoc']; exact div_le_div_of_nonneg_right (by nlinarith) hp.le
  have h2 : 256 / (c * (x ^ 2 - 1)) ≤ 25 * (11 / (c * (x ^ 2 - 1))) := by
    rw [mul_div_assoc']; exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
  have h3 : 0 ≤ c ^ 2 := sq_nonneg c
  nlinarith [mul_le_mul_of_nonneg_right (add_le_add h1 h2) h3]

/-- `192x/(x² − 1) + 64/(c(x² − 1)) ≤ 130` for `x ≥ 2`, `c ≥ 11`. -/
theorem strip_const_le {c x : ℝ} (hc : 11 ≤ c) (hx : 2 ≤ x) :
    192 * x / (x ^ 2 - 1) + 64 / (c * (x ^ 2 - 1)) ≤ 130 := by
  have hp : 3 ≤ x ^ 2 - 1 := by nlinarith
  have h1 : 192 * x / (x ^ 2 - 1) ≤ 128 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have h2 : 64 / (c * (x ^ 2 - 1)) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  linarith

/-- `34x/(x² − 1) + 11/(c(x² − 1)) ≤ 23` for `x ≥ 2`, `c ≥ 11`. -/
theorem real_const_le {c x : ℝ} (hc : 11 ≤ c) (hx : 2 ≤ x) :
    34 * x / (x ^ 2 - 1) + 11 / (c * (x ^ 2 - 1)) ≤ 23 := by
  have hp : 3 ≤ x ^ 2 - 1 := by nlinarith
  have h1 : 34 * x / (x ^ 2 - 1) ≤ 68 / 3 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have h2 : 11 / (c * (x ^ 2 - 1)) ≤ 1 / 3 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  linarith

/-- **`c²‖h‖ ≤ 130` on the strip** for `x ≥ 2`, `c ≥ 11`. -/
theorem norm_hcoC_le_strip_130 {c y x : ℝ} {ζ : ℂ} (hc : 11 ≤ c) (hx : 2 ≤ x) (hy : |y| ≤ 1 / 2)
    (hζ : ζ ∈ stripC) : ‖hcoC c y x ζ‖ ≤ 130 / c ^ 2 :=
  (norm_hcoC_le_strip (by linarith) (by linarith) hy hζ).trans
    (div_le_div_of_nonneg_right (strip_const_le hc hx) (sq_nonneg c))

/-- **`c²‖h‖ ≤ 23` at real `|η| ≥ 3/4`** for `x ≥ 2`, `c ≥ 11`. -/
theorem norm_hcoC_le_real_23 {c y x η : ℝ} (hc : 11 ≤ c) (hx : 2 ≤ x) (hy : |y| ≤ 1 / 2)
    (hη : 3 / 4 ≤ |η|) : ‖hcoC c y x (η : ℂ)‖ ≤ 23 / c ^ 2 :=
  (norm_hcoC_le_real (by linarith) (by linarith) hy hη).trans
    (div_le_div_of_nonneg_right (real_const_le hc hx) (sq_nonneg c))

end Cvs.L2a.CutSymbolWavenumber
