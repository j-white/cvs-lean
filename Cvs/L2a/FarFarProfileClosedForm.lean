import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FarFarBound
import Cvs.L2a.FarIntegrationByParts
import Cvs.L2a.RampIntegrals
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Upstream.CosineTransformHalfLine

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `FarFarBound`'s far-far profile in closed form, and the constant `C_η^sym`

With `Y = y² − 1`, `D = y² − 9/5` and `νᵢ` bounding `RampIntegrals`'s six x-norms, `η(c, y) ≤ Σᵢ bᵢ(y)/cⁱ` for `c ≥ 1`, `y > 3/2`
(the Re/Im split of the atoms, `|Q₀| ≥ c²pY`, `√(I² + R²) ≤ I + R²/(2I)`). With `βᵢ ≥ ‖w bᵢ‖` this discharges `FarFarBound`'s
`farFar_le` with `C_η^sym(c) = (2/π)(β₁ + β₂/c + β₃/c² + β₄/c³)²`, which is nonincreasing in `c`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.FarIntegrationByParts Cvs.L2a.FarFarBound Cvs.L2a.RampIntegrals

namespace Cvs.L2a.FarFarProfileClosedForm

/-! ### The four coefficients -/

/-- `b₁ = πy/D + 4ν₂yY/D²`, `Y = y² − 1`, `D = y² − 9/5`. -/
def bI₁ (ν₂ y : ℝ) : ℝ := π * y / (y ^ 2 - 9 / 5) + 4 * ν₂ * y * (y ^ 2 - 1) / (y ^ 2 - 9 / 5) ^ 2

/-- `b₂ = 8ν₃Y²/D³`. -/
def bI₂ (ν₃ y : ℝ) : ℝ := 8 * ν₃ * (y ^ 2 - 1) ^ 2 / (y ^ 2 - 9 / 5) ^ 3

/-- `b₃ = m₁²/(2πyD) + 4ν₆y/D² + (AY + 4ν₄y²)²/(8ν₂yYD²)`, `m₁² = 6ν₅² + 2ν₆² + π⁴`, `A = 4ν₃ + 4ν₅ + 2ν₄`. -/
def bI₃ (ν₂ ν₃ ν₄ ν₅ ν₆ y : ℝ) : ℝ :=
  (6 * ν₅ ^ 2 + 2 * ν₆ ^ 2 + π ^ 4) / (2 * π * y * (y ^ 2 - 9 / 5)) + 4 * ν₆ * y / (y ^ 2 - 9 / 5) ^ 2
    + ((4 * ν₃ + 4 * ν₅ + 2 * ν₄) * (y ^ 2 - 1) + 4 * ν₄ * y ^ 2) ^ 2
      / (8 * ν₂ * y * (y ^ 2 - 1) * (y ^ 2 - 9 / 5) ^ 2)

/-- `b₄ = 8ν₇y²/D³`. -/
def bI₄ (ν₇ y : ℝ) : ℝ := 8 * ν₇ * y ^ 2 / (y ^ 2 - 9 / 5) ^ 3

/-- The majorant `Bm = b₁/c + b₂/c² + b₃/c³ + b₄/c⁴`. -/
def bM (ν₂ ν₃ ν₄ ν₅ ν₆ ν₇ c y : ℝ) : ℝ :=
  bI₁ ν₂ y / c + bI₂ ν₃ y / c ^ 2 + bI₃ ν₂ ν₃ ν₄ ν₅ ν₆ y / c ^ 3 + bI₄ ν₇ y / c ^ 4

/-- `C_η^sym(c) = (2/π)(β₁ + β₂/c + β₃/c² + β₄/c³)²`. -/
def cEtaSym (β₁ β₂ β₃ β₄ c : ℝ) : ℝ := 2 / π * (β₁ + β₂ / c + β₃ / c ^ 2 + β₄ / c ^ 3) ^ 2

/-! ### The atoms -/

/-- `Re A₁ = 2xw′ + pw″`. -/
theorem aA₁_re (c y x : ℝ) : (aA₁ c y x).re = 2 * x * wF₁ x + pP x * wF₂ x := by
  simp only [aA₁, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
  ring

/-- `Im A₁ = 2cy p w′`. -/
theorem aA₁_im (c y x : ℝ) : (aA₁ c y x).im = 2 * (c * y) * pP x * wF₁ x := by
  simp only [aA₁, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
  ring

/-- `Re A₂ = −c²(4x²Y + 4y²p + 2pY)w − 4c²xYp w′`. -/
theorem aA₂_re (c y x : ℝ) :
    (aA₂ c y x).re = -(c ^ 2 * (4 * x ^ 2 * (y ^ 2 - 1) + 4 * y ^ 2 * pP x + 2 * pP x * (y ^ 2 - 1)) * wF x)
      - 4 * c ^ 2 * x * (y ^ 2 - 1) * pP x * wF₁ x := by
  simp only [aA₂, qQ₁, qQ₂, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  unfold pP; ring

/-- `Im A₂ = −4cxy(c²pY − 1)w + 4cyp w′`. -/
theorem aA₂_im (c y x : ℝ) :
    (aA₂ c y x).im = -(4 * c * x * y * (c ^ 2 * pP x * (y ^ 2 - 1) - 1) * wF x) + 4 * c * y * pP x * wF₁ x := by
  simp only [aA₂, qQ₁, qQ₂, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  unfold pP; ring

/-- `|Q′|² = (2c²xY)² + (2cy)²`. -/
theorem norm_qQ₁_sq (c y x : ℝ) :
    ‖qQ₁ c y x‖ ^ 2 = (2 * c ^ 2 * x * (y ^ 2 - 1)) ^ 2 + (2 * c * y) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [qQ₁, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- `c²pY = Re Q₀ ≤ |Q₀|`. -/
theorem le_norm_qQ₀ (c y x : ℝ) : c ^ 2 * pP x * (y ^ 2 - 1) ≤ ‖qQ₀ c y x‖ := by
  refine le_trans (le_of_eq ?_) (Complex.re_le_norm _)
  rw [qQ₀, qQ_re]; unfold pP; ring

/-- `(‖z‖/‖Q‖ᵏ)² ≤ (Re z/qᵏ)² + (Im z/qᵏ)²` whenever `0 < q ≤ ‖Q‖`. -/
theorem sq_norm_div_pow_le {z Q : ℂ} {q : ℝ} (k : ℕ) (hq : 0 < q) (hQ : q ≤ ‖Q‖) :
    (‖z‖ / ‖Q‖ ^ k) ^ 2 ≤ (z.re / q ^ k) ^ 2 + (z.im / q ^ k) ^ 2 := by
  have hqk : 0 < q ^ k := pow_pos hq k
  have hQk : q ^ k ≤ ‖Q‖ ^ k := pow_le_pow_left₀ hq.le hQ k
  have e : (z.re / q ^ k) ^ 2 + (z.im / q ^ k) ^ 2 = (‖z‖ / q ^ k) ^ 2 := by
    rw [div_pow, div_pow, div_pow, ← add_div, Complex.sq_norm, Complex.normSq_apply]; ring
  rw [e]
  exact pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_left (norm_nonneg _) hqk hQk) 2

/-! ### The three profiles, pointwise -/

/-- `(|A₁|/|Q₀|)² ≤ (2y w′/(cY))² + ((2xw′/p + w″)/(c²Y))²`. -/
theorem prof₁_sq_le {c y x : ℝ} (hc : 0 < c) (hy : 3 / 2 < y) (hx : 3 / 2 < x) :
    prof₁ c y x ^ 2 ≤ (2 * y / (c * (y ^ 2 - 1)) * wF₁ x) ^ 2
      + ((2 * x * wF₁ x / pP x + wF₂ x) / (c ^ 2 * (y ^ 2 - 1))) ^ 2 := by
  have hp : 0 < pP x := pP_pos (by linarith)
  have hY : 0 < y ^ 2 - 1 := by nlinarith
  have hq : 0 < c ^ 2 * pP x * (y ^ 2 - 1) := by positivity
  have h := sq_norm_div_pow_le (z := aA₁ c y x) 1 hq (le_norm_qQ₀ c y x)
  simp only [pow_one] at h
  unfold prof₁
  refine h.trans (le_of_eq ?_)
  rw [aA₁_re, aA₁_im]
  field_simp
  ring

/-- `|Im A₂|/(c²pY)² ≤ (4y/(cY))|xw/p| + (4y/(c³Y²))|w′/p|` for `c ≥ 1`. -/
theorem abs_im_aA₂_le {c y x : ℝ} (hc : 1 ≤ c) (hy : 3 / 2 < y) (hx : 3 / 2 < x) :
    |(aA₂ c y x).im| / (c ^ 2 * pP x * (y ^ 2 - 1)) ^ 2
      ≤ 4 * y / (c * (y ^ 2 - 1)) * |xP₂ x| + 4 * y / (c ^ 3 * (y ^ 2 - 1) ^ 2) * |xP₆ x| := by
  have hp : 0 < pP x := pP_pos (by linarith)
  have hp54 : 5 / 4 ≤ pP x := by unfold pP; nlinarith
  have hY : 5 / 4 ≤ y ^ 2 - 1 := by nlinarith
  have hc0 : 0 < c := by linarith
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  obtain ⟨hw0, -, -, -⟩ := wF_bounds x
  have h1 : 1 ≤ c ^ 2 * pP x * (y ^ 2 - 1) := by
    have : 1 ≤ c ^ 2 := by nlinarith
    have : 25 / 16 ≤ pP x * (y ^ 2 - 1) := by nlinarith
    nlinarith
  rw [aA₂_im, div_le_iff₀ (by positivity)]
  have e2 : |xP₂ x| = x * wF x / pP x := by unfold xP₂; rw [abs_of_nonneg (by positivity)]
  have e6 : |xP₆ x| = |wF₁ x| / pP x := by unfold xP₆; rw [abs_div, abs_of_pos hp]
  rw [e2, e6]
  have key : |-(4 * c * x * y * (c ^ 2 * pP x * (y ^ 2 - 1) - 1) * wF x) + 4 * c * y * pP x * wF₁ x|
      ≤ 4 * c * x * y * (c ^ 2 * pP x * (y ^ 2 - 1)) * wF x + 4 * c * y * pP x * |wF₁ x| := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg, abs_of_nonneg (by have := sub_nonneg.2 h1; positivity), abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * c * y * pP x)]
    have : 4 * c * x * y * (c ^ 2 * pP x * (y ^ 2 - 1) - 1) * wF x
        ≤ 4 * c * x * y * (c ^ 2 * pP x * (y ^ 2 - 1)) * wF x := by
      have : 0 ≤ 4 * c * x * y * wF x := by positivity
      nlinarith
    linarith
  refine key.trans (le_of_eq ?_)
  field_simp

/-- `|Re A₂|/(c²pY)² ≤ c⁻²((4/Y)|x²w/p²| + (4y²/Y² + 2/Y)|w/p| + (4/Y)|xw′/p|)`. -/
theorem abs_re_aA₂_le {c y x : ℝ} (hc : 0 < c) (hy : 3 / 2 < y) (hx : 3 / 2 < x) :
    |(aA₂ c y x).re| / (c ^ 2 * pP x * (y ^ 2 - 1)) ^ 2
      ≤ 1 / c ^ 2 * (4 / (y ^ 2 - 1) * |xP₃ x| + (4 * y ^ 2 / (y ^ 2 - 1) ^ 2 + 2 / (y ^ 2 - 1)) * |xP₄ x|
          + 4 / (y ^ 2 - 1) * |xP₅ x|) := by
  have hp : 0 < pP x := pP_pos (by linarith)
  have hY : 0 < y ^ 2 - 1 := by nlinarith
  have hx0 : 0 < x := by linarith
  obtain ⟨hw0, -, -, -⟩ := wF_bounds x
  rw [aA₂_re, div_le_iff₀ (by positivity)]
  have e3 : |xP₃ x| = x ^ 2 * wF x / pP x ^ 2 := by unfold xP₃; rw [abs_of_nonneg (by positivity)]
  have e4 : |xP₄ x| = wF x / pP x := by unfold xP₄; rw [abs_of_nonneg (by positivity)]
  have e5 : |xP₅ x| = x * |wF₁ x| / pP x := by
    unfold xP₅; rw [abs_div, abs_of_pos hp, abs_mul, abs_of_pos hx0]
  rw [e3, e4, e5]
  have key : |-(c ^ 2 * (4 * x ^ 2 * (y ^ 2 - 1) + 4 * y ^ 2 * pP x + 2 * pP x * (y ^ 2 - 1)) * wF x)
      - 4 * c ^ 2 * x * (y ^ 2 - 1) * pP x * wF₁ x|
      ≤ c ^ 2 * (4 * x ^ 2 * (y ^ 2 - 1) + 4 * y ^ 2 * pP x + 2 * pP x * (y ^ 2 - 1)) * wF x
        + 4 * c ^ 2 * x * (y ^ 2 - 1) * pP x * |wF₁ x| := by
    refine (abs_sub _ _).trans ?_
    rw [abs_neg, abs_of_nonneg (by positivity), abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * c ^ 2 * x * (y ^ 2 - 1) * pP x)]
  refine key.trans (le_of_eq ?_)
  field_simp
  ring

/-- `(|A₂|/|Q₀|²)² ≤ (Im-part majorant)² + (Re-part majorant)²` for `c ≥ 1`. -/
theorem prof₂_sq_le {c y x : ℝ} (hc : 1 ≤ c) (hy : 3 / 2 < y) (hx : 3 / 2 < x) :
    prof₂ c y x ^ 2 ≤ (4 * y / (c * (y ^ 2 - 1)) * |xP₂ x| + 4 * y / (c ^ 3 * (y ^ 2 - 1) ^ 2) * |xP₆ x|) ^ 2
      + (1 / c ^ 2 * (4 / (y ^ 2 - 1) * |xP₃ x| + (4 * y ^ 2 / (y ^ 2 - 1) ^ 2 + 2 / (y ^ 2 - 1)) * |xP₄ x|
          + 4 / (y ^ 2 - 1) * |xP₅ x|)) ^ 2 := by
  have hp : 0 < pP x := pP_pos (by linarith)
  have hY : 0 < y ^ 2 - 1 := by nlinarith
  have hc0 : 0 < c := by linarith
  have hq : 0 < c ^ 2 * pP x * (y ^ 2 - 1) := by positivity
  have h := sq_norm_div_pow_le (z := aA₂ c y x) 2 hq (le_norm_qQ₀ c y x)
  have hI := abs_im_aA₂_le hc hy hx
  have hR := abs_re_aA₂_le hc0 hy hx
  unfold prof₂
  refine h.trans ?_
  set Q := (c ^ 2 * pP x * (y ^ 2 - 1)) ^ 2
  have eI : ((aA₂ c y x).im / Q) ^ 2 = (|(aA₂ c y x).im| / Q) ^ 2 := by rw [div_pow, div_pow, sq_abs]
  have eR : ((aA₂ c y x).re / Q) ^ 2 = (|(aA₂ c y x).re| / Q) ^ 2 := by rw [div_pow, div_pow, sq_abs]
  rw [eI, eR, add_comm]
  exact add_le_add (pow_le_pow_left₀ (by positivity) hI 2) (pow_le_pow_left₀ (by positivity) hR 2)

/-- `|A₃|/|Q₀|³ ≤ (8/(c²Y))|x²w/p²| + (8y²/(c⁴Y³))|w/p²|`. -/
theorem prof₃_le {c y x : ℝ} (hc : 0 < c) (hy : 3 / 2 < y) (hx : 3 / 2 < x) :
    prof₃ c y x ≤ 8 / (c ^ 2 * (y ^ 2 - 1)) * |xP₃ x| + 8 * y ^ 2 / (c ^ 4 * (y ^ 2 - 1) ^ 3) * |xP₇ x| := by
  have hp : 0 < pP x := pP_pos (by linarith)
  have hY : 0 < y ^ 2 - 1 := by nlinarith
  have hx0 : 0 < x := by linarith
  obtain ⟨hw0, -, -, -⟩ := wF_bounds x
  have hq : 0 < c ^ 2 * pP x * (y ^ 2 - 1) := by positivity
  have hA : ‖aA₃ c y x‖ = 2 * pP x * ((2 * c ^ 2 * x * (y ^ 2 - 1)) ^ 2 + (2 * c * y) ^ 2) * wF x := by
    rw [aA₃, norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hp, abs_of_nonneg hw0, Complex.norm_two, norm_qQ₁_sq]
  have e3 : |xP₃ x| = x ^ 2 * wF x / pP x ^ 2 := by unfold xP₃; rw [abs_of_nonneg (by positivity)]
  have e7 : |xP₇ x| = wF x / pP x ^ 2 := by unfold xP₇; rw [abs_of_nonneg (by positivity)]
  unfold prof₃
  rw [hA, e3, e7]
  calc 2 * pP x * ((2 * c ^ 2 * x * (y ^ 2 - 1)) ^ 2 + (2 * c * y) ^ 2) * wF x / ‖qQ₀ c y x‖ ^ 3
      ≤ 2 * pP x * ((2 * c ^ 2 * x * (y ^ 2 - 1)) ^ 2 + (2 * c * y) ^ 2) * wF x
          / (c ^ 2 * pP x * (y ^ 2 - 1)) ^ 3 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_left₀ hq.le (le_norm_qQ₀ c y x) 3)
    _ = _ := by field_simp; ring

/-! ### `L²` facts -/

/-- `f² ≤ u² + v²` on `(3/2, ∞)` with `u, v ∈ L²` gives `N(f) ≤ (N(u)² + N(v)²)^{1/2}`. -/
theorem nN_le_sqrt_add {f u v : ℝ → ℝ} (hu : MemLp u 2 (volume.restrict (Ioi (3 / 2))))
    (hv : MemLp v 2 (volume.restrict (Ioi (3 / 2)))) (h : ∀ x, 3 / 2 < x → f x ^ 2 ≤ u x ^ 2 + v x ^ 2) :
    nN f ≤ √(nN u ^ 2 + nN v ^ 2) := by
  have hu2 := hu.integrable_sq
  have hv2 := hv.integrable_sq
  rw [nN_sq, nN_sq, ← integral_add hu2 hv2]
  unfold nN
  refine Real.sqrt_le_sqrt (integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) (hu2.add hv2) ?_)
  exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => h x hx)

/-- `√(I² + R²) ≤ I + R²/(2I)` for `I > 0`. -/
theorem sqrt_sq_add_sq_le {I R : ℝ} (hI : 0 < I) : √(I ^ 2 + R ^ 2) ≤ I + R ^ 2 / (2 * I) := by
  rw [Real.sqrt_le_left (by positivity)]
  have : 0 ≤ (R ^ 2 / (2 * I)) ^ 2 := sq_nonneg _
  have e : (I + R ^ 2 / (2 * I)) ^ 2 = I ^ 2 + R ^ 2 + (R ^ 2 / (2 * I)) ^ 2 := by field_simp; ring
  rw [e]; linarith

/-- `w′ ∈ L²(3/2, ∞)`. -/
theorem memLp_wF₁ : MemLp wF₁ 2 (volume.restrict (Ioi (3 / 2))) := by
  refine memLp_of_le_inv (C := 2 * π) continuous_wF.2.measurable fun x hx => ?_
  have hx0 : 0 < x := by linarith
  rcases le_or_gt x 2 with hx2 | hx2
  · rw [le_div_iff₀ hx0]
    have := (wF_bounds x).2.2.1
    nlinarith [pi_pos, abs_nonneg (wF₁ x)]
  · rw [(wF_of_two_le hx2.le).2, abs_zero]; positivity

/-- `‖w′‖ = π/2`. -/
theorem nN_wF₁ : nN wF₁ = π / 2 := by
  unfold nN; rw [integral_wF₁_sq, Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity)]; ring

/-- `‖xw/p‖ > 0`. -/
theorem nN_xP₂_pos : 0 < nN xP₂ := by
  unfold nN
  refine Real.sqrt_pos.2 ?_
  have hi : IntegrableOn (fun x => xP₂ x ^ 2) (Ioi (3 / 2)) :=
    memLp_xP.1.integrable_sq
  have hmono : ∫ x in Ioi (2 : ℝ), xP₂ x ^ 2 ≤ ∫ x in Ioi (3 / 2 : ℝ), xP₂ x ^ 2 :=
    setIntegral_mono_set hi (Eventually.of_forall fun x => sq_nonneg _)
      (Eventually.of_forall (Ioi_subset_Ioi (by norm_num)))
  refine lt_of_lt_of_le ?_ hmono
  have hi2 : IntegrableOn (fun x => xP₂ x ^ 2) (Ioi 2) := hi.mono_set (Ioi_subset_Ioi (by norm_num))
  rw [setIntegral_pos_iff_support_of_nonneg_ae (Eventually.of_forall fun x => sq_nonneg _) hi2]
  have hsub : Ioi (2 : ℝ) ⊆ Function.support (fun x => xP₂ x ^ 2) ∩ Ioi 2 := fun x hx => by
    refine ⟨?_, hx⟩
    have hx2 : (2 : ℝ) < x := hx
    have hp : 0 < pP x := pP_pos (by linarith)
    simp only [Function.mem_support]
    unfold xP₂; rw [(wF_of_two_le hx2.le).1]
    positivity
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  simp

/-! ### The three profile norms -/

/-- `N₁ ≤ πy/(cY) + m₁²/(2πyc³Y)` with `m₁² = 6ν₅² + 2ν₆² + π⁴`. -/
theorem nN_prof₁_le {c y ν₅ ν₆ : ℝ} (hc : 0 < c) (hy : 3 / 2 < y) (hν₅ : nN xP₅ ≤ ν₅) (hν₆ : nN xP₆ ≤ ν₆) :
    nN (prof₁ c y) ≤ π * y / (c * (y ^ 2 - 1))
      + (6 * ν₅ ^ 2 + 2 * ν₆ ^ 2 + π ^ 4) / (2 * π * y * c ^ 3 * (y ^ 2 - 1)) := by
  have hY : 0 < y ^ 2 - 1 := by nlinarith
  have hy0 : 0 < y := by linarith
  set a := 2 * y / (c * (y ^ 2 - 1)) with ha
  set b := 1 / (c ^ 2 * (y ^ 2 - 1)) with hb
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have h := nN_le_sqrt_add (f := prof₁ c y) (u := fun x => a * wF₁ x)
    (v := fun x => b * (2 * x * wF₁ x / pP x + wF₂ x)) (memLp_wF₁.const_mul a) (memLp_ibp.const_mul b)
    fun x hx => by
      have := prof₁_sq_le hc hy hx
      simp only [ha, hb]
      convert this using 2
      ring
  rw [nN_const_mul ha0, nN_const_mul hb0, nN_wF₁] at h
  have hm : nN (fun x => 2 * x * wF₁ x / pP x + wF₂ x) = √(6 * nN xP₅ ^ 2 + 2 * nN xP₆ ^ 2 + π ^ 4) := by
    show √(∫ x in Ioi (3 / 2 : ℝ), (2 * x * wF₁ x / pP x + wF₂ x) ^ 2) = _
    rw [integral_ibp_sq]
  rw [hm] at h
  have h5 : nN xP₅ ^ 2 ≤ ν₅ ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hν₅ 2
  have h6 : nN xP₆ ^ 2 ≤ ν₆ ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hν₆ 2
  have hI : 0 < a * (π / 2) := by positivity
  refine h.trans ((Real.sqrt_le_sqrt ?_).trans ((sqrt_sq_add_sq_le
    (R := b * √(6 * ν₅ ^ 2 + 2 * ν₆ ^ 2 + π ^ 4)) hI).trans (le_of_eq ?_)))
  · gcongr
  · rw [mul_pow, Real.sq_sqrt (by positivity)]
    simp only [ha, hb]
    field_simp

/-- `N₂ ≤ 4yν₂/(cY) + 4yν₆/(c³Y²) + Y(A/Y + 4y²ν₄/Y²)²/(8yν₂c³)`, `A = 4ν₃ + 4ν₅ + 2ν₄`, from
`√(I² + R²) ≤ I + R²/(2I)` with `I ≥ 4yν₂/(cY)`. -/
theorem nN_prof₂_le {c y ν₂ ν₃ ν₄ ν₅ ν₆ : ℝ} (hc : 1 ≤ c) (hy : 3 / 2 < y) (hν₂ : nN xP₂ ≤ ν₂)
    (hν₃ : nN xP₃ ≤ ν₃) (hν₄ : nN xP₄ ≤ ν₄) (hν₅ : nN xP₅ ≤ ν₅) (hν₆ : nN xP₆ ≤ ν₆) :
    nN (prof₂ c y) ≤ 4 * y * ν₂ / (c * (y ^ 2 - 1)) + 4 * y * ν₆ / (c ^ 3 * (y ^ 2 - 1) ^ 2)
      + (y ^ 2 - 1) * ((4 * ν₃ + 4 * ν₅ + 2 * ν₄) / (y ^ 2 - 1) + 4 * y ^ 2 * ν₄ / (y ^ 2 - 1) ^ 2) ^ 2
        / (8 * y * ν₂ * c ^ 3) := by
  have hY : 0 < y ^ 2 - 1 := by nlinarith
  have hy0 : 0 < y := by linarith
  have hc0 : 0 < c := by linarith
  have hν₂0 : 0 < ν₂ := nN_xP₂_pos.trans_le hν₂
  obtain ⟨m2, m3, m4, m5, m6, -⟩ := memLp_xP
  set a₁ := 4 * y / (c * (y ^ 2 - 1)) with ha₁
  set a₂ := 4 * y / (c ^ 3 * (y ^ 2 - 1) ^ 2) with ha₂
  set r₃ := 1 / c ^ 2 * (4 / (y ^ 2 - 1)) with hr₃
  set r₄ := 1 / c ^ 2 * (4 * y ^ 2 / (y ^ 2 - 1) ^ 2 + 2 / (y ^ 2 - 1)) with hr₄
  set r₅ := 1 / c ^ 2 * (4 / (y ^ 2 - 1)) with hr₅
  have h0 : ∀ r : ℝ, 0 ≤ r → ∀ f : ℝ → ℝ, ∀ x, 0 ≤ r * |f x| := fun r hr f x => by positivity
  have hIm : MemLp (fun x => a₁ * |xP₂ x| + a₂ * |xP₆ x|) 2 (volume.restrict (Ioi (3 / 2))) :=
    (m2.abs.const_mul a₁).add (m6.abs.const_mul a₂)
  have hRe : MemLp (fun x => r₃ * |xP₃ x| + r₄ * |xP₄ x| + r₅ * |xP₅ x|) 2 (volume.restrict (Ioi (3 / 2))) :=
    ((m3.abs.const_mul r₃).add (m4.abs.const_mul r₄)).add (m5.abs.const_mul r₅)
  have h := nN_le_sqrt_add (f := prof₂ c y) hIm hRe fun x hx => by
    have := prof₂_sq_le hc hy hx
    convert this using 2
    simp only [hr₃, hr₄, hr₅]; ring
  have hI : nN (fun x => a₁ * |xP₂ x| + a₂ * |xP₆ x|) ≤ a₁ * ν₂ + a₂ * ν₆ := by
    have := nN_add_le (h0 a₁ (by positivity) xP₂) (h0 a₂ (by positivity) xP₆) (m2.abs.const_mul a₁)
      (m6.abs.const_mul a₂)
    rw [nN_const_mul (by positivity), nN_const_mul (by positivity), nN_abs, nN_abs] at this
    exact this.trans (by gcongr)
  have hR : nN (fun x => r₃ * |xP₃ x| + r₄ * |xP₄ x| + r₅ * |xP₅ x|) ≤ r₃ * ν₃ + r₄ * ν₄ + r₅ * ν₅ := by
    have h1 := nN_add_le (h0 r₃ (by positivity) xP₃) (h0 r₄ (by positivity) xP₄) (m3.abs.const_mul r₃)
      (m4.abs.const_mul r₄)
    have h2 := nN_add_le (f := fun x => r₃ * |xP₃ x| + r₄ * |xP₄ x|) (fun x => by positivity)
      (h0 r₅ (by positivity) xP₅) ((m3.abs.const_mul r₃).add (m4.abs.const_mul r₄)) (m5.abs.const_mul r₅)
    rw [nN_const_mul (by positivity), nN_const_mul (by positivity), nN_abs, nN_abs] at h1
    rw [nN_const_mul (by positivity), nN_abs] at h2
    refine h2.trans ?_
    have : r₅ * nN xP₅ ≤ r₅ * ν₅ := by gcongr
    have : r₃ * nN xP₃ + r₄ * nN xP₄ ≤ r₃ * ν₃ + r₄ * ν₄ := by gcongr
    linarith
  have hI0 : 0 ≤ nN (fun x => a₁ * |xP₂ x| + a₂ * |xP₆ x|) := Real.sqrt_nonneg _
  have hR0 : 0 ≤ nN (fun x => r₃ * |xP₃ x| + r₄ * |xP₄ x| + r₅ * |xP₅ x|) := Real.sqrt_nonneg _
  have hν₆0 : 0 ≤ a₂ * ν₆ := mul_nonneg (by positivity) ((Real.sqrt_nonneg _).trans hν₆)
  have hIpos : 0 < a₁ * ν₂ + a₂ * ν₆ := by
    have : 0 < a₁ * ν₂ := by positivity
    linarith
  refine h.trans ((Real.sqrt_le_sqrt (add_le_add (pow_le_pow_left₀ hI0 hI 2)
    (pow_le_pow_left₀ hR0 hR 2))).trans ((sqrt_sq_add_sq_le hIpos).trans ?_))
  have hfin : (r₃ * ν₃ + r₄ * ν₄ + r₅ * ν₅) ^ 2 / (2 * (a₁ * ν₂ + a₂ * ν₆))
      ≤ (r₃ * ν₃ + r₄ * ν₄ + r₅ * ν₅) ^ 2 / (2 * (a₁ * ν₂)) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
  refine (add_le_add le_rfl hfin).trans (le_of_eq ?_)
  simp only [ha₁, ha₂, hr₃, hr₄, hr₅]
  field_simp
  ring

/-- `N₃ ≤ 8ν₃/(c²Y) + 8y²ν₇/(c⁴Y³)`. -/
theorem nN_prof₃_le {c y ν₃ ν₇ : ℝ} (hc : 0 < c) (hy : 3 / 2 < y) (hν₃ : nN xP₃ ≤ ν₃) (hν₇ : nN xP₇ ≤ ν₇) :
    nN (prof₃ c y) ≤ 8 * ν₃ / (c ^ 2 * (y ^ 2 - 1)) + 8 * y ^ 2 * ν₇ / (c ^ 4 * (y ^ 2 - 1) ^ 3) := by
  have hY : 0 < y ^ 2 - 1 := by nlinarith
  set a := 8 / (c ^ 2 * (y ^ 2 - 1)) with ha
  set b := 8 * y ^ 2 / (c ^ 4 * (y ^ 2 - 1) ^ 3) with hb
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  obtain ⟨-, m3, -, -, -, m7⟩ := memLp_xP
  have hg1 : MemLp (fun x => a * |xP₃ x|) 2 (volume.restrict (Ioi (3 / 2))) := m3.abs.const_mul a
  have hg2 : MemLp (fun x => b * |xP₇ x|) 2 (volume.restrict (Ioi (3 / 2))) := m7.abs.const_mul b
  have h1 := nN_mono (f := prof₃ c y) (g := fun x => a * |xP₃ x| + b * |xP₇ x|)
    (fun x hx => by
      rw [abs_of_nonneg (by unfold prof₃; positivity)]
      exact prof₃_le hc hy hx) (hg1.add hg2)
  have h2 := nN_add_le (fun x => by positivity) (fun x => by positivity) hg1 hg2
  rw [nN_const_mul ha0, nN_const_mul hb0, nN_abs, nN_abs] at h2
  calc nN (prof₃ c y) ≤ a * nN xP₃ + b * nN xP₇ := h1.trans h2
    _ ≤ a * ν₃ + b * ν₇ := by gcongr
    _ = _ := by simp only [ha, hb]; ring

/-! ### Theorem A -/

/-- `1 − ρ = D/Y`. -/
theorem one_sub_rho {y : ℝ} (hy : 3 / 2 < y) : 1 - rho y = (y ^ 2 - 9 / 5) / (y ^ 2 - 1) := by
  have hY : 0 < y ^ 2 - 1 := by nlinarith
  unfold rho; field_simp; ring

/-- **Theorem A**: for `c ≥ 1`, `y > 3/2` and `νᵢ` bounding the six x-norms, `η(c, y) ≤ Σᵢ bᵢ(y)/cⁱ`. -/
theorem etaProfile_le_bM {c y ν₂ ν₃ ν₄ ν₅ ν₆ ν₇ : ℝ} (hc : 1 ≤ c) (hy : 3 / 2 < y) (hν₂ : nN xP₂ ≤ ν₂)
    (hν₃ : nN xP₃ ≤ ν₃) (hν₄ : nN xP₄ ≤ ν₄) (hν₅ : nN xP₅ ≤ ν₅) (hν₆ : nN xP₆ ≤ ν₆) (hν₇ : nN xP₇ ≤ ν₇) :
    etaProfile c y ≤ bM ν₂ ν₃ ν₄ ν₅ ν₆ ν₇ c y := by
  have hY : 0 < y ^ 2 - 1 := by nlinarith
  have hD : 0 < y ^ 2 - 9 / 5 := by nlinarith
  have hy0 : 0 < y := by linarith
  have hc0 : 0 < c := by linarith
  have hν₂0 : 0 < ν₂ := nN_xP₂_pos.trans_le hν₂
  have h1 := nN_prof₁_le hc0 hy hν₅ hν₆
  have h2 := nN_prof₂_le hc hy hν₂ hν₃ hν₄ hν₅ hν₆
  have h3 := nN_prof₃_le hc0 hy hν₃ hν₇
  have hr : 0 < 1 - rho y := by rw [one_sub_rho hy]; positivity
  unfold etaProfile
  calc nN (prof₁ c y) / (1 - rho y) + nN (prof₂ c y) / (1 - rho y) ^ 2 + nN (prof₃ c y) / (1 - rho y) ^ 3
      ≤ (π * y / (c * (y ^ 2 - 1))
            + (6 * ν₅ ^ 2 + 2 * ν₆ ^ 2 + π ^ 4) / (2 * π * y * c ^ 3 * (y ^ 2 - 1))) / (1 - rho y)
        + (4 * y * ν₂ / (c * (y ^ 2 - 1)) + 4 * y * ν₆ / (c ^ 3 * (y ^ 2 - 1) ^ 2)
          + (y ^ 2 - 1) * ((4 * ν₃ + 4 * ν₅ + 2 * ν₄) / (y ^ 2 - 1) + 4 * y ^ 2 * ν₄ / (y ^ 2 - 1) ^ 2) ^ 2
            / (8 * y * ν₂ * c ^ 3)) / (1 - rho y) ^ 2
        + (8 * ν₃ / (c ^ 2 * (y ^ 2 - 1)) + 8 * y ^ 2 * ν₇ / (c ^ 4 * (y ^ 2 - 1) ^ 3)) / (1 - rho y) ^ 3 := by
        gcongr
    _ = bM ν₂ ν₃ ν₄ ν₅ ν₆ ν₇ c y := by
        rw [one_sub_rho hy]
        unfold bM bI₁ bI₂ bI₃ bI₄
        field_simp
        ring

/-! ### Integrability of the coefficients -/

/-- On `y > 3/2`: `y > 0`, `D > 0`, `y² ≤ 5D`, `Y ≤ y²`, `5y² ≤ 9Y`. -/
theorem y_facts {y : ℝ} (hy : 3 / 2 < y) :
    0 < y ∧ 0 < y ^ 2 - 9 / 5 ∧ y ^ 2 ≤ 5 * (y ^ 2 - 9 / 5) ∧ y ^ 2 - 1 ≤ y ^ 2 ∧ 5 * y ^ 2 ≤ 9 * (y ^ 2 - 1) :=
  ⟨by linarith, by nlinarith, by nlinarith, by linarith, by nlinarith⟩

/-- `|b₁(y)| ≤ (5π + 100|ν₂|)/y` on `y > 3/2`. -/
theorem abs_bI₁_le {ν₂ y : ℝ} (hy : 3 / 2 < y) : |bI₁ ν₂ y| ≤ (5 * π + 100 * |ν₂|) / y := by
  obtain ⟨hy0, hD, hyD, hYy, hYy'⟩ := y_facts hy
  have hY : 0 < y ^ 2 - 1 := by nlinarith
  unfold bI₁
  refine (abs_add_le _ _).trans ?_
  rw [abs_of_pos (by positivity : 0 < π * y / (y ^ 2 - 9 / 5)), abs_div, abs_mul, abs_mul, abs_mul,
    abs_of_pos hy0, abs_of_pos hY, abs_of_pos (by positivity : (0 : ℝ) < (y ^ 2 - 9 / 5) ^ 2),
    abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have h1 : π * y / (y ^ 2 - 9 / 5) ≤ 5 * π / y := by
    rw [div_le_div_iff₀ hD hy0]; nlinarith [pi_pos]
  have h2 : 4 * |ν₂| * y * (y ^ 2 - 1) / (y ^ 2 - 9 / 5) ^ 2 ≤ 100 * |ν₂| / y := by
    rw [div_le_div_iff₀ (by positivity) hy0]
    have hD2 : y ^ 4 ≤ 25 * (y ^ 2 - 9 / 5) ^ 2 := by nlinarith
    have hn : 0 ≤ |ν₂| := abs_nonneg _
    have : y * (y ^ 2 - 1) * y ≤ y ^ 4 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this hn, mul_le_mul_of_nonneg_left hD2 hn]
  rw [add_div]
  linarith

/-- `|b₂(y)| ≤ (2000/3)|ν₃|/y` on `y > 3/2`. -/
theorem abs_bI₂_le {ν₃ y : ℝ} (hy : 3 / 2 < y) : |bI₂ ν₃ y| ≤ 2000 / 3 * |ν₃| / y := by
  obtain ⟨hy0, hD, hyD, hYy, hYy'⟩ := y_facts hy
  have hY : 0 < y ^ 2 - 1 := by nlinarith
  unfold bI₂
  rw [abs_div, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8), abs_of_pos (by positivity :
    (0 : ℝ) < (y ^ 2 - 1) ^ 2), abs_of_pos (by positivity : (0 : ℝ) < (y ^ 2 - 9 / 5) ^ 3),
    div_le_div_iff₀ (by positivity) hy0]
  have hn : 0 ≤ |ν₃| := abs_nonneg _
  have hD3 : y ^ 6 ≤ 125 * (y ^ 2 - 9 / 5) ^ 3 := by
    have := pow_le_pow_left₀ (by positivity) hyD 3
    nlinarith
  have hY2 : (y ^ 2 - 1) ^ 2 * y ≤ 2 / 3 * y ^ 6 := by
    have h1 : (y ^ 2 - 1) ^ 2 ≤ y ^ 4 := by nlinarith
    have h2 : y ^ 4 * y ≤ 2 / 3 * y ^ 6 := by nlinarith [pow_pos hy0 4]
    nlinarith [pow_pos hy0 4]
  nlinarith [mul_le_mul_of_nonneg_left hY2 hn, mul_le_mul_of_nonneg_left hD3 hn]

/-- `|b₃(y)| ≤ (10m₁²/(9π) + (400/9)|ν₆| + 5(|A| + 4|ν₄|)²/(2ν₂))/y` on `y > 3/2`, for `ν₂ > 0`. -/
theorem abs_bI₃_le {ν₂ ν₃ ν₄ ν₅ ν₆ y : ℝ} (hν₂ : 0 < ν₂) (hy : 3 / 2 < y) :
    |bI₃ ν₂ ν₃ ν₄ ν₅ ν₆ y| ≤ (10 * (6 * ν₅ ^ 2 + 2 * ν₆ ^ 2 + π ^ 4) / (9 * π) + 400 / 9 * |ν₆|
      + 5 * (|4 * ν₃ + 4 * ν₅ + 2 * ν₄| + 4 * |ν₄|) ^ 2 / (2 * ν₂)) / y := by
  obtain ⟨hy0, hD, hyD, hYy, hYy'⟩ := y_facts hy
  have hY : 0 < y ^ 2 - 1 := by nlinarith
  set m := 6 * ν₅ ^ 2 + 2 * ν₆ ^ 2 + π ^ 4 with hm
  set A := 4 * ν₃ + 4 * ν₅ + 2 * ν₄ with hA
  have hm0 : 0 < m := by positivity
  have hD2 : y ^ 4 ≤ 25 * (y ^ 2 - 9 / 5) ^ 2 := by nlinarith
  have hy2 : 9 / 4 ≤ y ^ 2 := by nlinarith
  unfold bI₃
  rw [← hm, ← hA]
  refine (abs_add_le _ _).trans ?_
  refine (add_le_add (abs_add_le _ _) le_rfl).trans ?_
  have t1 : |m / (2 * π * y * (y ^ 2 - 9 / 5))| ≤ 10 * m / (9 * π) / y := by
    rw [abs_of_pos (by positivity), div_le_div_iff₀ (by positivity) hy0,
      show 10 * m / (9 * π) * (2 * π * y * (y ^ 2 - 9 / 5)) = 20 / 9 * (m * y) * (y ^ 2 - 9 / 5) by
        field_simp; ring]
    nlinarith [mul_pos hm0 hy0]
  have t2 : |4 * ν₆ * y / (y ^ 2 - 9 / 5) ^ 2| ≤ 400 / 9 * |ν₆| / y := by
    rw [abs_div, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_pos hy0,
      abs_of_pos (by positivity : (0 : ℝ) < (y ^ 2 - 9 / 5) ^ 2), div_le_div_iff₀ (by positivity) hy0]
    have hn : 0 ≤ |ν₆| := abs_nonneg _
    have : 4 * y * y * 9 ≤ 400 * (y ^ 2 - 9 / 5) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this hn]
  have t3 : |(A * (y ^ 2 - 1) + 4 * ν₄ * y ^ 2) ^ 2 / (8 * ν₂ * y * (y ^ 2 - 1) * (y ^ 2 - 9 / 5) ^ 2)|
      ≤ 5 * (|A| + 4 * |ν₄|) ^ 2 / (2 * ν₂) / y := by
    rw [abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) hy0,
      show 5 * (|A| + 4 * |ν₄|) ^ 2 / (2 * ν₂) * (8 * ν₂ * y * (y ^ 2 - 1) * (y ^ 2 - 9 / 5) ^ 2)
        = 20 * (|A| + 4 * |ν₄|) ^ 2 * (y * (y ^ 2 - 1) * (y ^ 2 - 9 / 5) ^ 2) by field_simp; ring]
    have hN : |A * (y ^ 2 - 1) + 4 * ν₄ * y ^ 2| ≤ (|A| + 4 * |ν₄|) * y ^ 2 := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos hY, abs_of_pos (by positivity : (0 : ℝ) < y ^ 2),
        abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      nlinarith [abs_nonneg A, abs_nonneg ν₄]
    have hN2 : (A * (y ^ 2 - 1) + 4 * ν₄ * y ^ 2) ^ 2 ≤ (|A| + 4 * |ν₄|) ^ 2 * y ^ 4 := by
      rw [← sq_abs]
      calc |A * (y ^ 2 - 1) + 4 * ν₄ * y ^ 2| ^ 2 ≤ ((|A| + 4 * |ν₄|) * y ^ 2) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) hN 2
        _ = (|A| + 4 * |ν₄|) ^ 2 * y ^ 4 := by ring
    have hden : y ^ 4 * y ≤ 20 * (y * (y ^ 2 - 1) * (y ^ 2 - 9 / 5) ^ 2) := by
      have h1 : y ^ 4 * (y ^ 2 - 1) ≤ 25 * (y ^ 2 - 9 / 5) ^ 2 * (y ^ 2 - 1) :=
        mul_le_mul_of_nonneg_right hD2 hY.le
      nlinarith [pow_pos hy0 4, pow_pos hy0 5]
    have hK : 0 ≤ (|A| + 4 * |ν₄|) ^ 2 := sq_nonneg _
    calc (A * (y ^ 2 - 1) + 4 * ν₄ * y ^ 2) ^ 2 * y ≤ (|A| + 4 * |ν₄|) ^ 2 * y ^ 4 * y :=
          mul_le_mul_of_nonneg_right hN2 hy0.le
      _ ≤ (|A| + 4 * |ν₄|) ^ 2 * (20 * (y * (y ^ 2 - 1) * (y ^ 2 - 9 / 5) ^ 2)) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hden hK
      _ = 20 * (|A| + 4 * |ν₄|) ^ 2 * (y * (y ^ 2 - 1) * (y ^ 2 - 9 / 5) ^ 2) := by ring
  calc _ ≤ 10 * m / (9 * π) / y + 400 / 9 * |ν₆| / y + 5 * (|A| + 4 * |ν₄|) ^ 2 / (2 * ν₂) / y := by
        linarith
    _ = _ := by ring

/-- `|b₄(y)| ≤ (8000/27)|ν₇|/y` on `y > 3/2`. -/
theorem abs_bI₄_le {ν₇ y : ℝ} (hy : 3 / 2 < y) : |bI₄ ν₇ y| ≤ 8000 / 27 * |ν₇| / y := by
  obtain ⟨hy0, hD, hyD, hYy, hYy'⟩ := y_facts hy
  unfold bI₄
  rw [abs_div, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8), abs_of_pos (by positivity :
    (0 : ℝ) < y ^ 2), abs_of_pos (by positivity : (0 : ℝ) < (y ^ 2 - 9 / 5) ^ 3),
    div_le_div_iff₀ (by positivity) hy0]
  have hn : 0 ≤ |ν₇| := abs_nonneg _
  have hD3 : y ^ 6 ≤ 125 * (y ^ 2 - 9 / 5) ^ 3 := by
    have := pow_le_pow_left₀ (by positivity) hyD 3
    nlinarith
  have hy3 : y ^ 2 * y ≤ 8 / 27 * y ^ 6 := by
    have : 27 / 8 ≤ y ^ 3 := by nlinarith
    nlinarith [pow_pos hy0 3]
  nlinarith [mul_le_mul_of_nonneg_left hy3 hn, mul_le_mul_of_nonneg_left hD3 hn]

/-- A measurable `b` with `|b| ≤ C/y` on `(3/2, ∞)` gives `wb ∈ L²(3/2, ∞)`. -/
theorem memLp_wF_mul {b : ℝ → ℝ} {C : ℝ} (hb : Measurable b) (h : ∀ y, 3 / 2 < y → |b y| ≤ C / y) :
    MemLp (fun y => wF y * b y) 2 (volume.restrict (Ioi (3 / 2))) := by
  refine memLp_of_le_inv (C := C) (continuous_wF.1.measurable.mul hb) fun y hy => ?_
  obtain ⟨h0, h1, -, -⟩ := wF_bounds y
  rw [abs_mul, abs_of_nonneg h0]
  exact (mul_le_of_le_one_left (abs_nonneg _) h1).trans (h y hy)

/-- `wb₁, wb₂, wb₃, wb₄ ∈ L²(3/2, ∞)` for `ν₂ > 0`. -/
theorem memLp_wF_mul_bI {ν₂ ν₃ ν₄ ν₅ ν₆ ν₇ : ℝ} (hν₂ : 0 < ν₂) :
    MemLp (fun y => wF y * bI₁ ν₂ y) 2 (volume.restrict (Ioi (3 / 2)))
      ∧ MemLp (fun y => wF y * bI₂ ν₃ y) 2 (volume.restrict (Ioi (3 / 2)))
      ∧ MemLp (fun y => wF y * bI₃ ν₂ ν₃ ν₄ ν₅ ν₆ y) 2 (volume.restrict (Ioi (3 / 2)))
      ∧ MemLp (fun y => wF y * bI₄ ν₇ y) 2 (volume.restrict (Ioi (3 / 2))) :=
  ⟨memLp_wF_mul (by unfold bI₁; fun_prop) fun y hy => abs_bI₁_le hy,
    memLp_wF_mul (by unfold bI₂; fun_prop) fun y hy => abs_bI₂_le hy,
    memLp_wF_mul (by unfold bI₃; fun_prop) fun y hy => abs_bI₃_le hν₂ hy,
    memLp_wF_mul (by unfold bI₄; fun_prop) fun y hy => abs_bI₄_le hy⟩

/-- `w·Bm = Σᵢ c⁻ⁱ(w bᵢ)`. -/
theorem wF_mul_bM_eq (ν₂ ν₃ ν₄ ν₅ ν₆ ν₇ c y : ℝ) :
    wF y * bM ν₂ ν₃ ν₄ ν₅ ν₆ ν₇ c y = 1 / c * (wF y * bI₁ ν₂ y) + 1 / c ^ 2 * (wF y * bI₂ ν₃ y)
      + 1 / c ^ 3 * (wF y * bI₃ ν₂ ν₃ ν₄ ν₅ ν₆ y) + 1 / c ^ 4 * (wF y * bI₄ ν₇ y) := by
  unfold bM; ring

/-- `w·Bm ∈ L²(3/2, ∞)` for `ν₂ > 0`. -/
theorem memLp_wF_mul_bM {ν₂ ν₃ ν₄ ν₅ ν₆ ν₇ : ℝ} (c : ℝ) (hν₂ : 0 < ν₂) :
    MemLp (fun y => wF y * bM ν₂ ν₃ ν₄ ν₅ ν₆ ν₇ c y) 2 (volume.restrict (Ioi (3 / 2))) := by
  obtain ⟨m1, m2, m3, m4⟩ := memLp_wF_mul_bI (ν₃ := ν₃) (ν₄ := ν₄) (ν₅ := ν₅) (ν₆ := ν₆) (ν₇ := ν₇) hν₂
  simp_rw [wF_mul_bM_eq]
  exact (((m1.const_mul _).add (m2.const_mul _)).add (m3.const_mul _)).add (m4.const_mul _)

/-- Minkowski: `‖w·Bm‖ ≤ Σᵢ ‖w bᵢ‖/cⁱ`. -/
theorem nN_wF_mul_bM_le {c ν₂ ν₃ ν₄ ν₅ ν₆ ν₇ : ℝ} (hc : 0 < c) (hν₂ : 0 < ν₂) :
    nN (fun y => wF y * bM ν₂ ν₃ ν₄ ν₅ ν₆ ν₇ c y)
      ≤ nN (fun y => wF y * bI₁ ν₂ y) / c + nN (fun y => wF y * bI₂ ν₃ y) / c ^ 2
        + nN (fun y => wF y * bI₃ ν₂ ν₃ ν₄ ν₅ ν₆ y) / c ^ 3 + nN (fun y => wF y * bI₄ ν₇ y) / c ^ 4 := by
  obtain ⟨m1, m2, m3, m4⟩ := memLp_wF_mul_bI (ν₃ := ν₃) (ν₄ := ν₄) (ν₅ := ν₅) (ν₆ := ν₆) (ν₇ := ν₇) hν₂
  set f₁ := fun y => wF y * bI₁ ν₂ y
  set f₂ := fun y => wF y * bI₂ ν₃ y
  set f₃ := fun y => wF y * bI₃ ν₂ ν₃ ν₄ ν₅ ν₆ y
  set f₄ := fun y => wF y * bI₄ ν₇ y
  have k1 : (0 : ℝ) ≤ 1 / c := by positivity
  have k2 : (0 : ℝ) ≤ 1 / c ^ 2 := by positivity
  have k3 : (0 : ℝ) ≤ 1 / c ^ 3 := by positivity
  have k4 : (0 : ℝ) ≤ 1 / c ^ 4 := by positivity
  have g1 : MemLp (fun y => 1 / c * |f₁ y|) 2 (volume.restrict (Ioi (3 / 2))) := m1.abs.const_mul (1 / c)
  have g2 : MemLp (fun y => 1 / c ^ 2 * |f₂ y|) 2 (volume.restrict (Ioi (3 / 2))) := m2.abs.const_mul _
  have g3 : MemLp (fun y => 1 / c ^ 3 * |f₃ y|) 2 (volume.restrict (Ioi (3 / 2))) := m3.abs.const_mul _
  have g4 : MemLp (fun y => 1 / c ^ 4 * |f₄ y|) 2 (volume.restrict (Ioi (3 / 2))) := m4.abs.const_mul _
  have gS : MemLp (fun y => 1 / c * |f₁ y| + 1 / c ^ 2 * |f₂ y| + 1 / c ^ 3 * |f₃ y| + 1 / c ^ 4 * |f₄ y|) 2
      (volume.restrict (Ioi (3 / 2))) := ((g1.add g2).add g3).add g4
  have hmono := nN_mono (f := fun y => wF y * bM ν₂ ν₃ ν₄ ν₅ ν₆ ν₇ c y)
    (g := fun y => 1 / c * |f₁ y| + 1 / c ^ 2 * |f₂ y| + 1 / c ^ 3 * |f₃ y| + 1 / c ^ 4 * |f₄ y|)
    (fun y _ => by
      rw [wF_mul_bM_eq]
      refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
        ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)) ?_) <;>
      rw [abs_mul, abs_of_nonneg (by positivity)])
    gS
  have g12 : MemLp (fun y => 1 / c * |f₁ y| + 1 / c ^ 2 * |f₂ y|) 2
      (volume.restrict (Ioi (3 / 2))) := g1.add g2
  have g123 : MemLp (fun y => 1 / c * |f₁ y| + 1 / c ^ 2 * |f₂ y| + 1 / c ^ 3 * |f₃ y|) 2
      (volume.restrict (Ioi (3 / 2))) := g12.add g3
  have a1 := nN_add_le (f := fun y => 1 / c * |f₁ y|) (g := fun y => 1 / c ^ 2 * |f₂ y|)
    (fun y => by positivity) (fun y => by positivity) g1 g2
  have a2 := nN_add_le (f := fun y => 1 / c * |f₁ y| + 1 / c ^ 2 * |f₂ y|)
    (g := fun y => 1 / c ^ 3 * |f₃ y|) (fun y => by positivity) (fun y => by positivity) g12 g3
  have a3 := nN_add_le (f := fun y => 1 / c * |f₁ y| + 1 / c ^ 2 * |f₂ y| + 1 / c ^ 3 * |f₃ y|)
    (g := fun y => 1 / c ^ 4 * |f₄ y|) (fun y => by positivity) (fun y => by positivity) g123 g4
  rw [nN_const_mul k1, nN_const_mul k2, nN_abs, nN_abs] at a1
  rw [nN_const_mul k3, nN_abs] at a2
  rw [nN_const_mul k4, nN_abs] at a3
  calc _ ≤ _ := hmono
    _ ≤ _ := a3
    _ ≤ 1 / c * nN f₁ + 1 / c ^ 2 * nN f₂ + 1 / c ^ 3 * nN f₃ + 1 / c ^ 4 * nN f₄ := by linarith
    _ = _ := by ring

/-! ### The far-far constant -/

/-- **`FarFarBound`'s three majorant hypotheses** for `Bm = Σ bᵢ/cⁱ` and `C_η = C_η^sym(c)`, given `c ≥ 1`, `νᵢ` bounding
the x-norms and `βᵢ ≥ ‖w bᵢ‖_{L²(3/2,∞)}`. -/
theorem ceta_hyps {c ν₂ ν₃ ν₄ ν₅ ν₆ ν₇ β₁ β₂ β₃ β₄ : ℝ} (hc : 1 ≤ c) (hν₂ : nN xP₂ ≤ ν₂)
    (hν₃ : nN xP₃ ≤ ν₃) (hν₄ : nN xP₄ ≤ ν₄) (hν₅ : nN xP₅ ≤ ν₅) (hν₆ : nN xP₆ ≤ ν₆) (hν₇ : nN xP₇ ≤ ν₇)
    (hβ₁ : nN (fun y => wF y * bI₁ ν₂ y) ≤ β₁) (hβ₂ : nN (fun y => wF y * bI₂ ν₃ y) ≤ β₂)
    (hβ₃ : nN (fun y => wF y * bI₃ ν₂ ν₃ ν₄ ν₅ ν₆ y) ≤ β₃) (hβ₄ : nN (fun y => wF y * bI₄ ν₇ y) ≤ β₄) :
    (∀ y, 3 / 2 < y → etaProfile c y ≤ bM ν₂ ν₃ ν₄ ν₅ ν₆ ν₇ c y)
      ∧ IntegrableOn (fun y => wF y ^ 2 * bM ν₂ ν₃ ν₄ ν₅ ν₆ ν₇ c y ^ 2) (Ioi (3 / 2))
      ∧ 2 * c / π * (∫ y in Ioi (3 / 2 : ℝ), wF y ^ 2 * bM ν₂ ν₃ ν₄ ν₅ ν₆ ν₇ c y ^ 2)
          ≤ cEtaSym β₁ β₂ β₃ β₄ c / c := by
  have hc0 : 0 < c := by linarith
  have hν₂0 : 0 < ν₂ := nN_xP₂_pos.trans_le hν₂
  have hM := memLp_wF_mul_bM (ν₃ := ν₃) (ν₄ := ν₄) (ν₅ := ν₅) (ν₆ := ν₆) (ν₇ := ν₇) c hν₂0
  have hsq : (fun y => wF y ^ 2 * bM ν₂ ν₃ ν₄ ν₅ ν₆ ν₇ c y ^ 2)
      = fun y => (wF y * bM ν₂ ν₃ ν₄ ν₅ ν₆ ν₇ c y) ^ 2 := by funext y; ring
  refine ⟨fun y hy => etaProfile_le_bM hc hy hν₂ hν₃ hν₄ hν₅ hν₆ hν₇, ?_, ?_⟩
  · rw [hsq]; exact hM.integrable_sq
  · have hN := nN_wF_mul_bM_le (ν₃ := ν₃) (ν₄ := ν₄) (ν₅ := ν₅) (ν₆ := ν₆) (ν₇ := ν₇) hc0 hν₂0
    have hS : nN (fun y => wF y * bM ν₂ ν₃ ν₄ ν₅ ν₆ ν₇ c y) ≤ β₁ / c + β₂ / c ^ 2 + β₃ / c ^ 3 + β₄ / c ^ 4 := by
      refine hN.trans ?_
      gcongr
    have hI : ∫ y in Ioi (3 / 2 : ℝ), wF y ^ 2 * bM ν₂ ν₃ ν₄ ν₅ ν₆ ν₇ c y ^ 2
        = nN (fun y => wF y * bM ν₂ ν₃ ν₄ ν₅ ν₆ ν₇ c y) ^ 2 := by rw [hsq, nN_sq]
    rw [hI]
    have h0 : 0 ≤ nN (fun y => wF y * bM ν₂ ν₃ ν₄ ν₅ ν₆ ν₇ c y) := Real.sqrt_nonneg _
    have h2 := pow_le_pow_left₀ h0 hS 2
    calc 2 * c / π * nN (fun y => wF y * bM ν₂ ν₃ ν₄ ν₅ ν₆ ν₇ c y) ^ 2
        ≤ 2 * c / π * (β₁ / c + β₂ / c ^ 2 + β₃ / c ^ 3 + β₄ / c ^ 4) ^ 2 := by gcongr
      _ = cEtaSym β₁ β₂ β₃ β₄ c / c := by unfold cEtaSym; field_simp

open Cvs.L2a.AngularProlateTailPositive Cvs.Upstream.CosineTransformHalfLine in
/-- **The far-far bound with `C_η^sym`**: `FarFarBound`'s `farFar_le` with `Bm = Σ bᵢ/cⁱ`, for `c ≥ 1`, `νᵢ` bounding the
x-norms and `βᵢ ≥ ‖w bᵢ‖`: `‖wK(wΦ)‖² ≤ (C_η^sym(c)/c) ∫_{Ioi 1} Φ²`. -/
theorem farFar_le_sym {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 1 ≤ c) (hχ : Function.Injective χ) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i ≤ c ^ 2)
    {ν₂ ν₃ ν₄ ν₅ ν₆ ν₇ β₁ β₂ β₃ β₄ : ℝ} (hν₂ : nN xP₂ ≤ ν₂)
    (hν₃ : nN xP₃ ≤ ν₃) (hν₄ : nN xP₄ ≤ ν₄) (hν₅ : nN xP₅ ≤ ν₅) (hν₆ : nN xP₆ ≤ ν₆) (hν₇ : nN xP₇ ≤ ν₇)
    (hβ₁ : nN (fun y => wF y * bI₁ ν₂ y) ≤ β₁) (hβ₂ : nN (fun y => wF y * bI₂ ν₃ y) ≤ β₂)
    (hβ₃ : nN (fun y => wF y * bI₃ ν₂ ν₃ ν₄ ν₅ ν₆ y) ≤ β₃) (hβ₄ : nN (fun y => wF y * bI₄ ν₇ y) ≤ β₄) :
    ∫ y in Ioi 1, ‖(wF y : ℂ)
        * calK c ((Ioi 1).indicator fun x => ((wF x * ∑ i, a i * psi c (g i) x : ℝ) : ℂ)) y‖ ^ 2
      ≤ cEtaSym β₁ β₂ β₃ β₄ c / c * ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2 := by
  obtain ⟨hBm, hBi, hBint⟩ := ceta_hyps hc hν₂ hν₃ hν₄ hν₅ hν₆ hν₇ hβ₁ hβ₂ hβ₃ hβ₄
  exact farFar_le a hg hg₁ hg₂c hang (by linarith) hχ hχ0 hχc hBm hBi hBint

/-- `C_η^sym` is nonincreasing on `c > 0` when every `βᵢ ≥ 0`. -/
theorem cEtaSym_antitoneOn {β₁ β₂ β₃ β₄ : ℝ} (h₁ : 0 ≤ β₁) (h₂ : 0 ≤ β₂) (h₃ : 0 ≤ β₃) (h₄ : 0 ≤ β₄) :
    AntitoneOn (cEtaSym β₁ β₂ β₃ β₄) (Ioi 0) := by
  intro s hs t ht hst
  have hs0 : (0 : ℝ) < s := hs
  have ht0 : (0 : ℝ) < t := ht
  unfold cEtaSym
  have k2 : β₂ / t ≤ β₂ / s := div_le_div_of_nonneg_left h₂ hs0 hst
  have k3 : β₃ / t ^ 2 ≤ β₃ / s ^ 2 := div_le_div_of_nonneg_left h₃ (by positivity) (by gcongr)
  have k4 : β₄ / t ^ 3 ≤ β₄ / s ^ 3 := div_le_div_of_nonneg_left h₄ (by positivity) (by gcongr)
  have hpos : 0 ≤ β₁ + β₂ / t + β₃ / t ^ 2 + β₄ / t ^ 3 := by positivity
  have hle : β₁ + β₂ / t + β₃ / t ^ 2 + β₄ / t ^ 3 ≤ β₁ + β₂ / s + β₃ / s ^ 2 + β₄ / s ^ 3 := by linarith
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hpos hle 2) (by positivity)

end Cvs.L2a.FarFarProfileClosedForm

end
