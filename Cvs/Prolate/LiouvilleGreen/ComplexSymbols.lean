import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Cvs.Upstream.HalfStripRayIntegrals

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Liouville–Green symbols of the prolate equation at level `χ = c²T`

`P = 1 − z²`, `Q = T − z²`, `p = Q/P`, `Φ′ = p^{1/2}`, `Λ = P^{−1/2}p^{−1/4}`, `ℓ = Λ′/Λ = z/2P + z/2Q` and
the residual `σ = 1/4P + (3/4)(2T − 1)/Q + (5/4)T(1 − T)/Q² = −2zℓ + P(ℓ² + ℓ′)`, with their bounds on the
half-strip `U_a`, `a² < T ≤ 1`.
-/

noncomputable section

open Real Set
open Complex (I)
open Cvs.Upstream.HalfStripRayIntegrals (strip RayBound)

namespace Cvs.Prolate.LiouvilleGreen.ComplexSymbols

/-- `P(z) = 1 − z²`. -/
def pP (z : ℂ) : ℂ := 1 - z ^ 2

/-- `Q(z) = T − z²`. -/
def pQ (T : ℝ) (z : ℂ) : ℂ := T - z ^ 2

/-- `p = Q/P`. -/
def pp (T : ℝ) (z : ℂ) : ℂ := pQ T z / pP z

/-- The Liouville–Green rate `Φ′ = p^{1/2}`. -/
def phiD (T : ℝ) (z : ℂ) : ℂ := Complex.exp (Complex.log (pp T z) / 2)

/-- The Liouville–Green amplitude `Λ = P^{−1/2}p^{−1/4}`. -/
def lam (T : ℝ) (z : ℂ) : ℂ := Complex.exp (-(Complex.log (pP z) / 2) - Complex.log (pp T z) / 4)

/-- `ℓ = Λ′/Λ = z/2P + z/2Q`. -/
def ell (T : ℝ) (z : ℂ) : ℂ := z / (2 * pP z) + z / (2 * pQ T z)

/-- `ℓ′ = 1/2P + 1/2Q + z²/P² + z²/Q²`. -/
def ellD (T : ℝ) (z : ℂ) : ℂ := 1 / (2 * pP z) + 1 / (2 * pQ T z) + z ^ 2 / pP z ^ 2 + z ^ 2 / pQ T z ^ 2

/-- The Liouville–Green residual `σ`. -/
def sig (T : ℝ) (z : ℂ) : ℂ :=
  1 / (4 * pP z) + 3 / 4 * (2 * T - 1) / pQ T z + 5 / 4 * (T * (1 - T)) / pQ T z ^ 2

/-- The error-control density `r = Λ²σ`. -/
def rr (T : ℝ) (z : ℂ) : ℂ := lam T z ^ 2 * sig T z

/-- The ray constant `K_r = (1 + 5T(1 − T)/4m)/m` of `r`. -/
def kR (T m : ℝ) : ℝ := (1 + 5 / 4 * (T * (1 - T)) / m) / m

/-! ### Real parts and norms on the strip -/

section strip

variable {a T : ℝ} {z : ℂ}

theorem re_pP (z : ℂ) : (pP z).re = 1 - z.re ^ 2 + z.im ^ 2 := by simp [pP, sq]; ring

theorem re_pQ (T : ℝ) (z : ℂ) : (pQ T z).re = T - z.re ^ 2 + z.im ^ 2 := by simp [pQ, sq]; ring

theorem sq_re_lt (hz : z ∈ strip a) : z.re ^ 2 < a ^ 2 := by
  have h := hz.1
  have ha : 0 < a := lt_of_le_of_lt (abs_nonneg _) h
  rw [← sq_abs]; exact pow_lt_pow_left₀ h (abs_nonneg _) two_ne_zero

theorem pQ_eq (T : ℝ) (z : ℂ) : pQ T z = pP z - (1 - T) := by unfold pQ pP; ring

theorem le_re_pQ (hz : z ∈ strip a) : T - a ^ 2 + z.im ^ 2 ≤ (pQ T z).re := by
  rw [re_pQ]; linarith [sq_re_lt hz]

theorem le_re_pP (hz : z ∈ strip a) : 1 - a ^ 2 + z.im ^ 2 ≤ (pP z).re := by
  rw [re_pP]; linarith [sq_re_lt hz]

theorem le_norm_pQ (hz : z ∈ strip a) : T - a ^ 2 + z.im ^ 2 ≤ ‖pQ T z‖ :=
  (le_re_pQ hz).trans (Complex.re_le_norm _)

theorem le_norm_pP (hT : T ≤ 1) (hz : z ∈ strip a) : T - a ^ 2 + z.im ^ 2 ≤ ‖pP z‖ :=
  (by linarith [le_re_pP hz] : T - a ^ 2 + z.im ^ 2 ≤ (pP z).re).trans (Complex.re_le_norm _)

theorem re_pP_pos (hT : a ^ 2 < T) (hT1 : T ≤ 1) (hz : z ∈ strip a) : 0 < (pP z).re := by
  have := le_re_pP hz; nlinarith [sq_nonneg z.im]

theorem re_pQ_pos (hT : a ^ 2 < T) (hz : z ∈ strip a) : 0 < (pQ T z).re := by
  have := le_re_pQ (T := T) hz; nlinarith [sq_nonneg z.im]

theorem pP_ne (hT : a ^ 2 < T) (hT1 : T ≤ 1) (hz : z ∈ strip a) : pP z ≠ 0 := fun h => by
  have := re_pP_pos hT hT1 hz; rw [h] at this; simp at this

theorem pQ_ne (hT : a ^ 2 < T) (hz : z ∈ strip a) : pQ T z ≠ 0 := fun h => by
  have := re_pQ_pos hT hz; rw [h] at this; simp at this

theorem pP_mem_slitPlane (hT : a ^ 2 < T) (hT1 : T ≤ 1) (hz : z ∈ strip a) : pP z ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.2 (Or.inl (re_pP_pos hT hT1 hz))

/-- `Re(1/w) ≤ 1/Re w` for `Re w > 0`. -/
theorem re_inv_le {w : ℂ} (hw : 0 < w.re) : (w⁻¹).re ≤ 1 / w.re := by
  rw [Complex.inv_re, div_le_div_iff₀ (by
    rw [Complex.normSq_apply]; nlinarith [mul_self_nonneg w.im]) hw]
  rw [Complex.normSq_apply]; nlinarith [mul_self_nonneg w.im]

/-- `Re p ≥ (T − L²)/(1 − L²)` whenever `(Re z)² ≤ L² < 1`. -/
theorem re_pp_ge {L : ℝ} (hT1 : T ≤ 1) (hL : L ^ 2 < 1) (hzL : z.re ^ 2 ≤ L ^ 2) :
    (T - L ^ 2) / (1 - L ^ 2) ≤ (pp T z).re := by
  have hP : 1 - L ^ 2 ≤ (pP z).re := by rw [re_pP]; nlinarith [sq_nonneg z.im]
  have hP0 : 0 < (pP z).re := by linarith
  have hPne : pP z ≠ 0 := fun h => by rw [h] at hP0; simp at hP0
  have e : pp T z = 1 - (1 - T) * (pP z)⁻¹ := by
    unfold pp; rw [pQ_eq]; field_simp
  have h1 := re_inv_le hP0
  have h2 : 1 / (pP z).re ≤ 1 / (1 - L ^ 2) := one_div_le_one_div_of_le (by linarith) hP
  have hre : (1 - (1 - (T : ℂ)) * (pP z)⁻¹).re = 1 - (1 - T) * (pP z)⁻¹.re := by simp [Complex.mul_re]
  rw [e, hre]
  have h3 : (1 - T) * (pP z)⁻¹.re ≤ (1 - T) * (1 / (1 - L ^ 2)) :=
    mul_le_mul_of_nonneg_left (h1.trans h2) (by linarith)
  have h4 : (T - L ^ 2) / (1 - L ^ 2) = 1 - (1 - T) * (1 / (1 - L ^ 2)) := by
    field_simp [show (1 - L ^ 2) ≠ 0 by linarith]; ring_nf
  rw [h4]; linarith

theorem re_pp_pos (hT : a ^ 2 < T) (hT1 : T ≤ 1) (hz : z ∈ strip a) : 0 < (pp T z).re := by
  have ha1 : a ^ 2 < 1 := lt_of_lt_of_le hT hT1
  have h := re_pp_ge (T := T) hT1 ha1 (sq_re_lt hz).le
  have : 0 < (T - a ^ 2) / (1 - a ^ 2) := div_pos (by linarith) (by linarith)
  linarith

theorem pp_mem_slitPlane (hT : a ^ 2 < T) (hT1 : T ≤ 1) (hz : z ∈ strip a) : pp T z ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.2 (Or.inl (re_pp_pos hT hT1 hz))

theorem pp_ne (hT : a ^ 2 < T) (hT1 : T ≤ 1) (hz : z ∈ strip a) : pp T z ≠ 0 :=
  Complex.slitPlane_ne_zero (pp_mem_slitPlane hT hT1 hz)

end strip

/-! ### The rate `Φ′` and the amplitude `Λ` -/

section rate

variable {a T : ℝ} {z : ℂ}

theorem phiD_sq (hp : pp T z ≠ 0) : phiD T z ^ 2 = pp T z := by
  unfold phiD
  rw [← Complex.exp_nat_mul]; push_cast
  rw [show (2 : ℂ) * (Complex.log (pp T z) / 2) = Complex.log (pp T z) by ring, Complex.exp_log hp]

theorem phiD_ne (T : ℝ) (z : ℂ) : phiD T z ≠ 0 := Complex.exp_ne_zero _

/-- `Λ²PΦ′ = 1`. -/
theorem lam_sq_mul (hP : pP z ≠ 0) : lam T z ^ 2 * pP z * phiD T z = 1 := by
  have hPe : pP z = Complex.exp (Complex.log (pP z)) := (Complex.exp_log hP).symm
  calc lam T z ^ 2 * pP z * phiD T z = Complex.exp (2 * (-(Complex.log (pP z) / 2) - Complex.log (pp T z) / 4)) *
        Complex.exp (Complex.log (pP z)) * Complex.exp (Complex.log (pp T z) / 2) := by
          rw [← hPe]; unfold lam phiD; rw [← Complex.exp_nat_mul]; push_cast; ring_nf
    _ = 1 := by
          rw [← Complex.exp_add, ← Complex.exp_add]
          rw [show (2 : ℂ) * (-(Complex.log (pP z) / 2) - Complex.log (pp T z) / 4) + Complex.log (pP z) +
            Complex.log (pp T z) / 2 = 0 by ring, Complex.exp_zero]

theorem re_phiD_nonneg (T : ℝ) (z : ℂ) : 0 ≤ (phiD T z).re := by
  unfold phiD
  rw [Complex.exp_re]
  refine mul_nonneg (Real.exp_pos _).le (Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩)
  · rw [Complex.div_ofNat_im, Complex.log_im]; linarith [Complex.neg_pi_lt_arg (pp T z)]
  · rw [Complex.div_ofNat_im, Complex.log_im]; linarith [Complex.arg_le_pi (pp T z)]

/-- `Re Φ′ ≥ √(Re p)`. -/
theorem sqrt_re_pp_le (hp : pp T z ∈ Complex.slitPlane) : √((pp T z).re) ≤ (phiD T z).re := by
  have h0 := re_phiD_nonneg T z
  have hsq := phiD_sq (Complex.slitPlane_ne_zero hp)
  have hre : (pp T z).re = (phiD T z).re ^ 2 - (phiD T z).im ^ 2 := by
    rw [← hsq]; simp [sq, Complex.mul_re]
  rw [hre]
  calc √((phiD T z).re ^ 2 - (phiD T z).im ^ 2) ≤ √((phiD T z).re ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (phiD T z).im])
    _ = (phiD T z).re := Real.sqrt_sq h0

theorem one_le_norm_phiD_add (T : ℝ) (z : ℂ) : 1 ≤ ‖phiD T z + 1‖ := by
  have := re_phiD_nonneg T z
  have h : (phiD T z + 1).re = (phiD T z).re + 1 := by simp
  linarith [Complex.re_le_norm (phiD T z + 1)]

/-- `|Φ′ − 1| ≤ |p − 1|`. -/
theorem norm_phiD_sub_one_le (hp : pp T z ∈ Complex.slitPlane) : ‖phiD T z - 1‖ ≤ ‖pp T z - 1‖ := by
  have hsq := phiD_sq (Complex.slitPlane_ne_zero hp)
  have e : pp T z - 1 = (phiD T z - 1) * (phiD T z + 1) := by rw [← hsq]; ring
  rw [e, norm_mul]
  have := one_le_norm_phiD_add T z
  nlinarith [norm_nonneg (phiD T z - 1)]

/-- `|p − 1| ≤ (1 − T)/(m + y²)` on the strip, `m = T − a²`. -/
theorem norm_pp_sub_one_le (hT : a ^ 2 < T) (hT1 : T ≤ 1) (hz : z ∈ strip a) :
    ‖pp T z - 1‖ ≤ (1 - T) / (T - a ^ 2 + z.im ^ 2) := by
  have hP := pP_ne hT hT1 hz
  have e : pp T z - 1 = -((1 - T : ℝ) : ℂ) / pP z := by unfold pp; rw [pQ_eq]; field_simp; push_cast; ring
  rw [e, norm_div, norm_neg, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have h1 := le_norm_pP (T := T) hT1 hz
  have h2 : 0 < T - a ^ 2 + z.im ^ 2 := by nlinarith [sq_nonneg z.im]
  exact div_le_div_of_nonneg_left (by linarith) h2 h1

/-- `|Φ′ − 1| ≤ (1 − T)/(m + y²)` on the strip. -/
theorem rayBound_phiD_sub_one (hT : a ^ 2 < T) (hT1 : T ≤ 1) :
    RayBound a (T - a ^ 2) (1 - T) (fun z => phiD T z - 1) := fun _ hz =>
  (norm_phiD_sub_one_le (pp_mem_slitPlane hT hT1 hz)).trans (norm_pp_sub_one_le hT hT1 hz)

/-- `|Φ′|² ≤ 1 + (1 − T)/m` on the strip. -/
theorem norm_phiD_sq_le (hT : a ^ 2 < T) (hT1 : T ≤ 1) (hz : z ∈ strip a) :
    ‖phiD T z‖ ^ 2 ≤ 1 + (1 - T) / (T - a ^ 2) := by
  have hsq := phiD_sq (pp_ne hT hT1 hz)
  have h0 := norm_pp_sub_one_le hT hT1 hz
  have h2 : 0 < T - a ^ 2 := by linarith
  have h3 : (1 - T) / (T - a ^ 2 + z.im ^ 2) ≤ (1 - T) / (T - a ^ 2) :=
    div_le_div_of_nonneg_left (by linarith) h2 (by nlinarith [sq_nonneg z.im])
  rw [← norm_pow, hsq]
  calc ‖pp T z‖ = ‖(pp T z - 1) + 1‖ := by ring_nf
    _ ≤ ‖pp T z - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ ≤ 1 + (1 - T) / (T - a ^ 2) := by rw [norm_one]; linarith

/-- `(|P| |Φ′|)² = |P| |Q|`. -/
theorem norm_pP_mul_phiD_sq (hP : pP z ≠ 0) (hp : pp T z ≠ 0) :
    (‖pP z‖ * ‖phiD T z‖) ^ 2 = ‖pP z‖ * ‖pQ T z‖ := by
  have hsq := phiD_sq hp
  have : ‖phiD T z‖ ^ 2 = ‖pQ T z‖ / ‖pP z‖ := by rw [← norm_pow, hsq, pp, norm_div]
  rw [mul_pow, this]
  have : 0 < ‖pP z‖ := norm_pos_iff.2 hP
  field_simp

/-- `|Λ|² ≤ 1/(m + y²)` on the strip. -/
theorem norm_lam_sq_le (hT : a ^ 2 < T) (hT1 : T ≤ 1) (hz : z ∈ strip a) :
    ‖lam T z‖ ^ 2 ≤ 1 / (T - a ^ 2 + z.im ^ 2) := by
  have hP := pP_ne hT hT1 hz
  have hp := pp_ne hT hT1 hz
  have h1 := lam_sq_mul (T := T) hP
  have h2 : ‖lam T z‖ ^ 2 * (‖pP z‖ * ‖phiD T z‖) = 1 := by
    have := congrArg norm h1
    rwa [norm_mul, norm_mul, norm_pow, norm_one, mul_assoc] at this
  have hm : 0 < T - a ^ 2 + z.im ^ 2 := by nlinarith [sq_nonneg z.im]
  have h3 : T - a ^ 2 + z.im ^ 2 ≤ ‖pP z‖ * ‖phiD T z‖ := by
    have e := norm_pP_mul_phiD_sq hP hp
    have h4 : (T - a ^ 2 + z.im ^ 2) ^ 2 ≤ (‖pP z‖ * ‖phiD T z‖) ^ 2 := by
      rw [e, sq]
      exact mul_le_mul (le_norm_pP hT1 hz) (le_norm_pQ hz) hm.le (norm_nonneg _)
    exact (pow_le_pow_iff_left₀ hm.le (by positivity) two_ne_zero).1 h4
  have h5 : 0 < ‖pP z‖ * ‖phiD T z‖ := by linarith
  rw [show ‖lam T z‖ ^ 2 = 1 / (‖pP z‖ * ‖phiD T z‖) by rw [eq_div_iff h5.ne']; exact h2]
  exact one_div_le_one_div_of_le hm h3

/-- `|σ| ≤ (1 + 5T(1 − T)/4m)/(m + y²)` on the strip. -/
theorem norm_sig_le (hT0 : 0 ≤ T) (hT : a ^ 2 < T) (hT1 : T ≤ 1) (hz : z ∈ strip a) :
    ‖sig T z‖ ≤ (1 + 5 / 4 * (T * (1 - T)) / (T - a ^ 2)) / (T - a ^ 2 + z.im ^ 2) := by
  set D := T - a ^ 2 + z.im ^ 2
  set m := T - a ^ 2
  have hm : 0 < m := by simp only [m]; linarith
  have hD : m ≤ D := by simp only [D, m]; nlinarith [sq_nonneg z.im]
  have hD0 : 0 < D := by linarith
  have hP := le_norm_pP hT1 hz
  have hQ := le_norm_pQ (T := T) hz
  have hP0 : 0 < ‖pP z‖ := by linarith
  have hQ0 : 0 < ‖pQ T z‖ := by linarith
  have e1 : ‖1 / (4 * pP z)‖ ≤ 1 / 4 * (1 / D) := by
    rw [norm_div, norm_one, norm_mul, show ‖(4 : ℂ)‖ = 4 by simp]
    rw [show 1 / 4 * (1 / D) = 1 / (4 * D) by ring_nf]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have e2 : ‖3 / 4 * (2 * (T : ℂ) - 1) / pQ T z‖ ≤ 3 / 4 * |2 * T - 1| * (1 / D) := by
    rw [norm_div, norm_mul, show ‖(3 / 4 : ℂ)‖ = 3 / 4 by norm_num [Complex.norm_div],
      show (2 * (T : ℂ) - 1) = ((2 * T - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hD0 hQ) (by positivity)
  have e3 : ‖5 / 4 * ((T : ℂ) * (1 - T)) / pQ T z ^ 2‖ ≤ 5 / 4 * (T * (1 - T)) / m * (1 / D) := by
    rw [norm_div, norm_mul, show ‖(5 / 4 : ℂ)‖ = 5 / 4 by norm_num [Complex.norm_div],
      show ((T : ℂ) * (1 - T)) = ((T * (1 - T) : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (mul_nonneg hT0 (by linarith)), norm_pow]
    have h1 : m * D ≤ ‖pQ T z‖ ^ 2 := by rw [sq]; exact mul_le_mul (hD.trans hQ) hQ hD0.le (norm_nonneg _)
    rw [show 5 / 4 * (T * (1 - T)) / m * (1 / D) = 5 / 4 * (T * (1 - T)) / (m * D) by field_simp]
    exact div_le_div_of_nonneg_left (by have := mul_nonneg hT0 (by linarith : (0 : ℝ) ≤ 1 - T); positivity)
      (by positivity) h1
  have hab : |2 * T - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  calc ‖sig T z‖ ≤ ‖1 / (4 * pP z)‖ + ‖3 / 4 * (2 * (T : ℂ) - 1) / pQ T z‖ +
        ‖5 / 4 * ((T : ℂ) * (1 - T)) / pQ T z ^ 2‖ := norm_add₃_le
    _ ≤ 1 / 4 * (1 / D) + 3 / 4 * |2 * T - 1| * (1 / D) + 5 / 4 * (T * (1 - T)) / m * (1 / D) := by
        linarith
    _ ≤ (1 + 5 / 4 * (T * (1 - T)) / m) / D := by
        rw [div_eq_mul_one_div (1 + _)]
        have : 0 ≤ 1 / D := by positivity
        nlinarith

/-- **The ray bound of `r = Λ²σ`**: `|r| ≤ K_r/(m + y²)`. -/
theorem rayBound_rr (hT0 : 0 ≤ T) (hT : a ^ 2 < T) (hT1 : T ≤ 1) :
    RayBound a (T - a ^ 2) (kR T (T - a ^ 2)) (rr T) := by
  intro z hz
  set D := T - a ^ 2 + z.im ^ 2
  set m := T - a ^ 2
  have hm : 0 < m := by simp only [m]; linarith
  have hD : m ≤ D := by simp only [D, m]; nlinarith [sq_nonneg z.im]
  have hD0 : 0 < D := by linarith
  have h1 := norm_lam_sq_le hT hT1 hz
  have h2 := norm_sig_le hT0 hT hT1 hz
  have hK : 0 ≤ 1 + 5 / 4 * (T * (1 - T)) / m := by
    have := mul_nonneg hT0 (by linarith : (0 : ℝ) ≤ 1 - T); positivity
  unfold rr kR
  rw [norm_mul, norm_pow]
  calc ‖lam T z‖ ^ 2 * ‖sig T z‖ ≤ (1 / D) * ((1 + 5 / 4 * (T * (1 - T)) / m) / D) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = (1 + 5 / 4 * (T * (1 - T)) / m) / (D * D) := by field_simp
    _ ≤ (1 + 5 / 4 * (T * (1 - T)) / m) / (m * D) :=
        div_le_div_of_nonneg_left hK (by positivity) (mul_le_mul_of_nonneg_right hD hD0.le)
    _ = (1 + 5 / 4 * (T * (1 - T)) / m) / m / D := by rw [div_div]

end rate

/-! ### Derivatives -/

section deriv

variable {a T : ℝ} {z : ℂ}

theorem hasDerivAt_pP (z : ℂ) : HasDerivAt pP (-(2 * z)) z := by
  have h := (hasDerivAt_pow 2 z).const_sub (1 : ℂ)
  exact h.congr_deriv (by push_cast; ring)

theorem hasDerivAt_pQ (T : ℝ) (z : ℂ) : HasDerivAt (pQ T) (-(2 * z)) z := by
  have h := (hasDerivAt_pow 2 z).const_sub (T : ℂ)
  exact h.congr_deriv (by push_cast; ring)

theorem hasDerivAt_pp (hP : pP z ≠ 0) :
    HasDerivAt (pp T) ((-(2 * z) * pP z - pQ T z * -(2 * z)) / pP z ^ 2) z :=
  (hasDerivAt_pQ T z).div (hasDerivAt_pP z) hP

/-- `Φ″ = Φ′ · z(1/P − 1/Q)`. -/
theorem hasDerivAt_phiD (hT : a ^ 2 < T) (hT1 : T ≤ 1) (hz : z ∈ strip a) :
    HasDerivAt (phiD T) (phiD T z * (z / pP z - z / pQ T z)) z := by
  have hP := pP_ne hT hT1 hz
  have hQ := pQ_ne hT hz
  have h := (((hasDerivAt_pp (T := T) hP).clog (pp_mem_slitPlane hT hT1 hz)).div_const 2).cexp
  refine h.congr_deriv ?_
  unfold phiD pp
  field_simp
  ring

/-- `Λ′ = Λℓ`. -/
theorem hasDerivAt_lam (hT : a ^ 2 < T) (hT1 : T ≤ 1) (hz : z ∈ strip a) :
    HasDerivAt (lam T) (lam T z * ell T z) z := by
  have hP := pP_ne hT hT1 hz
  have hQ := pQ_ne hT hz
  have h1 := ((hasDerivAt_pP z).clog (pP_mem_slitPlane hT hT1 hz)).div_const 2
  have h2 := ((hasDerivAt_pp (T := T) hP).clog (pp_mem_slitPlane hT hT1 hz)).div_const 4
  have h := (h1.neg.sub h2).cexp
  simp only [Pi.neg_apply, Pi.sub_apply] at h
  refine h.congr_deriv ?_
  unfold lam ell pp
  field_simp
  ring

theorem hasDerivAt_ell (hT : a ^ 2 < T) (hT1 : T ≤ 1) (hz : z ∈ strip a) :
    HasDerivAt (ell T) (ellD T z) z := by
  have hP := pP_ne hT hT1 hz
  have hQ := pQ_ne hT hz
  have h1 := (hasDerivAt_id z).div ((hasDerivAt_pP z).const_mul 2) (mul_ne_zero two_ne_zero hP)
  have h2 := (hasDerivAt_id z).div ((hasDerivAt_pQ T z).const_mul 2) (mul_ne_zero two_ne_zero hQ)
  refine (h1.add h2).congr_deriv ?_
  unfold ellD
  simp only [id]
  field_simp
  unfold pQ pP
  ring

/-- **The residual identity** `σ = −2zℓ + P(ℓ² + ℓ′)`. -/
theorem sig_eq (hT : a ^ 2 < T) (hT1 : T ≤ 1) (hz : z ∈ strip a) :
    sig T z = -(2 * z) * ell T z + pP z * (ell T z ^ 2 + ellD T z) := by
  have hP := pP_ne hT hT1 hz
  have hQ := pQ_ne hT hz
  unfold sig ell ellD
  field_simp
  unfold pP pQ
  ring

end deriv

/-! ### Differentiability on the strip -/

section diff

variable {a T : ℝ}

theorem differentiableOn_phiD (hT : a ^ 2 < T) (hT1 : T ≤ 1) : DifferentiableOn ℂ (phiD T) (strip a) :=
  fun _ hz => (hasDerivAt_phiD hT hT1 hz).differentiableAt.differentiableWithinAt

theorem differentiableOn_lam (hT : a ^ 2 < T) (hT1 : T ≤ 1) : DifferentiableOn ℂ (lam T) (strip a) :=
  fun _ hz => (hasDerivAt_lam hT hT1 hz).differentiableAt.differentiableWithinAt

theorem differentiableOn_sig (hT : a ^ 2 < T) (hT1 : T ≤ 1) : DifferentiableOn ℂ (sig T) (strip a) := by
  intro z hz
  have hP := pP_ne hT hT1 hz
  have hQ := pQ_ne hT hz
  have dP : DifferentiableAt ℂ pP z := (hasDerivAt_pP z).differentiableAt
  have dQ : DifferentiableAt ℂ (pQ T) z := (hasDerivAt_pQ T z).differentiableAt
  refine DifferentiableAt.differentiableWithinAt ?_
  have h4 : (4 : ℂ) ≠ 0 := by norm_num
  have e1 : DifferentiableAt ℂ (fun z => (1 : ℂ) / (4 * pP z)) z :=
    (differentiableAt_const (1 : ℂ)).div (dP.const_mul (4 : ℂ)) (mul_ne_zero h4 hP)
  have e2 : DifferentiableAt ℂ (fun z => (3 / 4 * (2 * (T : ℂ) - 1)) / pQ T z) z :=
    (differentiableAt_const (3 / 4 * (2 * (T : ℂ) - 1))).div dQ hQ
  have e3 : DifferentiableAt ℂ (fun z => (5 / 4 * ((T : ℂ) * (1 - T))) / pQ T z ^ 2) z :=
    (differentiableAt_const (5 / 4 * ((T : ℂ) * (1 - T)))).div (dQ.pow 2) (pow_ne_zero 2 hQ)
  exact (e1.add e2).add e3

theorem differentiableOn_rr (hT : a ^ 2 < T) (hT1 : T ≤ 1) : DifferentiableOn ℂ (rr T) (strip a) :=
  ((differentiableOn_lam hT hT1).pow 2).mul (differentiableOn_sig hT hT1)

end diff

/-! ### Real values on the real segment -/

section real

variable {a T : ℝ} {t : ℝ}

theorem pp_ofReal (T t : ℝ) : pp T t = (((T - t ^ 2) / (1 - t ^ 2) : ℝ) : ℂ) := by
  unfold pp pQ pP; push_cast; ring

/-- `Φ′(t) = √((T − t²)/(1 − t²))` on the real segment. -/
theorem phiD_ofReal (hT : a ^ 2 < T) (hT1 : T ≤ 1) (ht : |t| < a) :
    phiD T t = (√((T - t ^ 2) / (1 - t ^ 2)) : ℝ) := by
  have hz : (t : ℂ) ∈ strip a := ⟨by simpa using ht, by simp⟩
  have hp := re_pp_pos hT hT1 hz
  rw [pp_ofReal] at hp
  simp only [Complex.ofReal_re] at hp
  unfold phiD
  rw [pp_ofReal, ← Complex.ofReal_log hp.le, show ((Real.log ((T - t ^ 2) / (1 - t ^ 2)) : ℂ) / 2) =
    ((Real.log ((T - t ^ 2) / (1 - t ^ 2)) / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_exp]
  congr 1
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hp]
  ring_nf

theorem im_phiD_ofReal (hT : a ^ 2 < T) (hT1 : T ≤ 1) (ht : |t| < a) : (phiD T t).im = 0 := by
  rw [phiD_ofReal hT hT1 ht, Complex.ofReal_im]

end real

end Cvs.Prolate.LiouvilleGreen.ComplexSymbols

end
