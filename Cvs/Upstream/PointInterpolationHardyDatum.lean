import Mathlib
import Cvs.Upstream.ExpSumBlaschkeProduct
import Cvs.Upstream.RightHalfPlaneCauchyHardy

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Hardy datum of point interpolation

For a finite conjugation-closed `S` in `Re > 0` and `w ∉ S`, `Re w > 0`, `Im w ≠ 0`, the datum
`F(z) = B_S(z)(A/(z + w̄) + Ā/(z + w))` vanishes on `S`, has `F(z̄) = conj F(z)`, `∫|F(iy)|² dy ≤ 4π|A|²/Re w`,
and for `A = (uc − t c̄)/(u² − |t|²)`, `u = 1/(2 Re w)`, `t = 1/(2w)`, it has `F(w) = B_S(w)c` with
`|A| ≤ |c|/(u − |t|)` (caseinf-W Theorem F (ii)).
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology Finset
open scoped Interval ComplexConjugate
open Cvs.Upstream.ExpSumBlaschkeProduct (bfac)

namespace Cvs.Upstream.PointInterpolationHardyDatum

/-! ### Blaschke products over a finite set -/

/-- `B_S(z) = Π_{ζ ∈ S} (z − ζ)/(z + ζ̄)`. -/
def bS (S : Finset ℂ) (z : ℂ) : ℂ := ∏ ζ ∈ S, bfac ζ z

theorem bfac_conj (ζ z : ℂ) : bfac ζ (conj z) = conj (bfac (conj ζ) z) := by
  unfold bfac
  rw [map_div₀, map_sub, map_add, Complex.conj_conj]

/-- `B_S(z̄) = conj B_S(z)` for conjugation-closed `S`. -/
theorem bS_conj {S : Finset ℂ} (hS : ∀ ζ ∈ S, conj ζ ∈ S) (z : ℂ) : bS S (conj z) = conj (bS S z) := by
  unfold bS
  rw [map_prod]
  simp_rw [bfac_conj]
  refine Finset.prod_nbij' (fun ζ => conj ζ) (fun ζ => conj ζ) (fun ζ hζ => hS ζ hζ) (fun ζ hζ => hS ζ hζ)
    (fun ζ _ => Complex.conj_conj ζ) (fun ζ _ => Complex.conj_conj ζ) fun ζ _ => rfl

theorem bS_self {S : Finset ℂ} {ζ : ℂ} (hζ : ζ ∈ S) : bS S ζ = 0 := by
  unfold bS
  exact Finset.prod_eq_zero hζ (by simp [bfac])

theorem norm_bS_le_one {S : Finset ℂ} (hS : ∀ ζ ∈ S, 0 < ζ.re) {z : ℂ} (hz : 0 ≤ z.re) : ‖bS S z‖ ≤ 1 := by
  unfold bS
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun ζ hζ => Cvs.Upstream.ExpSumBlaschkeProduct.norm_bfac_le_one (hS ζ hζ) hz

theorem norm_bS_I {S : Finset ℂ} (hS : ∀ ζ ∈ S, 0 < ζ.re) (y : ℝ) : ‖bS S (y * I)‖ = 1 := by
  unfold bS
  rw [norm_prod]
  exact Finset.prod_eq_one fun ζ hζ => Cvs.Upstream.ExpSumBlaschkeProduct.norm_bfac_I ζ (hS ζ hζ) y

theorem differentiableOn_bS {S : Finset ℂ} {ε : ℝ} (hS : ∀ ζ ∈ S, ε ≤ ζ.re) :
    DifferentiableOn ℂ (bS S) {s | -ε < s.re} := by
  intro z hz
  simp only [mem_ofPred_eq] at hz
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold bS
  refine DifferentiableAt.fun_finsetProd fun ζ hζ => ?_
  unfold bfac
  exact (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => z - ζ) z).div (by fun_prop)
    (Cvs.Upstream.ExpSumBlaschkeProduct.add_conj_ne_zero' (by linarith [hS ζ hζ]))

/-! ### The datum -/

/-- `g(z) = A/(z + w̄) + Ā/(z + w)`. -/
def gfun (w A : ℂ) (z : ℂ) : ℂ := A / (z + conj w) + conj A / (z + w)

/-- The Hardy datum `F = B_S g`. -/
def datum (S : Finset ℂ) (w A : ℂ) (z : ℂ) : ℂ := bS S z * gfun w A z

theorem gfun_conj (w A z : ℂ) : gfun w A (conj z) = conj (gfun w A z) := by
  unfold gfun
  simp only [map_add, map_div₀, Complex.conj_conj]
  ring

theorem datum_conj {S : Finset ℂ} (hS : ∀ ζ ∈ S, conj ζ ∈ S) (w A z : ℂ) :
    datum S w A (conj z) = conj (datum S w A z) := by
  unfold datum; rw [bS_conj hS, gfun_conj, map_mul]

theorem datum_self {S : Finset ℂ} {ζ : ℂ} (hζ : ζ ∈ S) (w A : ℂ) : datum S w A ζ = 0 := by
  unfold datum; rw [bS_self hζ, zero_mul]

theorem gfun_at (w A : ℂ) :
    gfun w A w = A * ((1 / (2 * w.re) : ℝ) : ℂ) + conj A * (1 / (2 * w)) := by
  unfold gfun
  have h1 : w + conj w = ((2 * w.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp; ring
  rw [h1, show w + w = 2 * w by ring]
  push_cast
  ring

theorem differentiableOn_datum {S : Finset ℂ} {ε : ℝ} (hS : ∀ ζ ∈ S, ε ≤ ζ.re) {w : ℂ} (hw : ε ≤ w.re)
    (A : ℂ) : DifferentiableOn ℂ (datum S w A) {s | -ε < s.re} := by
  refine (differentiableOn_bS hS).mul ?_
  intro z hz
  simp only [mem_ofPred_eq] at hz
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold gfun
  have h1 : z + conj w ≠ 0 := Cvs.Upstream.ExpSumBlaschkeProduct.add_conj_ne_zero' (by linarith)
  have h2 : z + w ≠ 0 := by
    have := Cvs.Upstream.ExpSumBlaschkeProduct.add_conj_ne_zero' (q := conj w) (w := z) (by rw [Complex.conj_re]; linarith)
    rwa [Complex.conj_conj] at this
  have d1 : DifferentiableAt ℂ (fun z : ℂ => A / (z + conj w)) z := by
    fun_prop (disch := exact h1)
  have d2 : DifferentiableAt ℂ (fun z : ℂ => conj A / (z + w)) z := by
    fun_prop (disch := exact h2)
  exact d1.add d2

/-- The datum decays: `|F(s)| ≤ 4|A|/|s|` on `Re s ≥ 0`, `|s| ≥ 2|w|`. -/
theorem datum_dec {S : Finset ℂ} (hS : ∀ ζ ∈ S, 0 < ζ.re) (w A : ℂ) :
    ∀ s : ℂ, 0 ≤ s.re → 2 * ‖w‖ ≤ ‖s‖ → ‖datum S w A s‖ ≤ 4 * ‖A‖ / ‖s‖ := by
  intro s hs hR
  have hb := norm_bS_le_one hS hs
  have h1 := Cvs.Upstream.ExpSumBlaschkeProduct.half_norm_le_norm_add_conj hR
  have h2 : ‖s‖ / 2 ≤ ‖s + w‖ := by
    have := norm_sub_norm_le s (-w)
    rw [sub_neg_eq_add, norm_neg] at this; linarith
  by_cases hs0 : ‖s‖ = 0
  · rw [hs0, div_zero]
    have : s = 0 := norm_eq_zero.1 hs0
    have hw0 : ‖w‖ = 0 := by linarith [norm_nonneg w]
    have hw : w = 0 := norm_eq_zero.1 hw0
    simp [datum, gfun, this, hw]
  have hsp : 0 < ‖s‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hs0)
  unfold datum gfun
  rw [norm_mul]
  have hg : ‖A / (s + conj w) + conj A / (s + w)‖ ≤ 4 * ‖A‖ / ‖s‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_div, norm_div, Complex.norm_conj]
    have e1 : ‖A‖ / ‖s + conj w‖ ≤ ‖A‖ / (‖s‖ / 2) :=
      div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) h1
    have e2 : ‖A‖ / ‖s + w‖ ≤ ‖A‖ / (‖s‖ / 2) :=
      div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) h2
    calc _ ≤ ‖A‖ / (‖s‖ / 2) + ‖A‖ / (‖s‖ / 2) := add_le_add e1 e2
      _ = 4 * ‖A‖ / ‖s‖ := by field_simp; ring
  calc ‖bS S s‖ * ‖A / (s + conj w) + conj A / (s + w)‖ ≤ 1 * (4 * ‖A‖ / ‖s‖) :=
        mul_le_mul hb hg (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- `‖iy + v‖² = (Re v)² + (y − (−Im v))²`. -/
theorem norm_I_add_sq (v : ℂ) (y : ℝ) : ‖(y : ℂ) * I + v‖ ^ 2 = v.re ^ 2 + (y - -v.im) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring

/-- **The datum's boundary norm**: `∫|F(iy)|² dy ≤ 4π|A|²/Re w`. -/
theorem integral_norm_sq_datum_le {S : Finset ℂ} {ε : ℝ} (hε : 0 < ε) (hS : ∀ ζ ∈ S, ε ≤ ζ.re) {w : ℂ}
    (hw : ε ≤ w.re) (A : ℂ) :
    ∫ y : ℝ, ‖datum S w A (y * I)‖ ^ 2 ≤ 4 * Real.pi * ‖A‖ ^ 2 / w.re := by
  have hS0 : ∀ ζ ∈ S, 0 < ζ.re := fun ζ hζ => hε.trans_le (hS ζ hζ)
  have hw0 : 0 < w.re := hε.trans_le hw
  have hint := Cvs.Upstream.RightHalfPlaneCauchyHardy.integrable_norm_sq_line hε (differentiableOn_datum hS hw A) (datum_dec hS0 w A)
  have hb1 := (Cvs.Upstream.RightHalfPlaneCauchyHardy.integrable_inv_sq_add_sq hw0 w.im).const_mul (2 * ‖A‖ ^ 2)
  have hb2 := (Cvs.Upstream.RightHalfPlaneCauchyHardy.integrable_inv_sq_add_sq hw0 (-w.im)).const_mul (2 * ‖A‖ ^ 2)
  have hpt : ∀ y : ℝ, ‖datum S w A (y * I)‖ ^ 2
      ≤ 2 * ‖A‖ ^ 2 * (1 / (w.re ^ 2 + (y - w.im) ^ 2)) + 2 * ‖A‖ ^ 2 * (1 / (w.re ^ 2 + (y - -w.im) ^ 2)) := by
    intro y
    unfold datum
    rw [norm_mul, norm_bS_I hS0 y, one_mul]
    unfold gfun
    have e1 : ‖(y : ℂ) * I + conj w‖ ^ 2 = w.re ^ 2 + (y - w.im) ^ 2 := by
      rw [norm_I_add_sq]; simp
    have e2 := norm_I_add_sq w y
    have hp1 : 0 < ‖(y : ℂ) * I + conj w‖ ^ 2 := by rw [e1]; positivity
    have hp2 : 0 < ‖(y : ℂ) * I + w‖ ^ 2 := by rw [e2]; positivity
    have h := norm_add_le (A / ((y : ℂ) * I + conj w)) (conj A / ((y : ℂ) * I + w))
    rw [norm_div, norm_div, Complex.norm_conj] at h
    have hsq : ‖A / ((y : ℂ) * I + conj w) + conj A / ((y : ℂ) * I + w)‖ ^ 2
        ≤ 2 * ((‖A‖ / ‖(y : ℂ) * I + conj w‖) ^ 2 + (‖A‖ / ‖(y : ℂ) * I + w‖) ^ 2) := by
      have h0 := norm_nonneg (A / ((y : ℂ) * I + conj w) + conj A / ((y : ℂ) * I + w))
      nlinarith [sq_nonneg (‖A‖ / ‖(y : ℂ) * I + conj w‖ - ‖A‖ / ‖(y : ℂ) * I + w‖)]
    refine hsq.trans_eq ?_
    rw [div_pow, div_pow, e1, e2]
    ring
  calc ∫ y : ℝ, ‖datum S w A (y * I)‖ ^ 2
      ≤ ∫ y : ℝ, (2 * ‖A‖ ^ 2 * (1 / (w.re ^ 2 + (y - w.im) ^ 2))
          + 2 * ‖A‖ ^ 2 * (1 / (w.re ^ 2 + (y - -w.im) ^ 2))) :=
        integral_mono hint (hb1.fun_add hb2) hpt
    _ = 4 * Real.pi * ‖A‖ ^ 2 / w.re := by
        rw [integral_add hb1 hb2, integral_const_mul, integral_const_mul,
          Cvs.Upstream.RightHalfPlaneCauchyHardy.integral_inv_sq_add_sq hw0, Cvs.Upstream.RightHalfPlaneCauchyHardy.integral_inv_sq_add_sq hw0]
        ring

/-- The solution `A = (uc − t c̄)/(u² − t t̄)` of `Au + Āt = c`. -/
def solveA (u : ℝ) (t c : ℂ) : ℂ := ((u : ℂ) * c - t * conj c) / ((u : ℂ) ^ 2 - t * conj t)

theorem solveA_spec (u : ℝ) (t c : ℂ) (hD : (u : ℂ) ^ 2 - t * conj t ≠ 0) :
    solveA u t c * u + conj (solveA u t c) * t = c := by
  have hc : conj ((u : ℂ) ^ 2 - t * conj t) = (u : ℂ) ^ 2 - t * conj t := by
    rw [map_sub, map_pow, Complex.conj_ofReal, map_mul, Complex.conj_conj, mul_comm]
  unfold solveA
  rw [map_div₀, hc, map_sub, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_conj]
  field_simp
  ring

/-- `|A| ≤ |c|/(u − |t|)` for `|t| < u`. -/
theorem norm_solveA_le {u : ℝ} {t : ℂ} (h : ‖t‖ < u) (c : ℂ) : ‖solveA u t c‖ ≤ ‖c‖ / (u - ‖t‖) := by
  have ht0 := norm_nonneg t
  have hu0 : 0 < u := ht0.trans_lt h
  have htt : t * conj t = ((‖t‖ ^ 2 : ℝ) : ℂ) := by rw [Complex.mul_conj']; push_cast; ring
  have hD : (u : ℂ) ^ 2 - t * conj t = ((u ^ 2 - ‖t‖ ^ 2 : ℝ) : ℂ) := by rw [htt]; push_cast; ring
  have hDp : 0 < u ^ 2 - ‖t‖ ^ 2 := by nlinarith
  unfold solveA
  rw [hD, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hDp]
  have hn : ‖(u : ℂ) * c - t * conj c‖ ≤ (u + ‖t‖) * ‖c‖ := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu0]
    linarith
  rw [div_le_div_iff₀ hDp (by linarith)]
  have : (u + ‖t‖) * ‖c‖ * (u - ‖t‖) = ‖c‖ * (u ^ 2 - ‖t‖ ^ 2) := by ring
  nlinarith [mul_le_mul_of_nonneg_right hn (by linarith : (0 : ℝ) ≤ u - ‖t‖)]

/-- `1/(2|w|) < 1/(2 Re w)` for `Re w > 0`, `Im w ≠ 0`. -/
theorem norm_t_lt_u {w : ℂ} (hw : 0 < w.re) (him : w.im ≠ 0) : ‖1 / (2 * w)‖ < 1 / (2 * w.re) := by
  have hlt : w.re < ‖w‖ := by
    have h := Complex.abs_re_lt_norm.2 him
    rwa [abs_of_pos hw] at h
  have hn : 0 < ‖w‖ := hw.trans hlt
  rw [norm_div, norm_one, norm_mul, Complex.norm_two]
  exact one_div_lt_one_div_of_lt (by positivity) (by linarith)

/-- **The datum at `w`**: with `A = solveA (1/(2 Re w)) (1/(2w)) c`, `F(w) = B_S(w)c`. -/
theorem datum_at {S : Finset ℂ} {w : ℂ} (hw : 0 < w.re) (him : w.im ≠ 0) (c : ℂ) :
    datum S w (solveA (1 / (2 * w.re)) (1 / (2 * w)) c) w = bS S w * c := by
  have ht := norm_t_lt_u hw him
  have hD : ((1 / (2 * w.re) : ℝ) : ℂ) ^ 2 - (1 / (2 * w)) * conj (1 / (2 * w)) ≠ 0 := by
    have htt : (1 / (2 * w)) * conj (1 / (2 * w)) = ((‖1 / (2 * w)‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj']; push_cast; ring
    rw [htt, ← Complex.ofReal_pow, ← Complex.ofReal_sub, Complex.ofReal_ne_zero]
    have := norm_nonneg (1 / (2 * w))
    nlinarith
  unfold datum
  congr 1
  have h1 := solveA_spec (1 / (2 * w.re)) (1 / (2 * w)) c hD
  rw [gfun_at]
  exact h1

end Cvs.Upstream.PointInterpolationHardyDatum

end
