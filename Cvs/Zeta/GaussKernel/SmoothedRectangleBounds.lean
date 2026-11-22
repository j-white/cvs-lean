import Mathlib
import Cvs.PNT.Rectangle
import Cvs.PNT.ResidueCalcOnRectangles
import Cvs.Zeta.Convexity.ClassicalStripConvexity
import Cvs.Zeta.GaussKernel.SmoothedGaussMellin
import Cvs.Zeta.MollifiedDetectorSeries
import Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint
import Cvs.Zeta.ZetaPolyGrowth

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Smoothed Cauchy rectangle decomposition and left/horizontal `L²` bounds

On `w ∈ [-α, 3 - α] × [-log T, log T]`, `ResidueTheoremOnRectangleWithSimplePole'` decomposes `mollifiedDetector X z`
into `O(T^{-4})` horizontal edges, a `Re(z + w) = 3` right edge, and an `O_c(T^{1 - c/2})` `L²` left edge via `Cvs.Zeta.Convexity.ClassicalStripConvexity`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology Finset Asymptotics
open scoped Interval
open Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint (dirichletPolyC zetaMollifier norm_moebius_le_one secondMoment secondMoment_zetaMollifier_le sq_add_le_two_mul intervalIntegrable_normSq_dirichletPolyC)
open Cvs.Zeta.MollifiedDetectorSeries (mollifiedDetector differentiable_zetaMollifier differentiableOn_mollifiedDetector)
open Cvs.Zeta.GaussKernel.SmoothedGaussMellin (gaussMellinIntegrand differentiableOn_gaussMellinIntegrand norm_gaussMellinIntegrand_le_of_re_ne_zero norm_gaussMellinIntegrand_le_of_im_ne_zero integral_exp_neg_sq_le_pi)

namespace Cvs.Zeta.GaussKernel.SmoothedRectangleBounds

/-! ### Elementary ordinate bounds and rectangle decomposition -/

/-- For `T ≥ 32`, `log T ≤ T / 2 - 2`, keeping `t ± log T ∈ [1, 3T]` for `t ∈ [T - 1, 2T + 1]`. -/
theorem log_le_half_sub_two {T : ℝ} (hT : 32 ≤ T) : Real.log T ≤ T / 2 - 2 := by
  have h1 : Real.log (T / 4) ≤ T / 4 - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have h2 : Real.log 4 ≤ 3 := by linarith [Real.log_le_sub_one_of_pos (x := 4) (by norm_num)]
  have h3 : Real.log T = Real.log (T / 4) + Real.log 4 := by
    rw [← Real.log_mul (by linarith) (by norm_num)]
    congr 1; ring
  linarith

/-- Also `log T > 1` for `T ≥ 32` (`e < 3 < 32`). -/
theorem one_lt_log_of_ge_32 {T : ℝ} (hT : 32 ≤ T) : 1 < Real.log T := by
  have he : Real.exp 1 < T := lt_of_lt_of_le (by linarith [Real.exp_one_lt_d9]) hT
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ < Real.log T := Real.log_lt_log (Real.exp_pos 1) he

/-- The rectangle integrand `w ↦ mollifiedDetector X (z + w) · gaussMellinIntegrand T w`. -/
def rectIntegrand (X : ℕ) (T : ℝ) (z w : ℂ) : ℂ :=
  mollifiedDetector X (z + w) * gaussMellinIntegrand T w

/-- Bottom horizontal edge (`Im w = -log T`). -/
def botEdge (X : ℕ) (T α t : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * I)) *
    HIntegral (rectIntegrand X T ((α : ℂ) + (t : ℂ) * I)) (-α) (3 - α) (-Real.log T)

/-- Top horizontal edge (`Im w = +log T`). -/
def topEdge (X : ℕ) (T α t : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * I)) *
    HIntegral (rectIntegrand X T ((α : ℂ) + (t : ℂ) * I)) (-α) (3 - α) (Real.log T)

/-- Right vertical edge (`Re w = 3 - α`, so `Re(z + w) = 3`). -/
def rightEdge (X : ℕ) (T α t : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * I)) *
    VIntegral (rectIntegrand X T ((α : ℂ) + (t : ℂ) * I)) (3 - α) (-Real.log T) (Real.log T)

/-- Left vertical edge (`Re w = -α`, so `Re(z + w) = 0`). -/
def leftEdge (X : ℕ) (T α t : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * I)) *
    VIntegral (rectIntegrand X T ((α : ℂ) + (t : ℂ) * I)) (-α) (-Real.log T) (Real.log T)

/-- **Cauchy residue decomposition** of `mollifiedDetector X (α + it)` on `[-α, 3 - α] × [-log T, log T]`. -/
theorem mollifiedDetector_eq_edges (X : ℕ) {T α t : ℝ} (hT : 32 ≤ T)
    (hα : α ∈ Icc (1 / 2 : ℝ) (3 / 2)) (ht : t ∈ Icc (T - 1) (2 * T + 1)) :
    mollifiedDetector X ((α : ℂ) + (t : ℂ) * I)
      = botEdge X T α t - topEdge X T α t + rightEdge X T α t - leftEdge X T α t := by
  have hT0 : 0 < T := by linarith
  set L := Real.log T
  have hL1 : 1 < L := one_lt_log_of_ge_32 hT
  have hL_hi : L ≤ T / 2 - 2 := log_le_half_sub_two hT
  set z : ℂ := (α : ℂ) + (t : ℂ) * I
  set z₀ : ℂ := (-α : ℂ) - (L : ℂ) * I
  set w₀ : ℂ := ((3 - α : ℝ) : ℂ) + (L : ℂ) * I
  have hz₀_re : z₀.re = -α := by simp [z₀]
  have hz₀_im : z₀.im = -L := by simp [z₀]
  have hw₀_re : w₀.re = 3 - α := by simp [w₀]
  have hw₀_im : w₀.im = L := by simp [w₀]
  have hre_le : z₀.re ≤ w₀.re := by rw [hz₀_re, hw₀_re]; linarith [hα.2]
  have him_le : z₀.im ≤ w₀.im := by rw [hz₀_im, hw₀_im]; linarith
  have hp_in : Rectangle z₀ w₀ ∈ 𝓝 (0 : ℂ) := by
    rw [rectangle_mem_nhds_iff, hz₀_re, hz₀_im, hw₀_re, hw₀_im,
      uIoo_of_le (by linarith [hα.2]), uIoo_of_le (by linarith)]
    simp only [mem_reProdIm, Set.mem_Ioo, zero_re, zero_im]
    exact ⟨⟨by linarith [hα.1], by linarith [hα.2]⟩, ⟨by linarith, by linarith⟩⟩
  have hfHolo : HolomorphicOn (rectIntegrand X T z) (Rectangle z₀ w₀ \ {0}) := by
    intro w hw
    obtain ⟨hwR, hw0⟩ := hw
    rw [Rectangle, hz₀_re, hz₀_im, hw₀_re, hw₀_im,
      Set.uIcc_of_le (by linarith [hα.2]), Set.uIcc_of_le (by linarith)] at hwR
    simp only [mem_reProdIm, Set.mem_Icc] at hwR
    have hzw1 : z + w ≠ 1 := by
      intro h1
      have him := congrArg Complex.im h1
      simp only [z, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
        add_zero, zero_add, one_im] at him
      linarith [ht.1, hwR.2.1, hL_hi]
    have hd1 : DifferentiableAt ℂ (fun u => mollifiedDetector X (z + u)) w := by
      have hd_det : DifferentiableAt ℂ (mollifiedDetector X) (z + w) :=
        ((differentiableAt_riemannZeta hzw1).mul (differentiable_zetaMollifier X (z + w))).sub
          (differentiableAt_const 1)
      exact hd_det.comp w (differentiableAt_id.const_add z)
    have hd2 : DifferentiableAt ℂ (gaussMellinIntegrand T) w := by
      unfold gaussMellinIntegrand
      have hTC : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT0.ne'
      exact ((differentiableAt_id.pow 2).cexp.mul
        (differentiableAt_id.const_cpow (Or.inl hTC))).div differentiableAt_id hw0
    exact (hd1.mul hd2).differentiableWithinAt
  set h : ℂ → ℂ := fun w => mollifiedDetector X (z + w) * (Complex.exp (w ^ 2) * (T : ℂ) ^ w)
  have hz1 : z ≠ 1 := by
    intro h1
    have him := congrArg Complex.im h1
    simp [z] at him
    linarith [ht.1]
  have hh0 : h 0 = mollifiedDetector X z := by simp [h]
  have hh_diff : DifferentiableAt ℂ h 0 := by
    have hTC : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT0.ne'
    have hd1 : DifferentiableAt ℂ (fun w => mollifiedDetector X (z + w)) 0 := by
      have hd_det : DifferentiableAt ℂ (mollifiedDetector X) (z + 0) := by
        rw [add_zero]
        exact ((differentiableAt_riemannZeta hz1).mul (differentiable_zetaMollifier X z)).sub
          (differentiableAt_const 1)
      exact hd_det.comp 0 (differentiableAt_id.const_add z)
    have hd2 : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (w ^ 2) * (T : ℂ) ^ w) 0 :=
      ((differentiableAt_id.pow 2).cexp).mul (differentiableAt_id.const_cpow (Or.inl hTC))
    exact hd1.mul hd2
  have hnear : (rectIntegrand X T z - fun w => mollifiedDetector X z / (w - 0))
      =O[𝓝[≠] (0 : ℂ)] (1 : ℂ → ℂ) := by
    have hlim : Tendsto (fun w : ℂ => (h w - h 0) / w) (𝓝[≠] 0) (𝓝 (deriv h 0)) := by
      simpa only [zero_add, smul_eq_mul, div_eq_inv_mul] using hh_diff.hasDerivAt.tendsto_slope_zero
    have hbd := Metric.tendsto_nhds.mp hlim 1 one_pos
    rw [isBigO_iff]
    refine ⟨‖deriv h 0‖ + 1, ?_⟩
    filter_upwards [hbd, self_mem_nhdsWithin] with w hw _
    rw [Pi.sub_apply, Pi.one_apply, norm_one, mul_one, sub_zero, ← hh0]
    have heq : rectIntegrand X T z w - h 0 / w = (h w - h 0) / w := by
      dsimp only [rectIntegrand, gaussMellinIntegrand, h]
      ring
    rw [heq]
    have hdist : ‖(h w - h 0) / w - deriv h 0‖ < 1 := by simpa [dist_eq_norm] using hw
    linarith [norm_sub_norm_le ((h w - h 0) / w) (deriv h 0)]
  have hres := ResidueTheoremOnRectangleWithSimplePole' hre_le him_le hp_in hfHolo hnear
  rw [← hres]
  simp only [RectangleIntegral', RectangleIntegral, hz₀_re, hz₀_im, hw₀_re, hw₀_im,
    botEdge, topEdge, rightEdge, leftEdge, smul_eq_mul]
  ring

/-- Four-term Cauchy–Schwarz inequality `(a + b + c + d)² ≤ 4(a² + b² + c² + d²)`. -/
theorem norm_mollifiedDetector_sq_le_edges (X : ℕ) {T α t : ℝ} (hT : 32 ≤ T)
    (hα : α ∈ Icc (1 / 2 : ℝ) (3 / 2)) (ht : t ∈ Icc (T - 1) (2 * T + 1)) :
    ‖mollifiedDetector X ((α : ℂ) + (t : ℂ) * I)‖ ^ 2
      ≤ 4 * (‖botEdge X T α t‖ ^ 2 + ‖topEdge X T α t‖ ^ 2
          + ‖rightEdge X T α t‖ ^ 2 + ‖leftEdge X T α t‖ ^ 2) := by
  rw [mollifiedDetector_eq_edges X hT hα ht]
  have htri : ‖botEdge X T α t - topEdge X T α t + rightEdge X T α t - leftEdge X T α t‖
      ≤ ‖botEdge X T α t‖ + ‖topEdge X T α t‖ + ‖rightEdge X T α t‖ + ‖leftEdge X T α t‖ := by
    calc ‖botEdge X T α t - topEdge X T α t + rightEdge X T α t - leftEdge X T α t‖
        ≤ ‖botEdge X T α t - topEdge X T α t + rightEdge X T α t‖ + ‖leftEdge X T α t‖ :=
          norm_sub_le _ _
      _ ≤ ‖botEdge X T α t - topEdge X T α t‖ + ‖rightEdge X T α t‖ + ‖leftEdge X T α t‖ := by
          linarith [norm_add_le (botEdge X T α t - topEdge X T α t) (rightEdge X T α t)]
      _ ≤ ‖botEdge X T α t‖ + ‖topEdge X T α t‖ + ‖rightEdge X T α t‖ + ‖leftEdge X T α t‖ := by
          linarith [norm_sub_le (botEdge X T α t) (topEdge X T α t)]
  have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
  set a := ‖botEdge X T α t‖
  set b := ‖topEdge X T α t‖
  set c := ‖rightEdge X T α t‖
  set d := ‖leftEdge X T α t‖
  nlinarith [hsq, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]

/-! ### Horizontal edges (`botEdge` and `topEdge`) super-polynomial pointwise bound -/

/-- `‖zetaMollifier X s‖ ≤ X` throughout the right half-plane `Re s ≥ 0`. -/
theorem norm_zetaMollifier_le_of_re_nonneg (X : ℕ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖zetaMollifier X s‖ ≤ (X : ℝ) := by
  rw [zetaMollifier, dirichletPolyC]
  refine (norm_sum_le _ _).trans ?_
  have hcard : (Finset.Icc 1 X).card = X := by rw [Nat.card_Icc]; omega
  calc ∑ n ∈ Finset.Icc 1 X, ‖(ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s)‖
      ≤ ∑ _n ∈ Finset.Icc 1 X, (1 : ℝ) := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn1, Complex.neg_re]
        have h1 := norm_moebius_le_one n
        have h2 : (n : ℝ) ^ (-s.re) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn1) (by linarith)
        nlinarith [Real.rpow_nonneg (Nat.cast_nonneg n) (-s.re)]
    _ = (X : ℝ) := by rw [Finset.sum_const, hcard, nsmul_eq_mul, mul_one]

/-- **Horizontal edges pointwise bound**: for all `T ≥ T_hor` (independent of `α`, `t`, `X ≤ T`),
`‖botEdge X T α t‖ ^ 2 + ‖topEdge X T α t‖ ^ 2 ≤ 2 * T ^ (-4)`. -/
theorem norm_horizEdges_sq_le :
    ∃ T_hor : ℝ, 32 ≤ T_hor ∧ ∀ {T α t : ℝ} {X : ℕ}, T_hor ≤ T → (X : ℝ) ≤ T →
      α ∈ Icc (1 / 2 : ℝ) (3 / 2) → t ∈ Icc (T - 1) (2 * T + 1) →
      ‖botEdge X T α t‖ ^ 2 + ‖topEdge X T α t‖ ^ 2 ≤ 2 * T ^ (-(4 : ℝ)) := by
  obtain ⟨Cζ, hCζ0, hCζ⟩ := Cvs.Zeta.exists_norm_riemannZeta_le_sq_of_re_ge
  set K : ℝ := Real.log (16 * Cζ + 2) + 9
  refine ⟨max 32 (Real.exp (max 10 (K + 10))), le_max_left _ _,
    fun {T α t} {X} hT hXT hα ht => ?_⟩
  have hT32 : 32 ≤ T := (le_max_left _ _).trans hT
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  set L := Real.log T
  have hL_ge : max 10 (K + 10) ≤ L := by
    have := Real.log_le_log (Real.exp_pos _) ((le_max_right _ _).trans hT)
    rwa [Real.log_exp] at this
  have hL10 : 10 ≤ L := (le_max_left _ _).trans hL_ge
  have hLK : K + 10 ≤ L := (le_max_right _ _).trans hL_ge
  have hL_hi : L ≤ T / 2 - 2 := log_le_half_sub_two hT32
  have hpt_edge : ∀ y : ℝ, |y| = L →
      ‖(1 / (2 * (Real.pi : ℂ) * I)) *
          HIntegral (rectIntegrand X T ((α : ℂ) + (t : ℂ) * I)) (-α) (3 - α) y‖ ≤ T ^ (-(2 : ℝ)) := by
    intro y hy
    have hy0 : y ≠ 0 := by intro h; rw [h, abs_zero] at hy; linarith
    have hab : -α ≤ 3 - α := by linarith [hα.2]
    have hcoef : ‖(1 : ℂ) / (2 * (Real.pi : ℂ) * I)‖ ≤ 1 / 2 := by
      have hpi : 3 < Real.pi := Real.pi_gt_three
      rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le, norm_I, mul_one]
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have hint_le : ‖HIntegral (rectIntegrand X T ((α : ℂ) + (t : ℂ) * I)) (-α) (3 - α) y‖
        ≤ 3 * (((16 * Cζ + 2) * T ^ (3 : ℝ)) * (Real.exp (9 - L ^ 2) * T ^ (3 : ℝ) / L)) := by
      unfold HIntegral
      refine (intervalIntegral.norm_integral_le_of_norm_le_const
        (C := ((16 * Cζ + 2) * T ^ (3 : ℝ)) * (Real.exp (9 - L ^ 2) * T ^ (3 : ℝ) / L)) ?_).trans ?_
      · intro x hx
        rw [uIoc_of_le hab] at hx
        have hxIcc : x ∈ Icc (-α) (3 - α) := ⟨hx.1.le, hx.2⟩
        set s : ℂ := ((α : ℂ) + (t : ℂ) * I) + ((x : ℂ) + (y : ℂ) * I)
        have hs_re : s.re = α + x := by simp [s]
        have hs_im : s.im = t + y := by simp [s]
        have him_lo : 1 ≤ s.im := by
          rw [hs_im]
          have hy_lo : -L ≤ y := by rw [← hy]; exact neg_abs_le y
          linarith [ht.1, hL_hi]
        have him_hi : s.im ≤ 3 * T := by
          rw [hs_im]
          have hy_hi : y ≤ L := by rw [← hy]; exact le_abs_self y
          linarith [ht.2, hL_hi]
        have hζ : ‖riemannZeta s‖ ≤ 16 * Cζ * T ^ (2 : ℝ) := by
          have h1 := hCζ s (by rw [hs_re]; linarith [hxIcc.1])
            (by rw [abs_of_pos (by linarith)]; exact him_lo)
          rw [abs_of_pos (by linarith)] at h1
          have h2 : Cζ * (1 + s.im) ^ 2 ≤ Cζ * (4 * T) ^ 2 :=
            mul_le_mul_of_nonneg_left (by nlinarith) hCζ0
          have h3 : Cζ * (4 * T) ^ 2 = 16 * Cζ * T ^ (2 : ℝ) := by rw [Real.rpow_two]; ring
          exact (h1.trans h2).trans_eq h3
        have hM : ‖zetaMollifier X s‖ ≤ T :=
          (norm_zetaMollifier_le_of_re_nonneg X (by rw [hs_re]; linarith [hxIcc.1])).trans hXT
        have hdet : ‖mollifiedDetector X s‖ ≤ (16 * Cζ + 2) * T ^ (3 : ℝ) := by
          unfold mollifiedDetector
          have h1 : ‖riemannZeta s * zetaMollifier X s - 1‖ ≤ ‖riemannZeta s‖ * ‖zetaMollifier X s‖ + 1 :=
            (norm_sub_le _ _).trans (by rw [norm_mul, norm_one])
          have hT23 : T ^ (2 : ℝ) * T = T ^ (3 : ℝ) := by
            calc T ^ (2 : ℝ) * T = T ^ (2 : ℝ) * T ^ (1 : ℝ) := by rw [Real.rpow_one]
              _ = T ^ (3 : ℝ) := by rw [← Real.rpow_add hT0]; norm_num
          have hT3_ge : 1 ≤ T ^ (3 : ℝ) := Real.one_le_rpow hT1 (by norm_num)
          calc ‖riemannZeta s * zetaMollifier X s - 1‖
              ≤ (16 * Cζ * T ^ (2 : ℝ)) * T + 1 := by
                linarith [mul_le_mul hζ hM (norm_nonneg _) (by positivity)]
            _ = 16 * Cζ * T ^ (3 : ℝ) + 1 := by rw [mul_assoc, hT23]
            _ ≤ (16 * Cζ + 2) * T ^ (3 : ℝ) := by nlinarith
        have hkern : ‖gaussMellinIntegrand T ((x : ℂ) + (y : ℂ) * I)‖
            ≤ Real.exp (9 - L ^ 2) * T ^ (3 : ℝ) / L := by
          refine (norm_gaussMellinIntegrand_le_of_im_ne_zero hT0 hy0 x).trans ?_
          have hy2 : x ^ 2 - y ^ 2 = x ^ 2 - L ^ 2 := by rw [← sq_abs y, hy]
          rw [hy, hy2]
          have hx2 : x ^ 2 ≤ 9 := by nlinarith [hxIcc.1, hxIcc.2, hα.1, hα.2]
          have hTx : T ^ x ≤ T ^ (3 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hT1 (by linarith [hxIcc.2, hα.1])
          exact div_le_div_of_nonneg_right
            (mul_le_mul (Real.exp_le_exp.mpr (by linarith)) hTx (by positivity) (by positivity))
            (by linarith)
        rw [rectIntegrand, norm_mul]
        exact mul_le_mul hdet hkern (norm_nonneg _) (by positivity)
      · rw [abs_of_nonneg (sub_nonneg.mpr hab)]
        ring_nf; linarith [show (3 - α - -α) = 3 by ring]
    rw [norm_mul]
    have h3_div_2L : (1 / 2 : ℝ) * 3 / L ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have hexp_decay : (16 * Cζ + 2) * Real.exp (9 - L ^ 2) * T ^ (6 : ℝ) ≤ T ^ (-(2 : ℝ)) := by
      have h16 : 16 * Cζ + 2 = Real.exp (Real.log (16 * Cζ + 2)) :=
        (Real.exp_log (by positivity)).symm
      have hT6 : T ^ (6 : ℝ) = Real.exp (6 * L) := by
        rw [← Real.exp_log hT0, ← Real.exp_mul]; congr 1; ring
      have hTm2 : T ^ (-(2 : ℝ)) = Real.exp (-2 * L) := by
        rw [← Real.exp_log hT0, ← Real.exp_mul]; congr 1; ring
      rw [h16, hT6, hTm2, ← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hKL : K + 8 * L ≤ L ^ 2 := by nlinarith [hL10, hLK]
      dsimp only [K] at hKL
      linarith
    have hT33 : T ^ (3 : ℝ) * T ^ (3 : ℝ) = T ^ (6 : ℝ) := by
      rw [← Real.rpow_add hT0]; norm_num
    calc ‖(1 : ℂ) / (2 * (Real.pi : ℂ) * I)‖ *
          ‖HIntegral (rectIntegrand X T ((α : ℂ) + (t : ℂ) * I)) (-α) (3 - α) y‖
        ≤ (1 / 2) * (3 * (((16 * Cζ + 2) * T ^ (3 : ℝ))
            * (Real.exp (9 - L ^ 2) * T ^ (3 : ℝ) / L))) :=
          mul_le_mul hcoef hint_le (norm_nonneg _) (by positivity)
      _ = ((1 / 2) * 3 / L) * ((16 * Cζ + 2) * Real.exp (9 - L ^ 2)
            * (T ^ (3 : ℝ) * T ^ (3 : ℝ))) := by ring
      _ ≤ 1 * T ^ (-(2 : ℝ)) := by
          rw [hT33]
          exact mul_le_mul h3_div_2L hexp_decay (by positivity) (by positivity)
      _ = T ^ (-(2 : ℝ)) := one_mul _
  have hbot : ‖botEdge X T α t‖ ≤ T ^ (-(2 : ℝ)) :=
    hpt_edge (-L) (by rw [abs_neg, abs_of_pos (by linarith)])
  have htop : ‖topEdge X T α t‖ ≤ T ^ (-(2 : ℝ)) :=
    hpt_edge L (abs_of_pos (by linarith))
  have hsq_bot : ‖botEdge X T α t‖ ^ 2 ≤ T ^ (-(4 : ℝ)) := by
    refine (pow_le_pow_left₀ (norm_nonneg _) hbot 2).trans_eq ?_
    rw [← Real.rpow_natCast (T ^ (-(2 : ℝ))) 2, ← Real.rpow_mul hT0.le]; norm_num
  have hsq_top : ‖topEdge X T α t‖ ^ 2 ≤ T ^ (-(4 : ℝ)) := by
    refine (pow_le_pow_left₀ (norm_nonneg _) htop 2).trans_eq ?_
    rw [← Real.rpow_natCast (T ^ (-(2 : ℝ))) 2, ← Real.rpow_mul hT0.le]; norm_num
  linarith

/-! ### Gaussian Cauchy–Schwarz, Fubini on intervals, and the left-edge `L²` bound -/

/-- Weighted Cauchy–Schwarz against `e^{-v²}`:
`(∫_{-L}^L e^{-v²} g(v) dv)² ≤ π ∫_{-L}^L e^{-v²} g(v)² dv` for continuous `g ≥ 0` and `L > 0`. -/
theorem sq_integral_exp_mul_le {L : ℝ} (hL : 0 < L) {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ v in (-L)..L, Real.exp (-(v ^ 2)) * g v) ^ 2
      ≤ Real.pi * ∫ v in (-L)..L, Real.exp (-(v ^ 2)) * (g v) ^ 2 := by
  have hLL : -L ≤ L := by linarith
  set w : ℝ → ℝ := fun v => Real.exp (-(v ^ 2))
  have hw_cont : Continuous w := by fun_prop
  set I₀ : ℝ := ∫ v in (-L)..L, w v
  set J : ℝ := ∫ v in (-L)..L, w v * g v
  set K : ℝ := ∫ v in (-L)..L, w v * (g v) ^ 2
  have hI₀_pos : 0 < I₀ := by
    have hlow : ∫ _v in (-L)..L, Real.exp (-(L ^ 2)) ≤ I₀ := by
      refine intervalIntegral.integral_mono_on hLL intervalIntegrable_const
        (hw_cont.intervalIntegrable _ _) fun v hv => ?_
      refine Real.exp_le_exp.mpr ?_
      nlinarith [hv.1, hv.2]
    rw [intervalIntegral.integral_const, smul_eq_mul] at hlow
    have hpos : 0 < (L - -L) * Real.exp (-(L ^ 2)) := by
      have : 0 < L - -L := by linarith
      positivity
    linarith
  have hK_nonneg : 0 ≤ K :=
    intervalIntegral.integral_nonneg hLL fun v _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hquad_nonneg : 0 ≤ ∫ v in (-L)..L, w v * (I₀ * g v - J) ^ 2 :=
    intervalIntegral.integral_nonneg hLL fun v _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hquad_eq : (∫ v in (-L)..L, w v * (I₀ * g v - J) ^ 2) = I₀ * (I₀ * K - J ^ 2) := by
    have hexp_fn : (fun v => w v * (I₀ * g v - J) ^ 2)
        = fun v => (I₀ ^ 2 * (w v * (g v) ^ 2) - 2 * I₀ * J * (w v * g v)) + J ^ 2 * w v := by
      funext v; ring
    have hi1 : IntervalIntegrable (fun v => I₀ ^ 2 * (w v * (g v) ^ 2)) volume (-L) L :=
      ((hw_cont.mul (hg.pow 2)).const_mul _).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun v => 2 * I₀ * J * (w v * g v)) volume (-L) L :=
      ((hw_cont.mul hg).const_mul _).intervalIntegrable _ _
    have hi3 : IntervalIntegrable (fun v => J ^ 2 * w v) volume (-L) L :=
      (hw_cont.const_mul _).intervalIntegrable _ _
    rw [hexp_fn, intervalIntegral.integral_add (hi1.sub hi2) hi3,
      intervalIntegral.integral_sub hi1 hi2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    dsimp only [I₀, J, K]
    ring
  rw [hquad_eq] at hquad_nonneg
  have hJ2_le : J ^ 2 ≤ I₀ * K := by nlinarith
  exact hJ2_le.trans (mul_le_mul_of_nonneg_right (integral_exp_neg_sq_le_pi hL.le) hK_nonneg)

/-- Fubini swap on compact intervals for a jointly continuous real integrand. -/
theorem intervalIntegral_swap_of_continuous {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {ψ : ℝ × ℝ → ℝ} (hψ : Continuous ψ) :
    (∫ x in a..b, ∫ y in c..d, ψ (x, y)) = ∫ y in c..d, ∫ x in a..b, ψ (x, y) := by
  have hint1 : IntegrableOn ψ (Ioc a b ×ˢ Ioc c d) (volume.prod volume) :=
    (hψ.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hint2 : IntegrableOn (fun z : ℝ × ℝ => ψ z.swap) (Ioc c d ×ˢ Ioc a b) (volume.prod volume) :=
    ((hψ.comp continuous_swap).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  simp only [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  rw [← setIntegral_prod ψ hint1, ← setIntegral_prod_swap, setIntegral_prod _ hint2]
  rfl

/-- Explicit continuous majorant in `t` for `‖leftEdge X T α t‖²`. -/
def leftMajorant (C_L c : ℝ) (X : ℕ) (T t : ℝ) : ℝ :=
  C_L * T ^ (-(1 : ℝ)) + C_L * T ^ (-(3 / 2 * c)) *
    ∫ v in (-Real.log T)..(Real.log T),
      Real.exp (-(v ^ 2)) * ‖zetaMollifier X (((t + v : ℝ) : ℂ) * I)‖ ^ 2

/-- `leftMajorant C_L c X T` is continuous in `t` on all of `ℝ`. -/
theorem continuous_leftMajorant (C_L c : ℝ) (X : ℕ) (T : ℝ) :
    Continuous (leftMajorant C_L c X T) := by
  unfold leftMajorant
  refine continuous_const.add (continuous_const.mul ?_)
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _
  have hM : Continuous (zetaMollifier X) := (differentiable_zetaMollifier X).continuous
  have harg : Continuous (fun p : ℝ × ℝ => ((p.1 + p.2 : ℝ) : ℂ) * I) := by fun_prop
  exact (Continuous.rexp (by fun_prop)).mul (((hM.comp harg).norm).pow 2)

/-- **Left-edge pointwise bound by `leftMajorant`**: for `0 < c < 1/4`, there is `C_L ≥ 0` such that
`‖leftEdge X T α t‖² ≤ leftMajorant C_L c X T t` for all `T ≥ 32`, `X : ℕ`,
`α ∈ [1/2 + c, 3/2]`, and `t ∈ [T - 1, 2T + 1]`. -/
theorem norm_leftEdge_sq_le_leftMajorant {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1 / 4) :
    ∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ (X : ℕ) {T α t : ℝ}, 32 ≤ T →
      α ∈ Icc (1 / 2 + c) (3 / 2) → t ∈ Icc (T - 1) (2 * T + 1) →
      ‖leftEdge X T α t‖ ^ 2 ≤ leftMajorant C_L c X T t := by
  obtain ⟨C_conv, hC_conv⟩ := Cvs.Zeta.Convexity.ClassicalStripConvexity.norm_zeta_convexity (ε := c / 4) (by linarith)
  set K₀ : ℝ := max C_conv 0
  have hK₀ : 0 ≤ K₀ := le_max_right _ _
  set A₁ : ℝ := 2 * Real.exp (9 / 4)
  set A₂ : ℝ := 8 * K₀ * Real.exp (9 / 4)
  refine ⟨2 * A₁ ^ 2 * Real.pi ^ 2 + 2 * A₂ ^ 2 * Real.pi, by positivity,
    fun X {T α t} hT hα ht => ?_⟩
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  set L := Real.log T
  have hL0 : 0 < L := lt_trans zero_lt_one (one_lt_log_of_ge_32 hT)
  have hLL : -L ≤ L := by linarith
  have hL_hi : L ≤ T / 2 - 2 := log_le_half_sub_two hT
  have hα_half : 1 / 2 ≤ α := by linarith [hα.1]
  have hα_pos : 0 < α := by linarith
  have hM_cont : Continuous (fun v : ℝ => ‖zetaMollifier X (((t + v : ℝ) : ℂ) * I)‖) := by
    have h1 : Continuous (zetaMollifier X) := (differentiable_zetaMollifier X).continuous
    have h2 : Continuous (fun v : ℝ => ((t + v : ℝ) : ℂ) * I) := by fun_prop
    exact (h1.comp h2).norm
  -- pointwise bound on the vertical-line integrand at `Re w = -α`
  have hpt : ∀ v ∈ Ioc (-L) L,
      ‖rectIntegrand X T ((α : ℂ) + (t : ℂ) * I) (((-α : ℝ) : ℂ) + (v : ℂ) * I)‖
        ≤ A₁ * T ^ (-(1 / 2 : ℝ)) * Real.exp (-(v ^ 2))
          + A₂ * T ^ (-(3 / 4 * c)) * (Real.exp (-(v ^ 2)) * ‖zetaMollifier X (((t + v : ℝ) : ℂ) * I)‖) := by
    intro v hv
    set s : ℂ := ((t + v : ℝ) : ℂ) * I
    have hzw : ((α : ℂ) + (t : ℂ) * I) + (((-α : ℝ) : ℂ) + (v : ℂ) * I) = s := by
      dsimp only [s]; push_cast; ring
    have hs_re : s.re = 0 := by simp [s]
    have hs_im : s.im = t + v := by simp [s]
    have htv_lo : 1 ≤ t + v := by linarith [ht.1, hv.1, hL_hi]
    have htv_hi : t + v ≤ 3 * T := by linarith [ht.2, hv.2, hL_hi]
    have hζ : ‖riemannZeta s‖ ≤ 4 * K₀ * T ^ (1 / 2 + c / 4) := by
      have habs : |s.im| = t + v := by rw [hs_im, abs_of_pos (by linarith)]
      have h1 := hC_conv s (by rw [hs_re]) (by rw [hs_re]; norm_num) (by rw [habs]; exact htv_lo)
      rw [hs_re, habs, show (1 : ℝ) / 2 + c / 4 - 0 / 2 = 1 / 2 + c / 4 by ring] at h1
      have hCK : C_conv ≤ K₀ := le_max_left _ _
      have hbase_le : (1 + (t + v)) ^ (1 / 2 + c / 4) ≤ (4 * T) ^ (1 / 2 + c / 4) :=
        Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
      have h4T : (4 * T) ^ (1 / 2 + c / 4) ≤ 4 * T ^ (1 / 2 + c / 4) := by
        rw [Real.mul_rpow (by norm_num) hT0.le]
        have h4 : (4 : ℝ) ^ (1 / 2 + c / 4) ≤ (4 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        rw [Real.rpow_one] at h4
        exact mul_le_mul_of_nonneg_right h4 (by positivity)
      calc ‖riemannZeta s‖ ≤ K₀ * (1 + (t + v)) ^ (1 / 2 + c / 4) :=
            h1.trans (mul_le_mul_of_nonneg_right hCK (by positivity))
        _ ≤ K₀ * (4 * T ^ (1 / 2 + c / 4)) :=
            mul_le_mul_of_nonneg_left (hbase_le.trans h4T) hK₀
        _ = 4 * K₀ * T ^ (1 / 2 + c / 4) := by ring
    have hkern : ‖gaussMellinIntegrand T (((-α : ℝ) : ℂ) + (v : ℂ) * I)‖
        ≤ 2 * Real.exp (9 / 4) * T ^ (-(1 / 2 + c)) * Real.exp (-(v ^ 2)) := by
      have hnegα : (-α : ℝ) ≠ 0 := by linarith
      have hk1 := norm_gaussMellinIntegrand_le_of_re_ne_zero hT0 hnegα v
      rw [abs_neg, abs_of_pos hα_pos, neg_sq, div_eq_mul_inv] at hk1
      have hinv : α⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ hα_pos (by norm_num)]
        linarith
      have hexp : Real.exp (α ^ 2 - v ^ 2) ≤ Real.exp (9 / 4) * Real.exp (-(v ^ 2)) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have hα2 : α ^ 2 ≤ 9 / 4 := by nlinarith [hα.1, hα.2]
        linarith
      have hTα : T ^ (-α) ≤ T ^ (-(1 / 2 + c)) :=
        Real.rpow_le_rpow_of_exponent_le hT1 (by linarith [hα.1])
      calc ‖gaussMellinIntegrand T (((-α : ℝ) : ℂ) + (v : ℂ) * I)‖
          ≤ (Real.exp (9 / 4) * Real.exp (-(v ^ 2)) * T ^ (-(1 / 2 + c))) * 2 := by
            refine hk1.trans (mul_le_mul (mul_le_mul hexp hTα (by positivity) (by positivity))
              hinv (by positivity) (by positivity))
        _ = 2 * Real.exp (9 / 4) * T ^ (-(1 / 2 + c)) * Real.exp (-(v ^ 2)) := by ring
    rw [rectIntegrand, hzw, norm_mul]
    have hdet : ‖mollifiedDetector X s‖ ≤ 4 * K₀ * T ^ (1 / 2 + c / 4) * ‖zetaMollifier X s‖ + 1 := by
      unfold mollifiedDetector
      refine ((norm_sub_le _ _).trans (by rw [norm_mul, norm_one])).trans ?_
      linarith [mul_le_mul_of_nonneg_right hζ (norm_nonneg (zetaMollifier X s))]
    have hprod := mul_le_mul hdet hkern (norm_nonneg _) (by positivity)
    have hT_sub1 : T ^ (-(1 / 2 + c)) ≤ T ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
    have hT_sub2 : T ^ (1 / 2 + c / 4) * T ^ (-(1 / 2 + c)) = T ^ (-(3 / 4 * c)) := by
      rw [← Real.rpow_add hT0]; congr 1; ring
    calc ‖mollifiedDetector X s‖ * ‖gaussMellinIntegrand T (((-α : ℝ) : ℂ) + (v : ℂ) * I)‖
        ≤ (4 * K₀ * T ^ (1 / 2 + c / 4) * ‖zetaMollifier X s‖ + 1)
            * (2 * Real.exp (9 / 4) * T ^ (-(1 / 2 + c)) * Real.exp (-(v ^ 2))) := hprod
      _ = 2 * Real.exp (9 / 4) * T ^ (-(1 / 2 + c)) * Real.exp (-(v ^ 2))
            + 8 * K₀ * Real.exp (9 / 4) * (T ^ (1 / 2 + c / 4) * T ^ (-(1 / 2 + c)))
              * (Real.exp (-(v ^ 2)) * ‖zetaMollifier X s‖) := by ring
      _ ≤ A₁ * T ^ (-(1 / 2 : ℝ)) * Real.exp (-(v ^ 2))
            + A₂ * T ^ (-(3 / 4 * c)) * (Real.exp (-(v ^ 2)) * ‖zetaMollifier X s‖) := by
          rw [hT_sub2]
          dsimp only [A₁, A₂]
          linarith [mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hT_sub1 (by positivity : (0 : ℝ) ≤ 2 * Real.exp (9 / 4)))
            (Real.exp_pos (-(v ^ 2))).le]
  -- integrate `hpt` over `v ∈ (-L)..L`
  set g1 : ℝ → ℝ := fun v => A₁ * T ^ (-(1 / 2 : ℝ)) * Real.exp (-(v ^ 2))
  set g2 : ℝ → ℝ := fun v =>
    A₂ * T ^ (-(3 / 4 * c)) * (Real.exp (-(v ^ 2)) * ‖zetaMollifier X (((t + v : ℝ) : ℂ) * I)‖)
  have hg1_int : IntervalIntegrable g1 volume (-L) L :=
    ((by fun_prop : Continuous fun v : ℝ => Real.exp (-(v ^ 2))).const_mul _).intervalIntegrable _ _
  have hg2_int : IntervalIntegrable g2 volume (-L) L :=
    ((((by fun_prop : Continuous fun v : ℝ => Real.exp (-(v ^ 2))).mul hM_cont).const_mul _)).intervalIntegrable _ _
  have hcoef : ‖(1 : ℂ) / (2 * (Real.pi : ℂ) * I)‖ ≤ 1 := by
    have hpi : 3 < Real.pi := Real.pi_gt_three
    rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le, norm_I, mul_one, div_le_one (by positivity)]
    linarith
  have hnorm_left : ‖leftEdge X T α t‖
      ≤ A₁ * T ^ (-(1 / 2 : ℝ)) * (∫ v in (-L)..L, Real.exp (-(v ^ 2)))
        + A₂ * T ^ (-(3 / 4 * c)) *
          (∫ v in (-L)..L, Real.exp (-(v ^ 2)) * ‖zetaMollifier X (((t + v : ℝ) : ℂ) * I)‖) := by
    unfold leftEdge VIntegral
    rw [norm_mul, norm_smul, norm_I, one_mul]
    have hint_le : ‖∫ v in (-L)..L,
          rectIntegrand X T ((α : ℂ) + (t : ℂ) * I) (((-α : ℝ) : ℂ) + (v : ℂ) * I)‖
        ≤ ∫ v in (-L)..L, g1 v + g2 v :=
      intervalIntegral.norm_integral_le_of_norm_le hLL
        (ae_of_all _ fun v hv => hpt v hv) (hg1_int.add hg2_int)
    have hsum_eq : (∫ v in (-L)..L, g1 v + g2 v)
        = A₁ * T ^ (-(1 / 2 : ℝ)) * (∫ v in (-L)..L, Real.exp (-(v ^ 2)))
          + A₂ * T ^ (-(3 / 4 * c)) *
            (∫ v in (-L)..L, Real.exp (-(v ^ 2)) * ‖zetaMollifier X (((t + v : ℝ) : ℂ) * I)‖) := by
      rw [intervalIntegral.integral_add hg1_int hg2_int]
      dsimp only [g1, g2]
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    exact ((mul_le_of_le_one_left (norm_nonneg _) hcoef).trans hint_le).trans_eq hsum_eq
  -- square and apply `sq_integral_exp_mul_le`
  have hsq := (pow_le_pow_left₀ (norm_nonneg _) hnorm_left 2).trans (sq_add_le_two_mul _ _)
  have hI0_nonneg : 0 ≤ ∫ v in (-L)..L, Real.exp (-(v ^ 2)) :=
    intervalIntegral.integral_nonneg hLL fun _ _ => (Real.exp_pos _).le
  have hI0_sq : (∫ v in (-L)..L, Real.exp (-(v ^ 2))) ^ 2 ≤ Real.pi ^ 2 :=
    pow_le_pow_left₀ hI0_nonneg (integral_exp_neg_sq_le_pi hL0.le) 2
  have hT_sq1 : (T ^ (-(1 / 2 : ℝ))) ^ 2 = T ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_natCast (T ^ (-(1 / 2 : ℝ))) 2, ← Real.rpow_mul hT0.le]; norm_num
  have hT_sq2 : (T ^ (-(3 / 4 * c))) ^ 2 = T ^ (-(3 / 2 * c)) := by
    rw [← Real.rpow_natCast (T ^ (-(3 / 4 * c))) 2, ← Real.rpow_mul hT0.le]
    congr 1; ring
  have hCS := sq_integral_exp_mul_le hL0 hM_cont
  have hterm1 : 2 * (A₁ * T ^ (-(1 / 2 : ℝ)) * ∫ v in (-L)..L, Real.exp (-(v ^ 2))) ^ 2
      ≤ 2 * A₁ ^ 2 * Real.pi ^ 2 * T ^ (-(1 : ℝ)) := by
    calc 2 * (A₁ * T ^ (-(1 / 2 : ℝ)) * ∫ v in (-L)..L, Real.exp (-(v ^ 2))) ^ 2
        = 2 * A₁ ^ 2 * (T ^ (-(1 / 2 : ℝ))) ^ 2 * (∫ v in (-L)..L, Real.exp (-(v ^ 2))) ^ 2 := by ring
      _ ≤ 2 * A₁ ^ 2 * T ^ (-(1 : ℝ)) * Real.pi ^ 2 := by
          rw [hT_sq1]
          exact mul_le_mul_of_nonneg_left hI0_sq (by positivity)
      _ = 2 * A₁ ^ 2 * Real.pi ^ 2 * T ^ (-(1 : ℝ)) := by ring
  have hterm2 : 2 * (A₂ * T ^ (-(3 / 4 * c)) *
        ∫ v in (-L)..L, Real.exp (-(v ^ 2)) * ‖zetaMollifier X (((t + v : ℝ) : ℂ) * I)‖) ^ 2
      ≤ 2 * A₂ ^ 2 * Real.pi * T ^ (-(3 / 2 * c)) *
        ∫ v in (-L)..L, Real.exp (-(v ^ 2)) * ‖zetaMollifier X (((t + v : ℝ) : ℂ) * I)‖ ^ 2 := by
    calc 2 * (A₂ * T ^ (-(3 / 4 * c)) *
            ∫ v in (-L)..L, Real.exp (-(v ^ 2)) * ‖zetaMollifier X (((t + v : ℝ) : ℂ) * I)‖) ^ 2
        = 2 * A₂ ^ 2 * (T ^ (-(3 / 4 * c))) ^ 2 *
            (∫ v in (-L)..L, Real.exp (-(v ^ 2)) * ‖zetaMollifier X (((t + v : ℝ) : ℂ) * I)‖) ^ 2 := by ring
      _ ≤ 2 * A₂ ^ 2 * T ^ (-(3 / 2 * c)) *
            (Real.pi * ∫ v in (-L)..L,
              Real.exp (-(v ^ 2)) * ‖zetaMollifier X (((t + v : ℝ) : ℂ) * I)‖ ^ 2) := by
          rw [hT_sq2]
          exact mul_le_mul_of_nonneg_left hCS (by positivity)
      _ = 2 * A₂ ^ 2 * Real.pi * T ^ (-(3 / 2 * c)) *
            ∫ v in (-L)..L, Real.exp (-(v ^ 2)) * ‖zetaMollifier X (((t + v : ℝ) : ℂ) * I)‖ ^ 2 := by ring
  have hK_nonneg : 0 ≤ ∫ v in (-L)..L,
      Real.exp (-(v ^ 2)) * ‖zetaMollifier X (((t + v : ℝ) : ℂ) * I)‖ ^ 2 :=
    intervalIntegral.integral_nonneg hLL fun _ _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  unfold leftMajorant
  have hC1 : 2 * A₁ ^ 2 * Real.pi ^ 2 * T ^ (-(1 : ℝ))
      ≤ (2 * A₁ ^ 2 * Real.pi ^ 2 + 2 * A₂ ^ 2 * Real.pi) * T ^ (-(1 : ℝ)) :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (by positivity)
  have hC2 : 2 * A₂ ^ 2 * Real.pi * T ^ (-(3 / 2 * c)) *
        (∫ v in (-L)..L, Real.exp (-(v ^ 2)) * ‖zetaMollifier X (((t + v : ℝ) : ℂ) * I)‖ ^ 2)
      ≤ (2 * A₁ ^ 2 * Real.pi ^ 2 + 2 * A₂ ^ 2 * Real.pi) * T ^ (-(3 / 2 * c)) *
        (∫ v in (-L)..L, Real.exp (-(v ^ 2)) * ‖zetaMollifier X (((t + v : ℝ) : ℂ) * I)‖ ^ 2) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (by positivity)) hK_nonneg
  linarith

/-- **Integrated bound on `leftMajorant`** at `X = ⌊T ^ c⌋₊`:
`∫_{T-1}^{2T+1} leftMajorant C_L c ⌊T^c⌋₊ T t dt ≤ C_L * (4 + 10 π) * T^{1 - c/2}`. -/
theorem integral_leftMajorant_le {C_L c T : ℝ} (hCL : 0 ≤ C_L) (hc0 : 0 < c) (hc1 : c < 1 / 4)
    (hT : 32 ≤ T) :
    ∫ t in (T - 1)..(2 * T + 1), leftMajorant C_L c ⌊T ^ c⌋₊ T t
      ≤ C_L * (4 + 10 * Real.pi) * T ^ (1 - c / 2) := by
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  set X : ℕ := ⌊T ^ c⌋₊
  have hTc1 : 1 ≤ T ^ c := Real.one_le_rpow hT1 hc0.le
  have hX1 : 1 ≤ X := Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr hTc1).ne'
  have hX_le : (X : ℝ) ≤ T ^ c := Nat.floor_le (by positivity)
  have hX_pos : (0 : ℝ) < X := by exact_mod_cast hX1
  set L := Real.log T
  have hL0 : 0 < L := lt_trans zero_lt_one (one_lt_log_of_ge_32 hT)
  have hLL : -L ≤ L := by linarith
  have hL_hi : L ≤ T / 2 - 2 := log_le_half_sub_two hT
  have hab_t : T - 1 ≤ 2 * T + 1 := by linarith
  -- bound `(6T + 4X(1 + log X)) X ≤ 10 T^{1 + c}`
  have hMV_bound : (2 * (3 * T) + 4 * (X : ℝ) * (1 + Real.log X)) * (X : ℝ)
      ≤ 10 * T ^ (1 + c) := by
    have hlogX : 1 + Real.log X ≤ (X : ℝ) := by
      linarith [Real.log_le_sub_one_of_pos hX_pos]
    have hX2 : (X : ℝ) ^ 2 ≤ T := by
      calc (X : ℝ) ^ 2 ≤ (T ^ c) ^ 2 := pow_le_pow_left₀ hX_pos.le hX_le 2
        _ = T ^ (2 * c) := by
            rw [← Real.rpow_natCast (T ^ c) 2, ← Real.rpow_mul hT0.le]
            congr 1; ring
        _ ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
        _ = T := Real.rpow_one T
    have hbrack : 2 * (3 * T) + 4 * (X : ℝ) * (1 + Real.log X) ≤ 10 * T := by
      have h1 : 4 * (X : ℝ) * (1 + Real.log X) ≤ 4 * (X : ℝ) ^ 2 := by nlinarith
      linarith
    calc (2 * (3 * T) + 4 * (X : ℝ) * (1 + Real.log X)) * (X : ℝ)
        ≤ (10 * T) * T ^ c :=
          mul_le_mul hbrack hX_le hX_pos.le (by positivity)
      _ = 10 * (T ^ (1 : ℝ) * T ^ c) := by rw [Real.rpow_one]; ring
      _ = 10 * T ^ (1 + c) := by rw [← Real.rpow_add hT0]
  -- bound the double `(t, v)` integral via Fubini + shift `u = t + v`
  set ψ : ℝ × ℝ → ℝ := fun p =>
    Real.exp (-(p.2 ^ 2)) * ‖zetaMollifier X (((p.1 + p.2 : ℝ) : ℂ) * I)‖ ^ 2
  have hψ_cont : Continuous ψ := by
    have hM : Continuous (zetaMollifier X) := (differentiable_zetaMollifier X).continuous
    have harg : Continuous (fun p : ℝ × ℝ => ((p.1 + p.2 : ℝ) : ℂ) * I) := by fun_prop
    exact (Continuous.rexp (by fun_prop)).mul (((hM.comp harg).norm).pow 2)
  have hdouble_le : (∫ t in (T - 1)..(2 * T + 1), ∫ v in (-L)..L, ψ (t, v))
      ≤ Real.pi * (10 * T ^ (1 + c)) := by
    rw [intervalIntegral_swap_of_continuous hab_t hLL hψ_cont]
    have hinner_le : ∀ v ∈ Icc (-L) L,
        (∫ t in (T - 1)..(2 * T + 1), ψ (t, v)) ≤ Real.exp (-(v ^ 2)) * (10 * T ^ (1 + c)) := by
      intro v hv
      dsimp only [ψ]
      rw [intervalIntegral.integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      rw [intervalIntegral.integral_comp_add_right (fun u : ℝ => ‖zetaMollifier X ((u : ℂ) * I)‖ ^ 2) v]
      have hfi : IntervalIntegrable (fun u : ℝ => ‖zetaMollifier X ((u : ℂ) * I)‖ ^ 2)
          volume (-(3 * T)) (3 * T) := by
        simpa [zetaMollifier] using
          intervalIntegrable_normSq_dirichletPolyC
            (fun n => (ArithmeticFunction.moebius n : ℂ)) X 0 (3 * T)
      have hsub : (∫ u in (T - 1 + v)..(2 * T + 1 + v), ‖zetaMollifier X ((u : ℂ) * I)‖ ^ 2)
          ≤ ∫ u in (-(3 * T))..(3 * T), ‖zetaMollifier X ((u : ℂ) * I)‖ ^ 2 :=
        intervalIntegral.integral_mono_interval (by linarith [hv.1, hL_hi]) (by linarith)
          (by linarith [hv.2, hL_hi]) (ae_of_all _ fun _ => sq_nonneg _) hfi
      exact hsub.trans ((secondMoment_zetaMollifier_le X (T := 3 * T) (by linarith)).trans hMV_bound)
    have hcont_inner : Continuous (fun v : ℝ => ∫ t in (T - 1)..(2 * T + 1), ψ (t, v)) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (μ := volume) (f := fun v t => ψ (t, v)) (hψ_cont.comp continuous_swap) _ _
    have hmono := intervalIntegral.integral_mono_on (μ := volume) hLL
      (hcont_inner.intervalIntegrable _ _)
      (((by fun_prop : Continuous fun v : ℝ => Real.exp (-(v ^ 2))).mul_const _).intervalIntegrable _ _)
      hinner_le
    rw [intervalIntegral.integral_mul_const] at hmono
    exact hmono.trans (mul_le_mul_of_nonneg_right (integral_exp_neg_sq_le_pi hL0.le) (by positivity))
  -- combine constant term and mollifier term in `leftMajorant`
  have hi_const : IntervalIntegrable (fun _t : ℝ => C_L * T ^ (-(1 : ℝ))) volume (T - 1) (2 * T + 1) :=
    intervalIntegrable_const
  have hi_var : IntervalIntegrable
      (fun t : ℝ => C_L * T ^ (-(3 / 2 * c)) * ∫ v in (-L)..L, ψ (t, v))
      volume (T - 1) (2 * T + 1) := by
    have hc_in : Continuous (fun t : ℝ => ∫ v in (-L)..L, ψ (t, v)) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hψ_cont _ _
    exact (hc_in.const_mul _).intervalIntegrable _ _
  unfold leftMajorant
  change ∫ t in (T - 1)..(2 * T + 1),
      (C_L * T ^ (-(1 : ℝ)) + C_L * T ^ (-(3 / 2 * c)) * ∫ v in (-L)..L, ψ (t, v))
    ≤ C_L * (4 + 10 * Real.pi) * T ^ (1 - c / 2)
  rw [intervalIntegral.integral_add hi_const hi_var, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, smul_eq_mul]
  have h1 : (2 * T + 1 - (T - 1)) * (C_L * T ^ (-(1 : ℝ))) ≤ 4 * C_L * T ^ (1 - c / 2) := by
    have hlen : 2 * T + 1 - (T - 1) ≤ 4 * T := by linarith
    have hTTinv : T * T ^ (-(1 : ℝ)) = 1 := by
      calc T * T ^ (-(1 : ℝ)) = T ^ (1 : ℝ) * T ^ (-(1 : ℝ)) := by rw [Real.rpow_one]
        _ = 1 := by rw [← Real.rpow_add hT0]; norm_num
    have hone_le : 1 ≤ T ^ (1 - c / 2) := Real.one_le_rpow hT1 (by linarith)
    calc (2 * T + 1 - (T - 1)) * (C_L * T ^ (-(1 : ℝ)))
        ≤ (4 * T) * (C_L * T ^ (-(1 : ℝ))) :=
          mul_le_mul_of_nonneg_right hlen (by positivity)
      _ = 4 * C_L * (T * T ^ (-(1 : ℝ))) := by ring
      _ = 4 * C_L * 1 := by rw [hTTinv]
      _ ≤ 4 * C_L * T ^ (1 - c / 2) := mul_le_mul_of_nonneg_left hone_le (by positivity)
  have h2 : C_L * T ^ (-(3 / 2 * c)) * (∫ t in (T - 1)..(2 * T + 1), ∫ v in (-L)..L, ψ (t, v))
      ≤ C_L * (10 * Real.pi) * T ^ (1 - c / 2) := by
    have hexp_eq : T ^ (-(3 / 2 * c)) * T ^ (1 + c) = T ^ (1 - c / 2) := by
      rw [← Real.rpow_add hT0]; congr 1; ring
    calc C_L * T ^ (-(3 / 2 * c)) * (∫ t in (T - 1)..(2 * T + 1), ∫ v in (-L)..L, ψ (t, v))
        ≤ C_L * T ^ (-(3 / 2 * c)) * (Real.pi * (10 * T ^ (1 + c))) :=
          mul_le_mul_of_nonneg_left hdouble_le (by positivity)
      _ = C_L * (10 * Real.pi) * (T ^ (-(3 / 2 * c)) * T ^ (1 + c)) := by ring
      _ = C_L * (10 * Real.pi) * T ^ (1 - c / 2) := by rw [hexp_eq]
  linarith

end Cvs.Zeta.GaussKernel.SmoothedRectangleBounds

end
