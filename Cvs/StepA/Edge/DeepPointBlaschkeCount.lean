import Mathlib
import Cvs.StepA.Edge.DeepSetZeroSums
import Cvs.StepA.Edge.FiniteTopGap
import Cvs.StepA.Edge.TransplantAngleHighZeros
import Cvs.StepA.Edge.WindowCoshTransformDuality
import Cvs.StepA.RestEnvelopeSmall
import Cvs.StepA.StepACriterion
import Cvs.Upstream.ExpSumBlaschkeProduct
import Cvs.Upstream.ExpSumContourInterpolation
import Cvs.Zeta.CompletedZeroIndex
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.WeightedRateLemma
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.LocalCountTransfer
import Cvs.Zeta.RectArgument
import Cvs.Zeta.ZeroCounting.CarlsonCountBridge
import Cvs.Zeta.ZeroDensityTail
import Cvs.Zeta.ZetaSeamStatement
import Cvs.Zeta.ZetaZeroWindows

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The local zero count against `1/(1 + (y − γ)²)`, and Blaschke products of deep points

`Cvs.Zeta.ZeroDensityTail`'s local count `N(t, t + 1] ≤ 88 log(|t| + 3)` gives `Σ_{|γ| ≤ H} 1/(1 + (y − γ)²) ≤ 2112 log(2|y| + H + 5)`.
With `|b_ζ(u)|^{−2} = 1 + 4 Re u Re ζ/|u − ζ|²`, this bounds the Blaschke product of `w_ρ` over the deep set
`D = deepSet δ_D H` below by `(5H + 7)^{−67584}` on the boundary of `[δ_D/4, 2] × [−(2H + 1), 2H + 1]`
(caseinf-attack Lemma 3), and `|B_D(½)| ≥ e^{−Z}` with `Z = Σ m_ρ/γ²`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology Finset
open scoped Interval ComplexConjugate
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.StepA.Edge.FiniteTopGap (mult mult_nonneg)

namespace Cvs.StepA.Edge.DeepPointBlaschkeCount
open Cvs.ZeroCounting

/-! ### The local count in the zero side's coordinates -/

/-- **The local count**: a finite set of zeros with ordinates in `(t, t + 1]` has at most `88 log(|t| + 3)`
members. -/
theorem card_le_of_window (F : Finset nonTrivialZeroSet) (t : ℝ)
    (hF : ∀ ρ ∈ F, t < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ t + 1) :
    (F.card : ℝ) ≤ 88 * Real.log (|t| + 3) := by
  classical
  set F' := F.map Cvs.Criterion.zeroEquiv.symm.toEmbedding with hF'
  have h1 : F.card ≤ ∑ ρ ∈ F', Cvs.Zeta.Explicit.Venue.completedZetaZeroMultiplicity ρ := by
    rw [hF', Finset.sum_map]
    calc F.card = ∑ ρ ∈ F, 1 := by simp
      _ ≤ ∑ ρ ∈ F, Cvs.Zeta.Explicit.Venue.completedZetaZeroMultiplicity
            (Cvs.Criterion.zeroEquiv.symm.toEmbedding ρ) :=
          Finset.sum_le_sum fun ρ _ => Cvs.Zeta.Explicit.Venue.completedZetaZeroMultiplicity_pos _
  have h2 := Cvs.Zeta.LocalCountTransfer.sum_le_Ncount (a := t) (b := t + 1) F' (fun ρ hρ => by
    rw [hF', Finset.mem_map] at hρ
    obtain ⟨σ, hσ, rfl⟩ := hρ
    have := hF σ hσ
    exact this)
  have h3 := Cvs.Zeta.ZeroDensityTail.localCount_le t
  have : (F.card : ℝ) ≤ (Cvs.Zeta.Base.Ncount t (t + 1) : ℝ) := by exact_mod_cast h1.trans h2
  linarith

/-- `Σ_{|k| ≤ K} 1/(1 + k²) ≤ 5 − 4/(K + 1)`. -/
theorem sum_Icc_inv_one_add_sq_le (K : ℕ) :
    ∑ k ∈ Finset.Icc (-(K : ℤ)) K, 1 / (1 + ((k : ℝ)) ^ 2) ≤ 5 - 4 / ((K : ℝ) + 1) := by
  induction K with
  | zero => simp; norm_num
  | succ K ih =>
    have hset : Finset.Icc (-((K + 1 : ℕ) : ℤ)) ((K + 1 : ℕ) : ℤ)
        = insert (-((K : ℤ) + 1)) (insert ((K : ℤ) + 1) (Finset.Icc (-(K : ℤ)) K)) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    have h1 : -((K : ℤ) + 1) ∉ insert ((K : ℤ) + 1) (Finset.Icc (-(K : ℤ)) K) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have h2 : (K : ℤ) + 1 ∉ Finset.Icc (-(K : ℤ)) K := by simp only [Finset.mem_Icc]; omega
    rw [hset, Finset.sum_insert h1, Finset.sum_insert h2]
    push_cast
    have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have e : ((-((K : ℝ) + 1)) ^ 2) = ((K : ℝ) + 1) ^ 2 := by ring
    rw [e]
    have hb : 2 * (1 / (1 + ((K : ℝ) + 1) ^ 2)) ≤ 4 / ((K : ℝ) + 1) - 4 / ((K : ℝ) + 1 + 1) := by
      rw [div_sub_div _ _ (by positivity) (by positivity), mul_one_div, div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    linarith

/-- `1/(1 + s²) ≤ 4/(1 + k²)` for `0 ≤ k < s`. -/
theorem inv_one_add_sq_le_of_nonneg {s k : ℝ} (hk : 0 ≤ k) (hs : k < s) :
    1 / (1 + s ^ 2) ≤ 4 / (1 + k ^ 2) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- `1/(1 + s²) ≤ 4/(1 + k²)` for `s ≤ k + 1`, `k ≤ −1`. -/
theorem inv_one_add_sq_le_of_le {s k : ℝ} (hk : k ≤ -1) (hs : s ≤ k + 1) :
    1 / (1 + s ^ 2) ≤ 4 / (1 + k ^ 2) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : (k + 1) ^ 2 ≤ s ^ 2 := by nlinarith
  nlinarith

/-- **The zero sum against `1/(1 + (y − γ)²)`**: over zeros with `|γ| ≤ H`, at most `2112 log(2|y| + H + 5)`. -/
theorem sum_inv_one_add_sq_le (F : Finset nonTrivialZeroSet) {H : ℝ} (hH0 : 0 ≤ H)
    (hH : ∀ ρ ∈ F, |(ρ : ℂ).im| ≤ H) (y : ℝ) :
    ∑ ρ ∈ F, 1 / (1 + (y - (ρ : ℂ).im) ^ 2) ≤ 2112 * Real.log (2 * |y| + H + 5) := by
  classical
  set K : ℕ := ⌈|y| + H⌉₊ + 1 with hK
  have hKr : (K : ℝ) ≤ |y| + H + 2 := by
    rw [hK]; push_cast; linarith [Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ |y| + H)]
  have hKr' : |y| + H ≤ (K : ℝ) - 1 := by
    rw [hK]; push_cast; linarith [Nat.le_ceil (|y| + H)]
  set kf : nonTrivialZeroSet → ℤ := fun ρ => ⌈(ρ : ℂ).im - y⌉ - 1 with hkf
  have hk1 : ∀ ρ : nonTrivialZeroSet, ((kf ρ : ℤ) : ℝ) < (ρ : ℂ).im - y := fun ρ => by
    simp only [hkf]; push_cast; linarith [Int.ceil_lt_add_one ((ρ : ℂ).im - y)]
  have hk2 : ∀ ρ : nonTrivialZeroSet, (ρ : ℂ).im - y ≤ ((kf ρ : ℤ) : ℝ) + 1 := fun ρ => by
    simp only [hkf]; push_cast; linarith [Int.le_ceil ((ρ : ℂ).im - y)]
  have hmaps : ∀ ρ ∈ F, kf ρ ∈ Finset.Icc (-(K : ℤ)) K := by
    intro ρ hρ
    have hγ := hH ρ hρ
    have a1 := hk1 ρ; have a2 := hk2 ρ
    have b1 : -(H : ℝ) ≤ (ρ : ℂ).im := by linarith [neg_abs_le ((ρ : ℂ).im)]
    have b2 : (ρ : ℂ).im ≤ H := (le_abs_self _).trans hγ
    have c1 : -|y| ≤ y := neg_abs_le y
    have c2 : y ≤ |y| := le_abs_self y
    rw [Finset.mem_Icc]
    constructor
    · have : (-(K : ℝ)) < (kf ρ : ℝ) + 1 := by linarith
      have : -(K : ℤ) < kf ρ + 1 := by exact_mod_cast this
      omega
    · have : ((kf ρ : ℤ) : ℝ) < K := by linarith
      exact_mod_cast this.le
  set φ : ℤ → ℝ := fun k => 4 / (1 + (k : ℝ) ^ 2) with hφ
  have hpt : ∀ ρ : nonTrivialZeroSet, 1 / (1 + (y - (ρ : ℂ).im) ^ 2) ≤ φ (kf ρ) := by
    intro ρ
    have a1 := hk1 ρ; have a2 := hk2 ρ
    have hs : (y - (ρ : ℂ).im) ^ 2 = ((ρ : ℂ).im - y) ^ 2 := by ring
    rw [hs]
    simp only [hφ]
    by_cases hk : (0 : ℝ) ≤ (kf ρ : ℝ)
    · exact inv_one_add_sq_le_of_nonneg hk a1
    · have h0 : kf ρ < 0 := by exact_mod_cast (not_le.1 hk)
      have hk' : (kf ρ : ℝ) ≤ -1 := by
        have : kf ρ ≤ -1 := by omega
        exact_mod_cast this
      exact inv_one_add_sq_le_of_le hk' a2
  have hlog : ∀ k ∈ Finset.Icc (-(K : ℤ)) K, Real.log (|y + k| + 3) ≤ Real.log (2 * |y| + H + 5) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have h1a : (-(K : ℝ)) ≤ (k : ℝ) := by exact_mod_cast hk.1
    have h1b : (k : ℝ) ≤ K := by exact_mod_cast hk.2
    have h1 : |(k : ℝ)| ≤ K := abs_le.2 ⟨h1a, h1b⟩
    refine Real.log_le_log (by positivity) ?_
    have := abs_add_le y (k : ℝ)
    linarith
  calc ∑ ρ ∈ F, 1 / (1 + (y - (ρ : ℂ).im) ^ 2)
      ≤ ∑ ρ ∈ F, φ (kf ρ) := Finset.sum_le_sum fun ρ _ => hpt ρ
    _ = ∑ k ∈ Finset.Icc (-(K : ℤ)) K, ∑ ρ ∈ F.filter (fun ρ => kf ρ = k), φ (kf ρ) :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ k ∈ Finset.Icc (-(K : ℤ)) K, ((F.filter (fun ρ => kf ρ = k)).card : ℝ) * φ k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_congr rfl fun ρ hρ => by rw [(Finset.mem_filter.1 hρ).2], Finset.sum_const,
          nsmul_eq_mul]
    _ ≤ ∑ k ∈ Finset.Icc (-(K : ℤ)) K, (88 * Real.log (2 * |y| + H + 5)) * φ k := by
        refine Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_right ?_ (by positivity)
        refine (card_le_of_window _ (y + k) fun ρ hρ => ?_).trans ?_
        · have hρk := (Finset.mem_filter.1 hρ).2
          have a1 := hk1 ρ; have a2 := hk2 ρ
          rw [hρk] at a1 a2
          constructor <;> linarith
        · exact mul_le_mul_of_nonneg_left (hlog k hk) (by norm_num)
    _ = 88 * Real.log (2 * |y| + H + 5) * (4 * ∑ k ∈ Finset.Icc (-(K : ℤ)) K, 1 / (1 + (k : ℝ) ^ 2)) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [hφ]; ring
    _ ≤ 88 * Real.log (2 * |y| + H + 5) * (4 * 6) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith [abs_nonneg y])))
        have := sum_Icc_inv_one_add_sq_le K
        have : 0 < 4 / ((K : ℝ) + 1) := by positivity
        linarith
    _ = 2112 * Real.log (2 * |y| + H + 5) := by ring

/-! ### Blaschke factors -/

open Cvs.Upstream.ExpSumBlaschkeProduct (bfac blaschke)

/-- `|b_q(u)| ≥ e^{−2 Re u Re q/|u − q|²}` for `Re u ≥ 0`, `Re q > 0`, `u ≠ q`. -/
theorem exp_le_norm_bfac {q u : ℂ} (hq : 0 < q.re) (hu : 0 ≤ u.re) (hne : u ≠ q) :
    Real.exp (-(2 * u.re * q.re / ‖u - q‖ ^ 2)) ≤ ‖bfac q u‖ := by
  have h0 : 0 < ‖u - q‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have hd := Cvs.Upstream.ExpSumBlaschkeProduct.add_conj_ne_zero hq hu
  have hd0 : 0 < ‖u + conj q‖ := norm_pos_iff.2 hd
  have hid := Cvs.Upstream.ExpSumBlaschkeProduct.normSq_add_conj_sub q u
  set t := 4 * u.re * q.re / ‖u - q‖ ^ 2 with ht
  have ht0 : 0 ≤ t := by positivity
  have hsq : ‖bfac q u‖ ^ 2 = 1 / (1 + t) := by
    rw [Cvs.Upstream.ExpSumBlaschkeProduct.bfac, norm_div, div_pow, ht]
    have : ‖u + conj q‖ ^ 2 = ‖u - q‖ ^ 2 + 4 * u.re * q.re := by linarith
    rw [this]
    field_simp
  have he : Real.exp (-t) ≤ 1 / (1 + t) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) (by linarith [Real.add_one_le_exp t])
  have hsq' : Real.exp (-(2 * u.re * q.re / ‖u - q‖ ^ 2)) ^ 2 = Real.exp (-t) := by
    rw [← Real.exp_nat_mul, ht]; congr 1; push_cast; ring
  rw [← hsq] at he
  rw [← hsq'] at he
  exact (pow_le_pow_iff_left₀ (Real.exp_pos _).le (norm_nonneg _) two_ne_zero).1 he

/-- The left edge: `4 Re u Re ζ/|u − ζ|² ≤ 16/(1 + Δ²)` for `0 < Re u ≤ Re ζ/4`, `Re ζ ≤ ½`, `Δ = Im u − Im ζ`. -/
theorem ratio_le_left {u ζ : ℂ} (hu : 0 < u.re) (huζ : u.re ≤ ζ.re / 4) (hζ : ζ.re ≤ 1 / 2) :
    4 * u.re * ζ.re / ‖u - ζ‖ ^ 2 ≤ 16 / (1 + (u.im - ζ.im) ^ 2) := by
  have hn : ‖u - ζ‖ ^ 2 = (u.re - ζ.re) ^ 2 + (u.im - ζ.im) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
  have hζ0 : 0 < ζ.re := by linarith
  have hpos : 0 < ‖u - ζ‖ ^ 2 := by rw [hn]; nlinarith
  rw [div_le_div_iff₀ hpos (by positivity), hn]
  have hP : 4 * u.re * ζ.re ≤ ζ.re ^ 2 := by nlinarith
  have hA : 9 / 16 * ζ.re ^ 2 ≤ (u.re - ζ.re) ^ 2 := by nlinarith
  have hR : ζ.re ^ 2 ≤ 1 / 4 := by nlinarith
  have hD := sq_nonneg (u.im - ζ.im)
  nlinarith [mul_le_mul_of_nonneg_right hP hD, mul_le_mul_of_nonneg_right hR hD]

/-- The right edge: the same bound for `Re ζ + 3/2 ≤ Re u ≤ 2`, `0 < Re ζ`. -/
theorem ratio_le_right {u ζ : ℂ} (hu : u.re ≤ 2) (huζ : ζ.re + 3 / 2 ≤ u.re) (hζ0 : 0 < ζ.re) :
    4 * u.re * ζ.re / ‖u - ζ‖ ^ 2 ≤ 16 / (1 + (u.im - ζ.im) ^ 2) := by
  have hn : ‖u - ζ‖ ^ 2 = (u.re - ζ.re) ^ 2 + (u.im - ζ.im) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
  have hpos : 0 < ‖u - ζ‖ ^ 2 := by rw [hn]; nlinarith [sq_nonneg (u.im - ζ.im)]
  rw [div_le_div_iff₀ hpos (by positivity), hn]
  have hP : 4 * u.re * ζ.re ≤ 4 := by nlinarith
  have hA : 9 / 4 ≤ (u.re - ζ.re) ^ 2 := by nlinarith
  have hD := sq_nonneg (u.im - ζ.im)
  nlinarith [mul_le_mul_of_nonneg_right hP hD]

/-- Away in height: the same bound for `1 ≤ |Im u − Im ζ|`, `0 ≤ Re u ≤ 2`, `0 < Re ζ ≤ ½`. -/
theorem ratio_le_far {u ζ : ℂ} (hu0 : 0 ≤ u.re) (hu : u.re ≤ 2) (hζ0 : 0 < ζ.re) (hζ : ζ.re ≤ 1 / 2)
    (hΔ : 1 ≤ |u.im - ζ.im|) : 4 * u.re * ζ.re / ‖u - ζ‖ ^ 2 ≤ 16 / (1 + (u.im - ζ.im) ^ 2) := by
  have hn : ‖u - ζ‖ ^ 2 = (u.re - ζ.re) ^ 2 + (u.im - ζ.im) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
  have hΔ2 : 1 ≤ (u.im - ζ.im) ^ 2 := by
    have := sq_abs (u.im - ζ.im); nlinarith
  have hpos : 0 < ‖u - ζ‖ ^ 2 := by rw [hn]; nlinarith [sq_nonneg (u.re - ζ.re)]
  rw [div_le_div_iff₀ hpos (by positivity), hn]
  have hP : 4 * u.re * ζ.re ≤ 4 := by nlinarith
  have hD := sq_nonneg (u.im - ζ.im)
  nlinarith [mul_le_mul_of_nonneg_right hP hD, sq_nonneg (u.re - ζ.re)]

/-! ### The deep points -/

open Cvs.StepA.Edge.WindowCoshTransformDuality (wR)
open Cvs.StepA.Edge.DeepSetZeroSums (deepSet mem_deepSet)

/-- The points `w_ρ` of the deep set, `Λ = {w_ρ : ρ ∈ deepSet δ_D H}`. -/
def deepPts (δD H : ℝ) : Finset ℂ := (deepSet δD H).image wR

theorem coe_deepPts (δD H : ℝ) :
    (deepPts δD H : Set ℂ) = wR '' (deepSet δD H : Set nonTrivialZeroSet) := by
  rw [deepPts, Finset.coe_image]

/-- `w_{ρ̄} = conj w_ρ`. -/
theorem wR_conjZ (ρ : nonTrivialZeroSet) : wR (Cvs.GaussKernel.conjZ ρ) = conj (wR ρ) := by
  have hd : Cvs.GaussKernel.del (Cvs.GaussKernel.conjZ ρ) = Cvs.GaussKernel.del ρ := by
    simp [Cvs.GaussKernel.del]
  unfold wR
  rw [hd]
  split_ifs <;> simp [Cvs.GaussKernel.conjZ, map_ofNat]

/-- The deep points are closed under conjugation. -/
theorem conj_mem_deepPts {δD H : ℝ} {ζ : ℂ} (hζ : ζ ∈ deepPts δD H) : conj ζ ∈ deepPts δD H := by
  obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.1 hζ
  refine Finset.mem_image.2 ⟨Cvs.GaussKernel.conjZ ρ, ?_, wR_conjZ ρ⟩
  rw [mem_deepSet] at hρ ⊢
  have hd : Cvs.GaussKernel.del (Cvs.GaussKernel.conjZ ρ) = Cvs.GaussKernel.del ρ := by
    simp [Cvs.GaussKernel.del]
  rw [hd, Cvs.GaussKernel.conjZ_im, abs_neg]
  exact hρ

/-- The facts on a deep point: `δ_D ≤ Re ζ < ½` and `|Im ζ| ≤ H`, from a deep zero. -/
theorem deepPts_facts {δD H : ℝ} {ζ : ℂ} (hζ : ζ ∈ deepPts δD H) :
    ∃ ρ ∈ deepSet δD H, wR ρ = ζ ∧ δD ≤ ζ.re ∧ ζ.re < 1 / 2 ∧ |ζ.im| ≤ H := by
  obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.1 hζ
  have h := mem_deepSet.1 hρ
  refine ⟨ρ, hρ, rfl, ?_, ?_, ?_⟩
  · rw [Cvs.StepA.Edge.WindowCoshTransformDuality.wR_re]; exact h.2
  · rw [Cvs.StepA.Edge.WindowCoshTransformDuality.wR_re]; exact Cvs.StepA.Edge.TransplantAngleHighZeros.abs_del_lt_half ρ
  · rw [Cvs.StepA.Edge.WindowCoshTransformDuality.abs_wR_im]; exact h.1

/-- `Σ_{ζ ∈ Λ} 1/(1 + (y − Im ζ)²) ≤ 4224 log(2|y| + H + 5)`. -/
theorem sum_deepPts_le {δD H : ℝ} (hH0 : 0 ≤ H) (y : ℝ) :
    ∑ ζ ∈ deepPts δD H, 1 / (1 + (y - ζ.im) ^ 2) ≤ 4224 * Real.log (2 * |y| + H + 5) := by
  have hD : ∀ ρ ∈ deepSet δD H, |(ρ : ℂ).im| ≤ H := fun ρ hρ => (mem_deepSet.1 hρ).1
  have h1 := Finset.sum_image_le_of_nonneg (s := deepSet δD H) (g := wR)
    (f := fun ζ : ℂ => 1 / (1 + (y - ζ.im) ^ 2)) (fun ζ _ => by positivity)
  refine h1.trans ?_
  have h2 : ∀ ρ ∈ deepSet δD H, 1 / (1 + (y - (wR ρ).im) ^ 2)
      ≤ 1 / (1 + (y - (ρ : ℂ).im) ^ 2) + 1 / (1 + (-y - (ρ : ℂ).im) ^ 2) := by
    intro ρ _
    have ha := Cvs.StepA.Edge.WindowCoshTransformDuality.abs_wR_im ρ
    have h0a : 0 ≤ 1 / (1 + (y - (ρ : ℂ).im) ^ 2) := by positivity
    have h0b : 0 ≤ 1 / (1 + (-y - (ρ : ℂ).im) ^ 2) := by positivity
    rcases abs_eq_abs.1 ha with h | h
    · rw [h]; linarith
    · rw [h, show (-y - (ρ : ℂ).im) ^ 2 = (y - -(ρ : ℂ).im) ^ 2 by ring]; linarith
  refine (Finset.sum_le_sum h2).trans ?_
  rw [Finset.sum_add_distrib]
  have e1 := sum_inv_one_add_sq_le (deepSet δD H) hH0 hD y
  have e2 := sum_inv_one_add_sq_le (deepSet δD H) hH0 hD (-y)
  rw [abs_neg] at e2
  linarith

/-- The Blaschke exponent `8·4224 = 33792`. -/
irreducible_def bexp : ℕ := 33792

theorem bexp_cast : (bexp : ℝ) = 33792 := by rw [bexp_def]; norm_num

/-- **The Blaschke product on the rectangle's boundary** (caseinf-attack Lemma 3): on the boundary of
`[δ_D/4, 2] × [−(2H + 1), 2H + 1]`, `|B_Λ| ≥ e^{−bexp·log(5H + 7)}`, `bexp = 33792`. -/
theorem norm_blaschke_ge_onBd {δD H : ℝ} (hδ : 0 < δD) (hδ' : δD < 1 / 2) (hH0 : 0 ≤ H) {u : ℂ}
    (hu : Cvs.Upstream.ExpSumContourInterpolation.OnBd ((δD / 4 : ℝ) - (2 * H + 1 : ℝ) * I) ((2 : ℝ) + (2 * H + 1 : ℝ) * I) u) :
    Real.exp (-((bexp : ℝ) * Real.log (5 * H + 7)))
      ≤ ‖blaschke (fun ζ : deepPts δD H => (ζ : ℂ)) u‖ := by
  rw [bexp_cast]
  set Λ := deepPts δD H
  have hz : ((δD / 4 : ℝ) - (2 * H + 1 : ℝ) * I : ℂ).re = δD / 4 := by simp
  have hzi : ((δD / 4 : ℝ) - (2 * H + 1 : ℝ) * I : ℂ).im = -(2 * H + 1) := by simp
  have hw : ((2 : ℝ) + (2 * H + 1 : ℝ) * I : ℂ).re = 2 := by simp
  have hwi : ((2 : ℝ) + (2 * H + 1 : ℝ) * I : ℂ).im = 2 * H + 1 := by simp
  obtain ⟨⟨hure, huim⟩, hedge⟩ := hu
  rw [Set.mem_preimage, hz, hw, Set.uIcc_of_le (by linarith)] at hure
  rw [Set.mem_preimage, hzi, hwi, Set.uIcc_of_le (by linarith)] at huim
  rw [hz, hw, hzi, hwi] at hedge
  have hu0 : 0 < u.re := by linarith [hure.1]
  have hyabs : |u.im| ≤ 2 * H + 1 := abs_le.2 ⟨huim.1, huim.2⟩
  -- each factor
  have hfac : ∀ ζ ∈ Λ, Real.exp (-(8 * (1 / (1 + (u.im - ζ.im) ^ 2)))) ≤ ‖bfac ζ u‖ := by
    intro ζ hζ
    obtain ⟨ρ, _, _, h1, h2, h3⟩ := deepPts_facts hζ
    have hζ0 : 0 < ζ.re := by linarith
    have hne : u ≠ ζ := by
      intro h; subst h
      rcases hedge with h | h | h | h <;> [linarith; linarith;
        (rw [h] at h3; rw [abs_le] at h3; linarith [h3.1]);
        (rw [h] at h3; rw [abs_le] at h3; linarith [h3.2])]
    refine le_trans ?_ (exp_le_norm_bfac hζ0 hu0.le hne)
    refine Real.exp_le_exp.2 (neg_le_neg ?_)
    have key : 4 * u.re * ζ.re / ‖u - ζ‖ ^ 2 ≤ 16 / (1 + (u.im - ζ.im) ^ 2) := by
      rcases hedge with h | h | h | h
      · exact ratio_le_left hu0 (by rw [h]; linarith) h2.le
      · exact ratio_le_right (by rw [h]) (by rw [h]; linarith) hζ0
      · refine ratio_le_far hu0.le hure.2 hζ0 h2.le ?_
        rw [h]
        have := (abs_le.1 h3).1
        rw [abs_of_nonpos (by linarith [(abs_le.1 h3).2])]; linarith
      · refine ratio_le_far hu0.le hure.2 hζ0 h2.le ?_
        rw [h]
        have := (abs_le.1 h3).2
        rw [abs_of_nonneg (by linarith [(abs_le.1 h3).1])]; linarith
    have e : 2 * u.re * ζ.re / ‖u - ζ‖ ^ 2 = (4 * u.re * ζ.re / ‖u - ζ‖ ^ 2) / 2 := by ring
    rw [e]
    have : 16 / (1 + (u.im - ζ.im) ^ 2) / 2 = 8 * (1 / (1 + (u.im - ζ.im) ^ 2)) := by ring
    linarith
  have hprod : Real.exp (-(8 * ∑ ζ ∈ Λ, 1 / (1 + (u.im - ζ.im) ^ 2)))
      ≤ ‖blaschke (fun ζ : Λ => (ζ : ℂ)) u‖ := by
    rw [Cvs.Upstream.ExpSumBlaschkeProduct.blaschke, norm_prod, Finset.prod_coe_sort Λ (fun ζ => ‖bfac ζ u‖), Finset.mul_sum,
      ← Finset.sum_neg_distrib, Real.exp_sum]
    exact Finset.prod_le_prod₀ (fun ζ _ => (Real.exp_pos _).le) hfac
  refine le_trans (Real.exp_le_exp.2 (neg_le_neg ?_)) hprod
  have hs := sum_deepPts_le (δD := δD) hH0 u.im
  have hlog : Real.log (2 * |u.im| + H + 5) ≤ Real.log (5 * H + 7) :=
    Real.log_le_log (by positivity) (by linarith)
  nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ 2 * |u.im| + H + 5 by linarith [abs_nonneg u.im])]

/-- **The Blaschke product at `½`**: `|B_Λ(½)| ≥ e^{−Z}`, `Z = Σ m_ρ/γ²`, uniformly in `δ_D > 0` and `H`. -/
theorem norm_blaschke_half_ge {δD : ℝ} (hδ : 0 < δD) (H : ℝ) :
    Real.exp (-Cvs.StepA.Edge.DeepSetZeroSums.invSqSum) ≤ ‖blaschke (fun ζ : deepPts δD H => (ζ : ℂ)) (1 / 2)‖ := by
  set Λ := deepPts δD H
  have hhalf_re : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
  have hfac : ∀ ζ ∈ Λ, Real.exp (-(1 / ζ.im ^ 2)) ≤ ‖bfac ζ (1 / 2)‖ := by
    intro ζ hζ
    obtain ⟨ρ, _, hρζ, h1, h2, _⟩ := deepPts_facts hζ
    have hγ : |ζ.im| = |(ρ : ℂ).im| := by rw [← hρζ, Cvs.StepA.Edge.WindowCoshTransformDuality.abs_wR_im]
    have hγ2 : (6.24 : ℝ) < |ζ.im| := hγ ▸ Cvs.StepA.StepACriterion.lt_abs_im ρ
    have hsq : 0 < ζ.im ^ 2 := by rw [← sq_abs]; nlinarith
    have hζ0 : 0 < ζ.re := by linarith
    have hne : (1 / 2 : ℂ) ≠ ζ := fun h => by rw [← h] at h2; norm_num at h2
    refine le_trans ?_ (exp_le_norm_bfac hζ0 (by rw [hhalf_re]; norm_num) hne)
    refine Real.exp_le_exp.2 (neg_le_neg ?_)
    have hn : ‖(1 / 2 : ℂ) - ζ‖ ^ 2 = (1 / 2 - ζ.re) ^ 2 + ζ.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
    rw [hn, hhalf_re, div_le_div_iff₀ (by positivity) hsq]
    nlinarith [sq_nonneg (1 / 2 - ζ.re)]
  have hprod : Real.exp (-(∑ ζ ∈ Λ, 1 / ζ.im ^ 2)) ≤ ‖blaschke (fun ζ : Λ => (ζ : ℂ)) (1 / 2)‖ := by
    rw [Cvs.Upstream.ExpSumBlaschkeProduct.blaschke, norm_prod, Finset.prod_coe_sort Λ (fun ζ => ‖bfac ζ (1 / 2)‖),
      ← Finset.sum_neg_distrib, Real.exp_sum]
    exact Finset.prod_le_prod₀ (fun ζ _ => (Real.exp_pos _).le) hfac
  refine le_trans (Real.exp_le_exp.2 (neg_le_neg ?_)) hprod
  have h1 := Finset.sum_image_le_of_nonneg (s := deepSet δD H) (g := wR)
    (f := fun ζ : ℂ => 1 / ζ.im ^ 2) (fun ζ _ => by positivity)
  refine h1.trans ?_
  have h2 : ∀ ρ ∈ deepSet δD H, 1 / (wR ρ).im ^ 2 ≤ mult ρ * (1 / ((ρ : ℂ).im) ^ 2) := by
    intro ρ _
    have hsq : (wR ρ).im ^ 2 = ((ρ : ℂ).im) ^ 2 := by rw [← sq_abs, Cvs.StepA.Edge.WindowCoshTransformDuality.abs_wR_im, sq_abs]
    rw [hsq]
    have hm : (1 : ℝ) ≤ mult ρ := by exact_mod_cast Cvs.Criterion.one_le_divisorWeight ρ
    have : 0 ≤ 1 / ((ρ : ℂ).im) ^ 2 := by positivity
    nlinarith
  refine (Finset.sum_le_sum h2).trans ?_
  exact Summable.sum_le_tsum _ (fun ρ _ => mul_nonneg (mult_nonneg ρ) (by positivity))
    Cvs.StepA.RestEnvelopeSmall.summable_divisorWeight_div_sq

end Cvs.StepA.Edge.DeepPointBlaschkeCount

end
