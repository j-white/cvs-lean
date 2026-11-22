import Mathlib
import Cvs.Prolate.EntireRungProlateEquation
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Mellin.FirstAliasReflectedDual
import Cvs.Prolate.Mellin.HigherAliasRayTransforms
import Cvs.Prolate.Mellin.RayTransformEdgeSum
import Cvs.Prolate.Mellin.RightEdgeAliasLaw
import Cvs.Prolate.Mellin.RungProfileOutsideCircle
import Cvs.Prolate.Mellin.RungUnitCircleLaw
import Cvs.Prolate.Mellin.TrapezoidErrorAliasSeries
import Cvs.Prolate.RungProfileEntireExtension

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The first alias of a rung profile is at the edge scale

`cos(cz)` and `H_k = ψ_{h_k}/μ_k` are even series on the closed unit disk, and the dual of `H_k` is `μ_kH_k`, so
Cvs.Prolate.Mellin.FirstAliasReflectedDual gives `T_{W_1} = μ_k T_{rH_k} − 2i T_{H_k} T_{rC}`; reflection, Cvs.Prolate.Mellin.UnitCircleMellinEdgeBound and `|cos(ce^{−is})| ≤ e^{cs}` give
`g|T_{W_1}(σ + ig)| ≤ 4e⁶|h_k(1)|(|μ_k| + 2/(g − c))` for `|σ| ≤ 1`, `g ≥ 4c`.
-/

noncomputable section

open Real Set MeasureTheory Filter Complex Topology
open Cvs.Prolate.Mellin.RayTransformEdgeSum (rayT)
open Cvs.Prolate.RungProfileEntireExtension (psiC)
open Cvs.Prolate.EntireRungProlateEquation (Hk)
open Cvs.Prolate.EvenRungsByIndex (rung muR lamR lev IsLevelIdx)
open scoped ComplexConjugate

namespace Cvs.Prolate.Mellin.FirstAliasEdgeScale
open Cvs.ZeroCounting

/-- The cosine coefficients `d_l = (−1)^l c^{2l}/(2l)!`. -/
def cosCoeff (c : ℝ) (l : ℕ) : ℂ := (-1) ^ l * (c : ℂ) ^ (2 * l) / ((2 * l).factorial : ℂ)

theorem norm_cosCoeff (c : ℝ) (l : ℕ) : ‖cosCoeff c l‖ = |c| ^ (2 * l) / (2 * l).factorial := by
  unfold cosCoeff
  rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_natCast]

theorem summable_cosCoeff (c : ℝ) : Summable fun l => ‖cosCoeff c l‖ := by
  simp only [norm_cosCoeff]
  exact (Real.summable_pow_div_factorial |c|).comp_injective (mul_right_injective₀ two_ne_zero)

theorem hasSum_cos (c : ℝ) (z : ℂ) : HasSum (fun l => cosCoeff c l * z ^ (2 * l)) (Complex.cos (c * z)) := by
  have := Complex.hasSum_cos (c * z)
  refine this.congr_fun fun l => ?_
  unfold cosCoeff; rw [mul_pow]; ring

/-- `ψ_g(z) = Σ_l d_l (∫ g u^{2l}) z^{2l}` on the closed unit disk. -/
theorem hasSum_psiC (c : ℝ) {g : ℝ → ℝ} (hg : IntervalIntegrable g volume (-1) 1) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    HasSum (fun l => cosCoeff c l * (∫ u in (-1 : ℝ)..1, (g u : ℂ) * (u : ℂ) ^ (2 * l)) * z ^ (2 * l))
      (psiC c g z) := by
  have hterm : ∀ l : ℕ, ∫ u in (-1 : ℝ)..1, (g u : ℂ) * (cosCoeff c l * (z * u) ^ (2 * l))
      = cosCoeff c l * (∫ u in (-1 : ℝ)..1, (g u : ℂ) * (u : ℂ) ^ (2 * l)) * z ^ (2 * l) := fun l => by
    have e : (fun u : ℝ => (g u : ℂ) * (cosCoeff c l * (z * u) ^ (2 * l)))
        = fun u : ℝ => (cosCoeff c l * z ^ (2 * l)) * ((g u : ℂ) * (u : ℂ) ^ (2 * l)) := by
      funext u; rw [mul_pow]; ring
    rw [e, intervalIntegral.integral_const_mul]; ring
  simp_rw [← hterm]
  unfold psiC
  have hgc : IntervalIntegrable (fun u => (g u : ℂ)) volume (-1) 1 := ⟨hg.1.ofReal, hg.2.ofReal⟩
  refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun l u => ‖cosCoeff c l‖ * |g u|)
    (fun l => ?_) (fun l => ?_) ?_ ?_ ?_
  · exact (hgc.mul_continuousOn (by fun_prop : ContinuousOn (fun u : ℝ => cosCoeff c l * (z * u) ^ (2 * l)) _)
      |>.def'.aestronglyMeasurable)
  · refine Eventually.of_forall fun u hu => ?_
    rw [uIoc_of_le (by norm_num)] at hu
    have hu1 : ‖z * (u : ℂ)‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_one₀ hz (abs_nonneg _) (abs_le.2 ⟨by linarith [hu.1], hu.2⟩)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow]
    calc |g u| * (‖cosCoeff c l‖ * ‖z * (u : ℂ)‖ ^ (2 * l)) ≤ |g u| * (‖cosCoeff c l‖ * 1) := by
          gcongr; exact pow_le_one₀ (norm_nonneg _) hu1
      _ = ‖cosCoeff c l‖ * |g u| := by ring
  · exact Eventually.of_forall fun u _ => (summable_cosCoeff c).mul_right _
  · have : (fun u => ∑' l, ‖cosCoeff c l‖ * |g u|) = fun u => (∑' l, ‖cosCoeff c l‖) * |g u| := by
      funext u; rw [tsum_mul_right]
    rw [this]; exact hg.abs.const_mul _
  · refine Eventually.of_forall fun u _ => ?_
    have := (hasSum_cos c (z * u)).mul_left (g u : ℂ)
    simpa [mul_assoc] using this

/-- The moments `∫_{−1}^{1} g(u)u^{2l}` are at most `∫|g|`. -/
theorem norm_moment_le {g : ℝ → ℝ} (hg : IntervalIntegrable g volume (-1) 1) (l : ℕ) :
    ‖∫ u in (-1 : ℝ)..1, (g u : ℂ) * (u : ℂ) ^ (2 * l)‖ ≤ ∫ u in (-1 : ℝ)..1, |g u| := by
  refine intervalIntegral.norm_integral_le_of_norm_le (by norm_num) (Eventually.of_forall fun u hu => ?_) hg.abs
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hu1 : |u| ≤ 1 := abs_le.2 ⟨by linarith [hu.1], hu.2⟩
  calc |g u| * |u| ^ (2 * l) ≤ |g u| * 1 := by gcongr; exact pow_le_one₀ (abs_nonneg _) hu1
    _ = |g u| := mul_one _

/-- The coefficients `b_l = d_l (∫ h_k u^{2l})/μ_k` of `H_k`. -/
def hkCoeff (c : ℝ) (k : ℕ) (l : ℕ) : ℂ :=
  cosCoeff c l * (∫ u in (-1 : ℝ)..1, (rung c k u : ℂ) * (u : ℂ) ^ (2 * l)) / muR c k

theorem summable_hkCoeff {c : ℝ} {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) : Summable fun l => ‖hkCoeff c k l‖ := by
  have hg := Cvs.Prolate.RungProfileEntireExtension.intervalIntegrable_rung h
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun l => ?_)
    ((summable_cosCoeff c).mul_right ((∫ u in (-1 : ℝ)..1, |rung c k u|) / |muR c k|))
  unfold hkCoeff
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_div_assoc]
  gcongr
  exact norm_moment_le hg l

/-- `H_k` is the even series `Σ_l b_l z^{2l}` on the closed unit disk. -/
theorem hasSum_Hk {c : ℝ} {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    HasSum (fun l => hkCoeff c k l * z ^ (2 * l)) (Hk c k z) := by
  have := (hasSum_psiC c (Cvs.Prolate.RungProfileEntireExtension.intervalIntegrable_rung h) hz).div_const (muR c k : ℂ)
  refine this.congr_fun fun l => ?_
  unfold hkCoeff; ring

/-- **The dual of `H_k` is `μ_kH_k`**: `∫_{−1}^{1} H_k(t) cos(cτt) dt = μ_k H_k(τ)`. -/
theorem dual_Hk {c : ℝ} {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) (hμ : muR c k ≠ 0) (τ : ℂ) :
    ∫ t in (-1 : ℝ)..1, Hk c k t * Complex.cos (c * (τ * t)) = (muR c k : ℂ) * Hk c k τ := by
  have e : ∫ t in (-1 : ℝ)..1, Hk c k t * Complex.cos (c * (τ * t)) = psiC c (rung c k) τ := by
    unfold psiC
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le (by norm_num)] at ht
    rw [Cvs.Prolate.EntireRungProlateEquation.Hk_ofReal h hμ ht]; congr 2; ring
  rw [e]; unfold Hk
  have : (muR c k : ℂ) ≠ 0 := by exact_mod_cast hμ
  field_simp

/-- **Reflection**: for `F(z̄) = conj F(z)`, `T_{rF}(w) = conj T_F(−w̄)`. -/
theorem rayT_refl {F : ℂ → ℂ} (hF : ∀ z, F (conj z) = conj (F z)) (w : ℂ) :
    rayT (Cvs.Prolate.Mellin.FirstAliasReflectedDual.refl F) w = conj (rayT F (-conj w)) := by
  unfold rayT Cvs.Prolate.Mellin.FirstAliasReflectedDual.refl
  rw [← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  dsimp only
  have h1 : (Complex.exp (-(s * I)))⁻¹ = Complex.exp (s * I) := by rw [← Complex.exp_neg, neg_neg]
  have h2 : Complex.exp (s * I) = conj (Complex.exp (-(s * I))) := by
    rw [← Complex.exp_conj]; congr 1; simp [Complex.conj_ofReal]
  have hG' : F (Complex.exp (s * I)) = conj (F (Complex.exp (-(s * I)))) := by rw [h2]; exact hF _
  have h3 : conj (Complex.exp (-(s * I / 2))) = Complex.exp (s * I / 2) := by
    rw [← Complex.exp_conj]; congr 1
    rw [map_neg, map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]; ring
  have h4 : conj (Complex.exp (-conj w * (s * I))) = Complex.exp (w * (s * I)) := by
    rw [← Complex.exp_conj]; congr 1; simp [Complex.conj_ofReal]
  rw [h1, hG', map_mul, map_mul, h3, h4]
  have h5 : Complex.exp (s * I) * Complex.exp (-(s * I / 2)) = Complex.exp (s * I / 2) := by
    rw [← Complex.exp_add]; congr 1; ring
  calc Complex.exp (s * I) * conj (F (Complex.exp (-(s * I)))) * Complex.exp (-(s * I / 2))
        * Complex.exp (w * (s * I))
      = conj (F (Complex.exp (-(s * I)))) * (Complex.exp (s * I) * Complex.exp (-(s * I / 2)))
        * Complex.exp (w * (s * I)) := by ring
    _ = _ := by rw [h5]

/-- `|T_{cos(c·)}(w)| ≤ 1/(Im w − c)` for `0 ≤ c < Im w`. -/
theorem norm_rayT_cos_le {c : ℝ} (hc : 0 ≤ c) {w : ℂ} (hw : c < w.im) :
    ‖rayT (fun z => Complex.cos (c * z)) w‖ ≤ 1 / (w.im - c) := by
  have h := Cvs.Prolate.Mellin.HigherAliasRayTransforms.sum_norm_rayT_le (F := fun _ z => Complex.cos (c * z)) (fun _ => by fun_prop)
    (lt_of_le_of_lt hc hw) hw 1 (Ω := 1) fun s hs => by
      simp only [Finset.range_one, Finset.sum_singleton, one_mul]
      refine (Cvs.Prolate.Mellin.RungProfileOutsideCircle.norm_cos_le _).trans (Real.exp_le_exp.2 ?_)
      have : ((c : ℂ) * Complex.exp (-(s * I))).im = c * (Complex.exp (-(s * I))).im := by simp
      rw [this, abs_mul, abs_of_nonneg hc]
      exact mul_le_mul_of_nonneg_left (Cvs.Prolate.Mellin.HigherAliasRayTransforms.abs_im_circle_le hs.le) hc
  simpa using h

/-- `g|T_{H_{4j}}(σ + ig)| ≤ 4e⁶|h_{4j}(1)|` for `|σ| ≤ 1`, `g ≥ 8πx`. -/
theorem g_norm_rayT_Hk_le {x j : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) {σ : ℝ} (hσ : |σ| ≤ 1) {g : ℝ}
    (hg : 8 * π * x ≤ g) :
    g * ‖rayT (Hk (2 * π * x) (2 * j)) (σ + g * I)‖ ≤ 4 * Real.exp 6 * |rung (2 * π * x) (2 * j) 1| := by
  have h := Cvs.Prolate.Mellin.RightEdgeAliasLaw.g_norm_rayT_comb_le hx hj 1 0 hσ hg
  have e : (fun z => (1 : ℂ) * Hk (2 * π * x) (2 * j) z + 0 * Hk (2 * π * x) 0 z) = Hk (2 * π * x) (2 * j) := by
    funext z; ring
  rw [e] at h
  simpa using h

/-- **The first alias of `H_{4j}`**: `g|T_{W_1}(σ + ig)| ≤ 4e⁶|h_{4j}(1)|(|μ_{4j}| + 2/(g − c))`. -/
theorem g_norm_rayT_first_le {x j : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) {σ : ℝ} (hσ : |σ| ≤ 1) {g : ℝ}
    (hg : 8 * π * x ≤ g) :
    g * ‖rayT (fun ζ => ∫ t in (-1 : ℝ)..1, Hk (2 * π * x) (2 * j) (t * ζ)
        * Complex.cos ((2 * π * x : ℝ) * t)) (σ + g * I)‖
      ≤ 4 * Real.exp 6 * |rung (2 * π * x) (2 * j) 1| * (|muR (2 * π * x) (2 * j)| + 2 / (g - 2 * π * x)) := by
  set c := 2 * π * (x : ℝ) with hcd
  obtain ⟨h1, hμ, -⟩ := Cvs.Prolate.Mellin.RungUnitCircleLaw.rung_data hx hj
  have hc0 : 0 < c := by linarith
  have hgc : c < g := by nlinarith [Real.pi_pos]
  have hg0 : 0 < g := hc0.trans hgc
  have hwim : 0 < ((σ : ℂ) + g * I).im := by simp [hg0]
  have hHc := (Cvs.Prolate.EntireRungProlateEquation.differentiable_Hk h1).continuous
  have hid := Cvs.Prolate.Mellin.FirstAliasReflectedDual.rayT_alias_eq (summable_hkCoeff h1) (summable_cosCoeff c) hHc
    (by fun_prop : Continuous fun z : ℂ => Complex.cos (c * z)) (fun z hz => hasSum_Hk h1 hz)
    (fun z _ => hasSum_cos c z) hwim
  have hdual : (fun τ => ∫ t in (-1 : ℝ)..1, Hk c (2 * j) t * Complex.cos (c * (τ * t)))
      = fun τ => (muR c (2 * j) : ℂ) * Hk c (2 * j) τ := funext fun τ => dual_Hk h1 hμ τ
  have hW : (fun ζ => ∫ t in (-1 : ℝ)..1, Hk c (2 * j) (t * ζ) * Complex.cos ((c : ℝ) * t))
      = fun ζ => ∫ t in (-1 : ℝ)..1, Hk c (2 * j) (t * ζ) * Complex.cos (c * t) := rfl
  rw [hW, hid, hdual]
  have hrefl : Cvs.Prolate.Mellin.FirstAliasReflectedDual.refl (fun τ => (muR c (2 * j) : ℂ) * Hk c (2 * j) τ)
      = fun ζ => (muR c (2 * j) : ℂ) * Cvs.Prolate.Mellin.FirstAliasReflectedDual.refl (Hk c (2 * j)) ζ := by
    funext ζ; unfold Cvs.Prolate.Mellin.FirstAliasReflectedDual.refl; ring
  rw [hrefl, Cvs.Prolate.Mellin.TrapezoidErrorAliasSeries.rayT_const_mul, rayT_refl (Cvs.Prolate.Mellin.RungProfileOutsideCircle.Hk_conj c _),
    rayT_refl (F := fun z => Complex.cos (c * z)) (fun z => by
      rw [← Complex.cos_conj, map_mul, Complex.conj_ofReal])]
  have hw' : -conj ((σ : ℂ) + g * I) = ((-σ : ℝ) : ℂ) + g * I := by simp [Complex.conj_ofReal]; ring
  rw [hw']
  have hσ' : |-σ| ≤ 1 := by rwa [abs_neg]
  have bH := g_norm_rayT_Hk_le hx hj hσ hg
  have bH' := g_norm_rayT_Hk_le hx hj hσ' hg
  have bC := norm_rayT_cos_le hc0.le (w := ((-σ : ℝ) : ℂ) + g * I) (by simpa using hgc)
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, mul_zero, I_im, mul_one, zero_add, add_zero] at bC
  set A := 4 * Real.exp 6 * |rung c (2 * j) 1| with hA
  have hA0 : 0 ≤ A := by positivity
  have hTH : ‖rayT (Hk c (2 * j)) (σ + g * I)‖ ≤ A / g := by rw [le_div_iff₀ hg0]; linarith
  have hTH' : ‖rayT (Hk c (2 * j)) (((-σ : ℝ) : ℂ) + g * I)‖ ≤ A / g := by rw [le_div_iff₀ hg0]; linarith
  calc g * ‖(muR c (2 * j) : ℂ) * conj (rayT (Hk c (2 * j)) (((-σ : ℝ) : ℂ) + g * I))
        - 2 * I * rayT (Hk c (2 * j)) (σ + g * I) * conj (rayT (fun z => Complex.cos (c * z)) (((-σ : ℝ) : ℂ) + g * I))‖
      ≤ g * (|muR c (2 * j)| * (A / g) + 2 * (A / g) * (1 / (g - c))) := by
        gcongr
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj, Complex.norm_real,
          Real.norm_eq_abs, Complex.norm_I, Complex.norm_ofNat, mul_one]
        gcongr
    _ = A * (|muR c (2 * j)| + 2 / (g - c)) := by
        have : g - c ≠ 0 := by linarith
        field_simp

end Cvs.Prolate.Mellin.FirstAliasEdgeScale

end
