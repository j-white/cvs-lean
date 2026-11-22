import Mathlib
import Cvs.Finite.WindowMatrixSymbolKernel
import Cvs.Upstream.GammaEulerLimit
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.WindowSymbolZetaLogDeriv
import Cvs.Zeta.Digamma

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Laplace transform of the one-cell function is `(2/s²)·Re (ξ'/ξ)(½ + s)`

`G(L) = 16(cosh(L/2) − 1) + archSymbol(0)·L + 2Σ_k (1 − e^{−b_k L})/b_k² − 2Σ_n Λ(n)n^{−1/2}(L − log n)₊` has
Laplace transform `4/(s(s²−¼)) + s^{−2}[Re ψ(¼ + s/2) − log π] + 2 s^{−2} Re (ζ'/ζ)(½ + s)` for `s > ½`,
i.e. `2 s^{−2} Re (ξ'/ξ)(½ + s)` with `ξ(w) = w(w−1)Γ_ℝ(w)ζ(w)`: the box's pole cancels against `w(w−1)`.
-/

noncomputable section

open MeasureTheory Real Set Filter Topology
open scoped ArithmeticFunction

namespace Cvs.Route.OneCellLaplaceTransform

open Cvs.Finite.WindowMatrixSymbolKernel (bk bk_pos)

/-! ### A nonnegative series of integrable functions integrates term by term -/

/-- **Term-by-term integration for a nonnegative series**: measurable nonnegative terms, each integrable,
pointwise summable, with summable integrals, sum to an integrable function whose integral is the sum. -/
theorem integrable_tsum_of_nonneg {μ : Measure ℝ} {F : ℕ → ℝ → ℝ} (hm : ∀ n, Measurable (F n))
    (hnn : ∀ n L, 0 ≤ F n L) (hpt : ∀ L, Summable fun n => F n L) (hint : ∀ n, Integrable (F n) μ)
    (hsum : Summable fun n => ∫ L, F n L ∂μ) :
    Integrable (fun L => ∑' n, F n L) μ ∧ ∫ L, ∑' n, F n L ∂μ = ∑' n, ∫ L, F n L ∂μ := by
  have hrepr : (fun L => ∑' n, F n L) = fun L => (∑' n, ENNReal.ofReal (F n L)).toReal := by
    funext L
    rw [ENNReal.tsum_toReal_eq (fun n => ENNReal.ofReal_ne_top)]
    congr 1
    funext n
    rw [ENNReal.toReal_ofReal (hnn n L)]
  have hmeas : Measurable fun L => ∑' n, F n L := by
    rw [hrepr]
    exact (Measurable.tsum fun n => (hm n).ennreal_ofReal).ennreal_toReal
  have hlin : ∀ n, ∫⁻ L, ‖F n L‖ₑ ∂μ = ENNReal.ofReal (∫ L, F n L ∂μ) := by
    intro n
    rw [ofReal_integral_eq_lintegral_ofReal (hint n) (ae_of_all _ (hnn n))]
    congr 1
    funext L
    rw [Real.eNorm_eq_ofReal (hnn n L)]
  have hfin : ∑' n, ∫⁻ L, ‖F n L‖ₑ ∂μ ≠ ⊤ := by
    simp_rw [hlin]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg (hnn n)) hsum]
    exact ENNReal.ofReal_ne_top
  refine ⟨⟨hmeas.aestronglyMeasurable, ?_⟩, integral_tsum (fun n => (hm n).aestronglyMeasurable) hfin⟩
  rw [HasFiniteIntegral]
  have h1 : ∀ L, ‖∑' n, F n L‖ₑ = ∑' n, ENNReal.ofReal (F n L) := by
    intro L
    rw [Real.eNorm_eq_ofReal (tsum_nonneg fun n => hnn n L),
      ENNReal.ofReal_tsum_of_nonneg (hnn · L) (hpt L)]
  simp_rw [h1]
  rw [lintegral_tsum fun n => (hm n).ennreal_ofReal.aemeasurable]
  have : ∑' n, ∫⁻ L, ENNReal.ofReal (F n L) ∂μ = ∑' n, ∫⁻ L, ‖F n L‖ₑ ∂μ := by
    congr 1; funext n; congr 1; funext L; rw [Real.eNorm_eq_ofReal (hnn n L)]
  rw [this]
  exact lt_top_iff_ne_top.2 hfin

/-! ### The digamma difference series -/

/-- **`ψ(a) − ψ(b) = Σ_k [1/(b+k) − 1/(a+k)]`** for positive real `a`, `b`, from the Euler–Gauss limit. -/
theorem hasSum_digamma_sub {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    HasSum (fun k : ℕ => 1 / (b + k) - 1 / (a + k))
      ((Complex.digamma a).re - (Complex.digamma b).re) := by
  have hta := Cvs.Upstream.GammaEulerLimit.tendsto_digamma (s := (a : ℂ)) (by simpa using ha)
  have htb := Cvs.Upstream.GammaEulerLimit.tendsto_digamma (s := (b : ℂ)) (by simpa using hb)
  have hsub := (Complex.continuous_re.tendsto _).comp (hta.sub htb)
  have hcongr : ∀ n : ℕ, (Complex.re ∘ fun n : ℕ =>
      ((Real.log n : ℂ) - ∑ k ∈ Finset.range n, ((a : ℂ) + (k : ℂ))⁻¹)
        - ((Real.log n : ℂ) - ∑ k ∈ Finset.range n, ((b : ℂ) + (k : ℂ))⁻¹)) n
      = ∑ k ∈ Finset.range n, (1 / (b + k) - 1 / (a + k)) := by
    intro n
    simp only [Function.comp_apply]
    rw [show ((Real.log n : ℂ) - ∑ k ∈ Finset.range n, ((a : ℂ) + (k : ℂ))⁻¹)
        - ((Real.log n : ℂ) - ∑ k ∈ Finset.range n, ((b : ℂ) + (k : ℂ))⁻¹)
        = ∑ k ∈ Finset.range n, (((b : ℂ) + (k : ℂ))⁻¹ - ((a : ℂ) + (k : ℂ))⁻¹) by
      rw [Finset.sum_sub_distrib]; ring]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e1 : ((b : ℂ) + (k : ℂ))⁻¹ = (((1 / (b + k) : ℝ)) : ℂ) := by push_cast; ring
    have e2 : ((a : ℂ) + (k : ℂ))⁻¹ = (((1 / (a + k) : ℝ)) : ℂ) := by push_cast; ring
    rw [e1, e2, ← Complex.ofReal_sub, Complex.ofReal_re]
  have hS : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, (1 / (b + k) - 1 / (a + k))) atTop
      (𝓝 ((Complex.digamma a).re - (Complex.digamma b).re)) := by
    have := hsub
    rw [show (Complex.digamma a - Complex.digamma b).re
        = (Complex.digamma a).re - (Complex.digamma b).re from Complex.sub_re _ _] at this
    exact this.congr hcongr
  -- summability: `(a+k)(b+k) ≥ m²(k+1)²` with `m = min (min a b) 1`, so the terms are `O(1/(k+1)²)`
  have hsumm : Summable fun k : ℕ => 1 / (b + k) - 1 / (a + k) := by
    set m := min (min a b) 1 with hm
    have hm0 : 0 < m := lt_min (lt_min ha hb) one_pos
    have hm1 : m ≤ 1 := min_le_right _ _
    have hma : m ≤ a := (min_le_left _ _).trans (min_le_left _ _)
    have hmb : m ≤ b := (min_le_left _ _).trans (min_le_right _ _)
    have key : ∀ (c : ℝ) (k : ℕ), m ≤ c → m * ((k : ℝ) + 1) ≤ c + k := fun c k hc => by
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith
    have hab : ∀ k : ℕ, |1 / (b + k) - 1 / (a + k)| ≤ |a - b| / m ^ 2 * (1 / ((k : ℝ) + 1) ^ 2) := by
      intro k
      have hak : 0 < a + k := by positivity
      have hbk : 0 < b + k := by positivity
      have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      rw [show 1 / (b + k) - 1 / (a + k) = (a - b) / ((a + k) * (b + k)) by field_simp; ring,
        abs_div, abs_of_pos (mul_pos hak hbk), div_mul_div_comm, mul_one,
        div_le_div_iff₀ (mul_pos hak hbk) (by positivity)]
      have h := mul_le_mul (key a k hma) (key b k hmb) (by positivity) hak.le
      nlinarith [abs_nonneg (a - b), h]
    have hbase : Summable fun k : ℕ => |a - b| / m ^ 2 * (1 / ((k : ℝ) + 1) ^ 2) := by
      refine Summable.mul_left _ ?_
      have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))
      exact this.congr fun k => by push_cast; ring
    exact Summable.of_norm_bounded hbase fun k => by rw [Real.norm_eq_abs]; exact hab k
  exact (hsumm.hasSum_iff_tendsto_nat).2 hS

/-! ### Elementary Laplace integrals -/

/-- `∫₀^∞ e^{aL} dL = −1/a` for `a < 0`. -/
theorem laplace_exp {a : ℝ} (ha : a < 0) : ∫ L in Ioi (0:ℝ), Real.exp (a * L) = -1 / a := by
  rw [integral_exp_mul_Ioi ha 0]; simp

/-- The ramp `(L − c) e^{−sL}` is integrable on `(c, ∞)` for `s > 0`. -/
theorem integrableOn_ramp {s c : ℝ} (hs : 0 < s) :
    IntegrableOn (fun L => (L - c) * Real.exp (-(s * L))) (Ioi c) := by
  -- `L − c ≤ (2/s) e^{(s/2)(L−c)}` from `x ≤ e^x`, so the integrand is below `(2/s) e^{−sc/2} e^{−(s/2)L}`
  have hdom : IntegrableOn (fun L => (2 / s) * Real.exp (-(s * c / 2)) * Real.exp (-(s / 2) * L)) (Ioi c) :=
    (integrableOn_exp_mul_Ioi (by linarith : -(s / 2) < 0) c).const_mul _
  refine hdom.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun L hL => ?_))
  · exact (((continuous_id.sub continuous_const).mul
      ((continuous_const.mul continuous_id).neg.rexp)).aestronglyMeasurable)
  · have hcL : c ≤ L := le_of_lt hL
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith) (Real.exp_pos _).le)]
    have hx : (s / 2) * (L - c) + 1 ≤ Real.exp ((s / 2) * (L - c)) := Real.add_one_le_exp _
    have hle : L - c ≤ (2 / s) * Real.exp ((s / 2) * (L - c)) := by
      have : (s / 2) * (L - c) ≤ Real.exp ((s / 2) * (L - c)) := by linarith
      calc L - c = (2 / s) * ((s / 2) * (L - c)) := by field_simp
        _ ≤ (2 / s) * Real.exp ((s / 2) * (L - c)) := by gcongr
    calc (L - c) * Real.exp (-(s * L))
        ≤ (2 / s) * Real.exp ((s / 2) * (L - c)) * Real.exp (-(s * L)) :=
          mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
      _ = (2 / s) * Real.exp (-(s * c / 2)) * Real.exp (-(s / 2) * L) := by
          rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]; congr 2; ring
/-- `∫_c^∞ (L − c) e^{−sL} dL = e^{−sc}/s²` for `s > 0`. -/
theorem laplace_ramp {s c : ℝ} (hs : 0 < s) :
    ∫ L in Ioi c, (L - c) * Real.exp (-(s * L)) = Real.exp (-(s * c)) / s ^ 2 := by
  have hs0 : s ≠ 0 := hs.ne'
  -- antiderivative `F L = −e^{−sL}(L − c + 1/s)/s`
  have hF : ∀ L, HasDerivAt (fun L => -(Real.exp (-(s * L)) * (L - c + 1 / s) / s))
      ((L - c) * Real.exp (-(s * L))) L := by
    intro L
    have h1 : HasDerivAt (fun L => Real.exp (-(s * L))) (Real.exp (-(s * L)) * (-s)) L := by
      have := ((hasDerivAt_id L).const_mul s).neg.exp
      simpa [mul_comm] using this
    have h2 : HasDerivAt (fun L => L - c + 1 / s) 1 L := ((hasDerivAt_id L).sub_const c).add_const _
    refine (((h1.mul h2).div_const s).neg).congr_deriv ?_
    field_simp
    ring
  have hint := integrableOn_ramp (c := c) hs
  have hlim : Tendsto (fun L => -(Real.exp (-(s * L)) * (L - c + 1 / s) / s)) atTop (𝓝 0) := by
    -- `(L − c + 1/s) e^{−sL} = (1/s)(sL)e^{−sL} + (1/s − c)e^{−sL} → 0`
    have h1 : Tendsto (fun L : ℝ => (s * L) * Real.exp (-(s * L))) atTop (𝓝 0) := by
      have := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
        (tendsto_id.const_mul_atTop hs)
      simpa [Function.comp_def] using this
    have h2 : Tendsto (fun L : ℝ => Real.exp (-(s * L))) atTop (𝓝 0) := by
      have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hs)
      simpa [Function.comp_def] using this
    have h3 : Tendsto (fun L : ℝ => -((1 / s) * ((s * L) * Real.exp (-(s * L)))
        + (1 / s - c) * Real.exp (-(s * L))) / s) atTop (𝓝 (-((1 / s) * 0 + (1 / s - c) * 0) / s)) :=
      ((h1.const_mul _).add (h2.const_mul _)).neg.div_const _
    simp only [mul_zero, add_zero, neg_zero, zero_div] at h3
    refine h3.congr fun L => ?_
    field_simp
    ring
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (hF c).continuousAt.continuousWithinAt
    (fun L _ => hF L) hint hlim]
  field_simp
  ring

/-! ### The pole -/

/-- `∫₀^∞ 16(cosh(L/2) − 1) e^{−sL} dL = 4/(s(s² − ¼))` for `s > ½`. -/
theorem laplace_pole {s : ℝ} (hs : 1 / 2 < s) :
    IntegrableOn (fun L => 16 * (Real.cosh (L / 2) - 1) * Real.exp (-(s * L))) (Ioi 0) ∧
    ∫ L in Ioi (0:ℝ), 16 * (Real.cosh (L / 2) - 1) * Real.exp (-(s * L)) = 4 / (s * (s ^ 2 - 1 / 4)) := by
  have h1 : (1 / 2 - s) < 0 := by linarith
  have h2 : (-1 / 2 - s) < 0 := by linarith
  have h3 : -s < 0 := by linarith
  have hfun : (fun L => 16 * (Real.cosh (L / 2) - 1) * Real.exp (-(s * L))) =
      fun L => (8 * Real.exp ((1 / 2 - s) * L) + 8 * Real.exp ((-1 / 2 - s) * L))
        - 16 * Real.exp (-s * L) := by
    funext L
    rw [Real.cosh_eq]
    have e1 : Real.exp ((1 / 2 - s) * L) = Real.exp (L / 2) * Real.exp (-(s * L)) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp ((-1 / 2 - s) * L) = Real.exp (-(L / 2)) * Real.exp (-(s * L)) := by
      rw [← Real.exp_add]; ring_nf
    have e3 : Real.exp (-s * L) = Real.exp (-(s * L)) := by ring_nf
    rw [e1, e2, e3]; ring
  have i1 := (integrableOn_exp_mul_Ioi h1 0).const_mul (8:ℝ)
  have i2 := (integrableOn_exp_mul_Ioi h2 0).const_mul (8:ℝ)
  have i3 := (integrableOn_exp_mul_Ioi h3 0).const_mul (16:ℝ)
  have hi12 : IntegrableOn (fun L => 8 * Real.exp ((1 / 2 - s) * L) + 8 * Real.exp ((-1 / 2 - s) * L)) (Ioi 0) :=
    i1.add i2
  refine ⟨hfun ▸ hi12.sub i3, ?_⟩
  rw [hfun, integral_sub hi12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
    integral_const_mul, laplace_exp h1, laplace_exp h2, laplace_exp h3]
  have n1 : s ≠ 0 := by intro h; linarith
  have n2 : 1 / 2 - s ≠ 0 := by intro h; linarith
  have n3 : -1 / 2 - s ≠ 0 := by intro h; linarith
  have n4 : s ^ 2 - 1 / 4 ≠ 0 := by
    have : (s - 1 / 2) * (s + 1 / 2) ≠ 0 := mul_ne_zero (by intro h; linarith) (by intro h; linarith)
    intro h; apply this; linarith [h]
  simp only [← mul_div_assoc]
  rw [div_add_div _ _ n2 n3, div_sub_div _ _ (mul_ne_zero n2 n3) (neg_ne_zero.2 n1),
    div_eq_div_iff (mul_ne_zero (mul_ne_zero n2 n3) (neg_ne_zero.2 n1)) (mul_ne_zero n1 n4)]
  ring

/-! ### The archimedean ladder -/

/-- The ladder `Σ_k (1 − e^{−b_k L})/b_k²` of the archimedean kernel's tail factors. -/
def ladder (L : ℝ) : ℝ := ∑' k : ℕ, (1 - Real.exp (-(bk k * L))) / bk k ^ 2

theorem bk_ge (k : ℕ) : ((k : ℝ) + 1) / 2 ≤ bk k := by
  unfold bk; have : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith

theorem summable_inv_bk_sq : Summable fun k : ℕ => 1 / bk k ^ 2 := by
  have h : Summable fun k : ℕ => 4 * (1 / ((k : ℝ) + 1) ^ 2) := by
    have := (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
    have h2 := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).2 this
    refine (h2.mul_left 4).congr fun k => ?_
    simp [Nat.cast_add, Nat.cast_one]
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) h
  have hb := bk_ge k
  have hk : (0:ℝ) < (k : ℝ) + 1 := by positivity
  have hb2 : (((k : ℝ) + 1) / 2) ^ 2 ≤ bk k ^ 2 := by gcongr
  have hbpos : 0 < bk k ^ 2 := by have := bk_pos k; positivity
  rw [div_le_iff₀ hbpos]
  calc (1:ℝ) = 4 * (1 / ((k : ℝ) + 1) ^ 2) * (((k : ℝ) + 1) / 2) ^ 2 := by field_simp; ring
    _ ≤ 4 * (1 / ((k : ℝ) + 1) ^ 2) * bk k ^ 2 := by gcongr

/-- One rung: `∫₀^∞ (1 − e^{−bL})/b² · e^{−sL} dL = 1/(b s (s + b))`. -/
theorem laplace_rung {s b : ℝ} (hs : 0 < s) (hb : 0 < b) :
    ∫ L in Ioi (0:ℝ), (1 - Real.exp (-(b * L))) / b ^ 2 * Real.exp (-(s * L)) = 1 / (b * s * (s + b)) := by
  have h1 : -s < 0 := by linarith
  have h2 : -(s + b) < 0 := by linarith
  have hfun : (fun L => (1 - Real.exp (-(b * L))) / b ^ 2 * Real.exp (-(s * L))) =
      fun L => (1 / b ^ 2) * (Real.exp (-s * L) - Real.exp (-(s + b) * L)) := by
    funext L
    have : Real.exp (-(s + b) * L) = Real.exp (-(b * L)) * Real.exp (-(s * L)) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]
    have : Real.exp (-s * L) = Real.exp (-(s * L)) := by ring_nf
    rw [this]; ring
  rw [hfun, integral_const_mul, integral_sub (integrableOn_exp_mul_Ioi h1 0) (integrableOn_exp_mul_Ioi h2 0),
    laplace_exp h1, laplace_exp h2]
  have : s + b ≠ 0 := by positivity
  field_simp
  ring

/-- Pointwise summability of the ladder terms (any `L`, the `|L|`-form keeps every term nonnegative). -/
theorem summable_ladder_abs (s L : ℝ) :
    Summable fun k : ℕ => (1 - Real.exp (-(bk k * |L|))) / bk k ^ 2 * Real.exp (-(s * L)) := by
  refine (summable_inv_bk_sq.mul_right (Real.exp (-(s * L)))).of_nonneg_of_le (fun k => ?_) fun k => ?_
  · have := bk_pos k
    have : Real.exp (-(bk k * |L|)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [abs_nonneg L]
    have : 0 ≤ 1 - Real.exp (-(bk k * |L|)) := by linarith
    positivity
  · have := bk_pos k
    gcongr
    linarith [Real.exp_pos (-(bk k * |L|))]

/-- **The ladder's Laplace transform**: `∫₀^∞ Σ_k (1 − e^{−b_k L})/b_k² · e^{−sL} dL
= (Re ψ(¼ + s/2) − Re ψ(¼)) / (2 s²)`, the partial-fraction collapse of the archimedean tail. -/
theorem laplace_ladder {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun L => ladder L * Real.exp (-(s * L))) (Ioi 0) ∧
    ∫ L in Ioi (0:ℝ), ladder L * Real.exp (-(s * L)) =
      ((Complex.digamma ((1 / 4 + s / 2 : ℝ) : ℂ)).re - (Complex.digamma ((1 / 4 : ℝ) : ℂ)).re) / (2 * s ^ 2) := by
  -- work with the `|L|`-form, which agrees with the ladder on `(0, ∞)` and is nonnegative everywhere
  set F : ℕ → ℝ → ℝ := fun k L => (1 - Real.exp (-(bk k * |L|))) / bk k ^ 2 * Real.exp (-(s * L)) with hF
  have hagree : ∀ L ∈ Ioi (0:ℝ), ladder L * Real.exp (-(s * L)) = ∑' k, F k L := by
    intro L hL
    simp only [hF, ladder, abs_of_pos (show (0:ℝ) < L from hL)]
    rw [← tsum_mul_right]
  have hm : ∀ k, Measurable (F k) := fun k => by
    simp only [hF]
    exact (by fun_prop : Continuous fun L : ℝ => (1 - Real.exp (-(bk k * |L|))) / bk k ^ 2 * Real.exp (-(s * L))).measurable
  have hnn : ∀ k L, 0 ≤ F k L := by
    intro k L
    have := bk_pos k
    have : Real.exp (-(bk k * |L|)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [abs_nonneg L]
    have : 0 ≤ 1 - Real.exp (-(bk k * |L|)) := by linarith
    simp only [hF]; positivity
  have hpt : ∀ L, Summable fun k => F k L := fun L => summable_ladder_abs s L
  have hval : ∀ k, ∫ L in Ioi (0:ℝ), F k L = 1 / (bk k * s * (s + bk k)) := by
    intro k
    rw [← laplace_rung hs (bk_pos k)]
    refine setIntegral_congr_fun measurableSet_Ioi fun L hL => ?_
    simp only [hF, abs_of_pos (show (0:ℝ) < L from hL)]
  have hint : ∀ k, Integrable (F k) (volume.restrict (Ioi 0)) := by
    intro k
    have h1 : -s < 0 := by linarith
    have h2 : -(s + bk k) < 0 := by linarith [bk_pos k]
    have hi : IntegrableOn (fun L => (1 / bk k ^ 2) * (Real.exp (-s * L) - Real.exp (-(s + bk k) * L))) (Ioi 0) :=
      ((integrableOn_exp_mul_Ioi h1 0).sub (integrableOn_exp_mul_Ioi h2 0)).const_mul _
    refine hi.congr_fun (fun L hL => ?_) measurableSet_Ioi
    simp only [hF, abs_of_pos (show (0:ℝ) < L from hL)]
    have : Real.exp (-(s + bk k) * L) = Real.exp (-(bk k * L)) * Real.exp (-(s * L)) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]
    have : Real.exp (-s * L) = Real.exp (-(s * L)) := by ring_nf
    rw [this]; ring
  have hsum : Summable fun k => ∫ L in Ioi (0:ℝ), F k L := by
    simp_rw [hval]
    refine (summable_inv_bk_sq.mul_left (1 / s)).of_nonneg_of_le (fun k => by have := bk_pos k; positivity) fun k => ?_
    have := bk_pos k
    rw [div_le_iff₀ (by positivity)]
    calc (1:ℝ) = (1 / s) * (1 / bk k ^ 2) * (bk k * s * bk k) := by field_simp
      _ ≤ (1 / s) * (1 / bk k ^ 2) * (bk k * s * (s + bk k)) := by gcongr; linarith
  obtain ⟨hI, hE⟩ := integrable_tsum_of_nonneg hm hnn hpt hint hsum
  refine ⟨(show IntegrableOn (fun L => ∑' n, F n L) (Ioi 0) volume from hI).congr_fun
    (fun L hL => (hagree L hL).symm) measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hagree, hE]
  simp_rw [hval]
  -- partial fractions: `1/(b s (s+b)) = (1/(2s²)) (1/(¼+k) − 1/(¼+s/2+k))`
  have hd := hasSum_digamma_sub (a := 1 / 4 + s / 2) (b := 1 / 4) (by linarith) (by norm_num)
  have hd' := hd.mul_left (1 / (2 * s ^ 2))
  rw [div_eq_mul_one_div, mul_comm, ← hd'.tsum_eq]
  congr 1
  funext k
  have := bk_pos k
  have hk0 : (0:ℝ) < 1 / 4 + k := by positivity
  have hk1 : (0:ℝ) < 1 / 4 + s / 2 + k := by positivity
  have hbk : bk k = 2 * (1 / 4 + k) := by unfold bk; ring
  rw [hbk]
  field_simp
  ring

/-! ### The prime side -/

/-- `Σ_n Λ(n) n^{−1/2} (L − log n)₊`: the prime side of the box, a finite sum for each `L`. -/
def primeSide (L : ℝ) : ℝ := ∑' n : ℕ, Λ n / Real.sqrt n * max (L - Real.log n) 0

/-- `∫₀^∞ (L − c)₊ e^{−sL} dL = e^{−sc}/s²` for `c ≥ 0`, `s > 0`. -/
theorem laplace_ramp_plus {s c : ℝ} (hs : 0 < s) (hc : 0 ≤ c) :
    IntegrableOn (fun L => max (L - c) 0 * Real.exp (-(s * L))) (Ioi 0) ∧
    ∫ L in Ioi (0:ℝ), max (L - c) 0 * Real.exp (-(s * L)) = Real.exp (-(s * c)) / s ^ 2 := by
  have hfun : (fun L => max (L - c) 0 * Real.exp (-(s * L))) =
      Set.indicator (Ioi c) (fun L => (L - c) * Real.exp (-(s * L))) := by
    funext L
    by_cases h : c < L
    · rw [Set.indicator_of_mem (show L ∈ Ioi c from h), max_eq_left (by linarith)]
    · rw [Set.indicator_of_notMem (show L ∉ Ioi c from h), max_eq_right (by linarith [not_lt.1 h]),
        zero_mul]
  have hI : Integrable (Set.indicator (Ioi c) (fun L => (L - c) * Real.exp (-(s * L)))) :=
    (integrable_indicator_iff measurableSet_Ioi).2 (integrableOn_ramp hs)
  refine ⟨hfun ▸ hI.integrableOn, ?_⟩
  rw [hfun, integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    Set.Ioi_inter_Ioi, sup_of_le_left hc, laplace_ramp hs]

/-- One prime atom: `∫₀^∞ Λ(n) n^{−1/2} (L − log n)₊ e^{−sL} dL = Λ(n) n^{−(½+s)}/s²`. -/
theorem laplace_primeTerm {s : ℝ} (hs : 0 < s) (n : ℕ) :
    IntegrableOn (fun L => Λ n / Real.sqrt n * max (L - Real.log n) 0 * Real.exp (-(s * L))) (Ioi 0) ∧
    ∫ L in Ioi (0:ℝ), Λ n / Real.sqrt n * max (L - Real.log n) 0 * Real.exp (-(s * L)) =
      Λ n * (n : ℝ) ^ (-(1 / 2 + s)) / s ^ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hc : 0 ≤ Real.log n := Real.log_nonneg hn'
  obtain ⟨hI, hE⟩ := laplace_ramp_plus hs hc
  have hfun : (fun L => Λ n / Real.sqrt n * max (L - Real.log n) 0 * Real.exp (-(s * L))) =
      fun L => Λ n / Real.sqrt n * (max (L - Real.log n) 0 * Real.exp (-(s * L))) := by
    funext L; ring
  refine ⟨hfun ▸ hI.const_mul _, ?_⟩
  rw [hfun, integral_const_mul, hE]
  have e : Real.exp (-(s * Real.log n)) = (n:ℝ) ^ (-s) := by rw [Real.rpow_def_of_pos hnpos]; ring_nf
  rw [e, Real.sqrt_eq_rpow, show -(1 / 2 + s) = -(1 / 2:ℝ) + (-s) by ring, Real.rpow_add hnpos,
    Real.rpow_neg hnpos.le (1 / 2)]
  ring

/-- Summability of the atoms' transforms for `s > ½`: `Λ(n) ≤ log n ≤ n^ε/ε`. -/
theorem summable_primeTerm {s : ℝ} (hs : 1 / 2 < s) :
    Summable fun n : ℕ => Λ n * (n : ℝ) ^ (-(1 / 2 + s)) / s ^ 2 := by
  set ε := (s - 1 / 2) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hs0 : 0 < s := by linarith
  have hsum : Summable fun n : ℕ => (1 / (ε * s ^ 2)) * (n : ℝ) ^ (-1 - ε) :=
    (Real.summable_nat_rpow.2 (by linarith)).mul_left _
  refine hsum.of_nonneg_of_le (fun n => ?_) fun n => ?_
  · have := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    have := Real.rpow_nonneg (Nat.cast_nonneg n) (-(1 / 2 + s))
    positivity
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
      have := Real.rpow_nonneg (le_refl (0:ℝ)) (-1 - ε)
      positivity
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn
    have h1 : Λ n ≤ (n:ℝ) ^ ε / ε :=
      ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_rpow_div hnpos.le hε0)
    have h2 : (n:ℝ) ^ ε * (n:ℝ) ^ (-(1 / 2 + s)) = (n:ℝ) ^ (-1 - ε) := by
      rw [← Real.rpow_add hnpos]; congr 1; rw [hε]; ring
    have hp := Real.rpow_nonneg hnpos.le (-(1 / 2 + s))
    calc Λ n * (n:ℝ) ^ (-(1 / 2 + s)) / s ^ 2
        ≤ ((n:ℝ) ^ ε / ε) * (n:ℝ) ^ (-(1 / 2 + s)) / s ^ 2 := by gcongr
      _ = (1 / (ε * s ^ 2)) * (n:ℝ) ^ (-1 - ε) := by rw [← h2]; field_simp

/-- **The prime side's Laplace transform**: `∫₀^∞ Σ_n Λ(n)n^{−1/2}(L − log n)₊ e^{−sL} dL
= s^{−2} Σ_n Λ(n) n^{−(½+s)}` for `s > ½`. -/
theorem laplace_primeSide {s : ℝ} (hs : 1 / 2 < s) :
    IntegrableOn (fun L => primeSide L * Real.exp (-(s * L))) (Ioi 0) ∧
    ∫ L in Ioi (0:ℝ), primeSide L * Real.exp (-(s * L)) =
      (∑' n : ℕ, Λ n * (n : ℝ) ^ (-(1 / 2 + s))) / s ^ 2 := by
  have hs0 : 0 < s := by linarith
  set F : ℕ → ℝ → ℝ := fun n L => Λ n / Real.sqrt n * max (L - Real.log n) 0 * Real.exp (-(s * L)) with hF
  have hagree : ∀ L, primeSide L * Real.exp (-(s * L)) = ∑' n, F n L := by
    intro L; simp only [hF, primeSide]; rw [← tsum_mul_right]
  have hm : ∀ n, Measurable (F n) := fun n =>
    (by fun_prop : Continuous fun L : ℝ =>
      Λ n / Real.sqrt n * max (L - Real.log n) 0 * Real.exp (-(s * L))).measurable
  have hnn : ∀ n L, 0 ≤ F n L := by
    intro n L
    have h0 : 0 ≤ Λ n / Real.sqrt n :=
      div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
    simp only [hF]
    exact mul_nonneg (mul_nonneg h0 (le_max_right _ _)) (Real.exp_pos _).le
  have hpt : ∀ L, Summable fun n => F n L := by
    intro L
    refine summable_of_ne_finset_zero (s := Finset.range ⌈Real.exp L⌉₊) fun n hn => ?_
    rw [Finset.mem_range, not_lt] at hn
    have h1 : Real.exp L ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    have hnpos : (0:ℝ) < n := (Real.exp_pos L).trans_le h1
    have h2 : L ≤ Real.log n := (Real.le_log_iff_exp_le hnpos).2 h1
    simp only [hF]
    rw [max_eq_right (by linarith), mul_zero, zero_mul]
  have hint : ∀ n, Integrable (F n) (volume.restrict (Ioi 0)) := fun n => (laplace_primeTerm hs0 n).1
  have hval : ∀ n, ∫ L in Ioi (0:ℝ), F n L = Λ n * (n : ℝ) ^ (-(1 / 2 + s)) / s ^ 2 :=
    fun n => (laplace_primeTerm hs0 n).2
  have hsum : Summable fun n => ∫ L in Ioi (0:ℝ), F n L := by
    simp_rw [hval]; exact summable_primeTerm hs
  obtain ⟨hI, hE⟩ := integrable_tsum_of_nonneg hm hnn hpt hint hsum
  have hfun : (fun L => primeSide L * Real.exp (-(s * L))) = fun L => ∑' n, F n L := funext hagree
  refine ⟨hfun ▸ hI, ?_⟩
  rw [hfun, hE]
  simp_rw [hval]
  rw [tsum_div_const]

/-- The prime sum is `Re L(Λ, ½+s) = −Re (ζ'/ζ)(½ + s)`, Mathlib's Dirichlet series of `Λ`. -/
theorem tsum_vonMangoldt_eq {s : ℝ} (hs : 1 / 2 < s) :
    ∑' n : ℕ, Λ n * (n : ℝ) ^ (-(1 / 2 + s)) = -(logDeriv riemannZeta ((1 / 2 + s : ℝ) : ℂ)).re := by
  have hre : 1 < ((1 / 2 + s : ℝ) : ℂ).re := by simp; linarith
  have h := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre
  rw [logDeriv_apply, ← Complex.neg_re, ← neg_div, ← h]
  unfold LSeries
  have hterm : ∀ n : ℕ, LSeries.term (fun n => (Λ n : ℂ)) ((1 / 2 + s : ℝ) : ℂ) n =
      ((Λ n * (n : ℝ) ^ (-(1 / 2 + s)) : ℝ) : ℂ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [LSeries.term_of_ne_zero hn.ne', Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg n),
      Complex.ofReal_neg, Complex.cpow_neg, div_eq_mul_inv, Complex.ofReal_natCast]
  rw [tsum_congr hterm, ← Complex.ofReal_tsum, Complex.ofReal_re]

/-! ### Assembly -/

/-- The one-cell function `G(L) = Q(1_{(0,L)})` on the prime side: pole, linear archimedean term,
ladder, and the prime atoms, with `archSymbol 0 = Re ψ(¼) − log π`. -/
def G (L : ℝ) : ℝ :=
  16 * (Real.cosh (L / 2) - 1) + Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * L + 2 * ladder L - 2 * primeSide L

theorem archSymbol_zero :
    Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 = (Complex.digamma ((1 / 4 : ℝ) : ℂ)).re - Real.log Real.pi := by
  unfold Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol Cvs.Zeta.digammaArg
  simp

/-- **The Laplace transform of the one-cell function** for `s > ½`:
`∫₀^∞ G(L) e^{−sL} dL = 4/(s(s²−¼)) + s^{−2}[Re ψ(¼ + s/2) − log π] + 2 s^{−2} Re (ζ'/ζ)(½ + s)`. -/
theorem laplace_G {s : ℝ} (hs : 1 / 2 < s) :
    ∫ L in Ioi (0:ℝ), G L * Real.exp (-(s * L)) =
      4 / (s * (s ^ 2 - 1 / 4))
        + ((Complex.digamma ((1 / 4 + s / 2 : ℝ) : ℂ)).re - Real.log Real.pi) / s ^ 2
        + 2 * (logDeriv riemannZeta ((1 / 2 + s : ℝ) : ℂ)).re / s ^ 2 := by
  have hs0 : 0 < s := by linarith
  obtain ⟨hP, eP⟩ := laplace_pole hs
  obtain ⟨hLd, eLd⟩ := laplace_ladder hs0
  obtain ⟨hPr, ePr⟩ := laplace_primeSide hs
  have hA : IntegrableOn (fun L => Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * ((L - 0) * Real.exp (-(s * L)))) (Ioi 0) :=
    (integrableOn_ramp (c := 0) hs0).const_mul _
  have hfun : (fun L => G L * Real.exp (-(s * L))) = fun L =>
      ((16 * (Real.cosh (L / 2) - 1) * Real.exp (-(s * L))
        + Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * ((L - 0) * Real.exp (-(s * L))))
        + 2 * (ladder L * Real.exp (-(s * L)))) - 2 * (primeSide L * Real.exp (-(s * L))) := by
    funext L; simp only [G]; ring
  have h12 : IntegrableOn (fun L => 16 * (Real.cosh (L / 2) - 1) * Real.exp (-(s * L))
      + Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * ((L - 0) * Real.exp (-(s * L)))) (Ioi 0) := hP.add hA
  have h123 : IntegrableOn (fun L => (16 * (Real.cosh (L / 2) - 1) * Real.exp (-(s * L))
      + Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * ((L - 0) * Real.exp (-(s * L))))
      + 2 * (ladder L * Real.exp (-(s * L)))) (Ioi 0) := h12.add (hLd.const_mul 2)
  have h4 : IntegrableOn (fun L => 2 * (primeSide L * Real.exp (-(s * L)))) (Ioi 0) := hPr.const_mul 2
  rw [hfun, integral_sub h123 h4, integral_add h12 (hLd.const_mul 2), integral_add hP hA,
    integral_const_mul, integral_const_mul, integral_const_mul, eP, laplace_ramp hs0, eLd, ePr,
    tsum_vonMangoldt_eq hs, archSymbol_zero]
  simp only [mul_zero, neg_zero, Real.exp_zero]
  ring

/-- The pole term is the logarithmic derivative of `w(w−1)` at `w = ½ + s`, times `2/s²`. -/
theorem pole_split {s : ℝ} (hs : 1 / 2 < s) :
    4 / (s * (s ^ 2 - 1 / 4)) = 2 / s ^ 2 * (1 / (1 / 2 + s) + 1 / (s - 1 / 2)) := by
  have n1 : s ≠ 0 := by intro h; linarith
  have n2 : 1 / 2 + s ≠ 0 := by intro h; linarith
  have n3 : s - 1 / 2 ≠ 0 := by intro h; linarith
  have n4 : s * (s ^ 2 - 1 / 4) ≠ 0 := by
    refine mul_ne_zero n1 ?_
    have : (s - 1 / 2) * (s + 1 / 2) ≠ 0 := mul_ne_zero n3 (by intro h; linarith)
    intro h; apply this; linarith [h]
  rw [div_add_div _ _ n2 n3, div_mul_div_comm,
    div_eq_div_iff n4 (mul_ne_zero (pow_ne_zero 2 n1) (mul_ne_zero n2 n3))]
  ring

/-- **`∫₀^∞ G e^{−sL} dL = (2/s²) · Re (ξ'/ξ)(½ + s)`**, with `ξ(w) = ½ w(w−1) Γ_ℝ(w) ζ(w)` and its
logarithmic derivative split as `1/w + 1/(w−1) + (log Γ_ℝ)'(w) + (ζ'/ζ)(w)` at the real point `w = ½ + s`. -/
theorem laplace_G_logDeriv {s : ℝ} (hs : 1 / 2 < s) :
    ∫ L in Ioi (0:ℝ), G L * Real.exp (-(s * L)) =
      2 / s ^ 2 * (1 / (1 / 2 + s) + 1 / (s - 1 / 2)
        + (logDeriv Complex.Gammaℝ ((1 / 2 + s : ℝ) : ℂ)).re
        + (logDeriv riemannZeta ((1 / 2 + s : ℝ) : ℂ)).re) := by
  have hs0 : 0 < s := by linarith
  rw [laplace_G hs, Cvs.WeilForm.WindowSymbolZetaLogDeriv.logDeriv_Gammaℝ (by simp; linarith)]
  have : (((1 / 2 + s : ℝ) : ℂ) / 2) = ((1 / 4 + s / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this]
  simp only [Complex.add_re, Complex.div_ofNat_re, Complex.neg_re, Complex.ofReal_re]
  rw [pole_split hs]
  ring

/-- The completed zeta with its pole factor, `ξ(w) = w(w−1)·Λ(w)` with `Λ = Γ_ℝ ζ` (the conventional `½`
drops out of the logarithmic derivative). -/
def xi (w : ℂ) : ℂ := w * (w - 1) * completedRiemannZeta w

/-- **`∫₀^∞ G(L) e^{−sL} dL = (2/s²) · Re (ξ'/ξ)(½ + s)`** for `s > ½`. -/
theorem laplace_G_xi {s : ℝ} (hs : 1 / 2 < s) :
    ∫ L in Ioi (0:ℝ), G L * Real.exp (-(s * L)) = 2 / s ^ 2 * (logDeriv xi ((1 / 2 + s : ℝ) : ℂ)).re := by
  set w : ℂ := ((1 / 2 + s : ℝ) : ℂ) with hw
  have hre : w.re = 1 / 2 + s := by simp [hw]
  have hre1 : 1 < w.re := by rw [hre]; linarith
  have hw0 : w ≠ 0 := fun h => by
    have := congrArg Complex.re h; rw [hre] at this; simp at this; linarith
  have hw1 : w ≠ 1 := fun h => by
    have := congrArg Complex.re h; rw [hre] at this; simp at this; linarith
  have hw1' : w - 1 ≠ 0 := sub_ne_zero.2 hw1
  have hζ : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hre1
  have hΓ : Complex.Gammaℝ w ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hΛ : completedRiemannZeta w ≠ 0 := by
    rw [Cvs.WeilForm.WindowSymbolZetaLogDeriv.completedZeta_eq_mul hw0 hΓ]; exact mul_ne_zero hζ hΓ
  have h1 : logDeriv xi w = logDeriv (fun z : ℂ => z * (z - 1)) w + logDeriv completedRiemannZeta w := by
    have hxi : xi = fun z => (fun z : ℂ => z * (z - 1)) z * completedRiemannZeta z := rfl
    rw [hxi]
    exact logDeriv_mul w (mul_ne_zero hw0 hw1') hΛ
      (differentiableAt_id.mul (differentiableAt_id.sub_const 1)) (differentiableAt_completedZeta hw0 hw1)
  have h2 : logDeriv (fun z : ℂ => z * (z - 1)) w = 1 / w + 1 / (w - 1) := by
    have hm : (fun z : ℂ => z * (z - 1)) = fun z => (fun z : ℂ => z) z * (fun z : ℂ => z - 1) z := rfl
    rw [hm, logDeriv_fun_mul (f := fun z : ℂ => z) (g := fun z : ℂ => z - 1) w hw0 hw1' differentiableAt_id
      (differentiableAt_id.sub_const 1), logDeriv_apply, logDeriv_apply, deriv_id'', deriv_sub_const, deriv_id'']
  have h3 : logDeriv completedRiemannZeta w = logDeriv riemannZeta w + logDeriv Complex.Gammaℝ w := by
    have hev : completedRiemannZeta =ᶠ[𝓝 w] fun z => riemannZeta z * Complex.Gammaℝ z := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show w ∈ {b : ℂ | (0:ℝ) < b.re} by simp only [Set.mem_ofPred_eq]; linarith)] with z hz
      have hz0 : z ≠ 0 := fun h => by simp [h] at hz
      exact Cvs.WeilForm.WindowSymbolZetaLogDeriv.completedZeta_eq_mul hz0 (Complex.Gammaℝ_ne_zero_of_re_pos hz)
    rw [(logDeriv_congr_nhds hev).eq_of_nhds]
    exact logDeriv_mul w hζ hΓ (differentiableAt_riemannZeta hw1)
      (Cvs.WeilForm.WindowSymbolZetaLogDeriv.differentiableAt_Gammaℝ (by linarith))
  rw [laplace_G_logDeriv hs, h1, h2, h3]
  simp only [Complex.add_re]
  have e1 : (1 / w).re = 1 / (1 / 2 + s) := by
    rw [hw, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  have e2 : (1 / (w - 1)).re = 1 / (s - 1 / 2) := by
    rw [hw, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_div, Complex.ofReal_re]
    congr 1; ring
  rw [e1, e2]
  ring

end Cvs.Route.OneCellLaplaceTransform
