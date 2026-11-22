import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BandTransferBandForm
import Cvs.L2a.BandTransferKernelForm
import Cvs.L2a.CornerSuprema
import Cvs.L2a.CutKernelSimplified
import Cvs.L2a.CutKernels
import Cvs.L2a.FarFarBound
import Cvs.L2a.FarIntegrationByParts
import Cvs.L2a.OrbitGapIntegerM
import Cvs.L2a.QIdentityCutPoint
import Cvs.L2a.QIdentityIterated
import Cvs.L2a.RampTopQuadratic
import Cvs.L2a.ScaledBandTransfer
import Cvs.L2a.SpanPoleMellinFromRungs
import Cvs.L2a.TopCornerConstants
import Cvs.Prolate.Envelope.RungCountEnvelope
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RungCauchySplit
import Cvs.Prolate.RungExactOrthogonality
import Cvs.Upstream.ExpDifferenceBound

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The top corner `Σ|C_m|`, local and global

The exact cut kernel is `μ_si + μ_co` with `(1 − wF)|μ_co| ≤ ecap(M)/c²` on `(1, 2)`. The global bound is T0 with `Θ_m`;
the local one is `ScaledBandTransfer`'s band transfer pointwise in `t`, with collar `δ` for `m ≥ 3` and shells `min(δ, u_k/4)` plus a
T0 strip at `m = 2`, integrated against `w²`. Hence `Σ|C_m| ≤ min(T^loc, T^glob)·P`, `T^loc ≤ R̄₁ + remainder`,
`T^glob ≤ r₁^glob + O(1/c)`, and the `ρ_t` form at `S*`.
-/

noncomputable section

namespace Cvs.L2a.TopCornerSum

open Real Set MeasureTheory Complex
open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.AngularProlateTailPositive Cvs.L2a.SpanPoleMellinFromRungs Cvs.L2a.FarIntegrationByParts Cvs.L2a.OrbitGapIntegerM Cvs.Prolate.Envelope.RungCountEnvelope Cvs.Prolate.RungCauchySplit Cvs.Upstream.ExpDifferenceBound
open scoped ComplexConjugate

/-! ### The count envelope in pair form -/

/-- `|S[μ]| ≤ (|μ(k)| + |μ(−k)|)R/2`. -/
theorem norm_smp_le {μ : ℝ → ℂ} {c χ x : ℝ} {g : ℝ → ℝ} (hx : 1 < x) (hc : 0 < c) (hχc : χ < c ^ 2) :
    ‖Cvs.L2a.BandTransferBandForm.smp μ c χ g x‖ ≤ (‖μ (kP c χ x)‖ + ‖μ (-kP c χ x)‖) * (rungAmp c χ g x / 2) := by
  have h1 : ‖psiP c χ g x‖ = rungAmp c χ g x / 2 := norm_psiP hx hc hχc
  have h2 : ‖conj (psiP c χ g x)‖ = rungAmp c χ g x / 2 := by rw [RCLike.norm_conj, h1]
  unfold Cvs.L2a.BandTransferBandForm.smp
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [norm_mul, norm_mul, h1, h2]; ring

/-- **T0 in pair form**: `|μ(ξ)| + |μ(−ξ)| ≤ 2B` on `[c, cY(x₀)]` gives `|Σ aᵢSᵢ[μ]| ≤ B√(6J/(x₀² − 1))√P_X`. -/
theorem t0_pair {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    {X x₀ B : ℝ} {μ : ℝ → ℂ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hX : 2 ≤ X)
    (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2) (hx₀ : x₀ ∈ Icc (6 / 5 : ℝ) X)
    (hμ : ∀ ξ ∈ Icc c (c * Ymax x₀), ‖μ ξ‖ + ‖μ (-ξ)‖ ≤ 2 * B) :
    ‖∑ i, (a i : ℂ) * Cvs.L2a.BandTransferBandForm.smp μ c (χ i) (g i) x₀‖
      ≤ B * √(6 * (Fintype.card ι : ℝ) / (x₀ ^ 2 - 1)) * √(∑ i, a i ^ 2 * ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2) := by
  have hc0 : 0 < c := by linarith
  have hx1 : 1 < x₀ := by linarith [hx₀.1]
  have hY := Cvs.L2a.BandTransferBandForm.one_le_Ymax hx1
  have hB : 0 ≤ B := by
    have := hμ c ⟨le_rfl, le_mul_of_one_le_right hc0.le hY⟩
    linarith [norm_nonneg (μ c), norm_nonneg (μ (-c))]
  have hX' : ∀ i, ‖Cvs.L2a.BandTransferBandForm.smp μ c (χ i) (g i) x₀‖ ≤ B * rungAmp c (χ i) (g i) x₀ := fun i => by
    refine (norm_smp_le hx1 hc0 (hχc i)).trans ?_
    have := hμ _ (kP_mem_Icc hx1 hc0 (hχ0 i) (hχc i))
    have hR : 0 ≤ rungAmp c (χ i) (g i) x₀ := Real.sqrt_nonneg _
    nlinarith
  have herr := Cvs.L2a.BandTransferKernelForm.norm_sum_le_mass a (fun i => Cvs.L2a.BandTransferBandForm.smp μ c (χ i) (g i) x₀)
    (fun i => B * rungAmp c (χ i) (g i) x₀) (fun i => ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2) hM hX'
  rw [Cvs.L2a.BandTransferKernelForm.massSum_const_mul] at herr
  have henv := count_envelope hg hg₁ hg₂c hang hc hχ0 hχc hX hM hx₀
  have hsq : √(B ^ 2 * massSum (fun i => rungAmp c (χ i) (g i) x₀) (fun i => ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2))
      ≤ B * √(6 * (Fintype.card ι : ℝ) / (x₀ ^ 2 - 1)) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hB]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt henv) hB
  refine herr.trans ?_
  rw [mul_comm (√(∑ i, a i ^ 2 * ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2))]
  exact mul_le_mul_of_nonneg_right hsq (Real.sqrt_nonneg _)

/-- The span mass is at most `P = ∫₁^∞ Φ²`. -/
theorem spanMass_le {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) {X : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχi : Function.Injective χ) (hX : 1 ≤ X) :
    ∑ i, a i ^ 2 * (∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2) ≤ ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := by
  have hψ2 : ∀ i, IntegrableOn (fun x => psi c (g i) x ^ 2) (Ioi 1) := fun i =>
    (memLp_two_iff_integrable_sq ((Cvs.Prolate.Gram.RungGramFloorAtInfinity.rung_system (hg i) (hg₁ i) (hg₂c i)
      (hang i)).2.2.1.aestronglyMeasurable)).mp (Cvs.Prolate.RungExactOrthogonality.memLp_psi (hg i) (hg₁ i) (hg₂c i)
      (hang i) hc)
  rw [Cvs.Prolate.RungExactOrthogonality.integral_span_sq a hg hg₁ hg₂c hang hc hχi]
  refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  rw [intervalIntegral.integral_of_le hX]
  exact setIntegral_mono_set (hψ2 i) (ae_of_all _ fun x => sq_nonneg _)
    (ae_of_all _ fun x hx => show 1 < x from hx.1)

/-! ### The top kernels: the simplified part and the correction -/

theorem norm_muSi (c y x ξ : ℝ) : ‖Cvs.L2a.CutKernelSimplified.muSi c y x ξ‖ = 1 / |c * y + ξ| := by
  unfold Cvs.L2a.CutKernelSimplified.muSi
  rw [norm_div, norm_mul, norm_neg, Complex.norm_I, (continuous_eF c y).2, Complex.norm_real,
    Real.norm_eq_abs, one_mul]

/-- **The simplified pair**: `|μ_si(ξ)| + |μ_si(−ξ)| ≤ 2/(c(1 − y²))` for `ξ ≥ c` and `0 < y < 1`. -/
theorem norm_muSi_pair_le {c y x ξ : ℝ} (hc : 0 < c) (hy0 : 0 < y) (hy1 : y < 1) (hξ : c ≤ ξ) :
    ‖Cvs.L2a.CutKernelSimplified.muSi c y x ξ‖ + ‖Cvs.L2a.CutKernelSimplified.muSi c y x (-ξ)‖ ≤ 2 / (c * (1 - y ^ 2)) := by
  rw [norm_muSi, norm_muSi]
  have h1 : 0 < c * y + ξ := by nlinarith
  have h2 : c * y + -ξ < 0 := by nlinarith
  rw [abs_of_pos h1, abs_of_neg h2]
  have hy2 : 0 < 1 - y ^ 2 := by nlinarith
  have h3 : 0 < -(c * y + -ξ) := by linarith
  rw [div_add_div _ _ h1.ne' h3.ne', div_le_div_iff₀ (mul_pos h1 h3) (mul_pos hc hy2)]
  nlinarith [mul_nonneg (sub_nonneg.2 hξ) (add_nonneg (by linarith) (by positivity) : (0 : ℝ) ≤ ξ + c * y ^ 2)]

/-- The correction `μ_co = μ − μ_si` of the exact cut kernel. -/
def muCo (c y x ξ : ℝ) : ℂ := Cvs.L2a.QIdentityCutPoint.muCut c y x ξ - Cvs.L2a.CutKernelSimplified.muSi c y x ξ

/-- The correction factor `e(x, y) = 2xy/(p(1 − y)) + 2x/p + 1/(2x)`, `p = x² − 1`. -/
def eTop (x y : ℝ) : ℝ := 2 * x * y / (pP x * (1 - y)) + 2 * x / pP x + 1 / (2 * x)

theorem eTop_nonneg {x y : ℝ} (hx : 1 < x) (hy0 : 0 ≤ y) (hy1 : y < 1) : 0 ≤ eTop x y := by
  have hp : 0 < pP x := pP_pos hx
  have h1 : 0 < 1 - y := by linarith
  have hx0 : 0 < x := by linarith
  unfold eTop
  have := div_nonneg (by positivity : 0 ≤ 2 * x * y) (mul_pos hp h1).le
  positivity

/-- `|Q(cη)|² = p²c⁴(y² − η²)² + 4c²x²y²`. -/
theorem norm_qQk_sq (c y x η : ℝ) :
    ‖Cvs.L2a.QIdentityCutPoint.qQk c y x (c * η)‖ ^ 2 = (pP x * c ^ 2 * (η ^ 2 - y ^ 2)) ^ 2 + (2 * c * x * y) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Cvs.L2a.QIdentityCutPoint.qQk, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- **The correction at the top, absolute form**: `|μ_co(cη)| ≤ e(x, y)/(c²(1 − y²))` for `0 < y < 1 ≤ |η|`. -/
theorem norm_muCo_le {c y x η : ℝ} (hc : 0 < c) (hx : 1 < x) (hy0 : 0 < y) (hy1 : y < 1) (hη : 1 ≤ |η|) :
    ‖muCo c y x (c * η)‖ ≤ eTop x y / (c ^ 2 * (1 - y ^ 2)) := by
  have hx0 : 0 < x := by linarith
  have hp : 0 < pP x := pP_pos hx
  have hη2 : 1 ≤ η ^ 2 := by rw [← sq_abs]; nlinarith [abs_nonneg η]
  have hy2 : 0 < 1 - y ^ 2 := by nlinarith
  set D := η ^ 2 - y ^ 2 with hD
  have hDy : 1 - y ^ 2 ≤ D := by rw [hD]; linarith
  have hD0 : 0 < D := lt_of_lt_of_le hy2 hDy
  have hyη : 1 - y ≤ |y + η| := by
    have := abs_sub_abs_le_abs_sub η (-y)
    rw [abs_neg, abs_of_pos hy0, sub_neg_eq_add, add_comm η y] at this
    linarith
  have hyη0 : y + η ≠ 0 := fun h => by rw [h, abs_zero] at hyη; linarith
  have hs : c * y + c * η ≠ 0 := by rw [← mul_add]; exact mul_ne_zero hc.ne' hyη0
  set Q := Cvs.L2a.QIdentityCutPoint.qQk c y x (c * η) with hQ
  have hQsq := norm_qQk_sq c y x η
  rw [← hQ] at hQsq
  have hQlo : pP x * c ^ 2 * D ≤ ‖Q‖ := by
    have h := Cvs.L2a.QIdentityCutPoint.le_norm_qQk_re (c := c) (y := y) (ξ := c * η) hx.le
    rw [← hQ, show c ^ 2 * y ^ 2 - (c * η) ^ 2 = -(c ^ 2 * D) by rw [hD]; ring, abs_neg,
      abs_of_pos (by positivity)] at h
    linarith
  have hL : 0 < pP x * c ^ 2 * D := by positivity
  have hQ0 : 0 < ‖Q‖ := lt_of_lt_of_le hL hQlo
  have hQ2a : (pP x * c ^ 2 * D) ^ 2 ≤ ‖Q‖ ^ 2 := by rw [hQsq]; nlinarith [sq_nonneg (2 * c * x * y)]
  have hQ2b : 4 * pP x * c ^ 3 * x * y * D ≤ ‖Q‖ ^ 2 := by
    rw [hQsq]; nlinarith [sq_nonneg (pP x * c ^ 2 * D - 2 * c * x * y)]
  have hQ1 := Cvs.L2a.QIdentityIterated.norm_qQ₁_le_near (c := c) (y := y) (x := x) hx0.le hy0.le hy1.le hc.le
  unfold muCo
  rw [Cvs.L2a.CutKernelSimplified.muCut_eq_muSi_add hc hx0 hy0 hs, add_sub_cancel_left, norm_mul, (continuous_eF c y).2, one_mul]
  refine (norm_add_le _ _).trans ?_
  have hT1 : ‖((2 * c * x * y : ℝ) : ℂ) / (Q * ((c * y + c * η : ℝ) : ℂ))‖
      ≤ 2 * x * y / (pP x * (1 - y)) / (c ^ 2 * (1 - y ^ 2)) := by
    rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (by positivity), ← mul_add, abs_mul, abs_of_pos hc]
    have h1y : 0 < 1 - y := by linarith
    have hden : pP x * c ^ 2 * D * (c * (1 - y)) ≤ ‖Q‖ * (c * |y + η|) :=
      mul_le_mul hQlo (mul_le_mul_of_nonneg_left hyη hc.le) (by positivity) hQ0.le
    calc 2 * c * x * y / (‖Q‖ * (c * |y + η|)) ≤ 2 * c * x * y / (pP x * c ^ 2 * D * (c * (1 - y))) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = 2 * x * y / (pP x * (1 - y)) / (c ^ 2 * D) := by field_simp
      _ ≤ 2 * x * y / (pP x * (1 - y)) / (c ^ 2 * (1 - y ^ 2)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr)
  have hT2 : ‖((pP x : ℝ) : ℂ) * qQ₁ c y x / Q ^ 2‖
      ≤ (2 * x / pP x + 1 / (2 * x)) / (c ^ 2 * (1 - y ^ 2)) := by
    rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
    have hQq : 0 < ‖Q‖ ^ 2 := by positivity
    calc pP x * ‖qQ₁ c y x‖ / ‖Q‖ ^ 2 ≤ pP x * (2 * c ^ 2 * x * (1 - y ^ 2) + 2 * c * y) / ‖Q‖ ^ 2 := by
          gcongr
      _ = pP x * (2 * c ^ 2 * x * (1 - y ^ 2)) / ‖Q‖ ^ 2 + pP x * (2 * c * y) / ‖Q‖ ^ 2 := by ring
      _ ≤ pP x * (2 * c ^ 2 * x * (1 - y ^ 2)) / (pP x * c ^ 2 * D) ^ 2
          + pP x * (2 * c * y) / (4 * pP x * c ^ 3 * x * y * D) := by
          gcongr
      _ = (2 * x / pP x) * ((1 - y ^ 2) / D) / (c ^ 2 * D) + 1 / (2 * x) / (c ^ 2 * D) := by
          field_simp; ring
      _ ≤ (2 * x / pP x) * 1 / (c ^ 2 * (1 - y ^ 2)) + 1 / (2 * x) / (c ^ 2 * (1 - y ^ 2)) := by
          gcongr
          rw [div_le_one hD0]; exact hDy
      _ = _ := by ring
  calc _ ≤ 2 * x * y / (pP x * (1 - y)) / (c ^ 2 * (1 - y ^ 2))
        + (2 * x / pP x + 1 / (2 * x)) / (c ^ 2 * (1 - y ^ 2)) := add_le_add hT1 hT2
    _ = eTop x y / (c ^ 2 * (1 - y ^ 2)) := by unfold eTop; ring

/-- The correction pair: `|μ_co(ξ)| + |μ_co(−ξ)| ≤ 2e(x, y)/(c²(1 − y²))` for `ξ ≥ c`. -/
theorem norm_muCo_pair_le {c y x ξ : ℝ} (hc : 0 < c) (hx : 1 < x) (hy0 : 0 < y) (hy1 : y < 1) (hξ : c ≤ ξ) :
    ‖muCo c y x ξ‖ + ‖muCo c y x (-ξ)‖ ≤ 2 * (eTop x y / (c ^ 2 * (1 - y ^ 2))) := by
  have h1 : 1 ≤ |ξ / c| := by rw [abs_of_pos (div_pos (by linarith) hc), le_div_iff₀ hc]; linarith
  have h2 : 1 ≤ |-ξ / c| := by rwa [neg_div, abs_neg]
  have e1 : ξ = c * (ξ / c) := by field_simp
  have e2 : -ξ = c * (-ξ / c) := by field_simp
  have a1 := norm_muCo_le hc hx hy0 hy1 h1
  have a2 := norm_muCo_le hc hx hy0 hy1 h2
  rw [← e1] at a1; rw [← e2] at a2
  linarith

/-! ### The simplified real-part multiplier `α_η` -/

/-- `α_η(v) = (2c)⁻¹[−ie/(η + v) + iē/(η − v)]`, `e = e^{icxη}`: the symmetrised `μ_si` in `v = ξ/c`. -/
def alphaT (c x η v : ℝ) : ℂ :=
  (-I * eF c η x / (2 * c)) / ((η + 1 * v : ℝ) : ℂ) + (I * conj (eF c η x) / (2 * c)) / ((η + -1 * v : ℝ) : ℂ)

theorem pole_div_eq (A : ℂ) {c : ℝ} (hc : c ≠ 0) (p q ξ : ℝ) :
    (A / (2 * c)) / ((p + q * (ξ / c) : ℝ) : ℂ) = (A / ((c * p + q * ξ : ℝ) : ℂ)) / 2 := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have e : ((p + q * (ξ / c) : ℝ) : ℂ) = ((c * p + q * ξ : ℝ) : ℂ) / (c : ℂ) := by
    push_cast; field_simp
  rw [e]
  by_cases h : c * p + q * ξ = 0
  · simp [h]
  · have h' : ((c * p + q * ξ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h
    field_simp

/-- `α_η(ξ/c) = (μ_si)_s(ξ)`. -/
theorem alphaT_div_eq {c : ℝ} (hc : c ≠ 0) (x η ξ : ℝ) :
    alphaT c x η (ξ / c) = Cvs.L2a.QIdentityCutPoint.muSym (Cvs.L2a.CutKernelSimplified.muSi c η x) ξ := by
  unfold alphaT Cvs.L2a.QIdentityCutPoint.muSym Cvs.L2a.CutKernelSimplified.muSi
  rw [pole_div_eq _ hc, pole_div_eq _ hc]
  simp only [map_div₀, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

theorem norm_alphaT_le_pair {c x η v : ℝ} (hc : 0 < c) :
    ‖alphaT c x η v‖ ≤ (1 / |η + v| + 1 / |η - v|) / (2 * c) := by
  have hA : ∀ z : ℂ, ‖z‖ = 1 → ‖z / (2 * c)‖ = 1 / (2 * c) := fun z hz => by
    rw [norm_div, hz, show ((2 : ℂ) * c) = ((2 * c : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  have he := (continuous_eF c η).2 x
  have h1 : ‖-I * eF c η x / (2 * c)‖ = 1 / (2 * c) := hA _ (by rw [norm_mul, norm_neg, Complex.norm_I, he, one_mul])
  have h2 : ‖I * conj (eF c η x) / (2 * c)‖ = 1 / (2 * c) :=
    hA _ (by rw [norm_mul, Complex.norm_I, RCLike.norm_conj, he, one_mul])
  unfold alphaT
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [norm_div _ ((η + 1 * v : ℝ) : ℂ), norm_div _ ((η + -1 * v : ℝ) : ℂ), h1, h2, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, one_mul, show η + -1 * v = η - v by ring]
  ring

/-- **The band sup**: `|α_η(v)| ≤ a/(c(a² − η²))` for `0 ≤ η < a ≤ |v|`. -/
theorem norm_alphaT_le {c x η v a : ℝ} (hc : 0 < c) (hη : 0 ≤ η) (ha : η < a) (hv : a ≤ |v|) :
    ‖alphaT c x η v‖ ≤ a / (c * (a ^ 2 - η ^ 2)) := by
  refine (norm_alphaT_le_pair hc).trans ?_
  have hw : η < |v| := lt_of_lt_of_le ha hv
  have hsum : |η + v| + |η - v| = 2 * |v| := by
    rcases le_or_gt 0 v with h | h
    · rw [abs_of_nonneg h] at hw ⊢
      rw [abs_of_pos (by linarith), abs_of_neg (by linarith)]; ring
    · rw [abs_of_neg h] at hw ⊢
      rw [abs_of_neg (by linarith), abs_of_pos (by linarith)]; ring
  have hprod : |η + v| * |η - v| = v ^ 2 - η ^ 2 := by
    rw [← abs_mul, show (η + v) * (η - v) = -(v ^ 2 - η ^ 2) by ring, abs_neg, abs_of_pos]
    rw [← sq_abs v]; nlinarith
  have hp1 : 0 < |η + v| := by
    rcases le_or_gt 0 v with h | h
    · rw [abs_of_nonneg h] at hw; rw [abs_of_pos (by linarith)]; linarith
    · rw [abs_of_neg h] at hw; rw [abs_of_neg (by linarith)]; linarith
  have hp2 : 0 < |η - v| := by
    rcases le_or_gt 0 v with h | h
    · rw [abs_of_nonneg h] at hw; rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_neg h] at hw; rw [abs_of_pos (by linarith)]; linarith
  have hv2 : 0 < v ^ 2 - η ^ 2 := by rw [← hprod]; positivity
  have ha2 : 0 < a ^ 2 - η ^ 2 := by nlinarith
  have e : (1 / |η + v| + 1 / |η - v|) / (2 * c) = |v| / (c * (v ^ 2 - η ^ 2)) := by
    rw [div_add_div _ _ hp1.ne' hp2.ne', hprod, show 1 * |η - v| + |η + v| * 1 = 2 * |v| by linarith]
    field_simp
  rw [e, div_le_div_iff₀ (mul_pos hc hv2) (mul_pos hc ha2)]
  have hv2' : v ^ 2 = |v| ^ 2 := (sq_abs v).symm
  rw [hv2']
  have ha0 : 0 ≤ a := by linarith
  nlinarith [mul_nonneg hc.le (mul_nonneg (sub_nonneg.2 hv)
    (add_nonneg (mul_nonneg ha0 (abs_nonneg v)) (sq_nonneg η) : (0 : ℝ) ≤ a * |v| + η ^ 2))]

/-- The multiplier bounds of `α_η` on the band with collar `δ`: the sharp sup at `j = 0`, the poles beyond. -/
def nAlpha (c η δ D : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then (1 - δ) / (c * ((1 - δ) ^ 2 - η ^ 2)) else (j.factorial : ℝ) / (c * D ^ (j + 1))

/-- **`α_η` is a band multiplier**: poles at `±η`, at distance `≥ D` from the band when `D ≤ 1 − δ − η`. -/
theorem isBandMult_alphaT {c x η δ Y D : ℝ} (hc : 0 < c) (hη : 0 ≤ η) (hD : 0 < D) (hDle : D ≤ 1 - δ - η) :
    ∃ μ₁ μ₂ μ₃ : ℝ → ℂ, Cvs.L2a.BandTransferBandForm.IsBandMult (alphaT c x η) μ₁ μ₂ μ₃ δ Y (nAlpha c η δ D) := by
  set A₁ : ℂ := -I * eF c η x / (2 * c)
  set A₂ : ℂ := I * conj (eF c η x) / (2 * c)
  have hband : ∀ v ∈ Cvs.L2a.BandTransferBandForm.bandRg δ Y, 1 - δ ≤ |v| := fun v hv => hv.1
  have hd1 : ∀ v ∈ Cvs.L2a.BandTransferBandForm.bandRg δ Y, D ≤ |η + 1 * v| := fun v hv => by
    have := hband v hv
    have h2 := abs_sub_abs_le_abs_sub v (-η)
    rw [abs_neg, abs_of_nonneg hη, sub_neg_eq_add] at h2
    rw [one_mul, add_comm]; linarith
  have hd2 : ∀ v ∈ Cvs.L2a.BandTransferBandForm.bandRg δ Y, D ≤ |η + -1 * v| := fun v hv => by
    have := hband v hv
    have h2 := abs_sub_abs_le_abs_sub v η
    rw [abs_of_nonneg hη] at h2
    rw [show η + -1 * v = -(v - η) by ring, abs_neg]; linarith
  have hp := Cvs.L2a.ScaledBandTransfer.IsBandMult.add (Cvs.L2a.ScaledBandTransfer.isBandMult_pole (A := A₁) hD hd1) (Cvs.L2a.ScaledBandTransfer.isBandMult_pole (A := A₂) hD hd2)
  have hA : ∀ z : ℂ, ‖z‖ = 1 → ‖z / (2 * c)‖ = 1 / (2 * c) := fun z hz => by
    rw [norm_div, hz, show ((2 : ℂ) * c) = ((2 * c : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  have he := (continuous_eF c η).2 x
  have h1 : ‖A₁‖ = 1 / (2 * c) := hA _ (by rw [norm_mul, norm_neg, Complex.norm_I, he, one_mul])
  have h2 : ‖A₂‖ = 1 / (2 * c) := hA _ (by rw [norm_mul, Complex.norm_I, RCLike.norm_conj, he, one_mul])
  have hN : ∀ j : ℕ, 1 ≤ j → ‖A₁‖ * j.factorial * |(1 : ℝ)| ^ j / D ^ (j + 1)
      + ‖A₂‖ * j.factorial * |(-1 : ℝ)| ^ j / D ^ (j + 1) = nAlpha c η δ D j := fun j hj => by
    rw [h1, h2, abs_neg, abs_one, one_pow, nAlpha, ite_eq_right (by omega)]
    field_simp; ring
  refine ⟨_, _, _, { d0 := hp.d0, d1 := hp.d1, d2 := hp.d2, c3 := hp.c3, bd := fun v hv => ?_ }⟩
  obtain ⟨-, b1, b2, b3⟩ := hp.bd v hv
  refine ⟨?_, by rw [← hN 1 le_rfl]; exact b1, by rw [← hN 2 (by norm_num)]; exact b2,
    by rw [← hN 3 (by norm_num)]; exact b3⟩
  rw [nAlpha, ite_eq_left rfl]
  have hηa : η < 1 - δ := by linarith
  exact norm_alphaT_le hc hη hηa (hband v hv)

/-! ### Real parts of the samples -/

/-- The simplified top sample `Σᵢ aᵢSᵢ[μ_si]` at the cut `x`, height `y`. -/
def Asi {ι : Type} [Fintype ι] (c : ℝ) (χ : ι → ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (x y : ℝ) : ℂ :=
  ∑ i, (a i : ℂ) * Cvs.L2a.BandTransferBandForm.smp (Cvs.L2a.CutKernelSimplified.muSi c y x) c (χ i) (g i) x

/-- The correction sample `Σᵢ aᵢSᵢ[μ_co]`. -/
def Aco {ι : Type} [Fintype ι] (c : ℝ) (χ : ι → ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (x y : ℝ) : ℂ :=
  ∑ i, (a i : ℂ) * Cvs.L2a.BandTransferBandForm.smp (muCo c y x) c (χ i) (g i) x

theorem cutSample_eq_add {ι : Type} [Fintype ι] (c : ℝ) (χ : ι → ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (x y : ℝ) :
    Cvs.L2a.CutKernels.cutSample c χ g a x y = Asi c χ g a x y + Aco c χ g a x y := by
  unfold Cvs.L2a.CutKernels.cutSample Asi Aco
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold Cvs.L2a.BandTransferBandForm.smp muCo
  ring

/-- `Re Σᵢ aᵢSᵢ[μ_si] = Σᵢ aᵢSᵢ[α_η(·/c)]`. -/
theorem re_Asi_eq {ι : Type} [Fintype ι] {c : ℝ} (hc : c ≠ 0) (χ : ι → ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ)
    (x η : ℝ) :
    (((Asi c χ g a x η).re : ℝ) : ℂ) = ∑ i, (a i : ℂ) * Cvs.L2a.BandTransferBandForm.smp (fun ξ => alphaT c x η (ξ / c)) c (χ i) (g i) x := by
  unfold Asi
  rw [Complex.re_sum, ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_ofReal_mul, ofReal_mul, Cvs.L2a.QIdentityCutPoint.re_smp]
  congr 2
  funext ξ
  rw [alphaT_div_eq hc]

/-! ### LBT-h at the top cut, pointwise in the height -/

/-- The band `{|ξ| ∈ [c, cY]}`. -/
def bandB (c Y : ℝ) : Set ℝ := {ξ | |ξ| ∈ Icc c (c * Y)}

theorem measurableSet_bandB (c Y : ℝ) : MeasurableSet (bandB c Y) :=
  measurableSet_Icc.preimage continuous_abs.measurable

theorem volume_bandB_le {c Y : ℝ} (hc : 0 ≤ c) (hY : 1 ≤ Y) :
    (volume (bandB c Y)).toReal ≤ 2 * (c * Y - c) := by
  have hsub : bandB c Y ⊆ Icc (-(c * Y)) (-c) ∪ Icc c (c * Y) := fun ξ hξ => by
    obtain ⟨h1, h2⟩ := hξ
    rcases le_or_gt 0 ξ with h | h
    · rw [abs_of_nonneg h] at h1 h2; exact Or.inr ⟨h1, h2⟩
    · rw [abs_of_neg h] at h1 h2; exact Or.inl ⟨by linarith, by linarith⟩
  have hv : volume (bandB c Y) ≤ ENNReal.ofReal (2 * (c * Y - c)) := by
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans (le_of_eq ?_))
    rw [Real.volume_Icc, Real.volume_Icc, ← ENNReal.ofReal_add (by nlinarith) (by nlinarith)]
    congr 1; ring
  exact ENNReal.toReal_le_of_le_ofReal (by nlinarith) hv

theorem measurable_alphaT (c x η : ℝ) : Measurable (alphaT c x η) := by
  unfold alphaT; fun_prop

/-- `|α_η(ξ/c)| ≤ 1/(c(1 − η²))` on the band. -/
theorem norm_alphaT_band_le {c x η Y ξ : ℝ} (hc : 0 < c) (hη : 0 ≤ η) (hη1 : η < 1) (hξ : ξ ∈ bandB c Y) :
    ‖alphaT c x η (ξ / c)‖ ≤ 1 / (c * (1 - η ^ 2)) := by
  have h1 : 1 ≤ |ξ / c| := by rw [abs_div, abs_of_pos hc, le_div_iff₀ hc, one_mul]; exact hξ.1
  have := norm_alphaT_le (x := x) hc hη hη1 h1
  simpa using this

theorem integrableOn_alphaT_band {c x η Y : ℝ} (hc : 0 < c) (hη : 0 ≤ η) (hη1 : η < 1) :
    IntegrableOn (fun ξ => ‖alphaT c x η (ξ / c)‖ ^ 2) (bandB c Y) := by
  have hfin : volume (bandB c Y) ≠ ⊤ := by
    have hsub : bandB c Y ⊆ Icc (-(c * Y)) (c * Y) := fun ξ hξ => abs_le.1 hξ.2
    exact ne_top_of_le_ne_top measure_Icc_lt_top.ne (measure_mono hsub)
  refine Measure.integrableOn_of_bounded (M := (1 / (c * (1 - η ^ 2))) ^ 2) hfin ?_ ?_
  · exact (((measurable_alphaT c x η).comp (measurable_id.div_const c)).norm.pow_const 2).aestronglyMeasurable
  · refine (ae_restrict_iff' (measurableSet_bandB c Y)).2 (ae_of_all _ fun ξ hξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_alphaT_band_le hc hη hη1 hξ) 2

/-- **(B′) main term**: `(2π)⁻¹∫_B |α_η(ξ/c)|² ≤ ΔY/(πc(1 − η²)²)`. -/
theorem bprime_main {c x η Y : ℝ} (hc : 0 < c) (hη : 0 ≤ η) (hη1 : η < 1) (hY : 1 ≤ Y) :
    (2 * π)⁻¹ * ∫ ξ in bandB c Y, ‖alphaT c x η (ξ / c)‖ ^ 2 ≤ (Y - 1) / (π * c * (1 - η ^ 2) ^ 2) := by
  have hy2 : 0 < 1 - η ^ 2 := by nlinarith
  set K := (1 / (c * (1 - η ^ 2))) ^ 2 with hK
  have hfin : volume (bandB c Y) ≠ ⊤ := by
    have hsub : bandB c Y ⊆ Icc (-(c * Y)) (c * Y) := fun ξ hξ => abs_le.1 hξ.2
    exact ne_top_of_le_ne_top measure_Icc_lt_top.ne (measure_mono hsub)
  have h1 : ∫ ξ in bandB c Y, ‖alphaT c x η (ξ / c)‖ ^ 2 ≤ ∫ ξ in bandB c Y, K :=
    setIntegral_mono_on (integrableOn_alphaT_band hc hη hη1) (integrableOn_const hfin)
      (measurableSet_bandB c Y) fun ξ hξ => pow_le_pow_left₀ (norm_nonneg _) (norm_alphaT_band_le hc hη hη1 hξ) 2
  rw [setIntegral_const, smul_eq_mul] at h1
  have h2 := volume_bandB_le hc.le hY
  have hK0 : 0 ≤ K := sq_nonneg _
  have h3 : ∫ ξ in bandB c Y, ‖alphaT c x η (ξ / c)‖ ^ 2 ≤ 2 * (c * Y - c) * K :=
    h1.trans (mul_le_mul_of_nonneg_right h2 hK0)
  have hπ := pi_pos
  calc (2 * π)⁻¹ * ∫ ξ in bandB c Y, ‖alphaT c x η (ξ / c)‖ ^ 2 ≤ (2 * π)⁻¹ * (2 * (c * Y - c) * K) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (Y - 1) / (π * c * (1 - η ^ 2) ^ 2) := by rw [hK]; field_simp

/-- The P-charged coefficient `T = 2τ̂_r√((ΔY + 2κ_Sδ)G/π) + τ̂_r²G`, `G = 6J/(c(x₀² − 1))`. -/
def tC (c x₀ d δ r J : ℝ) : ℝ :=
  2 * Cvs.L2a.BandTransferBandForm.tauHat c x₀ d δ (fun j => (j.factorial : ℝ) / r ^ j)
      * √((Ymax x₀ - 1 + 2 * (181 / 462) * δ) * (6 * J / (c * (x₀ ^ 2 - 1))) / π)
    + Cvs.L2a.BandTransferBandForm.tauHat c x₀ d δ (fun j => (j.factorial : ℝ) / r ^ j) ^ 2 * (6 * J / (c * (x₀ ^ 2 - 1)))

/-- The window coefficient `a(η) = ΔY/(πc(1 − η²)²) + (2κ_Sδ/(πc))((1 − δ)/((1 − δ)² − η²))²`. -/
def aW (c x₀ δ η : ℝ) : ℝ :=
  (Ymax x₀ - 1) / (π * c * (1 - η ^ 2) ^ 2) + 2 * (181 / 462) * δ / (π * c) * ((1 - δ) / ((1 - δ) ^ 2 - η ^ 2)) ^ 2

/-- **LBT-h at the top cut, pointwise in `η`**: `(Re Σaᵢ Sᵢ[μ_si])² ≤ a(η)·W + T/(c(1 − δ − η)²)·P`,
for `0 ≤ η`, `0 < r ≤ 1 − δ − η`. -/
theorem local_pt {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    {X d δ η r : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχi : Function.Injective χ)
    (hX : 2 ≤ X) (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2)
    (hd : 0 < d) (hXd : 1 < X - d) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : 0 ≤ η) (hr : 0 < r)
    (hrD : r ≤ 1 - δ - η) :
    (Asi c χ g a X η).re ^ 2
      ≤ aW c X δ η * (∫ x in (X - d)..(X + d), (∑ i, a i * psi c (g i) x) ^ 2)
        + tC c X d δ r (Fintype.card ι) / (c * (1 - δ - η) ^ 2) * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hX1 : 1 < X := by linarith
  have hY := Cvs.L2a.BandTransferBandForm.one_le_Ymax hX1
  set D := 1 - δ - η with hDdef
  have hD : 0 < D := lt_of_lt_of_le hr hrD
  have hη1 : η < 1 := by linarith
  have hδ' : 0 < 1 - δ := by linarith
  obtain ⟨μ₁, μ₂, μ₃, hμ⟩ := isBandMult_alphaT (x := X) (Y := Ymax X) hc0 hη hD le_rfl
  have hNb : ∀ j ≤ 3, nAlpha c η δ D j ≤ 1 / (c * D) * ((j.factorial : ℝ) / r ^ j) := by
    intro j _
    rcases Nat.eq_zero_or_pos j with h0 | hj
    · subst h0
      rw [nAlpha, ite_eq_left rfl, Nat.factorial_zero, pow_zero, Nat.cast_one, div_one, mul_one]
      have hq : D * (1 - δ) ≤ (1 - δ) ^ 2 - η ^ 2 := by
        have : (1 - δ) ^ 2 - η ^ 2 = D * (1 - δ + η) := by rw [hDdef]; ring
        rw [this]; exact mul_le_mul_of_nonneg_left (by linarith) hD.le
      have hq0 : 0 < (1 - δ) ^ 2 - η ^ 2 := lt_of_lt_of_le (mul_pos hD hδ') hq
      rw [div_le_div_iff₀ (mul_pos hc0 hq0) (by positivity)]
      nlinarith
    · rw [nAlpha, ite_eq_right (by omega)]
      have hrj : r ^ j ≤ D ^ j := pow_le_pow_left₀ hr.le hrD j
      have hf : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
      rw [pow_succ, show (j.factorial : ℝ) / (c * (D ^ j * D)) = 1 / (c * D) * ((j.factorial : ℝ) / D ^ j) by
        field_simp]
      gcongr
  have hgen := Cvs.L2a.ScaledBandTransfer.lbt_band_scaled a hg hg₁ hg₂c hang hc hχ0 hχc hχi hX hM ⟨by linarith, le_rfl⟩ hd hXd hδ hδ1
    hμ hNb (measurableSet_bandB c (Ymax X)) (fun ξ h => h) (integrableOn_alphaT_band hc0 hη hη1)
  rw [← re_Asi_eq hc0.ne', Complex.norm_real, Real.norm_eq_abs, sq_abs] at hgen
  have hmain := bprime_main (x := X) hc0 hη hη1 hY
  set W := ∫ x in (X - d)..(X + d), (∑ i, a i * psi c (g i) x) ^ 2 with hW
  have hW0 : 0 ≤ W := intervalIntegral.integral_nonneg (by linarith) fun x _ => sq_nonneg _
  refine hgen.trans (le_of_le_of_eq (add_le_add (mul_le_mul_of_nonneg_right
    (add_le_add hmain le_rfl) hW0) le_rfl) ?_)
  rw [nAlpha, ite_eq_left rfl]
  unfold aW tC
  have hq : 0 < (1 - δ) ^ 2 - η ^ 2 := by nlinarith
  field_simp

/-! ### Cauchy–Schwarz on `(1, 2)` and the corner `C_m` -/

/-- **Two-term Cauchy–Schwarz**: `|f| ≤ |Φ|(F₁ + F₂)`, `F_k² ≤ g_k` give `|∫f| ≤ ‖Φ‖₂(√∫g₁ + √∫g₂)`. -/
theorem abs_integral_le_cs {Φ f F₁ F₂ g₁ g₂ : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hΦ : MemLp Φ 2 (volume.restrict s)) (hF₁ : AEStronglyMeasurable F₁ (volume.restrict s))
    (hF₂ : AEStronglyMeasurable F₂ (volume.restrict s)) (hg₁ : IntegrableOn g₁ s) (hg₂ : IntegrableOn g₂ s)
    (hF₁0 : ∀ t, 0 ≤ F₁ t) (hF₂0 : ∀ t, 0 ≤ F₂ t)
    (h₁ : ∀ t ∈ s, F₁ t ^ 2 ≤ g₁ t) (h₂ : ∀ t ∈ s, F₂ t ^ 2 ≤ g₂ t)
    (hf : ∀ t ∈ s, |f t| ≤ |Φ t| * (F₁ t + F₂ t)) :
    |∫ t in s, f t| ≤ √(∫ t in s, Φ t ^ 2) * (√(∫ t in s, g₁ t) + √(∫ t in s, g₂ t)) := by
  have hm : ∀ {F g : ℝ → ℝ}, AEStronglyMeasurable F (volume.restrict s) → IntegrableOn g s →
      (∀ t ∈ s, F t ^ 2 ≤ g t) → MemLp F 2 (volume.restrict s) ∧ ∫ t in s, F t ^ 2 ≤ ∫ t in s, g t :=
    fun {F g} hF hg h => by
      have hle : ∀ᵐ t ∂(volume.restrict s), ‖F t ^ 2‖ ≤ g t :=
        (ae_restrict_iff' hs).2 (ae_of_all _ fun t ht => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact h t ht)
      have hi : Integrable (fun t => F t ^ 2) (volume.restrict s) := hg.mono' (hF.pow 2) hle
      refine ⟨(memLp_two_iff_integrable_sq hF).2 hi, integral_mono_ae hi hg ?_⟩
      exact (ae_restrict_iff' hs).2 (ae_of_all _ fun t ht => h t ht)
  obtain ⟨m₁, i₁⟩ := hm hF₁ hg₁ h₁
  obtain ⟨m₂, i₂⟩ := hm hF₂ hg₂ h₂
  have hΦa : MemLp (fun t => |Φ t|) 2 (volume.restrict s) := hΦ.abs
  have j₁ : Integrable (fun t => F₁ t * |Φ t|) (volume.restrict s) := m₁.integrable_mul hΦa
  have j₂ : Integrable (fun t => F₂ t * |Φ t|) (volume.restrict s) := m₂.integrable_mul hΦa
  have hbd : ‖∫ t in s, f t‖ ≤ ∫ t in s, (F₁ t * |Φ t| + F₂ t * |Φ t|) :=
    norm_integral_le_of_norm_le (j₁.add j₂) ((ae_restrict_iff' hs).2 (ae_of_all _ fun t ht => by
      rw [Real.norm_eq_abs]; have := hf t ht; nlinarith [abs_nonneg (Φ t)]))
  rw [integral_add j₁ j₂, Real.norm_eq_abs] at hbd
  have c₁ := Cvs.L2a.FarFarBound.integral_mul_abs_le hF₁0 m₁ hΦ
  have c₂ := Cvs.L2a.FarFarBound.integral_mul_abs_le hF₂0 m₂ hΦ
  have s₁ := Real.sqrt_le_sqrt i₁
  have s₂ := Real.sqrt_le_sqrt i₂
  have hp := Real.sqrt_nonneg (∫ t in s, Φ t ^ 2)
  nlinarith [mul_le_mul_of_nonneg_right s₁ hp, mul_le_mul_of_nonneg_right s₂ hp]

theorem measurable_Asi {ι : Type} [Fintype ι] (c : ℝ) (χ : ι → ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (x : ℝ) :
    Measurable fun y => Asi c χ g a x y := by
  unfold Asi Cvs.L2a.BandTransferBandForm.smp Cvs.L2a.CutKernelSimplified.muSi eF
  fun_prop

/-- The span `Φ` is in `L²(1, 2)`. -/
theorem memLp_span_Ioo {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) {s : Set ℝ} (hs : s ⊆ Ioi 1) :
    MemLp (fun x => ∑ i, a i * psi c (g i) x) 2 (volume.restrict s) := by
  have h : MemLp (fun x => ∑ i, a i * psi c (g i) x) 2 (volume.restrict (Ioi 1)) := by
    have := memLp_finsetSum' Finset.univ fun i _ =>
      (Cvs.Prolate.RungExactOrthogonality.memLp_psi (hg i) (hg₁ i) (hg₂c i) (hang i) hc).const_mul (a i)
    refine this.ae_eq (ae_of_all _ fun x => ?_)
    simp [Finset.sum_apply]
  exact h.mono_measure (Measure.restrict_mono hs le_rfl)

/-- **The corner through Cauchy–Schwarz**: `(w|Re 𝒜_si|)² ≤ g` and `w|𝒜_co| ≤ B₂` on `(1, 2)` give
`|C_m| ≤ (2κ/m)‖Φ‖_{L²(1,2)}(√∫g + B₂)`. -/
theorem abs_cTop_le {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (M m : ℕ) (hm : 0 < m) {G : ℝ → ℝ} {B₂ : ℝ} (hG : IntegrableOn G (Ioo 1 2)) (hB₂ : 0 ≤ B₂)
    (h₁ : ∀ t ∈ Ioo (1 : ℝ) 2, ((1 - wF t) * |(Asi c χ g a M (t / m)).re|) ^ 2 ≤ G t)
    (h₂ : ∀ t ∈ Ioo (1 : ℝ) 2, (1 - wF t) * ‖Aco c χ g a M (t / m)‖ ≤ B₂) :
    |Cvs.L2a.CutKernels.cTop c χ g a M m|
      ≤ 2 * √(2 * c / π) / m * √(∫ t in Ioo 1 2, (∑ i, a i * psi c (g i) t) ^ 2)
        * (√(∫ t in Ioo 1 2, G t) + B₂) := by
  have hw0 : ∀ t, 0 ≤ 1 - wF t := fun t => by linarith [(Cvs.L2a.FarFarBound.wF_bounds t).2.1]
  have hκ : 0 ≤ 2 * √(2 * c / π) / m := by positivity
  have hcs := abs_integral_le_cs (Φ := fun t => ∑ i, a i * psi c (g i) t)
    (f := fun t => (1 - wF t) * (∑ i, a i * psi c (g i) t) * (Cvs.L2a.CutKernels.cutSample c χ g a M (t / m)).re)
    (F₁ := fun t => (1 - wF t) * |(Asi c χ g a M (t / m)).re|) (F₂ := fun _ => B₂) (g₂ := fun _ => B₂ ^ 2)
    measurableSet_Ioo (memLp_span_Ioo a hg hg₁ hg₂c hang hc fun t ht => ht.1)
    (((continuous_const.sub Cvs.L2a.FarIntegrationByParts.continuous_wF.1).measurable.mul
      ((Complex.measurable_re.comp ((measurable_Asi c χ g a M).comp
        (measurable_id.div_const _))).abs)).aestronglyMeasurable)
    aestronglyMeasurable_const hG (integrableOn_const (by simp)) (fun t => mul_nonneg (hw0 t) (abs_nonneg _))
    (fun _ => hB₂) h₁ (fun _ _ => le_rfl) (fun t ht => by
      rw [cutSample_eq_add, Complex.add_re, abs_mul, abs_mul, abs_of_nonneg (hw0 t)]
      have h1 : |(Asi c χ g a M (t / m)).re + (Aco c χ g a M (t / m)).re|
          ≤ |(Asi c χ g a M (t / m)).re| + ‖Aco c χ g a M (t / m)‖ :=
        (abs_add_le _ _).trans (add_le_add le_rfl (Complex.abs_re_le_norm _))
      have h2 := h₂ t ht
      have := abs_nonneg (∑ i, a i * psi c (g i) t)
      nlinarith [mul_le_mul_of_nonneg_left h1 (hw0 t), mul_nonneg this (hw0 t)])
  have hB : √(∫ _ in Ioo (1 : ℝ) 2, B₂ ^ 2) = B₂ := by
    rw [setIntegral_const, Real.volume_real_Ioo, smul_eq_mul]; norm_num; exact Real.sqrt_sq hB₂
  rw [hB] at hcs
  unfold Cvs.L2a.CutKernels.cTop
  rw [abs_mul, abs_neg, abs_of_nonneg hκ, mul_assoc]
  exact mul_le_mul_of_nonneg_left hcs hκ

/-! ### T0 at the top cut -/

/-- `‖Σaᵢ Sᵢ[μ_si]‖ ≤ (c(1 − y²))⁻¹√(6J/(X² − 1))√P`. -/
theorem norm_Asi_le {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) {X y J : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχi : Function.Injective χ)
    (hX : 2 ≤ X) (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2) (hJ : (Fintype.card ι : ℝ) ≤ J)
    (hy0 : 0 < y) (hy1 : y < 1) :
    ‖Asi c χ g a X y‖ ≤ 1 / (c * (1 - y ^ 2)) * √(6 * J / (X ^ 2 - 1))
      * √(∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2) := by
  have hc0 : 0 < c := by linarith
  have hy2 : 0 < 1 - y ^ 2 := by nlinarith
  have h := t0_pair a hg hg₁ hg₂c hang hc hχ0 hχc hX hM ⟨by linarith, le_rfl⟩ (B := 1 / (c * (1 - y ^ 2)))
    (μ := Cvs.L2a.CutKernelSimplified.muSi c y X) fun ξ hξ => by
      have := norm_muSi_pair_le (x := X) hc0 hy0 hy1 hξ.1
      rw [show 2 * (1 / (c * (1 - y ^ 2))) = 2 / (c * (1 - y ^ 2)) by ring]; exact this
  have hX1 : 0 < X ^ 2 - 1 := by nlinarith
  have hs1 : √(6 * (Fintype.card ι : ℝ) / (X ^ 2 - 1)) ≤ √(6 * J / (X ^ 2 - 1)) := by gcongr
  have hs2 := Real.sqrt_le_sqrt (spanMass_le a hg hg₁ hg₂c hang hc0 hχi (by linarith : (1 : ℝ) ≤ X))
  refine h.trans ?_
  gcongr

/-- `‖Σaᵢ Sᵢ[μ_co]‖ ≤ e(X, y)/(c²(1 − y²))·√(6J/(X² − 1))√P`. -/
theorem norm_Aco_le {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) {X y J : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχi : Function.Injective χ)
    (hX : 2 ≤ X) (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2) (hJ : (Fintype.card ι : ℝ) ≤ J)
    (hy0 : 0 < y) (hy1 : y < 1) :
    ‖Aco c χ g a X y‖ ≤ eTop X y / (c ^ 2 * (1 - y ^ 2)) * √(6 * J / (X ^ 2 - 1))
      * √(∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2) := by
  have hc0 : 0 < c := by linarith
  have h := t0_pair a hg hg₁ hg₂c hang hc hχ0 hχc hX hM ⟨by linarith, le_rfl⟩
    (B := eTop X y / (c ^ 2 * (1 - y ^ 2))) (μ := muCo c y X) fun ξ hξ =>
      norm_muCo_pair_le hc0 (by linarith) hy0 hy1 hξ.1
  have hX1 : 0 < X ^ 2 - 1 := by nlinarith
  have hs1 : √(6 * (Fintype.card ι : ℝ) / (X ^ 2 - 1)) ≤ √(6 * J / (X ^ 2 - 1)) := by gcongr
  have hs2 := Real.sqrt_le_sqrt (spanMass_le a hg hg₁ hg₂c hang hc0 hχi (by linarith : (1 : ℝ) ≤ X))
  have he := eTop_nonneg (by linarith : 1 < X) hy0.le hy1
  have hy2 : 0 < 1 - y ^ 2 := by nlinarith
  refine h.trans ?_
  gcongr

/-- The correction cap `(4π²/3)(6X/(X² − 1) + 1/(2X))`. -/
def ecap (X : ℝ) : ℝ := 4 * π ^ 2 / 3 * (6 * X / (X ^ 2 - 1) + 1 / (2 * X))

/-- **The weighted correction is bounded**: `(1 − wF t)·e(X, t/m)/(1 − (t/m)²) ≤ ecap X` on `(1, 2)`, `m ≥ 2`. -/
theorem w_eTop_le {X t : ℝ} {m : ℕ} (hX : 1 < X) (hm : 2 ≤ m) (ht : t ∈ Ioo (1 : ℝ) 2) :
    (1 - wF t) * (eTop X (t / m) / (1 - (t / m) ^ 2)) ≤ ecap X := by
  obtain ⟨ht1, ht2⟩ := ht
  have hp : 0 < X ^ 2 - 1 := by nlinarith
  have hpP : pP X = X ^ 2 - 1 := rfl
  have hX0 : 0 < X := by linarith
  have hw0 : 0 ≤ 1 - wF t := by linarith [(Cvs.L2a.FarFarBound.wF_bounds t).2.1]
  have hw1 : 1 - wF t ≤ 1 := by linarith [(Cvs.L2a.FarFarBound.wF_bounds t).1]
  have hπ : 9 ≤ π ^ 2 := by nlinarith [pi_gt_three]
  set E := 6 * X / (X ^ 2 - 1) + 1 / (2 * X) with hE
  have hE0 : 0 ≤ E := by positivity
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  rcases Nat.lt_or_ge m 3 with h3 | h3
  · -- `m = 2`: the weight `π²(2 − t)²` absorbs both poles
    have hm2 : m = 2 := by omega
    subst hm2
    set u := 2 - t with hu
    have hu0 : 0 < u := by linarith
    have hu1 : u < 1 := by linarith
    have hy : (t / (2 : ℕ)) = 1 - u / 2 := by push_cast; rw [hu]; ring
    rw [hy]
    have h1y : 1 - (1 - u / 2) = u / 2 := by ring
    have hq : 3 * u / 4 ≤ 1 - (1 - u / 2) ^ 2 := by nlinarith
    have hq0 : 0 < 1 - (1 - u / 2) ^ 2 := by nlinarith
    have heT : eTop X (1 - u / 2) ≤ 4 * X / ((X ^ 2 - 1) * u) + (2 * X / (X ^ 2 - 1) + 1 / (2 * X)) := by
      unfold eTop
      rw [h1y, hpP]
      have : 2 * X * (1 - u / 2) / ((X ^ 2 - 1) * (u / 2)) ≤ 4 * X / ((X ^ 2 - 1) * u) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_pos hX0 hp, mul_pos (mul_pos hX0 hp) hu0, mul_pos (mul_pos (mul_pos hX0 hp) hu0) hu0]
      linarith
    have hwu : 1 - wF t ≤ π ^ 2 * u ^ 2 := Cvs.L2a.RampTopQuadratic.one_sub_wF_le t
    have heT0 : 0 ≤ eTop X (1 - u / 2) := eTop_nonneg hX (by linarith) (by linarith)
    calc (1 - wF t) * (eTop X (1 - u / 2) / (1 - (1 - u / 2) ^ 2))
        ≤ π ^ 2 * u ^ 2 * (eTop X (1 - u / 2) / (3 * u / 4)) := by
          gcongr
      _ = 4 * π ^ 2 / 3 * (u * eTop X (1 - u / 2)) := by field_simp
      _ ≤ 4 * π ^ 2 / 3 * (u * (4 * X / ((X ^ 2 - 1) * u) + (2 * X / (X ^ 2 - 1) + 1 / (2 * X)))) := by
          gcongr
      _ = 4 * π ^ 2 / 3 * (4 * X / (X ^ 2 - 1) + u * (2 * X / (X ^ 2 - 1) + 1 / (2 * X))) := by
          field_simp
      _ ≤ 4 * π ^ 2 / 3 * (4 * X / (X ^ 2 - 1) + 1 * (2 * X / (X ^ 2 - 1) + 1 / (2 * X))) := by
          gcongr
      _ = ecap X := by unfold ecap; ring
  · -- `m ≥ 3`: `y ≤ 2/3`
    have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast h3
    have hy0 : 0 < t / m := by positivity
    have hy : t / m ≤ 2 / 3 := by rw [div_le_iff₀ hm0]; nlinarith
    have h1y : 1 / 3 ≤ 1 - t / m := by linarith
    have hq : 5 / 9 ≤ 1 - (t / m) ^ 2 := by nlinarith
    have heT : eTop X (t / m) ≤ E := by
      unfold eTop
      rw [hpP, hE]
      have : 2 * X * (t / m) / ((X ^ 2 - 1) * (1 - t / m)) ≤ 4 * X / (X ^ 2 - 1) := by
        rw [div_le_div_iff₀ (by nlinarith) hp]
        nlinarith [mul_pos hX0 hp]
      have e6 : 6 * X / (X ^ 2 - 1) = 4 * X / (X ^ 2 - 1) + 2 * X / (X ^ 2 - 1) := by ring
      linarith
    have heT0 : 0 ≤ eTop X (t / m) := eTop_nonneg hX hy0.le (by linarith)
    calc (1 - wF t) * (eTop X (t / m) / (1 - (t / m) ^ 2)) ≤ 1 * (E / (5 / 9)) := by
          gcongr
      _ ≤ ecap X := by
          unfold ecap; rw [← hE]
          nlinarith

/-! ### The global bound per corner -/

theorem setIntegral_Ioo_eq (f : ℝ → ℝ) : ∫ t in Ioo (1 : ℝ) 2, f t = ∫ t in (1 : ℝ)..2, f t := by
  rw [intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]

theorem integrableOn_wsq {m : ℕ} (hm : 2 ≤ m) :
    IntegrableOn (fun t => (1 - wF t) ^ 2 / (1 - t ^ 2 / (m : ℝ) ^ 2) ^ 2) (Ioo 1 2) := by
  have hi : IntegrableOn Cvs.L2a.CornerSuprema.theta2Int (Ioo 1 2) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).1 Cvs.L2a.CornerSuprema.intervalIntegrable_theta2Int
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  refine hi.mono' (((Cvs.L2a.CornerSuprema.continuous_one_sub_wF.pow 2).measurable.div
    (by fun_prop)).aestronglyMeasurable) ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun t ht => ?_))
  obtain ⟨ht1, ht2⟩ := ht
  unfold Cvs.L2a.CornerSuprema.theta2Int
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h4 : 0 < 1 - t ^ 2 / 2 ^ 2 := by
    rw [sub_pos, div_lt_one (by norm_num)]; nlinarith
  have hle : 1 - t ^ 2 / 2 ^ 2 ≤ 1 - t ^ 2 / (m : ℝ) ^ 2 := by
    have : t ^ 2 / (m : ℝ) ^ 2 ≤ t ^ 2 / 2 ^ 2 :=
      div_le_div_of_nonneg_left (sq_nonneg t) (by norm_num) (pow_le_pow_left₀ (by norm_num) hm2 2)
    linarith
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (pow_le_pow_left₀ h4.le hle 2)

theorem Theta_sq (m : ℝ) :
    Cvs.L2a.CornerSuprema.Theta m ^ 2 = ∫ t in Ioo (1 : ℝ) 2, (1 - wF t) ^ 2 / (1 - t ^ 2 / m ^ 2) ^ 2 := by
  unfold Cvs.L2a.CornerSuprema.Theta
  rw [Real.sq_sqrt, setIntegral_Ioo_eq]
  exact intervalIntegral.integral_nonneg (by norm_num) fun t _ => by positivity

/-- `∫_{(1,2)} Φ² ≤ ∫_{(1,∞)} Φ²`. -/
theorem H_le_P {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) {s : Set ℝ} (hs : s ⊆ Ioi 1) :
    ∫ t in s, (∑ i, a i * psi c (g i) t) ^ 2 ≤ ∫ t in Ioi 1, (∑ i, a i * psi c (g i) t) ^ 2 := by
  have hm := memLp_span_Ioo a hg hg₁ hg₂c hang hc (subset_refl (Ioi (1 : ℝ)))
  exact setIntegral_mono_set ((memLp_two_iff_integrable_sq hm.aestronglyMeasurable).1 hm) (ae_of_all _ fun t => sq_nonneg _)
    (ae_of_all _ hs)

/-- **The correction on `(1, 2)`**: `(1 − wF t)|Σaᵢ Sᵢ[μ_co](t/m)| ≤ ecap(M)/c²·√(6J/(M² − 1))√P`. -/
theorem w_Aco_le {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) {J : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχi : Function.Injective χ)
    {M : ℕ} (hM3 : 3 ≤ M) (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..M, psi c (g i) t ^ 2) (hJ : (Fintype.card ι : ℝ) ≤ J)
    {m : ℕ} (hm : 2 ≤ m) :
    ∀ t ∈ Ioo (1 : ℝ) 2, (1 - wF t) * ‖Aco c χ g a M (t / m)‖
      ≤ ecap M / c ^ 2 * √(6 * J / ((M : ℝ) ^ 2 - 1)) * √(∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2) := by
  intro t ht
  have hc0 : 0 < c := by linarith
  have hM3r : (3 : ℝ) ≤ M := by exact_mod_cast hM3
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hy0 : 0 < t / m := by have := ht.1; positivity
  have hy1 : t / m < 1 := by rw [div_lt_one hm0]; linarith [ht.2]
  have hA := norm_Aco_le a hg hg₁ hg₂c hang hc hχ0 hχc hχi (by linarith : (2 : ℝ) ≤ M) hM hJ hy0 hy1
  have hcap := w_eTop_le (X := M) (by linarith) hm ht
  have hy2 : 0 < 1 - (t / m) ^ 2 := by nlinarith
  have hw0 : 0 ≤ 1 - wF t := by linarith [(Cvs.L2a.FarFarBound.wF_bounds t).2.1]
  have hP0 : 0 ≤ √(∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2) := Real.sqrt_nonneg _
  have hG0 : 0 ≤ √(6 * J / ((M : ℝ) ^ 2 - 1)) := Real.sqrt_nonneg _
  calc (1 - wF t) * ‖Aco c χ g a M (t / m)‖
      ≤ (1 - wF t) * (eTop M (t / m) / (c ^ 2 * (1 - (t / m) ^ 2)) * √(6 * J / ((M : ℝ) ^ 2 - 1))
        * √(∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2)) := mul_le_mul_of_nonneg_left hA hw0
    _ = (1 - wF t) * (eTop M (t / m) / (1 - (t / m) ^ 2)) * (√(6 * J / ((M : ℝ) ^ 2 - 1))
        * √(∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2) / c ^ 2) := by field_simp
    _ ≤ ecap M * (√(6 * J / ((M : ℝ) ^ 2 - 1)) * √(∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2) / c ^ 2) :=
        mul_le_mul_of_nonneg_right hcap (by positivity)
    _ = _ := by ring

/-- **`r₁^glob` with the exact kernel**: `|C_m| ≤ (2κ/m)√(6J/(M² − 1))(Θ_m/c + ecap(M)/c²)·P`. -/
theorem cTop_glob_le {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) {J : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχi : Function.Injective χ)
    {M : ℕ} (hM3 : 3 ≤ M) (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..M, psi c (g i) t ^ 2) (hJ : (Fintype.card ι : ℝ) ≤ J)
    {m : ℕ} (hm : 2 ≤ m) :
    |Cvs.L2a.CutKernels.cTop c χ g a M m| ≤ 2 * √(2 * c / π) / m * √(6 * J / ((M : ℝ) ^ 2 - 1))
      * (Cvs.L2a.CornerSuprema.Theta m / c + ecap M / c ^ 2) * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hM3r : (3 : ℝ) ≤ M := by exact_mod_cast hM3
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  set P := ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 with hP
  set Gc := 6 * J / ((M : ℝ) ^ 2 - 1) with hGc
  have hP0 : 0 ≤ P := setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have hJ0 : 0 ≤ J := le_trans (Nat.cast_nonneg _) hJ
  have hGc0 : 0 ≤ Gc := by rw [hGc]; apply div_nonneg (by positivity); nlinarith
  have hy : ∀ t ∈ Ioo (1 : ℝ) 2, 0 < t / m ∧ t / m < 1 := fun t ht => ⟨by have := ht.1; positivity, by
    rw [div_lt_one hm0]; have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith [ht.2]⟩
  have hw0 : ∀ t, 0 ≤ 1 - wF t := fun t => by linarith [(Cvs.L2a.FarFarBound.wF_bounds t).2.1]
  have hcap0 : 0 ≤ ecap M := by unfold ecap; have : 0 < (M : ℝ) ^ 2 - 1 := by nlinarith
                                positivity
  have hB := abs_cTop_le a hg hg₁ hg₂c hang hc0 M m (by omega)
    (G := fun t => (1 - wF t) ^ 2 / (1 - t ^ 2 / (m : ℝ) ^ 2) ^ 2 * (Gc * P / c ^ 2))
    (B₂ := ecap M / c ^ 2 * √Gc * √P) ((integrableOn_wsq hm).mul_const _) (by positivity)
    (fun t ht => by
      obtain ⟨hy0, hy1⟩ := hy t ht
      have hA := norm_Asi_le a hg hg₁ hg₂c hang hc hχ0 hχc hχi (by linarith : (2 : ℝ) ≤ M) hM hJ hy0 hy1
      have hy2 : 0 < 1 - (t / m) ^ 2 := by nlinarith
      have h1 : (1 - wF t) * |(Asi c χ g a M (t / m)).re|
          ≤ (1 - wF t) * (1 / (c * (1 - (t / m) ^ 2)) * √Gc * √P) :=
        mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans hA) (hw0 t)
      have h2 := pow_le_pow_left₀ (mul_nonneg (hw0 t) (abs_nonneg _)) h1 2
      refine h2.trans (le_of_eq ?_)
      rw [div_pow t, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hGc0, Real.sq_sqrt hP0]
      field_simp)
    (w_Aco_le a hg hg₁ hg₂c hang hc hχ0 hχc hχi hM3 hM hJ hm)
  have hI : √(∫ t in Ioo (1 : ℝ) 2, (1 - wF t) ^ 2 / (1 - t ^ 2 / (m : ℝ) ^ 2) ^ 2 * (Gc * P / c ^ 2))
      = Cvs.L2a.CornerSuprema.Theta m * √Gc * √P / c := by
    have hΘ0 : 0 ≤ Cvs.L2a.CornerSuprema.Theta m := Real.sqrt_nonneg _
    rw [integral_mul_const, ← Theta_sq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hΘ0,
      Real.sqrt_div' _ (by positivity), Real.sqrt_sq hc0.le, Real.sqrt_mul hGc0]
    ring
  rw [hI] at hB
  have hH := Real.sqrt_le_sqrt (H_le_P a hg hg₁ hg₂c hang hc0 (s := Ioo 1 2) fun t ht => ht.1)
  rw [← hP] at hH
  have hΘ : 0 ≤ Cvs.L2a.CornerSuprema.Theta m := Real.sqrt_nonneg _
  refine hB.trans ?_
  have hsP : √P * √P = P := Real.mul_self_sqrt hP0
  calc 2 * √(2 * c / π) / m * √(∫ t in Ioo 1 2, (∑ i, a i * psi c (g i) t) ^ 2)
        * (Cvs.L2a.CornerSuprema.Theta m * √Gc * √P / c + ecap M / c ^ 2 * √Gc * √P)
      ≤ 2 * √(2 * c / π) / m * √P * (Cvs.L2a.CornerSuprema.Theta m * √Gc * √P / c + ecap M / c ^ 2 * √Gc * √P) := by
        gcongr
    _ = 2 * √(2 * c / π) / m * √Gc * (Cvs.L2a.CornerSuprema.Theta m / c + ecap M / c ^ 2) * (√P * √P) := by ring
    _ = _ := by rw [hsP]

/-! ### The local bound per corner, `m ≥ 3` -/

/-- `Θ_m^δ = (∫₁² w²((1 − δ)/((1 − δ)² − t²/m²))²)^{1/2}`, the collared `Θ_m`. -/
def ThetaD (δ m : ℝ) : ℝ := √(∫ t in (1 : ℝ)..2, (1 - wF t) ^ 2 * ((1 - δ) / ((1 - δ) ^ 2 - t ^ 2 / m ^ 2)) ^ 2)

/-- `Ψ_m = ∫₁² w²/(1 − δ − t/m)²`. -/
def PsiD (δ m : ℝ) : ℝ := ∫ t in (1 : ℝ)..2, (1 - wF t) ^ 2 / (1 - δ - t / m) ^ 2

/-- The window-charged local constant `(ΔY Θ_m² + 2κ_Sδ(Θ_m^δ)²)/(πc)`. -/
def Aloc (c X δ m : ℝ) : ℝ :=
  ((Ymax X - 1) * Cvs.L2a.CornerSuprema.Theta m ^ 2 + 2 * (181 / 462) * δ * ThetaD δ m ^ 2) / (π * c)

/-- The P-charged local constant `T(c, X, d, δ, 1 − δ − 2/m)Ψ_m/c`. -/
def Bloc (c X d δ m J : ℝ) : ℝ := tC c X d δ (1 - δ - 2 / m) J * PsiD δ m / c

theorem tauHat_r_nonneg {c x₀ d δ r : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (hxd : 1 < x₀ - d) (hδ : 0 ≤ δ) (hr : 0 < r) :
    0 ≤ Cvs.L2a.BandTransferBandForm.tauHat c x₀ d δ (fun j => (j.factorial : ℝ) / r ^ j) :=
  Cvs.L2a.ScaledBandTransfer.tauHat_nonneg hc hd hxd hδ fun j _ => by positivity

theorem tC_nonneg {c x₀ d δ r J : ℝ} (hc : 0 < c) (hd : 0 ≤ d) (hxd : 1 < x₀ - d) (hδ : 0 ≤ δ) (hr : 0 < r)
    (hJ : 0 ≤ J) : 0 ≤ tC c x₀ d δ r J := by
  have := tauHat_r_nonneg hc.le hd hxd hδ hr
  have hx : 0 < x₀ ^ 2 - 1 := by nlinarith
  have hJ' := hJ
  unfold tC; positivity

theorem tC_mono_J {c x₀ d δ r J J' : ℝ} (hc : 0 < c) (hd : 0 ≤ d) (hxd : 1 < x₀ - d) (hδ : 0 ≤ δ) (hr : 0 < r)
    (hJJ : J ≤ J') : tC c x₀ d δ r J ≤ tC c x₀ d δ r J' := by
  have := tauHat_r_nonneg hc.le hd hxd hδ hr
  have hx : 0 < x₀ ^ 2 - 1 := by nlinarith
  have hY := Cvs.L2a.BandTransferBandForm.one_le_Ymax (by linarith : 1 < x₀)
  unfold tC
  gcongr

/-- `∫_{(1,2)} Φ² + ∫_{X−d}^{X+d} Φ² ≤ ∫_{(1,∞)} Φ²` once `2 ≤ X − d`. -/
theorem H_add_W_le_P {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) {X d : ℝ} (hd : 0 ≤ d) (hXd : 2 ≤ X - d) :
    (∫ t in Ioo 1 2, (∑ i, a i * psi c (g i) t) ^ 2) + (∫ x in (X - d)..(X + d), (∑ i, a i * psi c (g i) x) ^ 2)
      ≤ ∫ t in Ioi 1, (∑ i, a i * psi c (g i) t) ^ 2 := by
  have hm := memLp_span_Ioo a hg hg₁ hg₂c hang hc (subset_refl (Ioi (1 : ℝ)))
  have hi : IntegrableOn (fun t => (∑ i, a i * psi c (g i) t) ^ 2) (Ioi 1) := (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).1 hm
  rw [intervalIntegral.integral_of_le (by linarith), ← setIntegral_union]
  · exact setIntegral_mono_set hi (ae_of_all _ fun t => sq_nonneg _)
      (ae_of_all _ (union_subset (fun t ht => ht.1) fun t ht => show 1 < t by linarith [ht.1]))
  · exact Set.disjoint_left.2 fun t h1 h2 => by linarith [h1.2, h2.1]
  · exact measurableSet_Ioc
  · exact hi.mono_set fun t ht => ht.1
  · exact hi.mono_set fun t ht => show 1 < t by linarith [ht.1]

/-- `√H√(AW + BP) ≤ (√A/2 + √B)P` when `H + W ≤ P`. -/
theorem sqrt_mix_le {A B H W P : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hH : 0 ≤ H) (hW : 0 ≤ W) (hHW : H + W ≤ P) :
    √H * √(A * W + B * P) ≤ (√A / 2 + √B) * P := by
  have hP : 0 ≤ P := by linarith
  have h1 : √(A * W + B * P) ≤ √A * √W + √B * √P := by
    rw [← Real.sqrt_mul hA, ← Real.sqrt_mul hB]
    exact Cvs.L2a.CornerSuprema.sqrt_add_le_add (by positivity) (by positivity)
  have h2 : √H * √W ≤ P / 2 := by
    rw [← Real.sqrt_mul hH]
    have : √(H * W) ≤ (H + W) / 2 := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith [sq_nonneg (H - W)]
    linarith
  have h3 : √H * √P ≤ P := by
    rw [← Real.sqrt_mul hH]
    rw [Real.sqrt_le_left hP]; nlinarith
  have := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg H)
  have hA' := Real.sqrt_nonneg A
  have hB' := Real.sqrt_nonneg B
  nlinarith [mul_le_mul_of_nonneg_left h2 hA', mul_le_mul_of_nonneg_left h3 hB']

theorem continuousOn_div_sq {f g : ℝ → ℝ} {s : Set ℝ} (hf : Continuous f) (hg : Continuous g)
    (h0 : ∀ t ∈ s, g t ≠ 0) : ContinuousOn (fun t => f t / g t ^ 2) s :=
  hf.continuousOn.div (hg.pow 2).continuousOn fun t ht => pow_ne_zero 2 (h0 t ht)

/-- **The local bound, `m ≥ 3`**: `|C_m| ≤ (2κ/m)(√A_m/2 + √B_m + √(6J/(M² − 1))·ecap(M)/c²)·P`. -/
theorem cTop_loc3_le {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) {J d δ : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχi : Function.Injective χ)
    {M : ℕ} (hM3 : 3 ≤ M) (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..M, psi c (g i) t ^ 2) (hJ : (Fintype.card ι : ℝ) ≤ J)
    (hd : 0 < d) (hd1 : d ≤ 1) (hδ : 0 < δ) (hδ3 : δ < 1 / 3) {m : ℕ} (hm : 3 ≤ m) :
    |Cvs.L2a.CutKernels.cTop c χ g a M m| ≤ 2 * √(2 * c / π) / m * (√(Aloc c M δ m) / 2 + √(Bloc c M d δ m J)
      + √(6 * J / ((M : ℝ) ^ 2 - 1)) * (ecap M / c ^ 2)) * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hM3r : (3 : ℝ) ≤ M := by exact_mod_cast hM3
  have hm3r : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  set P := ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 with hP
  set W := ∫ x in ((M : ℝ) - d)..(M + d), (∑ i, a i * psi c (g i) x) ^ 2 with hW
  set H := ∫ t in Ioo 1 2, (∑ i, a i * psi c (g i) t) ^ 2 with hH
  set Gc := 6 * J / ((M : ℝ) ^ 2 - 1) with hGc
  set rm := 1 - δ - 2 / (m : ℝ) with hrm
  have h2m : 2 / (m : ℝ) ≤ 2 / 3 := by gcongr
  have hrm0 : 0 < rm := by rw [hrm]; linarith
  have hP0 : 0 ≤ P := setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have hW0 : 0 ≤ W := intervalIntegral.integral_nonneg (by linarith) fun x _ => sq_nonneg _
  have hH0 : 0 ≤ H := setIntegral_nonneg measurableSet_Ioo fun _ _ => sq_nonneg _
  have hJ0 : 0 ≤ J := le_trans (Nat.cast_nonneg _) hJ
  have hGc0 : 0 ≤ Gc := by rw [hGc]; apply div_nonneg (by positivity); nlinarith
  have hw0 : ∀ t, 0 ≤ 1 - wF t := fun t => by linarith [(Cvs.L2a.FarFarBound.wF_bounds t).2.1]
  have hcap0 : 0 ≤ ecap M := by unfold ecap; have : 0 < (M : ℝ) ^ 2 - 1 := by nlinarith
                                positivity
  have hY := Cvs.L2a.BandTransferBandForm.one_le_Ymax (by linarith : (1 : ℝ) < M)
  have hMd : 1 < (M : ℝ) - d := by linarith
  have htc0 : 0 ≤ tC c M d δ rm J := tC_nonneg hc0 hd.le hMd hδ.le hrm0 hJ0
  -- the denominators on `[1, 2]`
  have hden : ∀ t ∈ Icc (1 : ℝ) 2, rm ≤ 1 - δ - t / m ∧ 5 / 9 ≤ 1 - t ^ 2 / (m : ℝ) ^ 2
      ∧ 0 < (1 - δ) ^ 2 - t ^ 2 / (m : ℝ) ^ 2 := fun t ht => by
    have htm : t / m ≤ 2 / m := by gcongr; exact ht.2
    have ht0 : 0 ≤ t / m := by have := ht.1; positivity
    have hsq : t ^ 2 / (m : ℝ) ^ 2 = (t / m) ^ 2 := by rw [div_pow]
    refine ⟨by rw [hrm]; linarith, ?_, ?_⟩
    · rw [hsq]; nlinarith
    · rw [hsq]; nlinarith
  set G : ℝ → ℝ := fun t => (1 - wF t) ^ 2 / (1 - t ^ 2 / (m : ℝ) ^ 2) ^ 2 * ((Ymax M - 1) / (π * c) * W)
      + (1 - wF t) ^ 2 * ((1 - δ) / ((1 - δ) ^ 2 - t ^ 2 / (m : ℝ) ^ 2)) ^ 2 * (2 * (181 / 462) * δ / (π * c) * W)
      + (1 - wF t) ^ 2 / (1 - δ - t / m) ^ 2 * (tC c M d δ rm J / c * P) with hG
  have hcw := Cvs.L2a.CornerSuprema.continuous_one_sub_wF
  have i1 : IntegrableOn (fun t => (1 - wF t) ^ 2 / (1 - t ^ 2 / (m : ℝ) ^ 2) ^ 2) (Ioo 1 2) :=
    integrableOn_wsq (by omega)
  have i2 : IntegrableOn (fun t => (1 - wF t) ^ 2 * ((1 - δ) / ((1 - δ) ^ 2 - t ^ 2 / (m : ℝ) ^ 2)) ^ 2) (Ioo 1 2) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioo_subset_Icc_self
    have hq : Continuous fun t : ℝ => (1 - δ) ^ 2 - t ^ 2 / (m : ℝ) ^ 2 := by fun_prop
    have hr : ContinuousOn (fun t : ℝ => (1 - δ) / ((1 - δ) ^ 2 - t ^ 2 / (m : ℝ) ^ 2)) (Icc 1 2) :=
      ContinuousOn.div (f := fun _ => 1 - δ) (g := fun t : ℝ => (1 - δ) ^ 2 - t ^ 2 / (m : ℝ) ^ 2)
        continuousOn_const hq.continuousOn fun t ht => (hden t ht).2.2.ne'
    exact (hcw.pow 2).continuousOn.mul (hr.pow 2)
  have i3 : IntegrableOn (fun t => (1 - wF t) ^ 2 / (1 - δ - t / m) ^ 2) (Ioo 1 2) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioo_subset_Icc_self
    exact continuousOn_div_sq (hcw.pow 2) (by fun_prop) fun t ht => by linarith [(hden t ht).1]
  have hGi : IntegrableOn G (Ioo 1 2) :=
    ((i1.mul_const _).add (i2.mul_const _)).add (i3.mul_const _)
  have hGint : ∫ t in Ioo 1 2, G t = Aloc c M δ m * W + Bloc c M d δ m J * P := by
    simp only [hG]
    have i12 : IntegrableOn (fun t => (1 - wF t) ^ 2 / (1 - t ^ 2 / (m : ℝ) ^ 2) ^ 2 * ((Ymax M - 1) / (π * c) * W)
        + (1 - wF t) ^ 2 * ((1 - δ) / ((1 - δ) ^ 2 - t ^ 2 / (m : ℝ) ^ 2)) ^ 2 * (2 * (181 / 462) * δ / (π * c) * W))
        (Ioo 1 2) := (i1.mul_const _).add (i2.mul_const _)
    rw [integral_add i12 (i3.mul_const _), integral_add (i1.mul_const _) (i2.mul_const _), integral_mul_const,
      integral_mul_const, integral_mul_const, ← Theta_sq]
    have e2 : ∫ t in Ioo (1 : ℝ) 2, (1 - wF t) ^ 2 * ((1 - δ) / ((1 - δ) ^ 2 - t ^ 2 / (m : ℝ) ^ 2)) ^ 2
        = ThetaD δ m ^ 2 := by
      unfold ThetaD
      rw [Real.sq_sqrt (intervalIntegral.integral_nonneg (by norm_num) fun t _ => by positivity),
        setIntegral_Ioo_eq]
    have e3 : ∫ t in Ioo (1 : ℝ) 2, (1 - wF t) ^ 2 / (1 - δ - t / m) ^ 2 = PsiD δ m := by
      unfold PsiD; rw [setIntegral_Ioo_eq]
    rw [e2, e3]
    unfold Aloc Bloc
    ring
  have hB := abs_cTop_le a hg hg₁ hg₂c hang hc0 M m (by omega) (G := G) (B₂ := ecap M / c ^ 2 * √Gc * √P) hGi
    (by positivity)
    (fun t ht => by
      have htI : t ∈ Icc (1 : ℝ) 2 := Ioo_subset_Icc_self ht
      obtain ⟨hr1, hq1, hq2⟩ := hden t htI
      have hη : 0 ≤ t / m := by have := ht.1; positivity
      have hloc := local_pt a hg hg₁ hg₂c hang hc hχ0 hχc hχi (by linarith : (2 : ℝ) ≤ M) hM hd hMd hδ
        (by linarith) hη hrm0 hr1
      have hD : 0 < 1 - δ - t / m := lt_of_lt_of_le hrm0 hr1
      have hT := tC_mono_J (c := c) (x₀ := M) (d := d) (δ := δ) hc0 hd.le hMd hδ.le hrm0 hJ
      have hloc' : (Asi c χ g a M (t / m)).re ^ 2
          ≤ aW c M δ (t / m) * W + tC c M d δ rm J / (c * (1 - δ - t / m) ^ 2) * P :=
        hloc.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right hT (by positivity)) hP0))
      calc ((1 - wF t) * |(Asi c χ g a M (t / m)).re|) ^ 2
          = (1 - wF t) ^ 2 * (Asi c χ g a M (t / m)).re ^ 2 := by rw [mul_pow, sq_abs]
        _ ≤ (1 - wF t) ^ 2 * (aW c M δ (t / m) * W + tC c M d δ rm J / (c * (1 - δ - t / m) ^ 2) * P) :=
          mul_le_mul_of_nonneg_left hloc' (sq_nonneg _)
        _ = G t := by
          simp only [hG]; unfold aW
          rw [div_pow t]
          have h1 : 1 - t ^ 2 / (m : ℝ) ^ 2 ≠ 0 := by linarith
          have h2 : (1 - δ) ^ 2 - t ^ 2 / (m : ℝ) ^ 2 ≠ 0 := hq2.ne'
          have h3 : 1 - δ - t / (m : ℝ) ≠ 0 := hD.ne'
          have h4 : π * c ≠ 0 := by positivity
          field_simp)
    (w_Aco_le a hg hg₁ hg₂c hang hc hχ0 hχc hχi hM3 hM hJ (by omega))
  rw [hGint] at hB
  have hA0 : 0 ≤ Aloc c M δ m := by
    unfold Aloc; have : 0 ≤ Ymax (M : ℝ) - 1 := by linarith
    positivity
  have hB0 : 0 ≤ Bloc c M d δ m J := by
    unfold Bloc
    have : 0 ≤ PsiD δ m := intervalIntegral.integral_nonneg (by norm_num) fun t _ => by positivity
    positivity
  have hHW := H_add_W_le_P a hg hg₁ hg₂c hang hc0 (X := M) hd.le (by linarith)
  rw [← hH, ← hW, ← hP] at hHW
  have hmix := sqrt_mix_le hA0 hB0 hH0 hW0 hHW
  have hHP : √H ≤ √P := Real.sqrt_le_sqrt (by linarith)
  have hκ : 0 ≤ 2 * √(2 * c / π) / m := by positivity
  refine hB.trans ?_
  have hsP : √P * √P = P := Real.mul_self_sqrt hP0
  have hcorr : √H * (ecap M / c ^ 2 * √Gc * √P) ≤ √Gc * (ecap M / c ^ 2) * P := by
    calc √H * (ecap M / c ^ 2 * √Gc * √P) ≤ √P * (ecap M / c ^ 2 * √Gc * √P) := by gcongr
      _ = √Gc * (ecap M / c ^ 2) * (√P * √P) := by ring
      _ = _ := by rw [hsP]
  calc 2 * √(2 * c / π) / m * √H * (√(Aloc c M δ m * W + Bloc c M d δ m J * P) + ecap M / c ^ 2 * √Gc * √P)
      = 2 * √(2 * c / π) / m * (√H * √(Aloc c M δ m * W + Bloc c M d δ m J * P)
        + √H * (ecap M / c ^ 2 * √Gc * √P)) := by ring
    _ ≤ 2 * √(2 * c / π) / m * ((√(Aloc c M δ m) / 2 + √(Bloc c M d δ m J)) * P + √Gc * (ecap M / c ^ 2) * P) := by
        gcongr
    _ = _ := by ring

/-! ### The local bound at `m = 2`: shells and the strip -/

/-- The shell `t ∈ (2 − u_{k+1}, 2 − u_k]`. -/
def shellSet (u : ℕ → ℝ) (k : ℕ) : Set ℝ := Ioc (2 - u (k + 1)) (2 - u k)

/-- The shell collar `δ_k = min(δ, u_k/4)`. -/
def dK (δ : ℝ) (u : ℕ → ℝ) (k : ℕ) : ℝ := min δ (u k / 4)

/-- The shell collar integral `∫_{shell} w²((1 − δ_k)/((1 − δ_k)² − t²/4))²`. -/
def collSh (δ : ℝ) (u : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∫ t in shellSet u k, (1 - wF t) ^ 2 * ((1 - dK δ u k) / ((1 - dK δ u k) ^ 2 - t ^ 2 / 2 ^ 2)) ^ 2

/-- The shell chirp integral `∫_{shell} w²/(1 − δ_k − t/2)²`. -/
def psiSh (δ : ℝ) (u : ℕ → ℝ) (k : ℕ) : ℝ := ∫ t in shellSet u k, (1 - wF t) ^ 2 / (1 - dK δ u k - t / 2) ^ 2

/-- The strip integral `∫_{2−s}^2 w²/(1 − t²/4)²`. -/
def stripI (s : ℝ) : ℝ := ∫ t in Ioo (2 - s) 2, (1 - wF t) ^ 2 / (1 - t ^ 2 / 2 ^ 2) ^ 2

/-- The window-charged constant at `m = 2`: `(ΔY Θ₂² + 2κ_S Σ_k δ_k collSh_k)/(πc)`. -/
def Aloc2 (c X δ : ℝ) (u : ℕ → ℝ) (K : ℕ) : ℝ :=
  ((Ymax X - 1) * Cvs.L2a.CornerSuprema.Theta 2 ^ 2
    + 2 * (181 / 462) * ∑ k ∈ Finset.range K, dK δ u k * collSh δ u k) / (π * c)

/-- The P-charged constant at `m = 2`: `Σ_k T(c, X, d, δ_k, u_k/4)psiSh_k/c + (6J/(X² − 1))stripI(s)/c²`. -/
def Bloc2 (c X d δ J s : ℝ) (u : ℕ → ℝ) (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.range K, tC c X d (dK δ u k) (u k / 4) J * psiSh δ u k / c + 6 * J / (X ^ 2 - 1) * stripI s / c ^ 2

/-- Every `v ∈ [u₀, 1)` lies in a shell `[u_k, u_{k+1})`, `k < K`, when `u_K = 1`. -/
theorem exists_shell {u : ℕ → ℝ} {K : ℕ} (huK : u K = 1) {v : ℝ} (hv0 : u 0 ≤ v) (hv1 : v < 1) :
    ∃ k < K, u k ≤ v ∧ v < u (k + 1) := by
  classical
  have hex : ∃ k, v < u k := ⟨K, by rw [huK]; exact hv1⟩
  have hk0 : Nat.find hex ≠ 0 := fun h => by
    have := Nat.find_spec hex; rw [h] at this; linarith
  have hkK : Nat.find hex ≤ K := Nat.find_min' hex (by rw [huK]; exact hv1)
  refine ⟨Nat.find hex - 1, by omega, ?_, ?_⟩
  · exact le_of_not_gt (Nat.find_min hex (by omega))
  · rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hk0)]; exact Nat.find_spec hex

/-- **Closing a corner**: `C ≤ κ√H(√(AW + BP) + e√G√P)` and `H + W ≤ P` give `C ≤ κ(√A/2 + √B + √G·e)P`. -/
theorem corner_finish {C κ A B H W P G e : ℝ} (hκ : 0 ≤ κ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hH : 0 ≤ H) (hW : 0 ≤ W)
    (hHW : H + W ≤ P) (he : 0 ≤ e) (h : C ≤ κ * √H * (√(A * W + B * P) + e * √G * √P)) :
    C ≤ κ * (√A / 2 + √B + √G * e) * P := by
  have hP : 0 ≤ P := by linarith
  have hmix := sqrt_mix_le hA hB hH hW hHW
  have hHP : √H ≤ √P := Real.sqrt_le_sqrt (by linarith)
  have hsP : √P * √P = P := Real.mul_self_sqrt hP
  have hcorr : √H * (e * √G * √P) ≤ √G * e * P := by
    calc √H * (e * √G * √P) ≤ √P * (e * √G * √P) := by gcongr
      _ = √G * e * (√P * √P) := by ring
      _ = _ := by rw [hsP]
  refine h.trans ?_
  calc κ * √H * (√(A * W + B * P) + e * √G * √P) = κ * (√H * √(A * W + B * P) + √H * (e * √G * √P)) := by ring
    _ ≤ κ * ((√A / 2 + √B) * P + √G * e * P) := by gcongr
    _ = _ := by ring

theorem Aloc2_nonneg {c X δ : ℝ} {u : ℕ → ℝ} {K : ℕ} (hc : 0 < c) (hX : 1 < X) (hdK : ∀ k, 0 ≤ dK δ u k) :
    0 ≤ Aloc2 c X δ u K := by
  unfold Aloc2
  have : 0 ≤ Ymax X - 1 := by linarith [Cvs.L2a.BandTransferBandForm.one_le_Ymax hX]
  have : 0 ≤ ∑ k ∈ Finset.range K, dK δ u k * collSh δ u k := Finset.sum_nonneg fun k _ =>
    mul_nonneg (hdK k) (setIntegral_nonneg measurableSet_Ioc fun t _ => by positivity)
  positivity

theorem Bloc2_nonneg {c X d δ J s : ℝ} {u : ℕ → ℝ} {K : ℕ} (hc : 0 < c) (hX : 1 < X) (hJ : 0 ≤ J)
    (htc : ∀ k, 0 ≤ tC c X d (dK δ u k) (u k / 4) J) : 0 ≤ Bloc2 c X d δ J s u K := by
  unfold Bloc2
  have : 0 ≤ ∑ k ∈ Finset.range K, tC c X d (dK δ u k) (u k / 4) J * psiSh δ u k / c := Finset.sum_nonneg
    fun k _ => div_nonneg (mul_nonneg (htc k) (setIntegral_nonneg measurableSet_Ioc fun t _ => by positivity))
      hc.le
  have : 0 ≤ stripI s := setIntegral_nonneg measurableSet_Ioo fun t _ => by positivity
  have : 0 < X ^ 2 - 1 := by nlinarith
  positivity

/-- **The local bound, `m = 2`**: shells `[u_k, u_{k+1})` of `u = 2 − t` with collars `min(δ, u_k/4)`, and T0
on the strip `u < s`: `|C₂| ≤ κ(√A₂/2 + √B₂ + √(6J/(M² − 1))·ecap(M)/c²)·P`. -/
theorem cTop_loc2_le {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) {J d δ s : ℝ}
    {u : ℕ → ℝ} {K : ℕ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχi : Function.Injective χ)
    {M : ℕ} (hM3 : 3 ≤ M) (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..M, psi c (g i) t ^ 2) (hJ : (Fintype.card ι : ℝ) ≤ J)
    (hd : 0 < d) (hd1 : d ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hs : 0 < s) (hs1 : s ≤ 1)
    (hu0 : u 0 = s) (huK : u K = 1) (hmono : Monotone u) :
    |Cvs.L2a.CutKernels.cTop c χ g a M 2| ≤ 2 * √(2 * c / π) / 2 * (√(Aloc2 c M δ u K) / 2 + √(Bloc2 c M d δ J s u K)
      + √(6 * J / ((M : ℝ) ^ 2 - 1)) * (ecap M / c ^ 2)) * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hM3r : (3 : ℝ) ≤ M := by exact_mod_cast hM3
  set P := ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 with hP
  set W := ∫ x in ((M : ℝ) - d)..(M + d), (∑ i, a i * psi c (g i) x) ^ 2 with hW
  set H := ∫ t in Ioo 1 2, (∑ i, a i * psi c (g i) t) ^ 2 with hH
  set Gc := 6 * J / ((M : ℝ) ^ 2 - 1) with hGc
  have hP0 : 0 ≤ P := setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have hW0 : 0 ≤ W := intervalIntegral.integral_nonneg (by linarith) fun x _ => sq_nonneg _
  have hH0 : 0 ≤ H := setIntegral_nonneg measurableSet_Ioo fun _ _ => sq_nonneg _
  have hJ0 : 0 ≤ J := le_trans (Nat.cast_nonneg _) hJ
  have hGc0 : 0 ≤ Gc := by rw [hGc]; apply div_nonneg (by positivity); nlinarith
  have hcap0 : 0 ≤ ecap M := by unfold ecap; have : 0 < (M : ℝ) ^ 2 - 1 := by nlinarith
                                positivity
  have hY := Cvs.L2a.BandTransferBandForm.one_le_Ymax (by linarith : (1 : ℝ) < M)
  have hMd : 1 < (M : ℝ) - d := by linarith
  have hcw := Cvs.L2a.CornerSuprema.continuous_one_sub_wF
  -- the shells
  have huk : ∀ k, s ≤ u k := fun k => hu0 ▸ hmono (Nat.zero_le k)
  have huk1 : ∀ k < K, u (k + 1) ≤ 1 := fun k hk => huK ▸ hmono (by omega)
  have hdK0 : ∀ k, 0 < dK δ u k := fun k => lt_min hδ (by linarith [huk k])
  have hdKu : ∀ k, dK δ u k ≤ u k / 4 := fun k => min_le_right _ _
  have hdKδ : ∀ k, dK δ u k ≤ δ := fun k => min_le_left _ _
  have hsh : ∀ k < K, ∀ t ∈ Icc (2 - u (k + 1)) (2 - u k),
      1 ≤ t ∧ u k / 4 ≤ 1 - dK δ u k - t / 2 ∧ 0 < (1 - dK δ u k) ^ 2 - t ^ 2 / 2 ^ 2 := fun k hk t ht => by
    have h1 := huk1 k hk
    have h2 := hdKu k
    have h3 := hdK0 k
    have h4 := hdKδ k
    have h5 := huk k
    refine ⟨by linarith [ht.1], by linarith [ht.2], ?_⟩
    have : (1 - dK δ u k) ^ 2 - t ^ 2 / 2 ^ 2 = (1 - dK δ u k - t / 2) * (1 - dK δ u k + t / 2) := by ring
    rw [this]; apply mul_pos <;> nlinarith [ht.1, ht.2]
  have hshIoo : ∀ k < K, shellSet u k ⊆ Ioo 1 2 := fun k hk t ht => by
    have h1 : 2 - u (k + 1) < t := ht.1
    have h2 : t ≤ 2 - u k := ht.2
    exact ⟨by linarith [huk1 k hk], by linarith [huk k]⟩
  have hw0 : ∀ t, 0 ≤ 1 - wF t := fun t => by linarith [(Cvs.L2a.FarFarBound.wF_bounds t).2.1]
  have htc : ∀ k, 0 ≤ tC c M d (dK δ u k) (u k / 4) J := fun k =>
    tC_nonneg hc0 hd.le hMd (hdK0 k).le (by linarith [huk k]) hJ0
  -- the majorant
  set fmain : ℝ → ℝ := fun t => (1 - wF t) ^ 2 / (1 - t ^ 2 / 2 ^ 2) ^ 2 * ((Ymax M - 1) / (π * c) * W)
    with hfmain
  set fsh : ℕ → ℝ → ℝ := fun k t =>
    (1 - wF t) ^ 2 * ((1 - dK δ u k) / ((1 - dK δ u k) ^ 2 - t ^ 2 / 2 ^ 2)) ^ 2
        * (2 * (181 / 462) * dK δ u k / (π * c) * W)
      + (1 - wF t) ^ 2 / (1 - dK δ u k - t / 2) ^ 2 * (tC c M d (dK δ u k) (u k / 4) J / c * P) with hfsh
  set fst : ℝ → ℝ := fun t => (1 - wF t) ^ 2 / (1 - t ^ 2 / 2 ^ 2) ^ 2 * (Gc * P / c ^ 2) with hfst
  set G : ℝ → ℝ := fun t => fmain t + ∑ k ∈ Finset.range K, (shellSet u k).indicator (fsh k) t
      + (Ioo (2 - s) 2).indicator fst t with hG
  have hfsh0 : ∀ k t, 0 ≤ fsh k t := fun k t => by
    have := htc k; have := hdK0 k
    simp only [hfsh]; positivity
  have hfmain0 : ∀ t, 0 ≤ fmain t := fun t => by
    have : 0 ≤ Ymax (M : ℝ) - 1 := by linarith
    simp only [hfmain]; positivity
  have hfst0 : ∀ t, 0 ≤ fst t := fun t => by simp only [hfst]; positivity
  -- integrability
  have i1 : IntegrableOn (fun t => (1 - wF t) ^ 2 / (1 - t ^ 2 / 2 ^ 2) ^ 2) (Ioo 1 2) := by
    have := integrableOn_wsq (m := 2) le_rfl
    rwa [show ((2 : ℕ) : ℝ) = 2 by norm_num] at this
  have imain : IntegrableOn fmain (Ioo 1 2) := i1.mul_const _
  have ishk : ∀ k < K, IntegrableOn (fsh k) (shellSet u k) := fun k hk => by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
    have hq : Continuous fun t : ℝ => (1 - dK δ u k) ^ 2 - t ^ 2 / 2 ^ 2 :=
      continuous_const.sub ((continuous_id.pow 2).div_const _)
    have hq' : Continuous fun t : ℝ => 1 - dK δ u k - t / 2 :=
      continuous_const.sub (continuous_id.div_const _)
    have hr : ContinuousOn (fun t : ℝ => (1 - dK δ u k) / ((1 - dK δ u k) ^ 2 - t ^ 2 / 2 ^ 2))
        (Icc (2 - u (k + 1)) (2 - u k)) :=
      ContinuousOn.div (f := fun _ => 1 - dK δ u k)
        (g := fun t : ℝ => (1 - dK δ u k) ^ 2 - t ^ 2 / 2 ^ 2)
        continuousOn_const hq.continuousOn fun t ht => (hsh k hk t ht).2.2.ne'
    refine ContinuousOn.add (((hcw.pow 2).continuousOn.mul (hr.pow 2)).mul continuousOn_const)
      ((continuousOn_div_sq (hcw.pow 2) hq' fun t ht => ?_).mul continuousOn_const)
    have := (hsh k hk t ht).2.1; have := huk k; linarith
  have ishI : ∀ k < K, IntegrableOn ((shellSet u k).indicator (fsh k)) (Ioo 1 2) := fun k hk =>
    ((ishk k hk).integrable_indicator measurableSet_Ioc).integrableOn
  have istr0 : IntegrableOn fst (Ioo 1 2) := i1.mul_const _
  have istr : IntegrableOn fst (Ioo (2 - s) 2) := istr0.mono_set fun t ht => ⟨by linarith [ht.1], ht.2⟩
  have istrI : IntegrableOn ((Ioo (2 - s) 2).indicator fst) (Ioo 1 2) :=
    (istr.integrable_indicator measurableSet_Ioo).integrableOn
  have isum : IntegrableOn (fun t => ∑ k ∈ Finset.range K, (shellSet u k).indicator (fsh k) t) (Ioo 1 2) :=
    integrable_finsetSum _ fun k hk => ishI k (Finset.mem_range.1 hk)
  have ims : IntegrableOn (fun t => fmain t + ∑ k ∈ Finset.range K, (shellSet u k).indicator (fsh k) t) (Ioo 1 2) :=
    imain.add isum
  have hGi : IntegrableOn G (Ioo 1 2) := ims.add istrI
  -- the integral of the majorant
  have hGint : ∫ t in Ioo 1 2, G t = Aloc2 c M δ u K * W + Bloc2 c M d δ J s u K * P := by
    simp only [hG]
    rw [integral_add ims istrI, integral_add imain isum, integral_finsetSum _ fun k hk =>
      ishI k (Finset.mem_range.1 hk)]
    have e1 : ∫ t in Ioo (1 : ℝ) 2, fmain t = Cvs.L2a.CornerSuprema.Theta 2 ^ 2 * ((Ymax M - 1) / (π * c) * W) := by
      simp only [hfmain]; rw [integral_mul_const, Theta_sq]
    have e2 : ∀ k ∈ Finset.range K, ∫ t in Ioo (1 : ℝ) 2, (shellSet u k).indicator (fsh k) t
        = 2 * (181 / 462) / (π * c) * W * (dK δ u k * collSh δ u k)
          + P * (tC c M d (dK δ u k) (u k / 4) J * psiSh δ u k / c) := fun k hk => by
      have hk' := Finset.mem_range.1 hk
      rw [setIntegral_indicator (show MeasurableSet (shellSet u k) from measurableSet_Ioc),
        inter_eq_right.2 (hshIoo k hk')]
      have ia : IntegrableOn (fun t => (1 - wF t) ^ 2 * ((1 - dK δ u k) / ((1 - dK δ u k) ^ 2 - t ^ 2 / 2 ^ 2)) ^ 2)
          (shellSet u k) := by
        refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
        exact (hcw.pow 2).continuousOn.mul ((continuousOn_const.div (by fun_prop)
          fun t ht => (hsh k hk' t ht).2.2.ne').pow 2)
      have ib : IntegrableOn (fun t => (1 - wF t) ^ 2 / (1 - dK δ u k - t / 2) ^ 2) (shellSet u k) := by
        refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
        exact continuousOn_div_sq (hcw.pow 2) (by fun_prop) fun t ht => by
          have := (hsh k hk' t ht).2.1; have := huk k; linarith
      simp only [hfsh]
      rw [integral_add (ia.mul_const _) (ib.mul_const _), integral_mul_const, integral_mul_const]
      unfold collSh psiSh
      ring
    have e3 : ∫ t in Ioo (1 : ℝ) 2, (Ioo (2 - s) 2).indicator fst t = Gc * P / c ^ 2 * stripI s := by
      rw [setIntegral_indicator measurableSet_Ioo,
        inter_eq_right.2 (show Ioo (2 - s) 2 ⊆ Ioo 1 2 from fun t ht => ⟨by linarith [ht.1], ht.2⟩)]
      simp only [hfst]; rw [integral_mul_const]; unfold stripI; ring
    rw [e1, Finset.sum_congr rfl e2, e3, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    unfold Aloc2 Bloc2
    rw [hGc]
    ring
  -- the pointwise majorant
  clear_value G fmain fsh fst
  have hc2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  have h₁ : ∀ t ∈ Ioo (1 : ℝ) 2, ((1 - wF t) * |(Asi c χ g a M (t / ((2 : ℕ) : ℝ))).re|) ^ 2 ≤ G t := by
    intro t ht
    rw [hc2, mul_pow, sq_abs]
    have hsum0 : 0 ≤ ∑ k ∈ Finset.range K, (shellSet u k).indicator (fsh k) t :=
      Finset.sum_nonneg fun k _ => indicator_nonneg (fun t _ => hfsh0 k t) t
    have hstr0 : 0 ≤ (Ioo (2 - s) 2).indicator fst t := indicator_nonneg (fun t _ => hfst0 t) t
    have hq : 0 < 1 - t ^ 2 / 2 ^ 2 := by nlinarith [ht.1, ht.2]
    by_cases hts : 2 - s < t
    · have hy0 : 0 < t / 2 := by linarith [ht.1]
      have hy1 : t / 2 < 1 := by linarith [ht.2]
      have hA := norm_Asi_le a hg hg₁ hg₂c hang hc hχ0 hχc hχi (by linarith : (2 : ℝ) ≤ M) hM hJ hy0 hy1
      have h1 : (Asi c χ g a M (t / 2)).re ^ 2 ≤ (1 / (c * (1 - (t / 2) ^ 2)) * √Gc * √P) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) ((Complex.abs_re_le_norm _).trans hA) 2
      have hst : (Ioo (2 - s) 2).indicator fst t = fst t :=
        indicator_of_mem (show t ∈ Ioo (2 - s) 2 from ⟨hts, ht.2⟩) _
      calc (1 - wF t) ^ 2 * (Asi c χ g a M (t / 2)).re ^ 2
          ≤ (1 - wF t) ^ 2 * (1 / (c * (1 - (t / 2) ^ 2)) * √Gc * √P) ^ 2 :=
            mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
        _ = fst t := by
            simp only [hfst]
            rw [mul_pow, mul_pow, Real.sq_sqrt hGc0, Real.sq_sqrt hP0, div_pow t]
            field_simp
        _ ≤ G t := by
            have e : G t = fmain t + ∑ k ∈ Finset.range K, (shellSet u k).indicator (fsh k) t
                + (Ioo (2 - s) 2).indicator fst t := by rw [hG]
            rw [e, hst]; linarith only [hfmain0 t, hsum0]
    · have hv0 : u 0 ≤ 2 - t := by rw [hu0]; linarith
      have hv1 : 2 - t < 1 := by linarith [ht.1]
      obtain ⟨k, hk, hk1, hk2⟩ := exists_shell huK hv0 hv1
      have htk : t ∈ shellSet u k := ⟨by linarith, by linarith⟩
      obtain ⟨-, hr, hq2⟩ := hsh k hk t (Ioc_subset_Icc_self htk)
      have hur : 0 < u k / 4 := by linarith [huk k]
      have hloc := local_pt a hg hg₁ hg₂c hang hc hχ0 hχc hχi (by linarith : (2 : ℝ) ≤ M) hM hd hMd (hdK0 k)
        (by linarith [hdKδ k]) (by linarith [ht.1] : (0 : ℝ) ≤ t / 2) hur hr
      have hT := tC_mono_J (c := c) (x₀ := M) (d := d) hc0 hd.le hMd (hdK0 k).le hur hJ
      have hD : 0 < 1 - dK δ u k - t / 2 := lt_of_lt_of_le hur hr
      have hloc' : (Asi c χ g a M (t / 2)).re ^ 2 ≤ aW c M (dK δ u k) (t / 2) * W
          + tC c M d (dK δ u k) (u k / 4) J / (c * (1 - dK δ u k - t / 2) ^ 2) * P :=
        hloc.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right hT (by positivity)) hP0))
      have hsh1 : (shellSet u k).indicator (fsh k) t = fsh k t := indicator_of_mem htk _
      have hle1 : (shellSet u k).indicator (fsh k) t ≤ ∑ k ∈ Finset.range K, (shellSet u k).indicator (fsh k) t :=
        Finset.single_le_sum (f := fun k => (shellSet u k).indicator (fsh k) t)
          (fun k _ => indicator_nonneg (fun t _ => hfsh0 k t) t) (Finset.mem_range.2 hk)
      calc (1 - wF t) ^ 2 * (Asi c χ g a M (t / 2)).re ^ 2
          ≤ (1 - wF t) ^ 2 * (aW c M (dK δ u k) (t / 2) * W
            + tC c M d (dK δ u k) (u k / 4) J / (c * (1 - dK δ u k - t / 2) ^ 2) * P) :=
            mul_le_mul_of_nonneg_left hloc' (sq_nonneg _)
        _ = fmain t + fsh k t := by
            simp only [hfmain, hfsh]; unfold aW
            rw [div_pow t]
            have h1 : 1 - t ^ 2 / 2 ^ 2 ≠ 0 := hq.ne'
            have h2 : (1 - dK δ u k) ^ 2 - t ^ 2 / 2 ^ 2 ≠ 0 := hq2.ne'
            have h3 : 1 - dK δ u k - t / 2 ≠ 0 := hD.ne'
            have h4 : π * c ≠ 0 := by positivity
            field_simp
            ring
        _ ≤ G t := by
            have e : G t = fmain t + ∑ k ∈ Finset.range K, (shellSet u k).indicator (fsh k) t
                + (Ioo (2 - s) 2).indicator fst t := by rw [hG]
            rw [e]; linarith only [hle1, hstr0, hsh1]
  have h₂ : ∀ t ∈ Ioo (1 : ℝ) 2, (1 - wF t) * ‖Aco c χ g a M (t / ((2 : ℕ) : ℝ))‖ ≤ ecap M / c ^ 2 * √Gc * √P :=
    w_Aco_le a hg hg₁ hg₂c hang hc hχ0 hχc hχi hM3 hM hJ (m := 2) le_rfl
  have hB₂ : 0 ≤ ecap M / c ^ 2 * √Gc * √P :=
    mul_nonneg (mul_nonneg (div_nonneg hcap0 (sq_nonneg c)) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hB := abs_cTop_le a hg hg₁ hg₂c hang hc0 M 2 (by norm_num) hGi hB₂ h₁ h₂
  rw [hGint, hc2] at hB
  have hA0 : 0 ≤ Aloc2 c M δ u K := Aloc2_nonneg hc0 (by linarith only [hM3r]) fun k => (hdK0 k).le
  have hB0 : 0 ≤ Bloc2 c M d δ J s u K := Bloc2_nonneg hc0 (by linarith only [hM3r]) hJ0 htc
  have hHW := H_add_W_le_P a hg hg₁ hg₂c hang hc0 (X := M) hd.le (by linarith only [hM3r, hd1])
  rw [← hH, ← hW, ← hP] at hHW
  exact corner_finish (div_nonneg (mul_nonneg zero_le_two (Real.sqrt_nonneg _)) zero_le_two) hA0 hB0 hH0 hW0 hHW
    (div_nonneg hcap0 (sq_nonneg c)) hB

/-! ### `Σ|C_m|`: the local and global bounds together -/

/-- The global constant of the corner `m`: `(2κ/m)√(6J/(M² − 1))·Θ_m/c`. -/
def globC (c J : ℝ) (M m : ℕ) : ℝ :=
  2 * √(2 * c / π) / m * √(6 * J / ((M : ℝ) ^ 2 - 1)) * (Cvs.L2a.CornerSuprema.Theta m / c)

/-- The correction constant of the corner `m`: `(2κ/m)√(6J/(M² − 1))·ecap(M)/c²`. -/
def corrC (c J : ℝ) (M m : ℕ) : ℝ := 2 * √(2 * c / π) / m * √(6 * J / ((M : ℝ) ^ 2 - 1)) * (ecap M / c ^ 2)

/-- The local constant of the corner `m`: `(2κ/m)(√A_m/2 + √B_m)`, shells and strip at `m = 2`. -/
def locC (c J d δ s : ℝ) (u : ℕ → ℝ) (K M m : ℕ) : ℝ :=
  if m = 2 then 2 * √(2 * c / π) / 2 * (√(Aloc2 c M δ u K) / 2 + √(Bloc2 c M d δ J s u K))
  else 2 * √(2 * c / π) / m * (√(Aloc c M δ m) / 2 + √(Bloc c M d δ m J))

/-- **Each corner**: `|C_m| ≤ (min(loc_m, glob_m) + corr_m)·P`. -/
theorem cTop_le_min {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) {J d δ s : ℝ}
    {u : ℕ → ℝ} {K : ℕ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχi : Function.Injective χ)
    {M : ℕ} (hM3 : 3 ≤ M) (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..M, psi c (g i) t ^ 2) (hJ : (Fintype.card ι : ℝ) ≤ J)
    (hd : 0 < d) (hd1 : d ≤ 1) (hδ : 0 < δ) (hδ3 : δ < 1 / 3) (hs : 0 < s) (hs1 : s ≤ 1)
    (hu0 : u 0 = s) (huK : u K = 1) (hmono : Monotone u) {m : ℕ} (hm : 2 ≤ m) :
    |Cvs.L2a.CutKernels.cTop c χ g a M m| ≤ (min (locC c J d δ s u K M m) (globC c J M m) + corrC c J M m)
      * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := by
  have hglob := cTop_glob_le a hg hg₁ hg₂c hang hc hχ0 hχc hχi hM3 hM hJ hm
  have hloc : |Cvs.L2a.CutKernels.cTop c χ g a M m| ≤ (locC c J d δ s u K M m + corrC c J M m)
      * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := by
    unfold locC corrC
    rcases Nat.lt_or_ge m 3 with h3 | h3
    · have hm2 : m = 2 := by omega
      subst hm2
      rw [ite_eq_left rfl]
      refine (cTop_loc2_le a hg hg₁ hg₂c hang hc hχ0 hχc hχi hM3 hM hJ hd hd1 hδ (by linarith) hs hs1 hu0 huK
        hmono).trans (le_of_eq ?_)
      push_cast; ring
    · rw [ite_eq_right (by omega)]
      refine (cTop_loc3_le a hg hg₁ hg₂c hang hc hχ0 hχc hχi hM3 hM hJ hd hd1 hδ hδ3 h3).trans (le_of_eq ?_)
      ring
  have hglob' : |Cvs.L2a.CutKernels.cTop c χ g a M m| ≤ (globC c J M m + corrC c J M m)
      * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := by
    refine hglob.trans (le_of_eq ?_); unfold globC corrC; ring
  rw [← min_add_add_right]
  have hP : 0 ≤ ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  rw [min_mul_of_nonneg _ _ hP]
  exact le_min hloc hglob'

/-- `T^loc(M) = Σ_m (loc_m + corr_m)`. -/
def Tloc (c J d δ s : ℝ) (u : ℕ → ℝ) (K M : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 2 (M - 1), (locC c J d δ s u K M m + corrC c J M m)

/-- `T^glob(M) = Σ_m (glob_m + corr_m)`. -/
def Tglob (c J : ℝ) (M : ℕ) : ℝ := ∑ m ∈ Finset.Icc 2 (M - 1), (globC c J M m + corrC c J M m)

/-- **`Dtop_flat`**: `Σ_{m=2}^{M−1} |C_m| ≤ min(T^loc, T^glob)·P`. -/
theorem Dtop_flat {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) {J d δ s : ℝ}
    {u : ℕ → ℝ} {K : ℕ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχi : Function.Injective χ)
    {M : ℕ} (hM3 : 3 ≤ M) (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..M, psi c (g i) t ^ 2) (hJ : (Fintype.card ι : ℝ) ≤ J)
    (hd : 0 < d) (hd1 : d ≤ 1) (hδ : 0 < δ) (hδ3 : δ < 1 / 3) (hs : 0 < s) (hs1 : s ≤ 1)
    (hu0 : u 0 = s) (huK : u K = 1) (hmono : Monotone u) :
    ∑ m ∈ Finset.Icc 2 (M - 1), |Cvs.L2a.CutKernels.cTop c χ g a M m|
      ≤ min (Tloc c J d δ s u K M) (Tglob c J M) * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := by
  have hP : 0 ≤ ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have h1 : ∑ m ∈ Finset.Icc 2 (M - 1), |Cvs.L2a.CutKernels.cTop c χ g a M m|
      ≤ ∑ m ∈ Finset.Icc 2 (M - 1), (min (locC c J d δ s u K M m) (globC c J M m) + corrC c J M m)
        * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 :=
    Finset.sum_le_sum fun m hm => cTop_le_min a hg hg₁ hg₂c hang hc hχ0 hχc hχi hM3 hM hJ hd hd1 hδ hδ3 hs hs1
      hu0 huK hmono (Finset.mem_Icc.1 hm).1
  refine h1.trans ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right (le_min ?_ ?_) hP
  · exact Finset.sum_le_sum fun m _ => add_le_add (min_le_left _ _) le_rfl
  · exact Finset.sum_le_sum fun m _ => add_le_add (min_le_right _ _) le_rfl

/-! ### Closed forms: `r₁^glob`, the correction, the chord and `Ψ_m` -/

theorem Icc_eq_Ico {M : ℕ} (hM : 1 ≤ M) : Finset.Icc 2 (M - 1) = Finset.Ico 2 M := by
  ext m; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega

/-- `κ_ι = 12J/(πc)`, the count constant of `r₁^glob`. -/
def kapI (c J : ℝ) : ℝ := 12 * J / (π * c)

theorem sqrt_factor_eq {c J X : ℝ} (hc : 0 < c) (hJ : 0 ≤ J) (hX : 1 < X) :
    √(2 * c / π) * √(6 * J / (X ^ 2 - 1)) / c = √(kapI c J) / √(X ^ 2 - 1) := by
  have hX1 : 0 < X ^ 2 - 1 := by nlinarith
  have hπ := pi_pos
  have hk0 : 0 ≤ kapI c J := by unfold kapI; positivity
  have hL : 0 ≤ √(2 * c / π) * √(6 * J / (X ^ 2 - 1)) / c := by positivity
  have hR : 0 ≤ √(kapI c J) / √(X ^ 2 - 1) := by positivity
  rw [← Real.sqrt_sq hL, ← Real.sqrt_sq hR]
  congr 1
  rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), div_pow, Real.sq_sqrt hk0,
    Real.sq_sqrt hX1.le, kapI]
  field_simp
  ring

/-- **`Σ glob_m ≤ r₁^glob(M)`**, `CornerSuprema`'s majorant `2√κ_ι N(M)/√(M² − 1)` with `Θ₂ = Θ 2`. -/
theorem sum_globC_le {c J : ℝ} (hc : 0 < c) (hJ : 0 ≤ J) {M : ℕ} (hM3 : 3 ≤ M) :
    ∑ m ∈ Finset.Icc 2 (M - 1), globC c J M m
      ≤ Cvs.L2a.CornerSuprema.r1globBar (kapI c J) (Cvs.L2a.CornerSuprema.Theta 2) M := by
  have hM3r : (3 : ℝ) ≤ M := by exact_mod_cast hM3
  have hk := sqrt_factor_eq hc hJ (by linarith : (1 : ℝ) < M)
  have e : ∀ m ∈ Finset.Icc 2 (M - 1), globC c J M m
      = 2 * (√(kapI c J) / √((M : ℝ) ^ 2 - 1)) * (Cvs.L2a.CornerSuprema.Theta m / m) := fun m _ => by
    unfold globC
    rw [← hk]; field_simp
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum, Icc_eq_Ico (by omega)]
  have hS := Cvs.L2a.CornerSuprema.sum_div_le_Nbar Cvs.L2a.CornerSuprema.Theta
    (fun m hm => Cvs.L2a.CornerSuprema.Theta_le (by linarith)) M hM3
  unfold Cvs.L2a.CornerSuprema.r1globBar
  have : 0 ≤ 2 * (√(kapI c J) / √((M : ℝ) ^ 2 - 1)) := by positivity
  calc 2 * (√(kapI c J) / √((M : ℝ) ^ 2 - 1)) * ∑ m ∈ Finset.Ico 2 M, Cvs.L2a.CornerSuprema.Theta m / m
      ≤ 2 * (√(kapI c J) / √((M : ℝ) ^ 2 - 1)) * Cvs.L2a.CornerSuprema.Nbar (Cvs.L2a.CornerSuprema.Theta 2) M :=
        mul_le_mul_of_nonneg_left hS this
    _ = _ := by ring

/-- The `M`-uniform correction constant `(29π²/(3√8))√κ_ι/c`. -/
def KcoBar (c J : ℝ) : ℝ := 29 * π ^ 2 / (3 * √8) * √(kapI c J) / c

/-- **`Σ corr_m ≤ (29π²/(3√8))√κ_ι/c`** for every `M ≥ 3`. -/
theorem sum_corrC_le {c J : ℝ} (hc : 0 < c) (hJ : 0 ≤ J) {M : ℕ} (hM3 : 3 ≤ M) :
    ∑ m ∈ Finset.Icc 2 (M - 1), corrC c J M m ≤ KcoBar c J := by
  have hM3r : (3 : ℝ) ≤ M := by exact_mod_cast hM3
  have hM1 : 0 < (M : ℝ) ^ 2 - 1 := by nlinarith
  have hk := sqrt_factor_eq hc hJ (by linarith : (1 : ℝ) < M)
  have hcap0 : 0 ≤ ecap M := by unfold ecap; positivity
  set A := 2 * (√(kapI c J) / √((M : ℝ) ^ 2 - 1)) * (ecap M / c) with hA
  have hA0 : 0 ≤ A := by positivity
  have e : ∀ m ∈ Finset.Icc 2 (M - 1), corrC c J M m = A * (1 / (m : ℝ)) := fun m _ => by
    unfold corrC; rw [hA, ← hk]; field_simp
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
  have hsum : ∑ m ∈ Finset.Icc 2 (M - 1), 1 / (m : ℝ) ≤ ((M : ℝ) - 2) / 2 := by
    have h1 : ∀ m ∈ Finset.Icc 2 (M - 1), 1 / (m : ℝ) ≤ 1 / 2 := fun m hm => by
      have : (2 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.1 hm).1
      exact one_div_le_one_div_of_le (by norm_num) this
    refine (Finset.sum_le_card_nsmul _ _ _ h1).trans (le_of_eq ?_)
    have hcard : (Finset.Icc 2 (M - 1)).card = M - 2 := by rw [Nat.card_Icc]; omega
    rw [hcard, nsmul_eq_mul, Nat.cast_sub (by omega)]
    push_cast; ring
  have hEM : ecap M * M ≤ 29 * π ^ 2 / 3 := by
    unfold ecap
    have h1 : 6 * (M : ℝ) / ((M : ℝ) ^ 2 - 1) * M ≤ 27 / 4 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hM1]; nlinarith
    have h2 : 1 / (2 * (M : ℝ)) * M = 1 / 2 := by field_simp
    have hπ : 0 ≤ π ^ 2 := by positivity
    nlinarith
  have hs8 : √8 ≤ √((M : ℝ) ^ 2 - 1) := Real.sqrt_le_sqrt (by nlinarith)
  have hs80 : 0 < √8 := by positivity
  calc A * ∑ m ∈ Finset.Icc 2 (M - 1), 1 / (m : ℝ) ≤ A * (((M : ℝ) - 2) / 2) := mul_le_mul_of_nonneg_left hsum hA0
    _ ≤ A * ((M : ℝ) / 2) := by gcongr; linarith
    _ = √(kapI c J) / c * (ecap M * M) / √((M : ℝ) ^ 2 - 1) := by rw [hA]; field_simp
    _ ≤ √(kapI c J) / c * (29 * π ^ 2 / 3) / √8 := by
        gcongr
    _ = KcoBar c J := by unfold KcoBar; field_simp

/-- **The §1.5(a) chord**: `Θ_m^δ ≤ (1 + 24δ/5)Θ_m` for `m ≥ 3`, `0 ≤ δ ≤ 1/8`. -/
theorem Theta_delta_le {δ m : ℝ} (hm : 3 ≤ m) (hδ : 0 ≤ δ) (hδ8 : δ ≤ 1 / 8) :
    ThetaD δ m ≤ (1 + 24 * δ / 5) * Cvs.L2a.CornerSuprema.Theta m := by
  have hm0 : 0 < m := by linarith
  have hcw := Cvs.L2a.CornerSuprema.continuous_one_sub_wF
  have hpt : ∀ t ∈ Icc (1 : ℝ) 2, 0 ≤ t ^ 2 / m ^ 2 ∧ t ^ 2 / m ^ 2 ≤ 4 / 9 := fun t ht => by
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ (by positivity)]; nlinarith [ht.1, ht.2]
  have hkey : ∀ t ∈ Icc (1 : ℝ) 2, (1 - wF t) ^ 2 * ((1 - δ) / ((1 - δ) ^ 2 - t ^ 2 / m ^ 2)) ^ 2
      ≤ (1 + 24 * δ / 5) ^ 2 * ((1 - wF t) ^ 2 / (1 - t ^ 2 / m ^ 2) ^ 2) := fun t ht => by
    obtain ⟨e0, e1⟩ := hpt t ht
    set e := t ^ 2 / m ^ 2
    have hq1 : 0 < 1 - e := by linarith
    have hq2 : 0 < (1 - δ) ^ 2 - e := by nlinarith
    have hr : (1 - δ) / ((1 - δ) ^ 2 - e) ≤ (1 + 24 * δ / 5) / (1 - e) := by
      rw [div_le_div_iff₀ hq2 hq1]
      have hb : 0 ≤ 19 / 5 - 43 / 5 * δ + 24 / 5 * δ ^ 2 - 29 / 5 * e := by nlinarith
      nlinarith [mul_nonneg hδ hb]
    have hr0 : 0 ≤ (1 - δ) / ((1 - δ) ^ 2 - e) := div_nonneg (by linarith) hq2.le
    calc (1 - wF t) ^ 2 * ((1 - δ) / ((1 - δ) ^ 2 - e)) ^ 2 ≤ (1 - wF t) ^ 2 * ((1 + 24 * δ / 5) / (1 - e)) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hr 2) (sq_nonneg _)
      _ = _ := by rw [div_pow]; ring
  have hc1 : ContinuousOn (fun t => (1 - wF t) ^ 2 * ((1 - δ) / ((1 - δ) ^ 2 - t ^ 2 / m ^ 2)) ^ 2) (Icc 1 2) :=
    have hq : Continuous fun t : ℝ => (1 - δ) ^ 2 - t ^ 2 / m ^ 2 := by fun_prop
    have hr : ContinuousOn (fun t : ℝ => (1 - δ) / ((1 - δ) ^ 2 - t ^ 2 / m ^ 2)) (Icc 1 2) :=
      ContinuousOn.div (f := fun _ => 1 - δ) (g := fun t : ℝ => (1 - δ) ^ 2 - t ^ 2 / m ^ 2)
        continuousOn_const hq.continuousOn fun t ht => by
          have := hpt t ht; nlinarith
    (hcw.pow 2).continuousOn.mul (hr.pow 2)
  have hc2 : ContinuousOn (fun t => (1 + 24 * δ / 5) ^ 2 * ((1 - wF t) ^ 2 / (1 - t ^ 2 / m ^ 2) ^ 2)) (Icc 1 2) :=
    have hq' : Continuous fun t : ℝ => 1 - t ^ 2 / m ^ 2 := by fun_prop
    have hd : ContinuousOn (fun t => (1 - wF t) ^ 2 / (1 - t ^ 2 / m ^ 2) ^ 2) (Icc 1 2) :=
      continuousOn_div_sq (f := fun t => (1 - wF t) ^ 2) (g := fun t : ℝ => 1 - t ^ 2 / m ^ 2)
        (hcw.pow 2) hq' fun t ht => by
          have := hpt t ht
          show 1 - t ^ 2 / m ^ 2 ≠ 0
          linarith
    by
      have h := hd.const_smul ((1 + 24 * δ / 5) ^ 2)
      exact h
  have hI := intervalIntegral.integral_mono_on (by norm_num : (1 : ℝ) ≤ 2)
    (hc1.intervalIntegrable_of_Icc (μ := volume) (by norm_num))
    (hc2.intervalIntegrable_of_Icc (μ := volume) (by norm_num)) hkey
  rw [intervalIntegral.integral_const_mul] at hI
  unfold ThetaD
  refine (Real.sqrt_le_sqrt hI).trans (le_of_eq ?_)
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith)]
  rfl

/-- **`S1♭`'s `Ψ_m`**: `Ψ_m ≤ (11/16)/(1 − δ − 2/m)²`, from `∫₁² w² = 11/16`. -/
theorem PsiD_le {δ m : ℝ} (hm : 3 ≤ m) (hδ3 : δ < 1 / 3) :
    PsiD δ m ≤ 11 / 16 / (1 - δ - 2 / m) ^ 2 := by
  have hm0 : 0 < m := by linarith
  have h2m : 2 / m ≤ 2 / 3 := by gcongr
  have hr : 0 < 1 - δ - 2 / m := by linarith
  have hcw := Cvs.L2a.CornerSuprema.continuous_one_sub_wF
  have hpt : ∀ t ∈ Icc (1 : ℝ) 2, 1 - δ - 2 / m ≤ 1 - δ - t / m := fun t ht => by
    have : t / m ≤ 2 / m := by gcongr; exact ht.2
    linarith
  have hkey : ∀ t ∈ Icc (1 : ℝ) 2, (1 - wF t) ^ 2 / (1 - δ - t / m) ^ 2 ≤ (1 - wF t) ^ 2 * (1 / (1 - δ - 2 / m) ^ 2) :=
    fun t ht => by
      rw [mul_one_div]
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (pow_le_pow_left₀ hr.le (hpt t ht) 2)
  have hc1 : ContinuousOn (fun t => (1 - wF t) ^ 2 / (1 - δ - t / m) ^ 2) (Icc 1 2) :=
    continuousOn_div_sq (hcw.pow 2) (by fun_prop) fun t ht => by linarith [hpt t ht]
  have hi2 : IntervalIntegrable (fun t => (1 - wF t) ^ 2 * (1 / (1 - δ - 2 / m) ^ 2)) volume 1 2 :=
    ((hcw.pow 2).mul continuous_const).intervalIntegrable 1 2
  have hI := intervalIntegral.integral_mono_on (by norm_num : (1 : ℝ) ≤ 2)
    (hc1.intervalIntegrable_of_Icc (μ := volume) (by norm_num)) hi2 hkey
  rw [intervalIntegral.integral_mul_const, Cvs.L2a.CornerSuprema.integral_weight_sq] at hI
  unfold PsiD
  refine hI.trans (le_of_eq ?_)
  ring

/-! ### The `m = 2` shells and strip in closed form, from `w² ≤ π⁴(2 − t)⁴` -/

/-- `∫_{(2−b, 2−a]} f ≤ K(b³ − a³)/3` when `f ≤ K(2 − t)²` there. -/
theorem integral_shell_le {f : ℝ → ℝ} {a b K : ℝ} (hab : a ≤ b) (hf : IntegrableOn f (Ioc (2 - b) (2 - a)))
    (hle : ∀ t ∈ Ioc (2 - b) (2 - a), f t ≤ K * (2 - t) ^ 2) :
    ∫ t in Ioc (2 - b) (2 - a), f t ≤ K * ((b ^ 3 - a ^ 3) / 3) := by
  have hg : IntegrableOn (fun t => K * (2 - t) ^ 2) (Ioc (2 - b) (2 - a)) :=
    (Continuous.integrableOn_Ioc (by fun_prop))
  refine (setIntegral_mono_on hf hg measurableSet_Ioc hle).trans (le_of_eq ?_)
  rw [← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_left (fun x => x ^ 2) 2, integral_pow]
  ring_nf

/-- The strip in closed form: `∫_{2−s}^2 w²/(1 − t²/4)² ≤ (16π⁴/9)(s³/3)` for `0 < s ≤ 1`. -/
theorem stripI_le {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) : stripI s ≤ 16 * π ^ 4 / 9 * (s ^ 3 / 3) := by
  have hf : IntegrableOn (fun t => (1 - wF t) ^ 2 / (1 - t ^ 2 / 2 ^ 2) ^ 2) (Ioc (2 - s) (2 - 0)) := by
    have h := (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1
      Cvs.L2a.CornerSuprema.intervalIntegrable_theta2Int
    exact h.mono_set fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hle : ∀ t ∈ Ioc (2 - s) (2 - 0), (1 - wF t) ^ 2 / (1 - t ^ 2 / 2 ^ 2) ^ 2 ≤ 16 * π ^ 4 / 9 * (2 - t) ^ 2 := by
    intro t ht
    obtain ⟨h1, h2⟩ := ht
    rw [sub_zero] at h2
    rcases eq_or_lt_of_le h2 with h | h
    · subst h; norm_num
    have hu : 0 < 2 - t := by linarith
    have hq : 3 * (2 - t) / 4 ≤ 1 - t ^ 2 / 2 ^ 2 := by nlinarith
    have hw : (1 - wF t) ^ 2 ≤ π ^ 4 * (2 - t) ^ 4 := by
      have := Cvs.L2a.RampTopQuadratic.one_sub_wF_le t
      have h0 : 0 ≤ 1 - wF t := by linarith [(Cvs.L2a.FarFarBound.wF_bounds t).2.1]
      calc (1 - wF t) ^ 2 ≤ (π ^ 2 * (2 - t) ^ 2) ^ 2 := pow_le_pow_left₀ h0 this 2
        _ = π ^ 4 * (2 - t) ^ 4 := by ring
    calc (1 - wF t) ^ 2 / (1 - t ^ 2 / 2 ^ 2) ^ 2 ≤ π ^ 4 * (2 - t) ^ 4 / (3 * (2 - t) / 4) ^ 2 := by
          gcongr
      _ = 16 * π ^ 4 / 9 * (2 - t) ^ 2 := by field_simp; ring
  have h := integral_shell_le (a := 0) (b := s) hs.le hf hle
  rw [sub_zero, integral_Ioc_eq_integral_Ioo] at h
  unfold stripI
  refine h.trans (le_of_eq ?_)
  ring

/-- The shells in closed form: `collSh_k, psiSh_k ≤ (16π⁴)(u_{k+1}³ − u_k³)/3` for `0 < u_k ≤ u_{k+1} ≤ 1`. -/
theorem shell_le {δ : ℝ} {u : ℕ → ℝ} {k : ℕ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hu0 : 0 < u k) (hu : u k ≤ u (k + 1))
    (hu1 : u (k + 1) ≤ 1) :
    collSh δ u k ≤ 16 * π ^ 4 * ((u (k + 1) ^ 3 - u k ^ 3) / 3)
      ∧ psiSh δ u k ≤ 16 * π ^ 4 * ((u (k + 1) ^ 3 - u k ^ 3) / 3) := by
  set D := dK δ u k with hDdef
  have hD0 : 0 < D := lt_min hδ (by linarith)
  have hDu : D ≤ u k / 4 := min_le_right _ _
  have hD1 : D ≤ 1 := (min_le_left _ _).trans hδ1
  have hcw := Cvs.L2a.CornerSuprema.continuous_one_sub_wF
  have hpt : ∀ t ∈ Icc (2 - u (k + 1)) (2 - u k), 1 ≤ t ∧ (2 - t) / 4 ≤ 1 - D - t / 2 := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hw : ∀ t, (1 - wF t) ^ 2 ≤ π ^ 4 * (2 - t) ^ 4 := fun t => by
    have := Cvs.L2a.RampTopQuadratic.one_sub_wF_le t
    have h0 : 0 ≤ 1 - wF t := by linarith [(Cvs.L2a.FarFarBound.wF_bounds t).2.1]
    calc (1 - wF t) ^ 2 ≤ (π ^ 2 * (2 - t) ^ 2) ^ 2 := pow_le_pow_left₀ h0 this 2
      _ = π ^ 4 * (2 - t) ^ 4 := by ring
  have hinv : ∀ t ∈ Ioc (2 - u (k + 1)) (2 - u k), (1 - wF t) ^ 2 / (1 - D - t / 2) ^ 2 ≤ 16 * π ^ 4 * (2 - t) ^ 2 :=
    fun t ht => by
      obtain ⟨h1, h2⟩ := hpt t (Ioc_subset_Icc_self ht)
      have hv : 0 < 2 - t := by linarith [ht.2]
      calc (1 - wF t) ^ 2 / (1 - D - t / 2) ^ 2 ≤ π ^ 4 * (2 - t) ^ 4 / ((2 - t) / 4) ^ 2 := by
            gcongr
            exact hw t
        _ = 16 * π ^ 4 * (2 - t) ^ 2 := by field_simp; ring
  have hq : ∀ t ∈ Icc (2 - u (k + 1)) (2 - u k), 0 < (1 - D) ^ 2 - t ^ 2 / 2 ^ 2 := fun t ht => by
    obtain ⟨h1, h2⟩ := hpt t ht
    have hv : 0 < 2 - t := by linarith [ht.2]
    have : (1 - D) ^ 2 - t ^ 2 / 2 ^ 2 = (1 - D - t / 2) * (1 - D + t / 2) := by ring
    rw [this]; apply mul_pos <;> linarith
  refine ⟨?_, ?_⟩
  · refine integral_shell_le hu ?_ fun t ht => ?_
    · refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
      exact (hcw.pow 2).continuousOn.mul ((continuousOn_const.div (by fun_prop)
        fun t ht => (hq t ht).ne').pow 2)
    · obtain ⟨h1, h2⟩ := hpt t (Ioc_subset_Icc_self ht)
      have hq' := hq t (Ioc_subset_Icc_self ht)
      have hD2 : 0 < 1 - D - t / 2 := by have : 0 < 2 - t := by linarith [ht.2]
                                         linarith
      have hr : (1 - D) / ((1 - D) ^ 2 - t ^ 2 / 2 ^ 2) ≤ 1 / (1 - D - t / 2) := by
        rw [div_le_div_iff₀ hq' hD2]
        have : (1 - D) ^ 2 - t ^ 2 / 2 ^ 2 = (1 - D - t / 2) * (1 - D + t / 2) := by ring
        rw [this]; nlinarith
      have hr0 : 0 ≤ (1 - D) / ((1 - D) ^ 2 - t ^ 2 / 2 ^ 2) := div_nonneg (by linarith) hq'.le
      calc (1 - wF t) ^ 2 * ((1 - D) / ((1 - D) ^ 2 - t ^ 2 / 2 ^ 2)) ^ 2
          ≤ (1 - wF t) ^ 2 * (1 / (1 - D - t / 2)) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hr 2) (sq_nonneg _)
        _ = (1 - wF t) ^ 2 / (1 - D - t / 2) ^ 2 := by rw [div_pow, one_pow, mul_one_div]
        _ ≤ _ := hinv t ht
  · refine integral_shell_le hu ?_ hinv
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
    exact continuousOn_div_sq (hcw.pow 2) (by fun_prop) fun t ht => by
      obtain ⟨h1, h2⟩ := hpt t ht
      have : 0 < 2 - t := by linarith [ht.2]
      linarith

/-! ### `T^loc` against `r₁♭ = R̄₁`: the collar, chirp and correction remainders -/

theorem Theta_ge {m : ℝ} (hm : 2 ≤ m) : √11 / 4 ≤ Cvs.L2a.CornerSuprema.Theta m := by
  have hcw := Cvs.L2a.CornerSuprema.continuous_one_sub_wF
  have hkey : ∀ t ∈ Icc (1 : ℝ) 2, (1 - wF t) ^ 2 ≤ (1 - wF t) ^ 2 / (1 - t ^ 2 / m ^ 2) ^ 2 := fun t ht => by
    have hm0 : 0 < m := by linarith
    have h1 : t ^ 2 / m ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith [ht.1, ht.2]
    have h0 : 0 ≤ t ^ 2 / m ^ 2 := by positivity
    rcases eq_or_lt_of_le h1 with h | h
    · -- `t = m = 2`, where the weight vanishes
      have ht2 : t = 2 := by
        rw [div_eq_one_iff_eq (by positivity)] at h
        nlinarith [ht.1, ht.2]
      have hw : 1 - wF t = 0 := by
        rw [ht2, (Cvs.L2a.FarIntegrationByParts.wF_of_two_le le_rfl).1]; ring
      rw [hw]; simp
    · have hq : 0 < 1 - t ^ 2 / m ^ 2 := by linarith
      have hq1 : (1 - t ^ 2 / m ^ 2) ^ 2 ≤ 1 := by nlinarith
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (1 - wF t), mul_le_mul_of_nonneg_left hq1 (sq_nonneg (1 - wF t))]
  have hI : ∫ t in (1 : ℝ)..2, (1 - wF t) ^ 2 ≤ ∫ t in (1 : ℝ)..2, (1 - wF t) ^ 2 / (1 - t ^ 2 / m ^ 2) ^ 2 := by
    refine intervalIntegral.integral_mono_on (by norm_num) ((hcw.pow 2).intervalIntegrable 1 2) ?_ hkey
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)]
    have := integrableOn_wsq (m := 2) le_rfl
    refine this.mono' (((hcw.pow 2).measurable.div (by fun_prop)).aestronglyMeasurable)
      ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun t ht => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h4 : 0 < 1 - t ^ 2 / ((2 : ℕ) : ℝ) ^ 2 := by
      push_cast; rw [sub_pos, div_lt_one (by norm_num)]; nlinarith [ht.1, ht.2]
    have hle : 1 - t ^ 2 / ((2 : ℕ) : ℝ) ^ 2 ≤ 1 - t ^ 2 / m ^ 2 := by
      push_cast
      have : t ^ 2 / m ^ 2 ≤ t ^ 2 / 2 ^ 2 :=
        div_le_div_of_nonneg_left (sq_nonneg t) (by norm_num) (pow_le_pow_left₀ (by norm_num) hm 2)
      linarith
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (pow_le_pow_left₀ h4.le hle 2)
  rw [Cvs.L2a.CornerSuprema.integral_weight_sq] at hI
  unfold Cvs.L2a.CornerSuprema.Theta
  calc √11 / 4 = √(11 / 16) := by
        rw [Real.sqrt_div' _ (by norm_num), show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    _ ≤ _ := Real.sqrt_le_sqrt hI

theorem dY_pos {X : ℝ} (hX : 1 < X) : 0 < Cvs.L2a.TopCornerConstants.dY X := by
  have hpos : 0 < X ^ 2 - 1 := by nlinarith
  have hs := Real.sqrt_pos.2 hpos
  have hsx : √(X ^ 2 - 1) < X := by
    rw [Real.sqrt_lt' (by linarith)]; linarith
  unfold Cvs.L2a.TopCornerConstants.dY Ymax
  rw [sub_pos, lt_div_iff₀ hs, one_mul]
  exact hsx

/-- `√(a² + C) ≤ a + min(√C, C/(2a))` for `a > 0`, `C ≥ 0`. -/
theorem sqrt_sq_add_le {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C) : √(a ^ 2 + C) ≤ a + min (√C) (C / (2 * a)) := by
  rw [← min_add_add_left]
  refine le_min ?_ ?_
  · refine (Cvs.L2a.CornerSuprema.sqrt_add_le_add (sq_nonneg a) hC).trans (le_of_eq ?_)
    rw [Real.sqrt_sq ha.le]
  · rw [Real.sqrt_le_left (by positivity)]
    have : (a + C / (2 * a)) ^ 2 = a ^ 2 + C + (C / (2 * a)) ^ 2 := by field_simp; ring
    rw [this]; nlinarith [sq_nonneg (C / (2 * a))]

theorem kappa_mul_sqrt_eq {c X : ℝ} (hc : 0 < c) :
    √(2 * c / π) * √(X / (π * c)) = √2 / π * √X := by
  have hπ := pi_pos
  rw [← Real.sqrt_mul (by positivity), div_mul_div_comm, show 2 * c * X / (π * (π * c)) = 2 * X / π ^ 2 by
    field_simp, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hπ.le, Real.sqrt_mul (by norm_num)]
  ring

/-- The collar budget of the corner `m`: `2κ_S Σ_k δ_k collSh_k` at `m = 2`, `2κ_Sδ(Θ_m^δ)²` beyond. -/
def collC (δ : ℝ) (u : ℕ → ℝ) (K m : ℕ) : ℝ :=
  if m = 2 then 2 * (181 / 462) * ∑ k ∈ Finset.range K, dK δ u k * collSh δ u k
  else 2 * (181 / 462) * δ * ThetaD δ m ^ 2

/-- The chirp budget of the corner `m`: `B₂` at `m = 2`, `B_m` beyond. -/
def chirpC (c J d δ s : ℝ) (u : ℕ → ℝ) (K M m : ℕ) : ℝ :=
  if m = 2 then Bloc2 c M d δ J s u K else Bloc c M d δ m J

/-- **The remainder of `T^loc` over `R̄₁`**: the collar `(√2/π)Σ_m min(√C_m, C_m/(2√ΔY Θ_m))/m`, the chirp
`Σ_m (2κ/m)√B_m`, and the correction `Σ_m corr_m`. -/
def remT (c J d δ s : ℝ) (u : ℕ → ℝ) (K M : ℕ) : ℝ :=
  √2 / π * ∑ m ∈ Finset.Icc 2 (M - 1),
      min (√(collC δ u K m)) (collC δ u K m / (2 * (√(Cvs.L2a.TopCornerConstants.dY M)
        * Cvs.L2a.CornerSuprema.Theta m))) / m
    + ∑ m ∈ Finset.Icc 2 (M - 1), 2 * √(2 * c / π) / m * √(chirpC c J d δ s u K M m)
    + ∑ m ∈ Finset.Icc 2 (M - 1), corrC c J M m

/-- **`T^loc ≤ R̄₁(M) + remainder`**, with `R̄₁ = r₁♭` of Cvs.L2a.CornerSuprema at `Θ₂ = Θ 2`. -/
theorem Tloc_le {c J d δ s : ℝ} {u : ℕ → ℝ} {K M : ℕ} (hc : 0 < c) (hM3 : 3 ≤ M) (hδ : 0 ≤ δ)
    (hdK : ∀ k, 0 ≤ dK δ u k) :
    Tloc c J d δ s u K M ≤ Cvs.L2a.CornerSuprema.R1bar (Cvs.L2a.CornerSuprema.Theta 2) M + remT c J d δ s u K M := by
  have hM3r : (3 : ℝ) ≤ M := by exact_mod_cast hM3
  have hdY := dY_pos (by linarith : (1 : ℝ) < M)
  have hdYe : Cvs.L2a.TopCornerConstants.dY M = Ymax M - 1 := rfl
  have hC0 : ∀ m, 0 ≤ collC δ u K m := fun m => by
    unfold collC; split_ifs
    · exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun k _ =>
        mul_nonneg (hdK k) (setIntegral_nonneg measurableSet_Ioc fun t _ => by positivity))
    · positivity
  -- each local term splits into the flat part and the collar and chirp budgets
  have hsplit : ∀ m ∈ Finset.Icc 2 (M - 1), locC c J d δ s u K M m
      ≤ √2 / π * √(Cvs.L2a.TopCornerConstants.dY M) * (Cvs.L2a.CornerSuprema.Theta m / m)
        + √2 / π * (min (√(collC δ u K m)) (collC δ u K m / (2 * (√(Cvs.L2a.TopCornerConstants.dY M)
          * Cvs.L2a.CornerSuprema.Theta m))) / m)
        + 2 * √(2 * c / π) / m * √(chirpC c J d δ s u K M m) := fun m hm => by
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.1 hm).1
    have hm0 : (0 : ℝ) < m := by linarith
    have hΘ := Theta_ge hm2
    have hΘ0 : 0 < Cvs.L2a.CornerSuprema.Theta m := lt_of_lt_of_le (by positivity) hΘ
    have ha : 0 < √(Cvs.L2a.TopCornerConstants.dY M) * Cvs.L2a.CornerSuprema.Theta m :=
      mul_pos (Real.sqrt_pos.2 hdY) hΘ0
    have hA : 2 * √(2 * c / π) / m * (√(((Ymax M - 1) * Cvs.L2a.CornerSuprema.Theta m ^ 2 + collC δ u K m)
          / (π * c)) / 2)
        ≤ √2 / π * √(Cvs.L2a.TopCornerConstants.dY M) * (Cvs.L2a.CornerSuprema.Theta m / m)
          + √2 / π * (min (√(collC δ u K m)) (collC δ u K m / (2 * (√(Cvs.L2a.TopCornerConstants.dY M)
            * Cvs.L2a.CornerSuprema.Theta m))) / m) := by
      have e : 2 * √(2 * c / π) / m * (√(((Ymax M - 1) * Cvs.L2a.CornerSuprema.Theta m ^ 2 + collC δ u K m)
          / (π * c)) / 2)
          = √2 / π * √((Ymax M - 1) * Cvs.L2a.CornerSuprema.Theta m ^ 2 + collC δ u K m) / m := by
        rw [show 2 * √(2 * c / π) / m * (√(((Ymax M - 1) * Cvs.L2a.CornerSuprema.Theta m ^ 2 + collC δ u K m)
            / (π * c)) / 2) = √(2 * c / π) * √(((Ymax M - 1) * Cvs.L2a.CornerSuprema.Theta m ^ 2 + collC δ u K m)
            / (π * c)) / m by field_simp, kappa_mul_sqrt_eq hc]
      rw [e]
      have hπ : 0 ≤ √2 / π := by positivity
      calc √2 / π * √((Ymax M - 1) * Cvs.L2a.CornerSuprema.Theta m ^ 2 + collC δ u K m) / m
          ≤ √2 / π * (√(Cvs.L2a.TopCornerConstants.dY M) * Cvs.L2a.CornerSuprema.Theta m
            + min (√(collC δ u K m)) (collC δ u K m / (2 * (√(Cvs.L2a.TopCornerConstants.dY M)
              * Cvs.L2a.CornerSuprema.Theta m)))) / m := by
            gcongr
            rw [← hdYe]
            calc √(Cvs.L2a.TopCornerConstants.dY M * Cvs.L2a.CornerSuprema.Theta m ^ 2 + collC δ u K m)
                = √((√(Cvs.L2a.TopCornerConstants.dY M) * Cvs.L2a.CornerSuprema.Theta m) ^ 2 + collC δ u K m) := by
                  rw [mul_pow, Real.sq_sqrt hdY.le]
              _ ≤ _ := sqrt_sq_add_le ha (hC0 m)
        _ = _ := by ring
    unfold locC chirpC
    split_ifs with h2
    · subst h2
      have e2 : Aloc2 c M δ u K = ((Ymax M - 1) * Cvs.L2a.CornerSuprema.Theta ((2 : ℕ) : ℝ) ^ 2
          + collC δ u K 2) / (π * c) := by
        unfold Aloc2 collC; rw [ite_eq_left rfl]; push_cast; ring
      rw [e2] at *
      have := hA
      push_cast at this ⊢
      linarith
    · have e3 : Aloc c M δ m = ((Ymax M - 1) * Cvs.L2a.CornerSuprema.Theta m ^ 2 + collC δ u K m) / (π * c) := by
        unfold Aloc collC; rw [ite_eq_right h2]
      rw [e3]
      linarith
  unfold Tloc remT
  rw [Finset.sum_add_distrib]
  have hflat := Cvs.L2a.CornerSuprema.r1flat_le Cvs.L2a.CornerSuprema.Theta
    (fun m hm => Cvs.L2a.CornerSuprema.Theta_le (by linarith))
    (le_trans (by positivity) (Theta_ge (le_refl 2))) M hM3
  rw [← Icc_eq_Ico (by omega)] at hflat
  have hsum := Finset.sum_le_sum hsplit
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  linarith

/-! ### The `ρ_t` form -/

/-- `sup_{3 ≤ M < X} f(M)⁺`. -/
def supBelow (f : ℕ → ℝ) (X : ℕ) : ℝ := (((Finset.Ico 3 X).sup fun M => (f M).toNNReal : NNReal) : ℝ)

theorem le_supBelow {f : ℕ → ℝ} {X M : ℕ} (hM : M ∈ Finset.Ico 3 X) : f M ≤ supBelow f X :=
  (Real.le_coe_toNNReal _).trans (NNReal.coe_le_coe.2 (Finset.le_sup (f := fun M => (f M).toNNReal) hM))

/-- `ρ_t = max(KcoBar, sup_{3 ≤ M < X_t} remT(M))`. -/
def rhoT (c J d δ s : ℝ) (u : ℕ → ℝ) (K Xt : ℕ) : ℝ :=
  max (KcoBar c J) (supBelow (fun M => remT c J d δ s u K M) Xt)

/-- `r₁(M) = R̄₁(M)` below the threshold `X_t`, `r₁^glob(M)` from it on. -/
def r1T (c J : ℝ) (Xt M : ℕ) : ℝ :=
  if M < Xt then Cvs.L2a.CornerSuprema.R1bar (Cvs.L2a.CornerSuprema.Theta 2) M
  else Cvs.L2a.CornerSuprema.r1globBar (kapI c J) (Cvs.L2a.CornerSuprema.Theta 2) M

/-- **LOC (top), `ρ_t` form**: `Σ_{m=2}^{M−1} |C_m| ≤ (r₁(M) + ρ_t)·P`. -/
theorem Dtop_flat_rho {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) {J d δ s : ℝ}
    {u : ℕ → ℝ} {K : ℕ} (Xt : ℕ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχi : Function.Injective χ)
    {M : ℕ} (hM3 : 3 ≤ M) (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..M, psi c (g i) t ^ 2) (hJ : (Fintype.card ι : ℝ) ≤ J)
    (hd : 0 < d) (hd1 : d ≤ 1) (hδ : 0 < δ) (hδ3 : δ < 1 / 3) (hs : 0 < s) (hs1 : s ≤ 1)
    (hu0 : u 0 = s) (huK : u K = 1) (hmono : Monotone u) :
    ∑ m ∈ Finset.Icc 2 (M - 1), |Cvs.L2a.CutKernels.cTop c χ g a M m|
      ≤ (r1T c J Xt M + rhoT c J d δ s u K Xt) * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hJ0 : 0 ≤ J := le_trans (Nat.cast_nonneg _) hJ
  have hP : 0 ≤ ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  refine (Dtop_flat a hg hg₁ hg₂c hang hc hχ0 hχc hχi hM3 hM hJ hd hd1 hδ hδ3 hs hs1 hu0 huK hmono).trans
    (mul_le_mul_of_nonneg_right ?_ hP)
  unfold r1T rhoT
  split_ifs with hX
  · have hdK : ∀ k, 0 ≤ dK δ u k := fun k => le_min hδ.le (by
      have := hu0 ▸ hmono (Nat.zero_le k); linarith)
    have h1 := Tloc_le (J := J) (d := d) (s := s) (K := K) hc0 hM3 hδ.le hdK
    have h2 : remT c J d δ s u K M ≤ supBelow (fun M => remT c J d δ s u K M) Xt :=
      le_supBelow (f := fun M => remT c J d δ s u K M) (Finset.mem_Ico.2 ⟨hM3, hX⟩)
    have h3 := le_max_right (KcoBar c J) (supBelow (fun M => remT c J d δ s u K M) Xt)
    exact (min_le_left _ _).trans (by linarith)
  · have h1 := sum_globC_le hc0 hJ0 hM3
    have h2 := sum_corrC_le hc0 hJ0 hM3
    have h3 := le_max_left (KcoBar c J) (supBelow (fun M => remT c J d δ s u K M) Xt)
    have e : Tglob c J M = ∑ m ∈ Finset.Icc 2 (M - 1), globC c J M m + ∑ m ∈ Finset.Icc 2 (M - 1), corrC c J M m := by
      unfold Tglob; rw [Finset.sum_add_distrib]
    exact (min_le_right _ _).trans (by rw [e]; linarith)

/-! ### The schedule `S*`: `δ = d = c^{−1/4}`, `s = (4/3)c^{−1/4}`, dyadic shells, `J ≤ c/4 + 1`, `X_t = 60` -/

/-- `δ(c) = c^{−1/4}`. -/
def deltaS (c : ℝ) : ℝ := c ^ (-(1 / 4 : ℝ))

/-- `s(c) = (4/3)c^{−1/4}`. -/
def sS (c : ℝ) : ℝ := 4 / 3 * deltaS c

/-- The dyadic shells `u_k = min(1, s·2^k)`. -/
def uS (c : ℝ) (k : ℕ) : ℝ := min 1 (sS c * 2 ^ k)

/-- The shell count `K = ⌈log₂(1/s)⌉`. -/
def KS (c : ℝ) : ℕ := ⌈Real.logb 2 (1 / sS c)⌉₊

theorem deltaS_pos {c : ℝ} (hc : 0 < c) : 0 < deltaS c := Real.rpow_pos_of_pos hc _

/-- `c ≥ 4096` gives `δ = c^{−1/4} ≤ 1/8`. -/
theorem deltaS_le {c : ℝ} (hc : 4096 ≤ c) : deltaS c ≤ 1 / 8 := by
  have hc0 : 0 < c := by linarith
  have h8 : (8 : ℝ) ≤ c ^ (1 / 4 : ℝ) := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 8 ^ 4) (show (8 : ℝ) ^ 4 ≤ c by norm_num; linarith)
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have e : ((8 : ℝ) ^ 4) ^ (1 / 4 : ℝ) = 8 := by
      rw [show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num, Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)]
    rwa [e] at h
  unfold deltaS
  rw [Real.rpow_neg hc0.le]
  rw [inv_le_comm₀ (by positivity) (by norm_num)]
  linarith

theorem sS_pos {c : ℝ} (hc : 0 < c) : 0 < sS c := by unfold sS; have := deltaS_pos hc; positivity

theorem sS_le {c : ℝ} (hc : 4096 ≤ c) : sS c ≤ 1 := by unfold sS; have := deltaS_le hc; linarith

theorem uS_zero {c : ℝ} (hc : 4096 ≤ c) : uS c 0 = sS c := by
  unfold uS; rw [pow_zero, mul_one]; exact min_eq_right (sS_le hc)

theorem uS_K {c : ℝ} (hc : 4096 ≤ c) : uS c (KS c) = 1 := by
  have hs := sS_pos (by linarith : 0 < c)
  unfold uS
  refine min_eq_left ?_
  have hK : Real.logb 2 (1 / sS c) ≤ (KS c : ℝ) := Nat.le_ceil _
  have h2 : (1 / sS c) ≤ (2 : ℝ) ^ (KS c) := by
    rw [← Real.rpow_natCast]
    calc 1 / sS c = (2 : ℝ) ^ Real.logb 2 (1 / sS c) :=
          (Real.rpow_logb (by norm_num) (by norm_num) (by positivity)).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hK
  rw [div_le_iff₀ hs] at h2
  linarith

theorem uS_mono {c : ℝ} (hc : 0 < c) : Monotone (uS c) := fun k l hkl => by
  have hs := sS_pos hc
  exact min_le_min le_rfl (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hkl) hs.le)

end Cvs.L2a.TopCornerSum
