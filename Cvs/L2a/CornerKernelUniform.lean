import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BandTransferBandForm
import Cvs.L2a.CutKernelRemainder
import Cvs.L2a.CutKernels
import Cvs.L2a.FarIntegrationByParts
import Cvs.L2a.OrbitGapIntegerM
import Cvs.L2a.QIdentityComplexWeight
import Cvs.L2a.QIdentityCutPoint
import Cvs.L2a.SigmaSquareMultiplier
import Cvs.L2a.TopCornerSum
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RungCauchySplit
import Cvs.Upstream.ExpDifferenceBound

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Lemma K quantitative, and `|𝔇|, |𝔈₁| ≤ γ·P` uniformly in `M`

On the orbit range `η ≥ M/m` the top kernel satisfies `|μ̃(ξ;η)| + |μ̃(−ξ;η)| ≤ 2A₀/(η − 1)` and, on the circle of
radius `(9/40)(η − 1)`, `≤ 2B₀/(η − 1)`; the count envelope and Cauchy's estimate bound `V_m, V_m′, V_m″`. Then
`𝔇` is the double boundary `𝒜̃² − (p/m)𝒜̃′Σaᵢψᵢ/Qᵢ` and `𝔈₁` the `σ²`-series about `c²`, summed by `ζ(s)`.
-/

noncomputable section

namespace Cvs.L2a.CornerKernelUniform

open Real Set Filter Topology MeasureTheory Complex
open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.AngularProlateTailPositive Cvs.L2a.FarIntegrationByParts Cvs.Prolate.RungCauchySplit Cvs.L2a.OrbitGapIntegerM Cvs.Prolate.Envelope.RungCountEnvelope Cvs.L2a.QIdentityComplexWeight Cvs.L2a.CutKernels Cvs.L2a.CutKernelRemainder
open scoped ComplexConjugate

/-! ### The orbit range -/

/-- **The orbit gap**: `10(M − m) ≤ (M² − 1)((M/m)² − 1)` for `2 ≤ m ≤ M − 1`. -/
theorem orbit_gap {M m : ℝ} (hm : 2 ≤ m) (hmM : m + 1 ≤ M) :
    10 * (M - m) ≤ (M ^ 2 - 1) * ((M / m) ^ 2 - 1) := by
  have hm0 : 0 < m := by linarith
  have he : (M / m) ^ 2 - 1 = (M - m) * (M + m) / m ^ 2 := by field_simp; ring
  rw [he, mul_div_assoc', le_div_iff₀ (by positivity)]
  have hj : 0 ≤ M - m := by linarith
  have key : 10 * m ^ 2 ≤ (M ^ 2 - 1) * (M + m) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ m - 2) (by linarith : (0 : ℝ) ≤ M - 1 - m),
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ M - 1) (by linarith : (0 : ℝ) ≤ 2 * M - 3))
        (by linarith : (0 : ℝ) ≤ M - 3)]
  nlinarith [mul_le_mul_of_nonneg_left key hj]

/-- `M/(M² − 1) ≤ 3/8` and `8 ≤ M² − 1` for `M ≥ 3`. -/
theorem pbar_facts {M : ℝ} (hM : 3 ≤ M) : M / (M ^ 2 - 1) ≤ 3 / 8 ∧ 8 ≤ M ^ 2 - 1 := by
  have h8 : 8 ≤ M ^ 2 - 1 := by nlinarith
  refine ⟨?_, h8⟩
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- `ξ ≤ c·Ymax x` gives `(x² − 1)ξ² ≤ c²x²`. -/
theorem sq_le_of_le_Ymax {c x ξ : ℝ} (hx : 1 < x) (hξ0 : 0 ≤ ξ) (hξ : ξ ≤ c * Ymax x) :
    (x ^ 2 - 1) * ξ ^ 2 ≤ c ^ 2 * x ^ 2 := by
  have hp : 0 < x ^ 2 - 1 := by nlinarith
  have hs : 0 < √(x ^ 2 - 1) := Real.sqrt_pos.2 hp
  have h1 : ξ * √(x ^ 2 - 1) ≤ c * x := by
    unfold Ymax at hξ
    rw [mul_div_assoc', le_div_iff₀ hs] at hξ
    exact hξ
  have h2 : (ξ * √(x ^ 2 - 1)) ^ 2 ≤ (c * x) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hξ0 hs.le) h1 2
  rw [mul_pow, Real.sq_sqrt hp.le] at h2
  nlinarith

/-- On the orbit range `η ≥ M/m`: `10 ≤ p(η² − 1)` and `4 ≤ p(η − 1)`, `p = M² − 1`. -/
theorem orbit_eta {M m η : ℝ} (hM : 3 ≤ M) (hm : 2 ≤ m) (hmM : m + 1 ≤ M) (hη : M / m ≤ η) :
    1 < η ∧ 10 ≤ (M ^ 2 - 1) * (η ^ 2 - 1) ∧ 4 ≤ (M ^ 2 - 1) * (η - 1) := by
  have hm0 : 0 < m := by linarith
  have hy1 : 1 < M / m := by rw [one_lt_div hm0]; linarith
  have hη1 : 1 < η := by linarith
  have hgap := orbit_gap hm hmM
  have hp : 0 ≤ M ^ 2 - 1 := by nlinarith
  refine ⟨hη1, ?_, ?_⟩
  · have h1 : (M / m) ^ 2 - 1 ≤ η ^ 2 - 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 hp]
  · have h1 : M / m - 1 ≤ η - 1 := by linarith
    have h2 : (M ^ 2 - 1) * (M / m - 1) = (M ^ 2 - 1) * (M - m) / m := by field_simp
    have h3 : 4 ≤ (M ^ 2 - 1) * (M - m) / m := by
      rw [le_div_iff₀ hm0]
      nlinarith [mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ M - m) hp]
    nlinarith [mul_le_mul_of_nonneg_left h1 hp]

/-! ### Lemma K: the top kernel on the orbit range -/

theorem qQkC_neg (c x ξ : ℝ) (z : ℂ) : Cvs.L2a.QIdentityCutPoint.qQkC c x (-ξ) z = Cvs.L2a.QIdentityCutPoint.qQkC c x ξ z := by
  unfold Cvs.L2a.QIdentityCutPoint.qQkC; push_cast; ring

/-- `‖ξ − cz‖ + ‖−ξ − cz‖ ≤ 2c(η + r)` for `0 ≤ ξ ≤ cη` and `‖z − η‖ ≤ r`. -/
theorem pair_lin_le {c ξ η r : ℝ} {z : ℂ} (hc : 0 ≤ c) (hξ : 0 ≤ ξ) (hξη : ξ ≤ c * η)
    (hz : ‖z - η‖ ≤ r) :
    ‖(ξ : ℂ) - c * z‖ + ‖(((-ξ : ℝ)) : ℂ) - c * z‖ ≤ 2 * c * (η + r) := by
  have hcz : ‖(c : ℂ) * (z - η)‖ ≤ c * r := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left hz hc
  have e1 : (ξ : ℂ) - c * z = ((ξ - c * η : ℝ) : ℂ) - c * (z - η) := by push_cast; ring
  have e2 : (((-ξ : ℝ)) : ℂ) - c * z = ((-ξ - c * η : ℝ) : ℂ) - c * (z - η) := by push_cast; ring
  have n1 : ‖(ξ : ℂ) - c * z‖ ≤ (c * η - ξ) + c * r := by
    rw [e1]
    refine (norm_sub_le _ _).trans (add_le_add (le_of_eq ?_) hcz)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]; ring
  have n2 : ‖(((-ξ : ℝ)) : ℂ) - c * z‖ ≤ (c * η + ξ) + c * r := by
    rw [e2]
    refine (norm_sub_le _ _).trans (add_le_add (le_of_eq ?_) hcz)
    have : 0 ≤ c * η := by linarith
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]; ring
  linarith

/-- `‖Q′(z)‖ ≤ 2c²x(η² − 1 + r(2η + r)) + 2c(η + r)` for `η ≥ 1`, `‖z − η‖ ≤ r`. -/
theorem norm_qQ₁C_le {c x η r : ℝ} {z : ℂ} (hc : 0 ≤ c) (hx : 0 ≤ x) (hη : 1 ≤ η) (hz : ‖z - η‖ ≤ r) :
    ‖Cvs.L2a.QIdentityCutPoint.qQ₁C c x z‖ ≤ 2 * c ^ 2 * x * (η ^ 2 - 1 + r * (2 * η + r)) + 2 * c * (η + r) := by
  have hr : 0 ≤ r := (norm_nonneg _).trans hz
  have hzn : ‖z‖ ≤ η + r := by
    calc ‖z‖ = ‖(z - η) + (η : ℂ)‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - η‖ + ‖(η : ℂ)‖ := norm_add_le _ _
      _ ≤ η + r := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith
  have hsum : ‖z + η‖ ≤ 2 * η + r := by
    calc ‖z + η‖ = ‖(z - η) + 2 * (η : ℂ)‖ := by ring_nf
      _ ≤ ‖z - η‖ + ‖2 * (η : ℂ)‖ := norm_add_le _ _
      _ ≤ 2 * η + r := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith), Complex.norm_ofNat]
          linarith
  have hz2 : ‖z ^ 2 - 1‖ ≤ η ^ 2 - 1 + r * (2 * η + r) := by
    have e : z ^ 2 - 1 = ((η ^ 2 - 1 : ℝ) : ℂ) + (z - η) * (z + η) := by push_cast; ring
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add (le_of_eq ?_) ?_)
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by nlinarith)]
    · rw [norm_mul]; exact mul_le_mul hz hsum (norm_nonneg _) hr
  unfold Cvs.L2a.QIdentityCutPoint.qQ₁C
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg hc, abs_of_nonneg hx, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left hz2 (by positivity)
  · rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc,
      Complex.norm_ofNat]
    nlinarith

/-- **The pair bound**: `‖μ̃(ξ;z)‖ + ‖μ̃(−ξ;z)‖ ≤ 2pc(η + r)/Q_m + 2p|Q′|/Q_m²` where `Q_m ≤ |Q(z)|`. -/
theorem muQC_pair_le {c x ξ η r Qm : ℝ} {z : ℂ} (hc : 0 ≤ c) (hx : 1 ≤ x) (hξ : 0 ≤ ξ) (hξη : ξ ≤ c * η)
    (hη : 1 ≤ η) (hz : ‖z - η‖ ≤ r) (hQm : 0 < Qm) (hQ : Qm ≤ ‖Cvs.L2a.QIdentityCutPoint.qQkC c x ξ z‖) :
    ‖Cvs.L2a.QIdentityCutPoint.muQC c x ξ z‖ + ‖Cvs.L2a.QIdentityCutPoint.muQC c x (-ξ) z‖
      ≤ 2 * pP x * c * (η + r) / Qm
        + 2 * pP x * (2 * c ^ 2 * x * (η ^ 2 - 1 + r * (2 * η + r)) + 2 * c * (η + r)) / Qm ^ 2 := by
  have hp : 0 ≤ pP x := by unfold pP; nlinarith
  have hQn : 0 < ‖Cvs.L2a.QIdentityCutPoint.qQkC c x ξ z‖ := hQm.trans_le hQ
  have hQ' : Qm ≤ ‖Cvs.L2a.QIdentityCutPoint.qQkC c x (-ξ) z‖ := by rw [qQkC_neg]; exact hQ
  have h1 := norm_qQ₁C_le (x := x) hc (by linarith) hη hz
  have hl := pair_lin_le hc hξ hξη hz
  have hr : 0 ≤ r := (norm_nonneg _).trans hz
  have hN0 : 0 ≤ 2 * c ^ 2 * x * (η ^ 2 - 1 + r * (2 * η + r)) + 2 * c * (η + r) := by
    have : 0 ≤ η ^ 2 - 1 + r * (2 * η + r) := by nlinarith
    have : 0 ≤ η + r := by linarith
    positivity
  set N := 2 * c ^ 2 * x * (η ^ 2 - 1 + r * (2 * η + r)) + 2 * c * (η + r)
  have one : ∀ ζ : ℝ, Qm ≤ ‖Cvs.L2a.QIdentityCutPoint.qQkC c x ζ z‖ →
      ‖Cvs.L2a.QIdentityCutPoint.muQC c x ζ z‖ ≤ pP x * (‖(ζ : ℂ) - c * z‖ / Qm + N / Qm ^ 2) := by
    intro ζ hζ
    have hζ0 : 0 < ‖Cvs.L2a.QIdentityCutPoint.qQkC c x ζ z‖ := hQm.trans_le hζ
    unfold Cvs.L2a.QIdentityCutPoint.muQC
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp]
    refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add ?_ ?_)) hp
    · rw [norm_div, norm_mul, Complex.norm_I, one_mul]
      exact div_le_div_of_nonneg_left (norm_nonneg _) hQm hζ
    · rw [norm_div, norm_pow]
      exact div_le_div₀ hN0 h1 (by positivity) (pow_le_pow_left₀ hQm.le hζ 2)
  have a := one ξ hQ
  have b := one (-ξ) hQ'
  calc ‖Cvs.L2a.QIdentityCutPoint.muQC c x ξ z‖ + ‖Cvs.L2a.QIdentityCutPoint.muQC c x (-ξ) z‖
      ≤ pP x * (‖(ξ : ℂ) - c * z‖ / Qm + N / Qm ^ 2) + pP x * (‖(((-ξ : ℝ)) : ℂ) - c * z‖ / Qm + N / Qm ^ 2) :=
        add_le_add a b
    _ = pP x * (‖(ξ : ℂ) - c * z‖ + ‖(((-ξ : ℝ)) : ℂ) - c * z‖) / Qm + 2 * pP x * N / Qm ^ 2 := by ring
    _ ≤ pP x * (2 * c * (η + r)) / Qm + 2 * pP x * N / Qm ^ 2 := by gcongr
    _ = _ := by ring

/-- `Re Q(ξ;η) ≥ c²(p(η² − 1) − 1)` for `pξ² ≤ c²x²`, `p = x² − 1`. -/
theorem re_qQkC_ge {c x ξ η : ℝ} (hξ : (x ^ 2 - 1) * ξ ^ 2 ≤ c ^ 2 * x ^ 2) :
    c ^ 2 * ((x ^ 2 - 1) * (η ^ 2 - 1) - 1) ≤ pP x * (c ^ 2 * η ^ 2 - ξ ^ 2) := by
  unfold pP; nlinarith

/-- The real-axis lower bound `(9/10)c²p(η² − 1) ≤ ‖Q(ξ;η)‖`, with `ξ ≤ cη`. -/
theorem norm_qQkC_real_ge {c x ξ η : ℝ} (hx : 1 ≤ x) (hξ : (x ^ 2 - 1) * ξ ^ 2 ≤ c ^ 2 * x ^ 2)
    (hc : 0 < c) (hη : 1 < η) (h10 : 10 ≤ (x ^ 2 - 1) * (η ^ 2 - 1)) :
    9 / 10 * (c ^ 2 * ((x ^ 2 - 1) * (η ^ 2 - 1))) ≤ ‖Cvs.L2a.QIdentityCutPoint.qQkC c x ξ (η : ℂ)‖ ∧ ξ ≤ c * η := by
  have hre := re_qQkC_ge (η := η) hξ
  have hn := Cvs.L2a.QIdentityCutPoint.le_norm_qQk_re (c := c) (y := η) (ξ := ξ) hx
  rw [qQkC_ofReal]
  have hp : 0 < pP x := by unfold pP; nlinarith
  have hc2 : 0 < c ^ 2 := by positivity
  have hpos : 0 < c ^ 2 * η ^ 2 - ξ ^ 2 := by
    by_contra h
    push Not at h
    have : pP x * (c ^ 2 * η ^ 2 - ξ ^ 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp.le h
    nlinarith
  refine ⟨?_, ?_⟩
  · rw [abs_of_pos hpos] at hn
    nlinarith
  · by_contra h
    push Not at h
    have hcη : 0 ≤ c * η := by positivity
    have := mul_lt_mul'' h h hcη hcη
    nlinarith

/-- `‖Q(ξ;z)‖ ≥ (9/40)c²p(η² − 1)` on `‖z − η‖ ≤ (9/40)(η − 1)`, for `c ≥ 1`, `x ≥ 3`. -/
theorem norm_qQkC_disc_ge {c x ξ η : ℝ} {z : ℂ} (hc : 1 ≤ c) (hx : 3 ≤ x)
    (hξ : (x ^ 2 - 1) * ξ ^ 2 ≤ c ^ 2 * x ^ 2) (hη : 1 < η) (h10 : 10 ≤ (x ^ 2 - 1) * (η ^ 2 - 1))
    (hz : ‖z - η‖ ≤ 9 / 40 * (η - 1)) :
    9 / 40 * (c ^ 2 * ((x ^ 2 - 1) * (η ^ 2 - 1))) ≤ ‖Cvs.L2a.QIdentityCutPoint.qQkC c x ξ z‖ := by
  have hc0 : 0 < c := by linarith
  obtain ⟨hre, -⟩ := norm_qQkC_real_ge (by linarith) hξ hc0 hη h10
  have hd := norm_qQkC_ge_on_disc (ξ := ξ) hc0.le (by linarith : (1 : ℝ) ≤ x) hz
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at hd
  obtain ⟨hν, h8⟩ := pbar_facts hx
  have hp : 0 < x ^ 2 - 1 := by linarith
  have hxp : x ≤ 3 / 8 * (x ^ 2 - 1) := by rwa [div_le_iff₀ hp] at hν
  set g := η - 1 with hg
  have hg0 : 0 < g := by linarith
  have hηg : η = g + 1 := by rw [hg]; ring
  have he : η ^ 2 - 1 = g * (g + 2) := by rw [hηg]; ring
  -- `r(pc²(2η + r)) ≤ (89/160)·c²p(η² − 1)` and `r·2cx ≤ (27/320)·c²p(η² − 1)`
  have t1 : 9 / 40 * g * (2 * η + 9 / 40 * g) ≤ 89 / 160 * (η ^ 2 - 1) := by
    rw [he, hηg]; nlinarith
  have t2 : 9 / 40 * g * (2 * c * x) ≤ 27 / 320 * (c ^ 2 * ((x ^ 2 - 1) * (η ^ 2 - 1))) := by
    rw [he]
    have h1 : 9 / 40 * g * (2 * c * x) ≤ 9 / 40 * g * (2 * c * (3 / 8 * (x ^ 2 - 1))) := by gcongr
    have h2 : c * ((x ^ 2 - 1) * g) ≤ c ^ 2 * ((x ^ 2 - 1) * g) := by
      have : 0 ≤ (x ^ 2 - 1) * g := by positivity
      have hcc : c ≤ c ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right hcc this
    have h3 : (x ^ 2 - 1) * g * 2 ≤ (x ^ 2 - 1) * (g * (g + 2)) := by
      have : 0 ≤ (x ^ 2 - 1) * g := by positivity
      nlinarith
    nlinarith
  have hpc : pP x * c ^ 2 = c ^ 2 * (x ^ 2 - 1) := by unfold pP; ring
  have e3 : 9 / 40 * (η - 1) * (pP x * c ^ 2 * (2 * η + 9 / 40 * (η - 1)) + 2 * c * x)
      = c ^ 2 * (x ^ 2 - 1) * (9 / 40 * g * (2 * η + 9 / 40 * g)) + 9 / 40 * g * (2 * c * x) := by
    rw [hpc, hg]; ring
  rw [e3] at hd
  have hcp : 0 ≤ c ^ 2 * (x ^ 2 - 1) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left t1 hcp]

/-- The real-axis algebra: the pair bound at `r = 0`, `Q_m = (9/10)c²p(η² − 1)`, is at most `2A₀/(η − 1)`. -/
theorem K_real_alg {c x p η : ℝ} (hc : 1 ≤ c) (hx0 : 0 ≤ x) (hxp : x ≤ 3 / 8 * p) (hη : 1 < η)
    (h4 : 4 ≤ p * (η - 1)) :
    2 * p * c * (η + 0) / (9 / 10 * (c ^ 2 * (p * (η ^ 2 - 1))))
        + 2 * p * (2 * c ^ 2 * x * (η ^ 2 - 1 + 0 * (2 * η + 0)) + 2 * c * (η + 0))
          / (9 / 10 * (c ^ 2 * (p * (η ^ 2 - 1)))) ^ 2
      ≤ 2 * (A0 c (9 / 10) (1 / 4) / (η - 1)) := by
  simp only [add_zero, zero_mul]
  have hc0 : 0 < c := by linarith
  set g := η - 1 with hg
  have hg0 : 0 < g := by linarith
  have hηg : η = g + 1 := by rw [hg]; ring
  have hp : 0 < p := by nlinarith
  set e := η ^ 2 - 1 with he'
  have he : e = g * (g + 2) := by rw [he', hηg]; ring
  have he0 : 0 < e := by rw [he]; positivity
  have L1 : 2 * p * c * η / (9 / 10 * (c ^ 2 * (p * e))) = 2 * η / (9 / 10 * c * e) := by
    field_simp
  have L2 : 2 * p * (2 * c ^ 2 * x * e + 2 * c * η) / (9 / 10 * (c ^ 2 * (p * e))) ^ 2
      = 4 * x / (81 / 100 * c ^ 2 * p * e) + 4 * η / (81 / 100 * c ^ 3 * p * e ^ 2) := by
    field_simp; ring
  rw [L1, L2]
  have hc2 : 0 < c ^ 2 := by positivity
  have hc3 : 0 < c ^ 3 := by positivity
  have a1 : 2 * η / (9 / 10 * c * e) ≤ 20 / 9 / (c * g) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : η * g ≤ e := by rw [he, hηg]; nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this hc0.le]
  have a2 : 4 * x / (81 / 100 * c ^ 2 * p * e) ≤ 3 / 4 / (81 / 100 * c ^ 2 * g) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h2 : 2 * g ≤ e := by rw [he]; nlinarith
    have h3 : x * g ≤ 3 / 8 * p * g := mul_le_mul_of_nonneg_right hxp hg0.le
    have h5 : 3 / 8 * p * (2 * g) ≤ 3 / 8 * p * e := mul_le_mul_of_nonneg_left h2 (by positivity)
    have key : 4 * (x * g) ≤ 3 / 4 * (p * e) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left key hc2.le]
  have a3 : 4 * η / (81 / 100 * c ^ 3 * p * e ^ 2) ≤ 1 / 2 / (81 / 100 * c ^ 3 * g) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : 4 * g * (g + 2) ^ 2 ≤ p * e ^ 2 := by
      rw [he]
      have : 4 * g ≤ p * g * g := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right this (sq_nonneg (g + 2))]
    have h2 : 8 * (η * g) ≤ 4 * g * (g + 2) ^ 2 := by rw [hηg]; nlinarith
    have key : 4 * (η * g) ≤ 1 / 2 * (p * e ^ 2) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left key hc3.le]
  have e2 : 2 * (A0 c (9 / 10) (1 / 4) / g)
      = 20 / 9 / (c * g) + 3 / 4 / (81 / 100 * c ^ 2 * g) + 1 / 2 / (81 / 100 * c ^ 3 * g) := by
    unfold A0; field_simp; ring
  rw [e2]
  linarith

/-- The circle algebra: at `r = (9/40)(η − 1)`, `Q_m = (9/40)c²p(η² − 1)`, the pair bound is at most `2B₀/(η − 1)`. -/
theorem K_circle_alg {c x p η : ℝ} (hc : 1 ≤ c) (hx0 : 0 ≤ x) (hxp : x ≤ 3 / 8 * p) (hη : 1 < η)
    (h4 : 4 ≤ p * (η - 1)) :
    2 * p * c * (η + 9 / 40 * (η - 1)) / (9 / 40 * (c ^ 2 * (p * (η ^ 2 - 1))))
        + 2 * p * (2 * c ^ 2 * x * (η ^ 2 - 1 + 9 / 40 * (η - 1) * (2 * η + 9 / 40 * (η - 1)))
            + 2 * c * (η + 9 / 40 * (η - 1))) / (9 / 40 * (c ^ 2 * (p * (η ^ 2 - 1)))) ^ 2
      ≤ 2 * (B0 c (9 / 10) 24 / (η - 1)) := by
  have hc0 : 0 < c := by linarith
  set g := η - 1 with hg
  have hg0 : 0 < g := by linarith
  have hηg : η = g + 1 := by rw [hg]; ring
  have hp : 0 < p := by nlinarith
  set e := η ^ 2 - 1 with he'
  have he : e = g * (g + 2) := by rw [he', hηg]; ring
  have he0 : 0 < e := by rw [he]; positivity
  set r := 9 / 40 * g with hr
  have hr0 : 0 ≤ r := by positivity
  have key3 : 4 * ((η + r) * g) ≤ 3 * (p * e ^ 2) := by
    have h1 : 4 * g * (g + 2) ^ 2 ≤ p * e ^ 2 := by
      have hg2 : 0 ≤ g * (g + 2) ^ 2 := by positivity
      have : 4 * (g * (g + 2) ^ 2) ≤ (p * g) * (g * (g + 2) ^ 2) := mul_le_mul_of_nonneg_right h4 hg2
      rw [he]; linarith
    have h2' : g + 1 + 9 / 40 * g ≤ 3 * (g + 2) ^ 2 := by nlinarith [sq_nonneg g]
    have h2 : (η + r) * g ≤ 3 * (g * (g + 2) ^ 2) := by
      have := mul_le_mul_of_nonneg_right h2' hg0.le
      have e5 : (η + r) * g = (g + 1 + 9 / 40 * g) * g := by rw [hr, hηg]
      rw [e5]; linarith
    linarith
  have L1 : 2 * p * c * (η + r) / (9 / 40 * (c ^ 2 * (p * e))) = 2 * (η + r) / (9 / 40 * c * e) := by
    field_simp
  have L2 : 2 * p * (2 * c ^ 2 * x * (e + r * (2 * η + r)) + 2 * c * (η + r)) / (9 / 40 * (c ^ 2 * (p * e))) ^ 2
      = 4 * x * (e + r * (2 * η + r)) / (81 / 1600 * c ^ 2 * p * e ^ 2)
        + 4 * (η + r) / (81 / 1600 * c ^ 3 * p * e ^ 2) := by
    field_simp; ring
  rw [L1, L2]
  have hc2 : 0 < c ^ 2 := by positivity
  have hc3 : 0 < c ^ 3 := by positivity
  have a1 : 2 * (η + r) / (9 / 40 * c * e) ≤ 400 / 9 / (c * g) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (η + r) * g ≤ 5 * e := by rw [he, hηg, hr]; nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this hc0.le]
  have hrr : r * (2 * η + r) ≤ 89 / 160 * e := by rw [he, hηg, hr]; nlinarith
  have a2 : 4 * x * (e + r * (2 * η + r)) / (81 / 1600 * c ^ 2 * p * e ^ 2) ≤ 108 / (81 / 100 * c ^ 2 * g) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (e + r * (2 * η + r)) * g ≤ 249 / 160 * e * g := by nlinarith
    have h2 : 249 / 160 * e * g ≤ 9 / 2 * e ^ 2 := by
      have : 2 * g ≤ e := by rw [he]; nlinarith
      nlinarith
    have h3 : x * ((e + r * (2 * η + r)) * g) ≤ 3 / 8 * p * (9 / 2 * e ^ 2) :=
      mul_le_mul hxp (h1.trans h2) (mul_nonneg (add_nonneg he0.le (mul_nonneg hr0 (by linarith))) hg0.le)
        (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left h3 hc2.le]
  have a3 : 4 * (η + r) / (81 / 1600 * c ^ 3 * p * e ^ 2) ≤ 48 / (81 / 100 * c ^ 3 * g) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_left key3 hc3.le
    linarith
  have e2 : 2 * (B0 c (9 / 10) 24 / g)
      = 400 / 9 / (c * g) + 108 / (81 / 100 * c ^ 2 * g) + 48 / (81 / 100 * c ^ 3 * g) := by
    unfold B0; field_simp; ring
  rw [e2]
  linarith

/-- **Lemma K (a)**: `‖Q(±ξ;z)‖ ≥ (9/40)c²p(η² − 1) > 0` on `‖z − η‖ ≤ (9/40)(η − 1)`, `η ≥ M/m`, `0 ≤ ξ ≤ cY`. -/
theorem lemmaK_disc {c M m η ξ : ℝ} {z : ℂ} (hc : 1 ≤ c) (hM : 3 ≤ M) (hm : 2 ≤ m) (hmM : m + 1 ≤ M)
    (hη : M / m ≤ η) (hξ0 : 0 ≤ ξ) (hξ : ξ ≤ c * Ymax M) (hz : ‖z - η‖ ≤ 9 / 40 * (η - 1)) :
    0 < 9 / 40 * (c ^ 2 * ((M ^ 2 - 1) * (η ^ 2 - 1)))
      ∧ 9 / 40 * (c ^ 2 * ((M ^ 2 - 1) * (η ^ 2 - 1))) ≤ ‖Cvs.L2a.QIdentityCutPoint.qQkC c M ξ z‖ := by
  obtain ⟨hη1, h10, -⟩ := orbit_eta hM hm hmM hη
  have hξ' := sq_le_of_le_Ymax (by linarith) hξ0 hξ
  have hc0 : (0 : ℝ) < c := by linarith
  have hp : 0 < M ^ 2 - 1 := by nlinarith
  have he : 0 < η ^ 2 - 1 := by nlinarith
  exact ⟨by positivity, norm_qQkC_disc_ge hc hM hξ' hη1 h10 hz⟩

/-- **Lemma K (b)**: `‖μ̃(ξ;η)‖ + ‖μ̃(−ξ;η)‖ ≤ 2A₀/(η − 1)` for `η ≥ M/m`, `0 ≤ ξ ≤ cY`. -/
theorem lemmaK_real {c M m η ξ : ℝ} (hc : 1 ≤ c) (hM : 3 ≤ M) (hm : 2 ≤ m) (hmM : m + 1 ≤ M)
    (hη : M / m ≤ η) (hξ0 : 0 ≤ ξ) (hξ : ξ ≤ c * Ymax M) :
    ‖Cvs.L2a.QIdentityCutPoint.muQC c M ξ η‖ + ‖Cvs.L2a.QIdentityCutPoint.muQC c M (-ξ) η‖ ≤ 2 * (A0 c (9 / 10) (1 / 4) / (η - 1)) := by
  obtain ⟨hη1, h10, h4⟩ := orbit_eta hM hm hmM hη
  have hξ' := sq_le_of_le_Ymax (by linarith) hξ0 hξ
  have hc0 : 0 < c := by linarith
  obtain ⟨hQ, hξη⟩ := norm_qQkC_real_ge (by linarith) hξ' hc0 hη1 h10
  obtain ⟨hν, h8⟩ := pbar_facts hM
  have hxp : M ≤ 3 / 8 * (M ^ 2 - 1) := by rwa [div_le_iff₀ (by linarith)] at hν
  have h := muQC_pair_le (r := 0) (z := (η : ℂ)) hc0.le (by linarith) hξ0 hξη hη1.le (by simp)
    (by have : (0 : ℝ) < M ^ 2 - 1 := by linarith
        have : 0 < η ^ 2 - 1 := by nlinarith
        positivity) hQ
  refine h.trans ?_
  have := K_real_alg (x := M) (p := M ^ 2 - 1) hc (by linarith) hxp hη1 h4
  unfold pP
  exact this

/-- **Lemma K (c)**: `‖μ̃(ξ;z)‖ + ‖μ̃(−ξ;z)‖ ≤ 2B₀/(η − 1)` on `‖z − η‖ ≤ (9/40)(η − 1)`. -/
theorem lemmaK_circle {c M m η ξ : ℝ} {z : ℂ} (hc : 1 ≤ c) (hM : 3 ≤ M) (hm : 2 ≤ m) (hmM : m + 1 ≤ M)
    (hη : M / m ≤ η) (hξ0 : 0 ≤ ξ) (hξ : ξ ≤ c * Ymax M) (hz : ‖z - η‖ ≤ 9 / 40 * (η - 1)) :
    ‖Cvs.L2a.QIdentityCutPoint.muQC c M ξ z‖ + ‖Cvs.L2a.QIdentityCutPoint.muQC c M (-ξ) z‖ ≤ 2 * (B0 c (9 / 10) 24 / (η - 1)) := by
  obtain ⟨hη1, h10, h4⟩ := orbit_eta hM hm hmM hη
  have hξ' := sq_le_of_le_Ymax (by linarith) hξ0 hξ
  have hc0 : 0 < c := by linarith
  obtain ⟨-, hξη⟩ := norm_qQkC_real_ge (by linarith) hξ' hc0 hη1 h10
  obtain ⟨hQ0, hQ⟩ := lemmaK_disc hc hM hm hmM hη hξ0 hξ hz
  obtain ⟨hν, h8⟩ := pbar_facts hM
  have hxp : M ≤ 3 / 8 * (M ^ 2 - 1) := by rwa [div_le_iff₀ (by linarith)] at hν
  have h := muQC_pair_le hc0.le (by linarith) hξ0 hξη hη1.le hz hQ0 hQ
  refine h.trans ?_
  have := K_circle_alg (x := M) (p := M ^ 2 - 1) hc (by linarith) hxp hη1 h4
  unfold pP
  exact this

/-! ### The `ζ` sums over the cuts and the boundary term in `(w, w′)` -/

/-- `Σ_{2 ≤ m ≤ M − 1} (M − m)^{−s} ≤ ζ(s)` for `s > 1`. -/
theorem sum_inv_rpow_le {M : ℕ} {s : ℝ} (hs : 1 < s) :
    ∑ m ∈ Finset.Icc 2 (M - 1), 1 / ((M : ℝ) - m) ^ s ≤ zR s := by
  have e : ∑ m ∈ Finset.Icc 2 (M - 1), 1 / ((M : ℝ) - m) ^ s
      = ∑ n ∈ Finset.range (M - 2), 1 / ((n : ℝ) + 1) ^ s := by
    refine Finset.sum_nbij' (fun m => M - 1 - m) (fun n => M - 1 - n) ?_ ?_ ?_ ?_ ?_
    · intro m hm; simp only [Finset.mem_Icc, Finset.mem_range] at hm ⊢; omega
    · intro n hn; simp only [Finset.mem_Icc, Finset.mem_range] at hn ⊢; omega
    · intro m hm; simp only [Finset.mem_Icc] at hm; omega
    · intro n hn; simp only [Finset.mem_range] at hn; omega
    · intro m hm
      simp only [Finset.mem_Icc] at hm
      have : ((M - 1 - m : ℕ) : ℝ) + 1 = (M : ℝ) - m := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
      rw [this]
  rw [e]
  have hsum : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ s) := by
    have h := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_rpow.2 hs)
    simpa using h
  exact hsum.sum_le_tsum _ (fun n _ => by positivity)

/-- The natural-power form of `sum_inv_rpow_le`. -/
theorem sum_inv_pow_le {M : ℕ} {k : ℕ} (hk : 2 ≤ k) :
    ∑ m ∈ Finset.Icc 2 (M - 1), 1 / ((M : ℝ) - m) ^ k ≤ zR k := by
  have h := sum_inv_rpow_le (M := M) (s := k) (by exact_mod_cast hk)
  refine le_of_eq_of_le (Finset.sum_congr rfl fun m _ => ?_) h
  rw [Real.rpow_natCast]

/-- **The boundary term is affine in `(w(x), w′(x))`**: `B[w] = w(x)B[1] − w′(x)e^{icxy}pψ/Q`. -/
theorem bBc_lin {w w₁ : ℝ → ℂ} {c χ y x : ℝ} {g : ℝ → ℝ} (hQ : qQ c χ y x ≠ 0) :
    bBc w w₁ c χ g y x
      = w x * bBc (fun _ => 1) (fun _ => 0) c χ g y x
        - w₁ x * (eF c y x * ((pP x : ℝ) : ℂ) * (psi c g x : ℂ) / qQ c χ y x) := by
  unfold bBc gWc gWc₁
  field_simp
  ring

/-! ### The `t`-profiles on `(M, ∞)` and the far atoms on the orbit -/

/-- `∫_{(M,∞)} (t − m)^{−(n+2)} = 1/((n + 1)(M − m)^{n+1})` for `m < M`. -/
theorem integral_Ioi_inv_sub_pow {m M : ℝ} (hmM : m < M) (n : ℕ) :
    IntegrableOn (fun t : ℝ => 1 / (t - m) ^ (n + 2)) (Ioi M)
      ∧ ∫ t in Ioi M, 1 / (t - m) ^ (n + 2) = 1 / ((n + 1) * (M - m) ^ (n + 1)) := by
  set F : ℝ → ℝ := fun t => -(1 / ((n + 1) * (t - m) ^ (n + 1))) with hF
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hd : ∀ t ∈ Ici M, HasDerivAt F (1 / (t - m) ^ (n + 2)) t := by
    intro t ht
    have htm : t - m ≠ 0 := by have : M ≤ t := ht; linarith
    have h1 : HasDerivAt (fun t : ℝ => (n + 1) * (t - m) ^ (n + 1))
        ((n + 1) * ((n + 1 : ℕ) * (t - m) ^ n * 1)) t :=
      (((hasDerivAt_id t).sub_const m).pow (n + 1)).const_mul _
    have h2 := (h1.inv (by positivity)).neg
    refine h2.congr_deriv ?_ |>.congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
    · push_cast; field_simp; ring
    · simp only [hF, one_div, Pi.neg_apply, Pi.inv_apply]
  have hlim : Tendsto F atTop (𝓝 0) := by
    have h0 : Tendsto (fun t : ℝ => t - m) atTop atTop :=
      (tendsto_atTop_add_const_right _ (-m) tendsto_id).congr fun t => by simp [sub_eq_add_neg]
    have h1 : Tendsto (fun t : ℝ => (n + 1) * (t - m) ^ (n + 1)) atTop atTop :=
      ((tendsto_pow_atTop (show n + 1 ≠ 0 by omega)).comp h0).const_mul_atTop hn
    have h2 := (tendsto_inv_atTop_zero.comp h1).neg
    simpa [hF, one_div] using h2
  have hint : IntegrableOn (fun t : ℝ => 1 / (t - m) ^ (n + 2)) (Ioi M) :=
    integrableOn_Ioi_deriv_of_nonneg (hd M self_mem_Ici).continuousAt.continuousWithinAt
      (fun t ht => hd t (mem_Ici_of_Ioi ht))
      (fun t ht => by have : M < t := ht; have : 0 < t - m := by linarith
                      positivity) hlim
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hd hint hlim]
  simp [hF]

/-- The profile `fₖ(t) = 1/|t − m|^k` on `(M, ∞)`: `L²`, with `∫fₖ² = 1/((2k − 1)(M − m)^{2k−1})`. -/
theorem prof_memLp {m M : ℝ} (hmM : m < M) {k : ℕ} (hk : 1 ≤ k) :
    MemLp (fun t : ℝ => 1 / |t - m| ^ k) 2 (volume.restrict (Ioi M))
      ∧ ∫ t in Ioi M, (1 / |t - m| ^ k) ^ 2 = 1 / ((2 * k - 1) * (M - m) ^ (2 * k - 1)) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hsq : ∀ t : ℝ, (1 / |t - m| ^ (n + 1)) ^ 2 = 1 / (t - m) ^ (2 * n + 2) := fun t => by
    rw [div_pow, one_pow, ← pow_mul, show (n + 1) * 2 = 2 * n + 2 by ring, pow_abs,
      abs_of_nonneg (Even.pow_nonneg ⟨n + 1, by ring⟩ _)]
  obtain ⟨hI, hV⟩ := integral_Ioi_inv_sub_pow hmM (2 * n)
  have hmeas : AEStronglyMeasurable (fun t : ℝ => 1 / |t - m| ^ (n + 1)) (volume.restrict (Ioi M)) :=
    (by fun_prop : Measurable fun t : ℝ => 1 / |t - m| ^ (n + 1)).aestronglyMeasurable
  refine ⟨(memLp_two_iff_integrable_sq hmeas).2 ?_, ?_⟩
  · simp_rw [hsq]; exact hI
  · simp_rw [hsq]
    rw [hV]
    push_cast
    rw [show 2 * n + 1 = 2 * (n + 1) - 1 by omega]
    ring_nf

/-- The far coefficients on the orbit, `y = M/m`, `t ≥ M`: the `k_E`, `k_E′` factors and `y/ε, 1/ε ≤ M/(2j)`. -/
theorem orbit_coeffs {c M m t : ℝ} (hc : 0 < c) (hM : 3 ≤ M) (hm : 2 ≤ m) (hmM : m + 1 ≤ M) (ht : M ≤ t) :
    2 * t + 2 * (c * (M / m)) * (t ^ 2 - 1) ≤ 2 * c * (M / m) * (t ^ 2 - 1) * (1 + 3 / (8 * c))
      ∧ 2 * c ^ 2 * t * ((M / m) ^ 2 - 1) + 2 * c * (M / m) ≤ 2 * c ^ 2 * t * ((M / m) ^ 2 - 1) * (1 + 1 / (2 * c))
      ∧ (M / m) / ((M / m) ^ 2 - 1) ≤ M / (2 * (M - m))
      ∧ 1 / ((M / m) ^ 2 - 1) ≤ M / (2 * (M - m))
      ∧ t / (t ^ 2 - 1) ≤ M / (M ^ 2 - 1)
      ∧ 1 / (t ^ 2 - 1) ≤ 1 / (M ^ 2 - 1) := by
  have hm0 : 0 < m := by linarith
  have hy1 : 1 ≤ M / m := by rw [le_div_iff₀ hm0]; linarith
  have he : (M / m) ^ 2 - 1 = (M - m) * (M + m) / m ^ 2 := by field_simp; ring
  have hj : 0 < M - m := by linarith
  have hε : 0 < (M / m) ^ 2 - 1 := by rw [he]; positivity
  have ht1 : 0 < t ^ 2 - 1 := by nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h8 : 8 * t ≤ 3 * (t ^ 2 - 1) := by nlinarith
    have : 2 * t ≤ 3 / 4 * (M / m) * (t ^ 2 - 1) := by nlinarith
    have e : 2 * c * (M / m) * (t ^ 2 - 1) * (1 + 3 / (8 * c))
        = 2 * (c * (M / m)) * (t ^ 2 - 1) + 3 / 4 * (M / m) * (t ^ 2 - 1) := by field_simp; ring
    rw [e]; linarith
  · have h2 : 2 * (M / m) ≤ t * ((M / m) ^ 2 - 1) := by
      rw [he]
      have : 2 * (M / m) = 2 * M * m / m ^ 2 := by field_simp
      rw [this, mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
      have : 2 * m ≤ (M - m) * (M + m) := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left this (by linarith : (0 : ℝ) ≤ M), mul_le_mul_of_nonneg_right ht
        (by positivity : (0 : ℝ) ≤ (M - m) * (M + m))]
    have e : 2 * c ^ 2 * t * ((M / m) ^ 2 - 1) * (1 + 1 / (2 * c))
        = 2 * c ^ 2 * t * ((M / m) ^ 2 - 1) + c * (t * ((M / m) ^ 2 - 1)) := by field_simp
    rw [e]; nlinarith
  · rw [he, div_le_div_iff₀ (by positivity) (by positivity)]
    have e : M / m * (2 * (M - m)) = 2 * M * (M - m) / m := by ring
    rw [e]
    have e2 : M * ((M - m) * (M + m) / m ^ 2) = M * (M - m) * (M + m) / m ^ 2 := by ring
    rw [e2, div_le_div_iff₀ hm0 (by positivity)]
    have : 0 ≤ M * (M - m) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left (by linarith : 2 * m ≤ M + m) (mul_nonneg this hm0.le)]
  · rw [he, div_le_div_iff₀ (by positivity) (by positivity)]
    have e2 : M * ((M - m) * (M + m) / m ^ 2) = M * (M - m) * (M + m) / m ^ 2 := by ring
    rw [e2, le_div_iff₀ (by positivity)]
    have : 2 * m ^ 2 ≤ M * (M + m) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this hj.le]
  · exact Cvs.Upstream.ExpDifferenceBound.div_sq_sub_one_anti (by linarith) ht
  · exact one_div_le_one_div_of_le (by nlinarith) (by nlinarith)

/-- **The far atoms on the orbit** (`χ₀ = c²`, `y = M/m`, `t > M`), `j = M − m`, `p = M² − 1`, `ν = M/p`. -/
theorem pr_orbit {w w₁ w₂ : ℝ → ℂ} {c M m t : ℝ} (hc : 0 < c) (hM : 3 ≤ M) (hm : 2 ≤ m) (hmM : m + 1 ≤ M)
    (ht : M < t) :
    Cvs.L2a.SigmaSquareMultiplier.pr₁ w₁ w₂ c (c ^ 2) (M / m) t
        ≤ (1 + 3 / (8 * c)) * M / (c * (M - m)) * ‖w₁ t‖ + M / (2 * c ^ 2 * (M - m)) * ‖w₂ t‖
      ∧ Cvs.L2a.SigmaSquareMultiplier.pr₂ w w₁ c (c ^ 2) (M / m) t
        ≤ (2 * (1 + 3 / (8 * c)) * (1 + 1 / (2 * c)) * (M / (M ^ 2 - 1)) * M / (c * (M - m))
            + M / (c ^ 2 * (M ^ 2 - 1) * (M - m))) * ‖w t‖
          + 2 * (1 + 1 / (2 * c)) * (M / (M ^ 2 - 1)) * M / (c ^ 2 * (M - m)) * ‖w₁ t‖
      ∧ Cvs.L2a.SigmaSquareMultiplier.pr₃ w c (c ^ 2) (M / m) t
        ≤ 4 * (M / (M ^ 2 - 1)) ^ 2 * (1 + 1 / (2 * c)) ^ 2 * M / (c ^ 2 * (M - m)) * ‖w t‖ := by
  have hm0 : 0 < m := by linarith
  have hy1 : 1 < M / m := by rw [lt_div_iff₀ hm0]; linarith
  obtain ⟨p1, p2, p3⟩ := pr_le_far (w := w) (w₁ := w₁) (w₂ := w₂) hc (by linarith : 1 < t) hy1
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := orbit_coeffs hc hM hm hmM ht.le
  set y := M / m
  set ε := y ^ 2 - 1 with hε
  set P := t ^ 2 - 1 with hP
  set kE := 1 + 3 / (8 * c)
  set kE' := 1 + 1 / (2 * c)
  set j := M - m with hj
  set ν := M / (M ^ 2 - 1)
  have hj0 : 0 < j := by linarith
  have hε0 : 0 < ε := by rw [hε]; nlinarith
  have hP0 : 0 < P := by rw [hP]; nlinarith
  have ht0 : 0 < t := by linarith
  have hy0 : 0 < y := by positivity
  have hkE : 0 ≤ kE := by positivity
  have hkE' : 0 ≤ kE' := by positivity
  have hp0 : 0 < M ^ 2 - 1 := by nlinarith
  have n0 := norm_nonneg (w t)
  have n1 := norm_nonneg (w₁ t)
  have n2 := norm_nonneg (w₂ t)
  have hc2 : 0 < c ^ 2 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · refine p1.trans ?_
    calc ((2 * t + 2 * (c * y) * P) * ‖w₁ t‖ + P * ‖w₂ t‖) / (c ^ 2 * (P * ε))
        ≤ (2 * c * y * P * kE * ‖w₁ t‖ + P * ‖w₂ t‖) / (c ^ 2 * (P * ε)) := by gcongr
      _ = 2 * kE / c * (y / ε) * ‖w₁ t‖ + 1 / c ^ 2 * (1 / ε) * ‖w₂ t‖ := by field_simp
      _ ≤ 2 * kE / c * (M / (2 * j)) * ‖w₁ t‖ + 1 / c ^ 2 * (M / (2 * j)) * ‖w₂ t‖ := by gcongr
      _ = _ := by field_simp
  · refine p2.trans ?_
    have hA : 2 * t + 2 * (c * y) * P ≤ 2 * c * y * P * kE := f1
    have hB : 2 * c ^ 2 * t * ε + 2 * c * y ≤ 2 * c ^ 2 * t * ε * kE' := f2
    have hA0 : 0 ≤ 2 * t + 2 * (c * y) * P := by positivity
    have hB0 : 0 ≤ 2 * c ^ 2 * t * ε + 2 * c * y := by positivity
    calc (((2 * t + 2 * (c * y) * P) * (2 * c ^ 2 * t * ε + 2 * c * y) + P * (2 * c ^ 2 * ε)) * ‖w t‖
          + 2 * P * (2 * c ^ 2 * t * ε + 2 * c * y) * ‖w₁ t‖) / (c ^ 2 * (P * ε)) ^ 2
        ≤ (((2 * c * y * P * kE) * (2 * c ^ 2 * t * ε * kE') + P * (2 * c ^ 2 * ε)) * ‖w t‖
          + 2 * P * (2 * c ^ 2 * t * ε * kE') * ‖w₁ t‖) / (c ^ 2 * (P * ε)) ^ 2 := by
          gcongr
      _ = (4 * kE * kE' / c * (y / ε) * (t / P) + 2 / c ^ 2 * (1 / ε) * (1 / P)) * ‖w t‖
          + 4 * kE' / c ^ 2 * (1 / ε) * (t / P) * ‖w₁ t‖ := by field_simp; ring
      _ ≤ (4 * kE * kE' / c * (M / (2 * j)) * ν + 2 / c ^ 2 * (M / (2 * j)) * (1 / (M ^ 2 - 1))) * ‖w t‖
          + 4 * kE' / c ^ 2 * (M / (2 * j)) * ν * ‖w₁ t‖ := by gcongr
      _ = _ := by field_simp; ring
  · refine p3.trans ?_
    have hB : 2 * c ^ 2 * t * ε + 2 * c * y ≤ 2 * c ^ 2 * t * ε * kE' := f2
    have hB0 : 0 ≤ 2 * c ^ 2 * t * ε + 2 * c * y := by positivity
    calc 2 * P * (2 * c ^ 2 * t * ε + 2 * c * y) ^ 2 * ‖w t‖ / (c ^ 2 * (P * ε)) ^ 3
        ≤ 2 * P * (2 * c ^ 2 * t * ε * kE') ^ 2 * ‖w t‖ / (c ^ 2 * (P * ε)) ^ 3 := by gcongr
      _ = 8 * kE' ^ 2 / c ^ 2 * (1 / ε) * (t / P) ^ 2 * ‖w t‖ := by field_simp; ring
      _ ≤ 8 * kE' ^ 2 / c ^ 2 * (M / (2 * j)) * ν ^ 2 * ‖w t‖ := by
          gcongr
      _ = _ := by field_simp; ring

/-- The atom profiles are a.e.-strongly measurable on `(M, ∞)` for weights continuous there, where `Q ≠ 0`. -/
theorem pr_aesm {w w₁ w₂ : ℝ → ℂ} {c χ₀ y M : ℝ} (hw : ContinuousOn w (Ioi M)) (hw₁ : ContinuousOn w₁ (Ioi M))
    (hw₂ : ContinuousOn w₂ (Ioi M)) (hQ0 : ∀ t ∈ Ioi M, qQ c χ₀ y t ≠ 0) :
    AEStronglyMeasurable (fun t => Cvs.L2a.SigmaSquareMultiplier.pr₁ w₁ w₂ c χ₀ y t) (volume.restrict (Ioi M))
      ∧ AEStronglyMeasurable (fun t => Cvs.L2a.SigmaSquareMultiplier.pr₂ w w₁ c χ₀ y t) (volume.restrict (Ioi M))
      ∧ AEStronglyMeasurable (fun t => Cvs.L2a.SigmaSquareMultiplier.pr₃ w c χ₀ y t) (volume.restrict (Ioi M)) := by
  have hK : Continuous fun t => kK c y t := by unfold kK pP; fun_prop
  have hp : Continuous fun t : ℝ => ((pP t : ℝ) : ℂ) := by unfold pP; fun_prop
  have hq : Continuous fun t => qQ c χ₀ y t := by unfold qQ; fun_prop
  have hq₁ : Continuous fun t => qQ₁ c y t := by unfold qQ₁; fun_prop
  have hn : ∀ k : ℕ, ∀ t ∈ Ioi M, ‖qQ c χ₀ y t‖ ^ k ≠ 0 := fun k t ht => pow_ne_zero _ (norm_ne_zero_iff.2 (hQ0 t ht))
  have hq' : ∀ k : ℕ, ContinuousOn (fun t => ‖qQ c χ₀ y t‖ ^ k) (Ioi M) := fun k =>
    (hq.norm.pow k).continuousOn
  have c1 : ContinuousOn (fun t => aC₁ w₁ w₂ c y t) (Ioi M) := by unfold aC₁ kK pP; fun_prop
  have c2 : ContinuousOn (fun t => aC₂ w w₁ c y t) (Ioi M) := by unfold aC₂ kK qQ₁ qQ₂ pP; fun_prop
  have c3 : ContinuousOn (fun t => aC₃ w c y t) (Ioi M) := by
    have h2 : ContinuousOn (fun t => (2 : ℂ) * ((pP t : ℝ) : ℂ) * qQ₁ c y t ^ 2) (Ioi M) :=
      ((continuous_const.mul hp).mul (hq₁.pow 2)).continuousOn
    exact h2.mul hw
  refine ⟨?_, ?_, ?_⟩
  · have h : ContinuousOn (fun t => Cvs.L2a.SigmaSquareMultiplier.pr₁ w₁ w₂ c χ₀ y t) (Ioi M) :=
      ContinuousOn.div₀ (f := fun t => ‖aC₁ w₁ w₂ c y t‖) (g := fun t => ‖qQ c χ₀ y t‖) c1.norm hq.norm.continuousOn
        (fun t ht => norm_ne_zero_iff.2 (hQ0 t ht))
    exact h.aestronglyMeasurable measurableSet_Ioi
  · have h : ContinuousOn (fun t => Cvs.L2a.SigmaSquareMultiplier.pr₂ w w₁ c χ₀ y t) (Ioi M) :=
      ContinuousOn.div₀ (f := fun t => ‖aC₂ w w₁ c y t‖) (g := fun t => ‖qQ c χ₀ y t‖ ^ 2) c2.norm (hq' 2) (hn 2)
    exact h.aestronglyMeasurable measurableSet_Ioi
  · have h : ContinuousOn (fun t => Cvs.L2a.SigmaSquareMultiplier.pr₃ w c χ₀ y t) (Ioi M) :=
      ContinuousOn.div₀ (f := fun t => ‖aC₃ w c y t‖) (g := fun t => ‖qQ c χ₀ y t‖ ^ 3) c3.norm (hq' 3) (hn 3)
    exact h.aestronglyMeasurable measurableSet_Ioi

/-- The `𝔈₁` bracket at `ν = M/(M² − 1)`, `ι = 1/(M² − 1)` and `h = √(M − m)`. -/
def e1Br (c ν ip h : ℝ) : ℝ :=
  10 / 9 * (40 / 9 * (1 + 3 / (8 * c)) * B0 c (9 / 10) 24 / (√3 * c) / h ^ 5
      + 1600 / 81 * B0 c (9 / 10) 24 / (√5 * c ^ 2) / h ^ 7)
    + (10 / 9) ^ 2 * ((2 * (1 + 3 / (8 * c)) * (1 + 1 / (2 * c)) * ν * A0 c (9 / 10) (1 / 4) / c
        + A0 c (9 / 10) (1 / 4) * ip / c ^ 2) / h ^ 3
      + 80 / 9 * (1 + 1 / (2 * c)) * ν * B0 c (9 / 10) 24 / (√3 * c ^ 2) / h ^ 5)
    + (10 / 9) ^ 3 * (4 * ν ^ 2 * (1 + 1 / (2 * c)) ^ 2 * A0 c (9 / 10) (1 / 4) / c ^ 2 / h ^ 3)

/-- `√(1/(k(h²)ⁿ)) = 1/(√k·hⁿ)` for `k, h ≥ 0`. -/
theorem sqrt_one_div_mul_sq_pow {k h : ℝ} (hk : 0 ≤ k) (hh : 0 ≤ h) (n : ℕ) :
    √(1 / (k * (h ^ 2) ^ n)) = 1 / (√k * h ^ n) := by
  rw [← pow_mul, show h ^ (2 * n) = (h ^ n) ^ 2 by ring, Real.sqrt_div' _ (by positivity), Real.sqrt_one,
    Real.sqrt_mul hk, Real.sqrt_sq (by positivity)]

/-- `Σ_{2 ≤ m ≤ M − 1} (√(M − m))^{−k} ≤ ζ(k/2)` for `k ≥ 3`. -/
theorem sum_inv_sqrt_pow_le {M : ℕ} {k : ℕ} (hk : 3 ≤ k) :
    ∑ m ∈ Finset.Icc 2 (M - 1), 1 / √((M : ℝ) - m) ^ k ≤ zR (k / 2) := by
  have h := sum_inv_rpow_le (M := M) (s := (k : ℝ) / 2) (by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith)
  refine le_of_eq_of_le (Finset.sum_congr rfl fun m hm => ?_) h
  have hm : m ≤ M - 1 := (Finset.mem_Icc.1 hm).2
  have h0 : (0 : ℝ) ≤ (M : ℝ) - m := by
    have : (m : ℝ) ≤ M := by exact_mod_cast (show m ≤ M by omega)
    linarith
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul h0]
  congr 2
  ring

/-- `√(6J/(M² − 1))·M ≤ 3√(6J)/√8` for `M ≥ 3`, `J ≥ 0`. -/
theorem sqrt_sixJ_mul_le {M J : ℝ} (hM : 3 ≤ M) (hJ : 0 ≤ J) :
    √(6 * J / (M ^ 2 - 1)) * M ≤ 3 * √(6 * J) / √8 := by
  have hp : 0 < M ^ 2 - 1 := by nlinarith
  have hM0 : 0 ≤ M := by linarith
  have e1 : √(6 * J / (M ^ 2 - 1)) * M = √(6 * J / (M ^ 2 - 1) * M ^ 2) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hM0]
  have e2 : 3 * √(6 * J) / √8 = √(6 * J * 9 / 8) := by
    have h9 : √(9 : ℝ) = 3 := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
    rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 8), Real.sqrt_mul' _ (by norm_num : (0 : ℝ) ≤ 9), h9]
    ring
  rw [e1, e2]
  refine Real.sqrt_le_sqrt ?_
  rw [div_mul_eq_mul_div, div_le_div_iff₀ hp (by norm_num)]
  have : 0 ≤ 6 * J := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (by nlinarith : 8 * M ^ 2 ≤ 9 * (M ^ 2 - 1)) this]

/-- The `γ_E₁` bracket dominates the summed `𝔈₁` bracket at `ν = 3/8`, `ι = 1/8`; `s_k` stand for `√k`. -/
theorem e1_bracket_le {A B kE kE' c z3 z5 z7 s2 s3 s5 L : ℝ} (hc : 0 < c) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hkE : 0 ≤ kE) (hkE' : 0 ≤ kE') (hz3 : 0 ≤ z3) (hz5 : 0 ≤ z5) (hs2 : 0 < s2) (hs3 : 0 < s3)
    (hs5 : 0 < s5) (hL : 0 ≤ L) :
    ((10 / 9) ^ 2 * (2 * kE * kE' * (3 / 8) * A / c + A * (1 / 8) / c ^ 2)
        + (10 / 9) ^ 3 * (4 * (3 / 8) ^ 2 * kE' ^ 2 * A / c ^ 2)) * z3
      + (10 / 9 * (40 / 9 * kE * B / (s3 * c)) + (10 / 9) ^ 2 * (80 / 9 * kE' * (3 / 8) * B / (s3 * c ^ 2))) * z5
      + 10 / 9 * (1600 / 81 * B / (s5 * c ^ 2)) * z7
      ≤ 10 / 9 * (8 * kE * B / (s3 * (9 / 10) * c)) * z5
        + 10 / 9 * (16 * B / (s5 * (9 / 10) ^ 2 * c ^ 2)) * z7
        + (10 / 9) ^ 2 * (9 * kE * kE' / (2 * c)) * (A * z3 / 3 + 1 / (4 * c) / s2 * (L / 3))
        + (10 / 9) ^ 2 * (9 / (8 * c ^ 2)) * (A * z3 / 6 + 1 / (4 * c) / s3 / (2 * s2) * (L / 3))
        + (10 / 9) ^ 2 * (9 * kE' * B / (s3 * (9 / 10) * c ^ 2)) * z5 / 3
        + (10 / 9) ^ 3 * (81 * kE' ^ 2 / (16 * c ^ 2)) * (A * z3 / 6 + 1 / (4 * c) / s3 / (2 * s2) * (L / 3)) := by
  have L1 : 0 ≤ (10 / 9) ^ 2 * (9 * kE * kE' / (2 * c)) * (1 / (4 * c) / s2 * (L / 3)) := by positivity
  have L2 : 0 ≤ (10 / 9) ^ 2 * (9 / (8 * c ^ 2)) * (1 / (4 * c) / s3 / (2 * s2) * (L / 3)) := by positivity
  have L3 : 0 ≤ (10 / 9) ^ 3 * (81 * kE' ^ 2 / (16 * c ^ 2)) * (1 / (4 * c) / s3 / (2 * s2) * (L / 3)) := by
    positivity
  have a1 : 10 / 9 * (40 / 9 * kE * B / (s3 * c)) * z5 ≤ 10 / 9 * (8 * kE * B / (s3 * (9 / 10) * c)) * z5 := by
    have e : 10 / 9 * (8 * kE * B / (s3 * (9 / 10) * c)) * z5 = 2 * (10 / 9 * (40 / 9 * kE * B / (s3 * c)) * z5) := by
      field_simp; ring
    rw [e]
    have : 0 ≤ 10 / 9 * (40 / 9 * kE * B / (s3 * c)) * z5 := by positivity
    linarith
  have a2 : 10 / 9 * (1600 / 81 * B / (s5 * c ^ 2)) * z7 = 10 / 9 * (16 * B / (s5 * (9 / 10) ^ 2 * c ^ 2)) * z7 := by
    field_simp; ring
  have a3 : (10 / 9) ^ 2 * (80 / 9 * kE' * (3 / 8) * B / (s3 * c ^ 2)) * z5
      = (10 / 9) ^ 2 * (9 * kE' * B / (s3 * (9 / 10) * c ^ 2)) * z5 / 3 := by
    field_simp; ring
  have a4 : (10 / 9) ^ 2 * (2 * kE * kE' * (3 / 8) * A / c) * z3 ≤ (10 / 9) ^ 2 * (9 * kE * kE' / (2 * c)) * (A * z3 / 3) := by
    have e : (10 / 9) ^ 2 * (9 * kE * kE' / (2 * c)) * (A * z3 / 3)
        = 2 * ((10 / 9) ^ 2 * (2 * kE * kE' * (3 / 8) * A / c) * z3) := by field_simp; ring
    rw [e]
    have : 0 ≤ (10 / 9) ^ 2 * (2 * kE * kE' * (3 / 8) * A / c) * z3 := by positivity
    linarith
  have a5 : (10 / 9) ^ 2 * (A * (1 / 8) / c ^ 2) * z3 ≤ (10 / 9) ^ 2 * (9 / (8 * c ^ 2)) * (A * z3 / 6) := by
    have e : (10 / 9) ^ 2 * (9 / (8 * c ^ 2)) * (A * z3 / 6) = 3 / 2 * ((10 / 9) ^ 2 * (A * (1 / 8) / c ^ 2) * z3) := by
      field_simp; ring
    rw [e]
    have : 0 ≤ (10 / 9) ^ 2 * (A * (1 / 8) / c ^ 2) * z3 := by positivity
    linarith
  have a6 : (10 / 9) ^ 3 * (4 * (3 / 8) ^ 2 * kE' ^ 2 * A / c ^ 2) * z3
      ≤ (10 / 9) ^ 3 * (81 * kE' ^ 2 / (16 * c ^ 2)) * (A * z3 / 6) := by
    have e : (10 / 9) ^ 3 * (81 * kE' ^ 2 / (16 * c ^ 2)) * (A * z3 / 6)
        = 3 / 2 * ((10 / 9) ^ 3 * (4 * (3 / 8) ^ 2 * kE' ^ 2 * A / c ^ 2) * z3) := by field_simp; ring
    rw [e]
    have : 0 ≤ (10 / 9) ^ 3 * (4 * (3 / 8) ^ 2 * kE' ^ 2 * A / c ^ 2) * z3 := by positivity
    linarith
  nlinarith [a1, a2, a3, a4, a5, a6, L1, L2, L3]

/-! ### The count envelope and the top sample -/

variable {ι : Type} [Fintype ι]

/-- The count-envelope scale `S₀ = √(6J/(M² − 1))·√P`, with `P = ∫_{(1,∞)} Φ²`. -/
def S0 (c : ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (J : ℝ) (M : ℕ) : ℝ :=
  √(6 * J / ((M : ℝ) ^ 2 - 1)) * √(∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2)

theorem S0_nonneg (c : ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (J : ℝ) (M : ℕ) : 0 ≤ S0 c g a J M := by
  unfold S0; positivity

section span

variable {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
  (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
  (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
  (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
  (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
    (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
  (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχ : Function.Injective χ) {M : ℕ}
  (hM : 3 ≤ M) (hmass : ∀ i, 0 < ∫ t in (1 : ℝ)..M, psi c (g i) t ^ 2) {J : ℝ}
  (hJ : (Fintype.card ι : ℝ) ≤ J)

include hg hg₁ hg₂c hang hc hχ0 hχc hχ hM hmass hJ

/-- **T0 at `x₀ = M`**: a pair bound `2B` on `[c, cY]` gives `‖Σᵢaᵢ Sᵢ[μ](M)‖ ≤ B·S₀`. -/
theorem count_pair {μ : ℝ → ℂ} {B : ℝ} (hμ : ∀ ξ ∈ Icc c (c * Ymax M), ‖μ ξ‖ + ‖μ (-ξ)‖ ≤ 2 * B) :
    ‖∑ i, (a i : ℂ) * Cvs.L2a.BandTransferBandForm.smp μ c (χ i) (g i) M‖ ≤ B * S0 c g a J M := by
  have hc0 : 0 < c := by linarith
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hY := Cvs.L2a.BandTransferBandForm.one_le_Ymax (by linarith : (1 : ℝ) < M)
  have hB : 0 ≤ B := by
    have := hμ c ⟨le_rfl, le_mul_of_one_le_right hc0.le hY⟩
    linarith [norm_nonneg (μ c), norm_nonneg (μ (-c))]
  have h := Cvs.L2a.TopCornerSum.t0_pair a hg hg₁ hg₂c hang hc hχ0 hχc (X := M) (x₀ := M) (by linarith) hmass
    ⟨by linarith, le_rfl⟩ hμ
  have hmle := Cvs.L2a.TopCornerSum.spanMass_le a hg hg₁ hg₂c hang hc0 hχ (X := M) (by linarith)
  refine h.trans ?_
  unfold S0
  have hp : 0 ≤ (M : ℝ) ^ 2 - 1 := by nlinarith
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left (mul_le_mul (Real.sqrt_le_sqrt ?_) (Real.sqrt_le_sqrt hmle)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hB
  exact div_le_div_of_nonneg_right (by linarith) hp

/-- The top sample under a pair bound on `μ̃(·; z)`: `‖𝒜̃(z)‖ ≤ B·S₀`. -/
theorem norm_sampleC_le {z : ℂ} {B : ℝ}
    (hμ : ∀ ξ ∈ Icc c (c * Ymax M), ‖Cvs.L2a.QIdentityCutPoint.muQC c M ξ z‖ + ‖Cvs.L2a.QIdentityCutPoint.muQC c M (-ξ) z‖ ≤ 2 * B) :
    ‖sampleC c χ g a M z‖ ≤ B * S0 c g a J M :=
  count_pair a hg hg₁ hg₂c hang hc hχ0 hχc hχ hM hmass hJ (μ := fun ξ => Cvs.L2a.QIdentityCutPoint.muQC c M ξ z) hμ

/-- **Lemma K (d)**: on `η ≥ M/m`, `‖𝒜̃(η)‖ ≤ (A₀/g)S₀`, `‖𝒜̃′(η)‖ ≤ (B₀/g)S₀/r`, `‖𝒜̃″(η)‖ ≤ 2(B₀/g)S₀/r²`,
with `g = η − 1` and `r = (9/40)g`. -/
theorem sampleC_bounds {m : ℕ} (hm : 2 ≤ m) (hmM : m + 1 ≤ M) {η : ℝ} (hη : (M : ℝ) / m ≤ η) :
    ‖sampleC c χ g a M η‖ ≤ A0 c (9 / 10) (1 / 4) / (η - 1) * S0 c g a J M
      ∧ ‖deriv (sampleC c χ g a M) η‖ ≤ B0 c (9 / 10) 24 / (η - 1) * S0 c g a J M / (9 / 40 * (η - 1))
      ∧ ‖deriv (deriv (sampleC c χ g a M)) η‖
          ≤ 2 * (B0 c (9 / 10) 24 / (η - 1) * S0 c g a J M) / (9 / 40 * (η - 1)) ^ 2 := by
  have hc1 : 1 ≤ c := by linarith
  have hc0 : 0 < c := by linarith
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmM' : (m : ℝ) + 1 ≤ M := by exact_mod_cast hmM
  obtain ⟨hη1, -, -⟩ := orbit_eta hM3 hm2 hmM' hη
  have hr : 0 < 9 / 40 * (η - 1) := by linarith
  have hreal := norm_sampleC_le a hg hg₁ hg₂c hang hc hχ0 hχc hχ hM hmass hJ (z := (η : ℂ))
    (B := A0 c (9 / 10) (1 / 4) / (η - 1)) fun ξ hξ =>
      lemmaK_real hc1 hM3 hm2 hmM' hη (by linarith [hξ.1]) hξ.2
  have hk : ∀ i, kP c (χ i) M ∈ Icc c (c * Ymax M) := fun i =>
    Cvs.Upstream.ExpDifferenceBound.kP_mem_Icc (by linarith) hc0 (hχ0 i) (hχc i)
  have hdiff : ∀ z ∈ Metric.closedBall (η : ℂ) (9 / 40 * (η - 1)), DifferentiableAt ℂ (sampleC c χ g a M) z := by
    intro z hz
    have hz' : ‖z - η‖ ≤ 9 / 40 * (η - 1) := by rw [← dist_eq_norm]; exact hz
    have hne : ∀ i, Cvs.L2a.QIdentityCutPoint.qQkC c M (kP c (χ i) M) z ≠ 0 := fun i => by
      obtain ⟨h0, h1⟩ := lemmaK_disc hc1 hM3 hm2 hmM' hη (by linarith [(hk i).1]) (hk i).2 hz'
      exact norm_pos_iff.1 (h0.trans_le h1)
    have hne' : ∀ i, Cvs.L2a.QIdentityCutPoint.qQkC c M (-kP c (χ i) M) z ≠ 0 := fun i => by rw [qQkC_neg]; exact hne i
    have : DifferentiableAt ℂ (fun η => ∑ i, (a i : ℂ) * (Cvs.L2a.QIdentityCutPoint.muQC c M (kP c (χ i) M) η
        * psiP c (χ i) (g i) M + Cvs.L2a.QIdentityCutPoint.muQC c M (-kP c (χ i) M) η * conj (psiP c (χ i) (g i) M))) z :=
      DifferentiableAt.fun_sum fun i _ =>
        (((Cvs.L2a.QIdentityCutPoint.differentiableAt_muQC (hne i)).mul_const _).fun_add
          ((Cvs.L2a.QIdentityCutPoint.differentiableAt_muQC (hne' i)).mul_const _)).const_mul _
    exact this
  have hsph : ∀ z ∈ Metric.sphere (η : ℂ) (9 / 40 * (η - 1)),
      ‖sampleC c χ g a M z‖ ≤ B0 c (9 / 10) 24 / (η - 1) * S0 c g a J M := by
    intro z hz
    have hz' : ‖z - η‖ ≤ 9 / 40 * (η - 1) := by rw [← dist_eq_norm]; exact le_of_eq hz
    exact norm_sampleC_le a hg hg₁ hg₂c hang hc hχ0 hχc hχ hM hmass hJ fun ξ hξ =>
      lemmaK_circle hc1 hM3 hm2 hmM' hη (by linarith [hξ.1]) hξ.2 hz'
  have h1 := norm_iteratedDeriv_le_of_closedBall hr hdiff hsph 1
  have h2 := norm_iteratedDeriv_le_of_closedBall hr hdiff hsph 2
  rw [iteratedDeriv_one] at h1
  rw [iteratedDeriv_succ, iteratedDeriv_one] at h2
  simp only [Nat.factorial, Nat.cast_one, one_mul, pow_one, Nat.succ_eq_add_one, zero_add, Nat.mul_one] at h1 h2
  refine ⟨hreal, h1, ?_⟩
  refine h2.trans (le_of_eq ?_)
  norm_num

/-- **The weight bounds** for `t ≥ M`: `‖V‖ ≤ A₀S₀m/(t − m)`, `‖V′‖ ≤ (40/9)B₀S₀m/(t − m)²`,
`‖V″‖ ≤ 2(40/9)²B₀S₀m/(t − m)³`. -/
theorem vW_bounds {m : ℕ} (hm : 2 ≤ m) (hmM : m + 1 ≤ M) {t : ℝ} (ht : (M : ℝ) ≤ t) :
    ‖vW c χ g a M m t‖ ≤ A0 c (9 / 10) (1 / 4) * S0 c g a J M * m / (t - m)
      ∧ ‖vW₁ c χ g a M m t‖ ≤ 40 / 9 * B0 c (9 / 10) 24 * S0 c g a J M * m / (t - m) ^ 2
      ∧ ‖vW₂ c χ g a M m t‖ ≤ 2 * (40 / 9) ^ 2 * B0 c (9 / 10) 24 * S0 c g a J M * m / (t - m) ^ 3 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmM' : (m : ℝ) + 1 ≤ M := by exact_mod_cast hmM
  have hη : (M : ℝ) / m ≤ t / m := div_le_div_of_nonneg_right ht hm0.le
  obtain ⟨h0, h1, h2⟩ := sampleC_bounds a hg hg₁ hg₂c hang hc hχ0 hχc hχ hM hmass hJ hm hmM hη
  have htm : 0 < t - m := by linarith
  have hg : t / m - 1 = (t - m) / m := by field_simp
  rw [hg] at h0 h1 h2
  have hmC : ‖(1 / (m : ℂ))‖ = 1 / m := by rw [norm_div, norm_one, Complex.norm_natCast]
  refine ⟨?_, ?_, ?_⟩
  · unfold vW
    refine h0.trans (le_of_eq ?_)
    field_simp
  · unfold vW₁
    rw [norm_mul, hmC]
    calc 1 / (m : ℝ) * ‖deriv (sampleC c χ g a M) ((t / m : ℝ) : ℂ)‖
        ≤ 1 / m * (B0 c (9 / 10) 24 / ((t - m) / m) * S0 c g a J M / (9 / 40 * ((t - m) / m))) := by gcongr
      _ = _ := by field_simp
  · unfold vW₂
    rw [norm_mul, norm_pow, hmC]
    calc (1 / (m : ℝ)) ^ 2 * ‖deriv (deriv (sampleC c χ g a M)) ((t / m : ℝ) : ℂ)‖
        ≤ (1 / m) ^ 2 * (2 * (B0 c (9 / 10) 24 / ((t - m) / m) * S0 c g a J M) / (9 / 40 * ((t - m) / m)) ^ 2) := by
          gcongr
      _ = _ := by field_simp

/-! ### `𝔇`: the double boundary at the orbit point -/

/-- `Σᵢaᵢψᵢ(M)/Qᵢ` at `y = M/m` is at most `S₀/(9c²(M − m))`. -/
theorem psi_div_Q_le {m : ℕ} (hm : 2 ≤ m) (hmM : m + 1 ≤ M) :
    (∀ i, (9 * c ^ 2 * ((M : ℝ) - m)) ≤ ‖qQ c (χ i) ((M : ℝ) / m) M‖)
      ∧ ‖∑ i, (a i : ℂ) * ((psi c (g i) M : ℂ) / qQ c (χ i) ((M : ℝ) / m) M)‖
        ≤ 1 / (9 * c ^ 2 * ((M : ℝ) - m)) * S0 c g a J M := by
  have hc0 : 0 < c := by linarith
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmM' : (m : ℝ) + 1 ≤ M := by exact_mod_cast hmM
  have hM1 : (1 : ℝ) < M := by linarith
  set y := (M : ℝ) / m with hy
  have hgap := orbit_gap hm2 hmM'
  have hQk : ∀ ξ ∈ Icc c (c * Ymax M), 9 * c ^ 2 * ((M : ℝ) - m) ≤ ‖Cvs.L2a.QIdentityCutPoint.qQk c y M ξ‖ := by
    intro ξ hξ
    have hξ' := sq_le_of_le_Ymax hM1 (by linarith [hξ.1]) hξ.2
    have hre := re_qQkC_ge (η := y) hξ'
    have hn := Cvs.L2a.QIdentityCutPoint.le_norm_qQk_re (c := c) (y := y) (ξ := ξ) hM1.le
    have hp : 0 ≤ pP (M : ℝ) := by unfold pP; nlinarith
    have hab : pP (M : ℝ) * (c ^ 2 * y ^ 2 - ξ ^ 2) ≤ pP (M : ℝ) * |c ^ 2 * y ^ 2 - ξ ^ 2| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hp
    have hc2 : 0 < c ^ 2 := by positivity
    have : c ^ 2 * (10 * ((M : ℝ) - m) - 1) ≤ c ^ 2 * (((M : ℝ) ^ 2 - 1) * (y ^ 2 - 1) - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hc2.le
    nlinarith
  have hQi : ∀ i, 9 * c ^ 2 * ((M : ℝ) - m) ≤ ‖qQ c (χ i) y M‖ := fun i => by
    rw [← Cvs.L2a.QIdentityCutPoint.qQk_kP hM1 hc0 (hχc i)]
    exact hQk _ (Cvs.Upstream.ExpDifferenceBound.kP_mem_Icc hM1 hc0 (hχ0 i) (hχc i))
  refine ⟨hQi, ?_⟩
  have hj : 0 < 9 * c ^ 2 * ((M : ℝ) - m) := by
    have : (0 : ℝ) < M - m := by linarith
    positivity
  have hμ : ∀ ξ ∈ Icc c (c * Ymax M),
      ‖(fun ξ => 1 / Cvs.L2a.QIdentityCutPoint.qQk c y M ξ) ξ‖ + ‖(fun ξ => 1 / Cvs.L2a.QIdentityCutPoint.qQk c y M ξ) (-ξ)‖
        ≤ 2 * (1 / (9 * c ^ 2 * ((M : ℝ) - m))) := by
    intro ξ hξ
    simp only [Cvs.L2a.QIdentityCutPoint.qQk_neg, norm_div, norm_one]
    have := one_div_le_one_div_of_le hj (hQk ξ hξ)
    linarith
  have h := count_pair a hg hg₁ hg₂c hang hc hχ0 hχc hχ hM hmass hJ hμ
  refine le_of_eq_of_le ?_ h
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsum : psiP c (χ i) (g i) M + conj (psiP c (χ i) (g i) M) = (psi c (g i) M : ℂ) := split_add_conj
  unfold Cvs.L2a.BandTransferBandForm.smp
  simp only [Cvs.L2a.QIdentityCutPoint.qQk_neg, Cvs.L2a.QIdentityCutPoint.qQk_kP hM1 hc0 (hχc i)]
  rw [← hsum]
  ring

/-- **`𝔇` per cut**: `(2κ/m)|Re D_m| ≤ (3κJA₀²/j² + (160/27)κJB₀/(c²j³))·P`, `j = M − m`. -/
theorem frakD_term_le {m : ℕ} (hm : 2 ≤ m) (hmM : m + 1 ≤ M) :
    |2 * √(2 * c / π) / m
        * (∑ i, (a i : ℂ) * bBc (vW c χ g a M m) (vW₁ c χ g a M m) c (χ i) (g i) ((M : ℝ) / m) M).re|
      ≤ (3 * kap c * J * A0 c (9 / 10) (1 / 4) ^ 2 / ((M : ℝ) - m) ^ 2
          + 160 / 27 * kap c * J * B0 c (9 / 10) 24 / (c ^ 2 * ((M : ℝ) - m) ^ 3))
        * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmM' : (m : ℝ) + 1 ≤ M := by exact_mod_cast hmM
  have hm0 : (0 : ℝ) < m := by linarith
  have hM1 : (1 : ℝ) < M := by linarith
  set y := (M : ℝ) / m with hy
  set j := (M : ℝ) - m with hjdef
  have hj1 : 1 ≤ j := by linarith
  set S := S0 c g a J M with hS
  set P := ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 with hP
  obtain ⟨hQi, hpsi⟩ := psi_div_Q_le a hg hg₁ hg₂c hang hc hχ0 hχc hχ hM hmass hJ hm hmM
  have hQne : ∀ i, qQ c (χ i) y M ≠ 0 := fun i => by
    have : 0 < 9 * c ^ 2 * j := by positivity
    exact norm_pos_iff.1 (this.trans_le (hQi i))
  -- the affine split
  have hsplit : ∑ i, (a i : ℂ) * bBc (vW c χ g a M m) (vW₁ c χ g a M m) c (χ i) (g i) y M
      = vW c χ g a M m M * (eF c y M * sampleC c χ g a M (y : ℂ))
        - vW₁ c χ g a M m M * (eF c y M * ((pP (M : ℝ) : ℝ) : ℂ)
          * ∑ i, (a i : ℂ) * ((psi c (g i) M : ℂ) / qQ c (χ i) y M)) := by
    rw [← cutSample_eq]
    unfold cutSample
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [bBc_lin (w := vW c χ g a M m) (hQne i),
      Cvs.L2a.QIdentityCutPoint.bBc_cut_split (w := fun _ => (1 : ℂ)) (w₁ := fun _ => (0 : ℂ)) hM1 hc0 (hχc i) rfl rfl]
    ring
  obtain ⟨hA, -, -⟩ := sampleC_bounds a hg hg₁ hg₂c hang hc hχ0 hχc hχ hM hmass hJ hm hmM (η := y) le_rfl
  obtain ⟨hV, hV₁, -⟩ := vW_bounds a hg hg₁ hg₂c hang hc hχ0 hχc hχ hM hmass hJ hm hmM (t := M) le_rfl
  have hyg : y - 1 = j / m := by rw [hy, hjdef]; field_simp
  rw [hyg] at hA
  have hVeq : vW c χ g a M m M = sampleC c χ g a M (y : ℂ) := rfl
  have hS0 : 0 ≤ S := S0_nonneg c g a J M
  have hA0 : 0 ≤ A0 c (9 / 10) (1 / 4) := by unfold A0; positivity
  have hB0 : 0 ≤ B0 c (9 / 10) 24 := by unfold B0; positivity
  have hp : pP (M : ℝ) = (M : ℝ) ^ 2 - 1 := rfl
  have hp0 : 0 < (M : ℝ) ^ 2 - 1 := by nlinarith
  have heF : ‖eF c y M‖ = 1 := (continuous_eF c y).2 M
  have hnorm : ‖∑ i, (a i : ℂ) * bBc (vW c χ g a M m) (vW₁ c χ g a M m) c (χ i) (g i) y M‖
      ≤ (A0 c (9 / 10) (1 / 4) / (j / m) * S) ^ 2
        + 40 / 9 * B0 c (9 / 10) 24 * S * m / j ^ 2 * ((M : ℝ) ^ 2 - 1) * (1 / (9 * c ^ 2 * j) * S) := by
    rw [hsplit]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, norm_mul, heF, one_mul, hVeq, sq]
      exact mul_le_mul hA hA (norm_nonneg _) (by positivity)
    · rw [norm_mul, norm_mul, norm_mul, heF, one_mul, Complex.norm_real, Real.norm_eq_abs, hp,
        abs_of_pos hp0, ← mul_assoc]
      have hjm : (M : ℝ) - m = j := rfl
      rw [hjm] at hV₁
      exact mul_le_mul (mul_le_mul_of_nonneg_right hV₁ hp0.le) hpsi (norm_nonneg _) (by positivity)
  have hκ : 0 ≤ kap c := Real.sqrt_nonneg _
  have hre : |(∑ i, (a i : ℂ) * bBc (vW c χ g a M m) (vW₁ c χ g a M m) c (χ i) (g i) y M).re|
      ≤ ‖∑ i, (a i : ℂ) * bBc (vW c χ g a M m) (vW₁ c χ g a M m) c (χ i) (g i) y M‖ := Complex.abs_re_le_norm _
  have hJ0 : 0 ≤ J := le_trans (Nat.cast_nonneg _) hJ
  have hP0 : 0 ≤ P := integral_nonneg fun x => sq_nonneg _
  have hS2 : S ^ 2 = 6 * J / ((M : ℝ) ^ 2 - 1) * P := by
    rw [hS, S0, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hP0]
  have hmp : (m : ℝ) / ((M : ℝ) ^ 2 - 1) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hp0 (by norm_num)]; nlinarith
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * √(2 * c / π) / (m : ℝ))]
  calc 2 * √(2 * c / π) / m * |(∑ i, (a i : ℂ) * bBc (vW c χ g a M m) (vW₁ c χ g a M m) c (χ i) (g i) y M).re|
      ≤ 2 * kap c / m * ((A0 c (9 / 10) (1 / 4) / (j / m) * S) ^ 2
        + 40 / 9 * B0 c (9 / 10) 24 * S * m / j ^ 2 * ((M : ℝ) ^ 2 - 1) * (1 / (9 * c ^ 2 * j) * S)) :=
        mul_le_mul_of_nonneg_left (hre.trans hnorm) (by positivity)
    _ = 12 * kap c * J * (A0 c (9 / 10) (1 / 4) ^ 2 * (m / ((M : ℝ) ^ 2 - 1)) / j ^ 2) * P
        + 160 / 27 * kap c * J * B0 c (9 / 10) 24 / (c ^ 2 * j ^ 3) * P := by
        rw [show (A0 c (9 / 10) (1 / 4) / (j / m) * S) ^ 2 = (A0 c (9 / 10) (1 / 4) * m / j) ^ 2 * S ^ 2 by
          field_simp]
        rw [show 40 / 9 * B0 c (9 / 10) 24 * S * m / j ^ 2 * ((M : ℝ) ^ 2 - 1) * (1 / (9 * c ^ 2 * j) * S)
          = 40 / 81 * B0 c (9 / 10) 24 * m * ((M : ℝ) ^ 2 - 1) / (c ^ 2 * j ^ 3) * S ^ 2 by
          field_simp; ring]
        rw [hS2]
        field_simp
        ring
    _ ≤ 12 * kap c * J * (A0 c (9 / 10) (1 / 4) ^ 2 * (1 / 4) / j ^ 2) * P
        + 160 / 27 * kap c * J * B0 c (9 / 10) 24 / (c ^ 2 * j ^ 3) * P := by gcongr
    _ = _ := by ring

/-- **`|𝔇| ≤ γ_D·P`**, uniformly in `M`. -/
theorem D_le : |frakD c χ g a M| ≤ γD c J * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := by
  set P := ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 with hP
  have hP0 : 0 ≤ P := integral_nonneg fun x => sq_nonneg _
  have hJ0 : 0 ≤ J := le_trans (Nat.cast_nonneg _) hJ
  have hκ : 0 ≤ kap c := Real.sqrt_nonneg _
  have hc0 : 0 < c := by linarith
  have hA0 : 0 ≤ A0 c (9 / 10) (1 / 4) := by unfold A0; positivity
  have hB0 : 0 ≤ B0 c (9 / 10) 24 := by unfold B0; positivity
  unfold frakD
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun m hm => frakD_term_le a hg hg₁ hg₂c hang hc hχ0 hχc hχ hM hmass hJ
    (Finset.mem_Icc.1 hm).1 (by have := (Finset.mem_Icc.1 hm).2; omega)).trans ?_
  have s2 := sum_inv_pow_le (M := M) (k := 2) le_rfl
  have s3 := sum_inv_pow_le (M := M) (k := 3) (by norm_num)
  push_cast at s2 s3
  have e : ∑ m ∈ Finset.Icc 2 (M - 1), (3 * kap c * J * A0 c (9 / 10) (1 / 4) ^ 2 / ((M : ℝ) - m) ^ 2
          + 160 / 27 * kap c * J * B0 c (9 / 10) 24 / (c ^ 2 * ((M : ℝ) - m) ^ 3)) * P
      = (3 * kap c * J * A0 c (9 / 10) (1 / 4) ^ 2 * ∑ m ∈ Finset.Icc 2 (M - 1), 1 / ((M : ℝ) - m) ^ 2
          + 160 / 27 * kap c * J * B0 c (9 / 10) 24 / c ^ 2
            * ∑ m ∈ Finset.Icc 2 (M - 1), 1 / ((M : ℝ) - m) ^ 3) * P := by
    rw [← Finset.sum_mul]
    congr 1
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    field_simp
  rw [e]
  refine mul_le_mul_of_nonneg_right ?_ hP0
  have z2 : 0 ≤ zR 2 := tsum_nonneg fun n => by positivity
  have z3 : 0 ≤ zR 3 := tsum_nonneg fun n => by positivity
  have hlog : 0 ≤ 1 + Real.log 3 := by linarith [one_lt_log_three]
  have t1 : 3 * kap c * J * A0 c (9 / 10) (1 / 4) ^ 2 * ∑ m ∈ Finset.Icc 2 (M - 1), 1 / ((M : ℝ) - m) ^ 2
      ≤ 6 * J * kap c * A0 c (9 / 10) (1 / 4) ^ 2 * zR 2 := by
    have := mul_le_mul_of_nonneg_left s2 (by positivity : 0 ≤ 3 * kap c * J * A0 c (9 / 10) (1 / 4) ^ 2)
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hJ0 hκ) (sq_nonneg (A0 c (9 / 10) (1 / 4)))) z2]
  have t3 : 160 / 27 * kap c * J * B0 c (9 / 10) 24 / c ^ 2 * ∑ m ∈ Finset.Icc 2 (M - 1), 1 / ((M : ℝ) - m) ^ 3
      ≤ 60 * J * kap c * B0 c (9 / 10) 24 * zR 3 / (9 * (9 / 10) * c ^ 2) := by
    have := mul_le_mul_of_nonneg_left s3 (by positivity : 0 ≤ 160 / 27 * kap c * J * B0 c (9 / 10) 24 / c ^ 2)
    refine this.trans ?_
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ kap c * J * B0 c (9 / 10) 24 * zR 3 * c ^ 2 := by positivity
    nlinarith
  have t2 : 0 ≤ 3 * (1 + Real.log 3) * J * kap c / (16 * c ^ 2) := by positivity
  unfold γD
  linarith

/-! ### `𝔈₁`: the `t`-bulk on `(M, ∞)` -/

/-- **`𝔈₁` per cut**: `(2κ/m)|Re E_m| ≤ 2κ·(√(6J/(M² − 1))·M)·P·e1Br`, `h = √(M − m)`. -/
theorem frakE1_term_le {m : ℕ} (hm : 2 ≤ m) (hmM : m + 1 ≤ M) :
    |2 * √(2 * c / π) / m
        * (∑ i, (a i : ℂ) * ∫ t in Ioi (M : ℝ), eF c ((M : ℝ) / m) t * (psi c (g i) t : ℂ)
          * rRc (vW c χ g a M m) (vW₁ c χ g a M m) (vW₂ c χ g a M m) c (χ i) ((M : ℝ) / m) t).re|
      ≤ 2 * kap c * (√(6 * J / ((M : ℝ) ^ 2 - 1)) * M) * (∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2)
        * e1Br c ((M : ℝ) / ((M : ℝ) ^ 2 - 1)) (1 / ((M : ℝ) ^ 2 - 1)) √((M : ℝ) - m) := by
  have hc0 : 0 < c := by linarith
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmM' : (m : ℝ) + 1 ≤ M := by exact_mod_cast hmM
  have hm0 : (0 : ℝ) < m := by linarith
  have hlt : (m : ℝ) < M := by linarith
  set y := (M : ℝ) / m with hy
  set j := (M : ℝ) - m with hjdef
  have hj0 : 0 < j := by linarith
  set h := √j with hh
  have hh0 : 0 < h := Real.sqrt_pos.2 hj0
  have hjh : j = h ^ 2 := (Real.sq_sqrt hj0.le).symm
  set P := ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 with hP
  have hP0 : 0 ≤ P := integral_nonneg fun x => sq_nonneg _
  set u := √(6 * J / ((M : ℝ) ^ 2 - 1)) with hu
  have hS : S0 c g a J M = u * √P := rfl
  set S := S0 c g a J M
  have hS0 : 0 ≤ S := S0_nonneg c g a J M
  set A := A0 c (9 / 10) (1 / 4) with hA
  set B := B0 c (9 / 10) 24 with hB
  have hA0 : 0 ≤ A := by rw [hA]; unfold A0; positivity
  have hB0 : 0 ≤ B := by rw [hB]; unfold B0; positivity
  set kE := 1 + 3 / (8 * c) with hkE
  set kE' := 1 + 1 / (2 * c) with hkE'
  have hkE0 : 0 ≤ kE := by positivity
  have hkE'0 : 0 ≤ kE' := by positivity
  have hp0 : 0 < (M : ℝ) ^ 2 - 1 := by nlinarith
  set ν := (M : ℝ) / ((M : ℝ) ^ 2 - 1) with hν
  have hν0 : 0 ≤ ν := by positivity
  set f : ℕ → ℝ → ℝ := fun k t => 1 / |t - m| ^ k with hf
  have hfIoi : ∀ k, ∀ t ∈ Ioi (M : ℝ), f k t = 1 / (t - m) ^ k := fun k t ht => by
    have : (M : ℝ) < t := ht
    simp only [hf, abs_of_pos (by linarith : (0 : ℝ) < t - m)]
  have hf0 : ∀ k t, 0 ≤ f k t := fun k t => by simp only [hf]; positivity
  -- the weight bounds as profiles
  have hV : ∀ t ∈ Ioi (M : ℝ), ‖vW c χ g a M m t‖ ≤ A * S * m * f 1 t
      ∧ ‖vW₁ c χ g a M m t‖ ≤ 40 / 9 * B * S * m * f 2 t
      ∧ ‖vW₂ c χ g a M m t‖ ≤ 2 * (40 / 9) ^ 2 * B * S * m * f 3 t := by
    intro t ht
    obtain ⟨v0, v1, v2⟩ := vW_bounds a hg hg₁ hg₂c hang hc hχ0 hχc hχ hM hmass hJ hm hmM (t := t) (le_of_lt ht)
    rw [hfIoi 1 t ht, hfIoi 2 t ht, hfIoi 3 t ht]
    refine ⟨v0.trans (le_of_eq (by ring)), v1.trans (le_of_eq (by ring)), v2.trans (le_of_eq (by ring))⟩
  -- the profiles
  obtain ⟨mf1, If1⟩ := prof_memLp (m := (m : ℝ)) (M := M) hlt (k := 1) le_rfl
  obtain ⟨mf2, If2⟩ := prof_memLp (m := (m : ℝ)) (M := M) hlt (k := 2) (by norm_num)
  obtain ⟨mf3, If3⟩ := prof_memLp (m := (m : ℝ)) (M := M) hlt (k := 3) (by norm_num)
  have If1' : ∫ t in Ioi (M : ℝ), f 1 t ^ 2 = 1 / j := by simp only [hf]; rw [If1, hjdef]; norm_num
  have If2' : ∫ t in Ioi (M : ℝ), f 2 t ^ 2 = 1 / (3 * j ^ 3) := by simp only [hf]; rw [If2, hjdef]; norm_num
  have If3' : ∫ t in Ioi (M : ℝ), f 3 t ^ 2 = 1 / (5 * j ^ 5) := by simp only [hf]; rw [If3, hjdef]; norm_num
  -- the atom bounds
  set α₁ := kE * M / (c * j) * (40 / 9 * B * S * m)
  set β₁ := M / (2 * c ^ 2 * j) * (2 * (40 / 9) ^ 2 * B * S * m)
  set α₂ := (2 * kE * kE' * ν * M / (c * j) + M / (c ^ 2 * ((M : ℝ) ^ 2 - 1) * j)) * (A * S * m)
  set β₂ := 2 * kE' * ν * M / (c ^ 2 * j) * (40 / 9 * B * S * m)
  set α₃ := 4 * ν ^ 2 * kE' ^ 2 * M / (c ^ 2 * j) * (A * S * m)
  have hα₁ : 0 ≤ α₁ := by positivity
  have hβ₁ : 0 ≤ β₁ := by positivity
  have hα₂ : 0 ≤ α₂ := by positivity
  have hβ₂ : 0 ≤ β₂ := by positivity
  have hα₃ : 0 ≤ α₃ := by positivity
  have hpr : ∀ t ∈ Ioi (M : ℝ),
      Cvs.L2a.SigmaSquareMultiplier.pr₁ (vW₁ c χ g a M m) (vW₂ c χ g a M m) c (c ^ 2) y t ≤ α₁ * f 2 t + β₁ * f 3 t
      ∧ Cvs.L2a.SigmaSquareMultiplier.pr₂ (vW c χ g a M m) (vW₁ c χ g a M m) c (c ^ 2) y t ≤ α₂ * f 1 t + β₂ * f 2 t
      ∧ Cvs.L2a.SigmaSquareMultiplier.pr₃ (vW c χ g a M m) c (c ^ 2) y t ≤ α₃ * f 1 t + 0 * f 1 t := by
    intro t ht
    obtain ⟨v0, v1, v2⟩ := hV t ht
    obtain ⟨p1, p2, p3⟩ := pr_orbit (w := vW c χ g a M m) (w₁ := vW₁ c χ g a M m) (w₂ := vW₂ c χ g a M m)
      hc0 hM3 hm2 hmM' ht
    have c1 : 0 ≤ kE * M / (c * j) := by positivity
    have c2 : 0 ≤ M / (2 * c ^ 2 * j) := by positivity
    have c3 : 0 ≤ 2 * kE * kE' * ν * M / (c * j) + M / (c ^ 2 * ((M : ℝ) ^ 2 - 1) * j) := by positivity
    have c4 : 0 ≤ 2 * kE' * ν * M / (c ^ 2 * j) := by positivity
    have c5 : 0 ≤ 4 * ν ^ 2 * kE' ^ 2 * M / (c ^ 2 * j) := by positivity
    refine ⟨p1.trans ?_, p2.trans ?_, p3.trans ?_⟩
    · have e1 : (1 + 3 / (8 * c)) * M / (c * ((M : ℝ) - m)) = kE * M / (c * j) := rfl
      have e2 : (M : ℝ) / (2 * c ^ 2 * ((M : ℝ) - m)) = M / (2 * c ^ 2 * j) := rfl
      rw [e1, e2]
      calc kE * M / (c * j) * ‖vW₁ c χ g a M m t‖ + M / (2 * c ^ 2 * j) * ‖vW₂ c χ g a M m t‖
          ≤ kE * M / (c * j) * (40 / 9 * B * S * m * f 2 t)
            + M / (2 * c ^ 2 * j) * (2 * (40 / 9) ^ 2 * B * S * m * f 3 t) := by gcongr
        _ = _ := by ring
    · calc (2 * (1 + 3 / (8 * c)) * (1 + 1 / (2 * c)) * ((M : ℝ) / ((M : ℝ) ^ 2 - 1)) * M / (c * ((M : ℝ) - m))
            + (M : ℝ) / (c ^ 2 * ((M : ℝ) ^ 2 - 1) * ((M : ℝ) - m))) * ‖vW c χ g a M m t‖
            + 2 * (1 + 1 / (2 * c)) * ((M : ℝ) / ((M : ℝ) ^ 2 - 1)) * M / (c ^ 2 * ((M : ℝ) - m))
              * ‖vW₁ c χ g a M m t‖
          ≤ (2 * kE * kE' * ν * M / (c * j) + M / (c ^ 2 * ((M : ℝ) ^ 2 - 1) * j)) * (A * S * m * f 1 t)
            + 2 * kE' * ν * M / (c ^ 2 * j) * (40 / 9 * B * S * m * f 2 t) := by gcongr
        _ = _ := by ring
    · calc 4 * ((M : ℝ) / ((M : ℝ) ^ 2 - 1)) ^ 2 * (1 + 1 / (2 * c)) ^ 2 * M / (c ^ 2 * ((M : ℝ) - m))
            * ‖vW c χ g a M m t‖
          ≤ 4 * ν ^ 2 * kE' ^ 2 * M / (c ^ 2 * j) * (A * S * m * f 1 t) := by gcongr
        _ = _ := by ring
  -- the far `Q`
  have hratio : 10 ≤ ((M : ℝ) ^ 2 - 1) * (y ^ 2 - 1) := Cvs.L2a.QIdentityCutPoint.orbit_ratio M m hm (by omega)
  have hQ : ∀ t ∈ Ioi (M : ℝ), c ^ 2 ≤ 1 / 10 * ‖qQ c (c ^ 2) y t‖ := by
    intro t ht
    have hy1 : 1 ≤ y := by rw [hy, le_div_iff₀ hm0]; linarith
    have h1 := Cvs.L2a.QIdentityCutPoint.re_qQ_far_ge (c := c) (by linarith : (1 : ℝ) ≤ M) hy1 (le_of_lt ht) le_rfl
    have h2 := Complex.re_le_norm (qQ c (c ^ 2) y t)
    calc c ^ 2 = 1 / 10 * (c ^ 2 * 10) := by ring
      _ ≤ 1 / 10 * (c ^ 2 * (((M : ℝ) ^ 2 - 1) * (y ^ 2 - 1))) := by gcongr
      _ ≤ 1 / 10 * ‖qQ c (c ^ 2) y t‖ := by gcongr; exact h1.trans h2
  have hQ0 : ∀ t ∈ Ioi (M : ℝ), qQ c (c ^ 2) y t ≠ 0 := fun t ht h0 => by
    have := hQ t ht
    rw [h0, norm_zero, mul_zero] at this
    have : 0 < c ^ 2 := by positivity
    linarith
  have hD : ∀ i, |χ i - c ^ 2| ≤ c ^ 2 := fun i => by
    rw [abs_of_neg (by linarith [hχc i])]; linarith [hχ0 i]
  obtain ⟨hvc, hv₁c, hv₂c⟩ := continuousOn_vW (g := g) (χ := χ) a hc0 (M := M) (m := m) (by omega) (by omega)
    (s := Ioi (M : ℝ)) fun t (ht : (M : ℝ) < t) => show (0 : ℝ) < t by linarith
  obtain ⟨ae1, ae2, ae3⟩ := pr_aesm (c := c) (χ₀ := c ^ 2) (y := y) hvc hv₁c hv₂c hQ0
  have dom : ∀ {F G : ℝ → ℝ}, AEStronglyMeasurable F (volume.restrict (Ioi (M : ℝ))) →
      MemLp G 2 (volume.restrict (Ioi (M : ℝ))) → (∀ t ∈ Ioi (M : ℝ), 0 ≤ F t) →
      (∀ t ∈ Ioi (M : ℝ), F t ≤ G t) → MemLp F 2 (volume.restrict (Ioi (M : ℝ))) := by
    intro F G hF hG hF0 hFG
    refine hG.of_le hF ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_))
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hF0 t ht)]
    exact (hFG t ht).trans (le_abs_self _)
  have pr0 : ∀ t, 0 ≤ Cvs.L2a.SigmaSquareMultiplier.pr₁ (vW₁ c χ g a M m) (vW₂ c χ g a M m) c (c ^ 2) y t
      ∧ 0 ≤ Cvs.L2a.SigmaSquareMultiplier.pr₂ (vW c χ g a M m) (vW₁ c χ g a M m) c (c ^ 2) y t
      ∧ 0 ≤ Cvs.L2a.SigmaSquareMultiplier.pr₃ (vW c χ g a M m) c (c ^ 2) y t := fun t => by
    exact ⟨by unfold Cvs.L2a.SigmaSquareMultiplier.pr₁; positivity, by unfold Cvs.L2a.SigmaSquareMultiplier.pr₂; positivity, by unfold Cvs.L2a.SigmaSquareMultiplier.pr₃; positivity⟩
  have hp₁ := dom ae1 ((mf2.const_mul α₁).add (mf3.const_mul β₁)) (fun t _ => (pr0 t).1)
    (fun t ht => (hpr t ht).1)
  have hp₂ := dom ae2 ((mf1.const_mul α₂).add (mf2.const_mul β₂)) (fun t _ => (pr0 t).2.1)
    (fun t ht => (hpr t ht).2.1)
  have hp₃ := dom ae3 ((mf1.const_mul α₃).add (mf1.const_mul 0)) (fun t _ => (pr0 t).2.2)
    (fun t ht => (hpr t ht).2.2)
  have N1 := sqrt_window_le hα₁ hβ₁ measurableSet_Ioi (hf0 2) (hf0 3) mf2 mf3 If2'.le If3'.le
    (fun t _ => (pr0 t).1) (fun t ht => (hpr t ht).1)
  have N2 := sqrt_window_le hα₂ hβ₂ measurableSet_Ioi (hf0 1) (hf0 2) mf1 mf2 If1'.le If2'.le
    (fun t _ => (pr0 t).2.1) (fun t ht => (hpr t ht).2.1)
  have N3 := sqrt_window_le hα₃ le_rfl measurableSet_Ioi (hf0 1) (hf0 1) mf1 mf1 If1'.le If1'.le
    (fun t _ => (pr0 t).2.2) (fun t ht => (hpr t ht).2.2)
  have hE := Cvs.L2a.SigmaSquareMultiplier.span_bulk_le a hg hg₁ hg₂c hang hc0 hχ measurableSet_Ioi
    (fun t (ht : t ∈ Ioi (M : ℝ)) => show (1 : ℝ) < t by have : (M : ℝ) < t := ht; linarith)
    (w := vW c χ g a M m) (w₁ := vW₁ c χ g a M m) (w₂ := vW₂ c χ g a M m) (y := y) (χ₀ := c ^ 2) (D := c ^ 2)
    (ρ := 1 / 10) hD (by norm_num) (by norm_num) hQ hQ0 hp₁ hp₂ hp₃ (hvc.aestronglyMeasurable measurableSet_Ioi).aemeasurable
    (hv₁c.aestronglyMeasurable measurableSet_Ioi).aemeasurable (hv₂c.aestronglyMeasurable measurableSet_Ioi).aemeasurable
  have hE' : ‖∑ i, (a i : ℂ) * ∫ t in Ioi (M : ℝ), eF c y t * (psi c (g i) t : ℂ)
        * rRc (vW c χ g a M m) (vW₁ c χ g a M m) (vW₂ c χ g a M m) c (χ i) y t‖
      ≤ ((√(1 / (3 * j ^ 3)) * α₁ + √(1 / (5 * j ^ 5)) * β₁) / (1 - 1 / 10)
          + (√(1 / j) * α₂ + √(1 / (3 * j ^ 3)) * β₂) / (1 - 1 / 10) ^ 2
          + (√(1 / j) * α₃ + √(1 / j) * 0) / (1 - 1 / 10) ^ 3) * √P := by
    refine hE.trans ?_
    gcongr
  have q3 : √(1 / (3 * j ^ 3)) = 1 / (√3 * h ^ 3) := by
    rw [hjh]; exact sqrt_one_div_mul_sq_pow (by norm_num) hh0.le 3
  have q5 : √(1 / (5 * j ^ 5)) = 1 / (√5 * h ^ 5) := by
    rw [hjh]; exact sqrt_one_div_mul_sq_pow (by norm_num) hh0.le 5
  have q1 : √(1 / j) = 1 / h := by
    have := sqrt_one_div_mul_sq_pow (k := 1) (by norm_num) hh0.le 1
    rw [one_mul, pow_one, Real.sqrt_one, one_mul, pow_one] at this
    rw [hjh]; exact this
  rw [q3, q5, q1] at hE'
  have hre := Complex.abs_re_le_norm (∑ i, (a i : ℂ) * ∫ t in Ioi (M : ℝ), eF c y t * (psi c (g i) t : ℂ)
        * rRc (vW c χ g a M m) (vW₁ c χ g a M m) (vW₂ c χ g a M m) c (χ i) y t)
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * √(2 * c / π) / (m : ℝ))]
  refine (mul_le_mul_of_nonneg_left (hre.trans hE') (by positivity)).trans (le_of_eq ?_)
  set sP := √P with hsP
  have hPP : P = sP ^ 2 := (Real.sq_sqrt hP0).symm
  have h3 : √3 ≠ 0 := by positivity
  have h5 : √5 ≠ 0 := by positivity
  simp only [α₁, β₁, α₂, β₂, α₃, hS, hjh]
  rw [hPP, show √(2 * c / π) = kap c from rfl]
  unfold e1Br
  rw [← hA, ← hB, ← hkE, ← hkE']
  field_simp
  ring

/-- **`|𝔈₁| ≤ γ_E₁·P`**, uniformly in `M`. -/
theorem E1_le : |frakE1 c χ g a M| ≤ γE1 c J * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := by
  set P := ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 with hP
  have hP0 : 0 ≤ P := integral_nonneg fun x => sq_nonneg _
  have hJ0 : 0 ≤ J := le_trans (Nat.cast_nonneg _) hJ
  have hκ : 0 ≤ kap c := Real.sqrt_nonneg _
  have hc0 : 0 < c := by linarith
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hp0 : 0 < (M : ℝ) ^ 2 - 1 := by nlinarith
  obtain ⟨A, hA⟩ : ∃ x, x = A0 c (9 / 10) (1 / 4) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ x, x = B0 c (9 / 10) 24 := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; unfold A0; positivity
  have hB0 : 0 ≤ B := by rw [hB]; unfold B0; positivity
  obtain ⟨kE, hkE⟩ : ∃ x, x = 1 + 3 / (8 * c) := ⟨_, rfl⟩
  obtain ⟨kE', hkE'⟩ : ∃ x, x = 1 + 1 / (2 * c) := ⟨_, rfl⟩
  have hkE0 : 0 ≤ kE := by rw [hkE]; positivity
  have hkE'0 : 0 ≤ kE' := by rw [hkE']; positivity
  set ν := (M : ℝ) / ((M : ℝ) ^ 2 - 1) with hν
  set ip := 1 / ((M : ℝ) ^ 2 - 1) with hip
  have hν0 : 0 ≤ ν := by positivity
  have hip0 : 0 ≤ ip := by positivity
  obtain ⟨hν38, h8⟩ := pbar_facts hM3
  have hip8 : ip ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) h8
  set u := √(6 * J / ((M : ℝ) ^ 2 - 1)) with hu
  have huM : u * M ≤ 3 * √(6 * J) / √8 := sqrt_sixJ_mul_le hM3 hJ0
  have hu0 : 0 ≤ u * M := by positivity
  obtain ⟨z3, hz3d⟩ : ∃ x, x = zR (3 / 2) := ⟨_, rfl⟩
  obtain ⟨z5, hz5d⟩ : ∃ x, x = zR (5 / 2) := ⟨_, rfl⟩
  obtain ⟨z7, hz7d⟩ : ∃ x, x = zR (7 / 2) := ⟨_, rfl⟩
  have hz : ∀ s, 0 ≤ zR s := fun s => tsum_nonneg fun n => by positivity
  have hz3 : 0 ≤ z3 := hz3d ▸ hz _
  have hz5 : 0 ≤ z5 := hz5d ▸ hz _
  have hz7 : 0 ≤ z7 := hz7d ▸ hz _
  have hs3 : ∑ m ∈ Finset.Icc 2 (M - 1), 1 / √((M : ℝ) - m) ^ 3 ≤ z3 := by
    have := sum_inv_sqrt_pow_le (M := M) (k := 3) le_rfl
    rw [show ((3 : ℕ) : ℝ) / 2 = 3 / 2 by norm_num, ← hz3d] at this; exact this
  have hs5 : ∑ m ∈ Finset.Icc 2 (M - 1), 1 / √((M : ℝ) - m) ^ 5 ≤ z5 := by
    have := sum_inv_sqrt_pow_le (M := M) (k := 5) (by norm_num)
    rw [show ((5 : ℕ) : ℝ) / 2 = 5 / 2 by norm_num, ← hz5d] at this; exact this
  have hs7 : ∑ m ∈ Finset.Icc 2 (M - 1), 1 / √((M : ℝ) - m) ^ 7 ≤ z7 := by
    have := sum_inv_sqrt_pow_le (M := M) (k := 7) (by norm_num)
    rw [show ((7 : ℕ) : ℝ) / 2 = 7 / 2 by norm_num, ← hz7d] at this; exact this
  have hsq3 : 0 < √3 := by positivity
  have hsq5 : 0 < √5 := by positivity
  obtain ⟨E3, hE3d⟩ : ∃ E, E = (10 / 9) ^ 2 * (2 * kE * kE' * ν * A / c + A * ip / c ^ 2)
      + (10 / 9) ^ 3 * (4 * ν ^ 2 * kE' ^ 2 * A / c ^ 2) := ⟨_, rfl⟩
  obtain ⟨E5, hE5d⟩ : ∃ E, E = 10 / 9 * (40 / 9 * kE * B / (√3 * c))
      + (10 / 9) ^ 2 * (80 / 9 * kE' * ν * B / (√3 * c ^ 2)) := ⟨_, rfl⟩
  obtain ⟨E7, hE7d⟩ : ∃ E, E = 10 / 9 * (1600 / 81 * B / (√5 * c ^ 2)) := ⟨_, rfl⟩
  have hE3 : 0 ≤ E3 := by rw [hE3d]; positivity
  have hE5 : 0 ≤ E5 := by rw [hE5d]; positivity
  have hE7 : 0 ≤ E7 := by rw [hE7d]; positivity
  have esum : ∑ m ∈ Finset.Icc 2 (M - 1), e1Br c ν ip √((M : ℝ) - m)
      = E3 * ∑ m ∈ Finset.Icc 2 (M - 1), 1 / √((M : ℝ) - m) ^ 3
        + E5 * ∑ m ∈ Finset.Icc 2 (M - 1), 1 / √((M : ℝ) - m) ^ 5
        + E7 * ∑ m ∈ Finset.Icc 2 (M - 1), 1 / √((M : ℝ) - m) ^ 7 := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    unfold e1Br
    rw [← hA, ← hB, ← hkE, ← hkE', hE3d, hE5d, hE7d]
    ring
  have hbr : ∑ m ∈ Finset.Icc 2 (M - 1), e1Br c ν ip √((M : ℝ) - m) ≤ E3 * z3 + E5 * z5 + E7 * z7 := by
    rw [esum]
    gcongr
  -- the bracket of `γ_E₁`
  obtain ⟨E3', hE3'd⟩ : ∃ E, E = (10 / 9) ^ 2 * (2 * kE * kE' * (3 / 8) * A / c + A * (1 / 8) / c ^ 2)
      + (10 / 9) ^ 3 * (4 * (3 / 8) ^ 2 * kE' ^ 2 * A / c ^ 2) := ⟨_, rfl⟩
  obtain ⟨E5', hE5'd⟩ : ∃ E, E = 10 / 9 * (40 / 9 * kE * B / (√3 * c))
      + (10 / 9) ^ 2 * (80 / 9 * kE' * (3 / 8) * B / (√3 * c ^ 2)) := ⟨_, rfl⟩
  have h3 : E3 ≤ E3' := by rw [hE3d, hE3'd]; gcongr
  have h5 : E5 ≤ E5' := by rw [hE5d, hE5'd]; gcongr
  have hE3' : 0 ≤ E3' := by rw [hE3'd]; positivity
  have hE5' : 0 ≤ E5' := by rw [hE5'd]; positivity
  have hγ := e1_bracket_le (A := A) (B := B) (kE := kE) (kE' := kE') (z3 := z3) (z5 := z5) (z7 := z7)
    (s2 := √2) (s3 := √3) (s5 := √5) (L := 1 + Real.log 3) hc0 hA0 hB0 hkE0 hkE'0 hz3 hz5
    (by positivity) (by positivity) (by positivity) (by linarith [one_lt_log_three])
  rw [← hE3'd, ← hE5'd, ← hE7d] at hγ
  unfold frakE1
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun m hm => frakE1_term_le a hg hg₁ hg₂c hang hc hχ0 hχc hχ hM hmass hJ
    (Finset.mem_Icc.1 hm).1 (by have := (Finset.mem_Icc.1 hm).2; omega)).trans ?_
  rw [← Finset.mul_sum]
  have hK0 : 0 ≤ 2 * kap c * (u * M) * P := by positivity
  calc 2 * kap c * (u * M) * P * ∑ m ∈ Finset.Icc 2 (M - 1), e1Br c ν ip √((M : ℝ) - m)
      ≤ 2 * kap c * (u * M) * P * (E3' * z3 + E5' * z5 + E7 * z7) := by
        refine mul_le_mul_of_nonneg_left (hbr.trans ?_) hK0
        gcongr
    _ ≤ 2 * kap c * (3 * √(6 * J) / √8) * P * (E3' * z3 + E5' * z5 + E7 * z7) := by
        have : 0 ≤ E3' * z3 + E5' * z5 + E7 * z7 := by positivity
        gcongr
    _ ≤ γE1 c J * P := by
        unfold γE1
        rw [← hA, ← hB, ← hkE, ← hkE', ← hz3d, ← hz5d, ← hz7d]
        have h0 : 0 ≤ 2 * kap c * (3 * √(6 * J) / √8) * P := by positivity
        have := mul_le_mul_of_nonneg_left hγ h0
        refine this.trans (le_of_eq ?_)
        ring

/-- **Ca_le**: `|𝔇| ≤ γ_D·P` and `|𝔈₁| ≤ γ_E₁·P`, uniformly in `M`; these are `CutKernelRemainder`'s `hD` and `hE1`. -/
theorem Ca_le :
    |frakD c χ g a M| ≤ γD c J * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2
      ∧ |frakE1 c χ g a M| ≤ γE1 c J * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 :=
  ⟨D_le a hg hg₁ hg₂c hang hc hχ0 hχc hχ hM hmass hJ, E1_le a hg hg₁ hg₂c hang hc hχ0 hχc hχ hM hmass hJ⟩

/-- **`|𝒞_a| ≤ (γ_D + γ_E₁)·P`**, by `𝒞_a = 𝔇 − 𝔈₁`. -/
theorem calCa_le :
    |calCa c χ g a M| ≤ (γD c J + γE1 c J) * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 := by
  have hc0 : 0 < c := by linarith
  rw [Ca_eq_D_sub_E a hg hg₁ hg₂c hang hc0 hχ0 hχc hM]
  obtain ⟨hD, hE⟩ := Ca_le a hg hg₁ hg₂c hang hc hχ0 hχc hχ hM hmass hJ
  have := abs_sub (frakD c χ g a M) (frakE1 c χ g a M)
  linarith

end span

end Cvs.L2a.CornerKernelUniform
