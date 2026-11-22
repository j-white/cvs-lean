import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BandTransferBandForm
import Cvs.L2a.FarIntegrationByParts
import Cvs.L2a.QIdentityComplexWeight
import Cvs.L2a.QIdentityIterated
import Cvs.L2a.QIdentityRealWeight
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RungCauchySplit

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Q-identity at a cut point

`Q` is symmetric in `(x, y)` and affine in `χ`, and at `ξ = ±k` it is `Q(ξ) = p(c²y² − ξ²) − 2icxy`. Where `w = 1` and
`w′ = 0`, `QIdentityComplexWeight`'s boundary term is the Cauchy-split sample `μ(k)ψ⁺ + μ(−k)ψ⁻` with `μ(ξ) = e^{icxy}p[i(ξ − cy)/Q(ξ) + Q′/Q(ξ)²]`,
and its real part is the sample of `μ_s(ξ) = (μ(ξ) + conj μ(−ξ))/2`. The two sides of `Re Q` give the expansion ratios.
-/

namespace Cvs.L2a.QIdentityCutPoint

open Real Set Complex MeasureTheory
open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.L2a.FarIntegrationByParts Cvs.L2a.QIdentityComplexWeight Cvs.Prolate.RungCauchySplit
open scoped ComplexConjugate

/-! ### `Q` in `χ` and in `(x, y)` -/

/-- **`Q` is affine in `χ`**: `Q_χ = Q_{χ₀} + (χ − χ₀)`. -/
theorem qQ_add_chi (c χ χ₀ y x : ℝ) : qQ c χ y x = qQ c χ₀ y x + ((χ - χ₀ : ℝ) : ℂ) := by
  unfold qQ; push_cast; ring

/-! ### The wavenumber `k = cY` -/

/-- `p k² = q` on `x > 1`. -/
theorem pP_mul_kP_sq {c χ x : ℝ} (hx : 1 < x) (hc : 0 < c) (hχc : χ < c ^ 2) :
    pP x * kP c χ x ^ 2 = qP c χ x := by
  have hp := pP_pos hx
  have ha := aP_sq hx (by positivity : (0 : ℝ) < c ^ 2) hχc
  unfold kP
  field_simp
  rw [ha]

/-- The normalised wavenumber `Y = √(1 + σ²/(c²(x² − 1)))`. -/
noncomputable def yN (c χ x : ℝ) : ℝ := √(1 + (c ^ 2 - χ) / (c ^ 2 * (x ^ 2 - 1)))

/-- **`k = cY`** on `x > 1`. -/
theorem kP_eq_cY {c χ x : ℝ} (hx : 1 < x) (hc : 0 < c) (hχc : χ < c ^ 2) :
    kP c χ x = c * yN c χ x := by
  have hp := pP_pos hx
  have hk : 0 < kP c χ x := div_pos (aP_pos hx (by positivity) hχc) hp
  have h := pP_mul_kP_sq hx hc hχc
  unfold pP at hp h
  unfold qP at h
  have hx1 : 0 < x ^ 2 - 1 := hp
  have hin : 0 ≤ 1 + (c ^ 2 - χ) / (c ^ 2 * (x ^ 2 - 1)) := by
    have : 0 ≤ (c ^ 2 - χ) / (c ^ 2 * (x ^ 2 - 1)) := div_nonneg (by linarith) (by positivity)
    linarith
  rw [← sq_eq_sq₀ hk.le (by unfold yN; positivity), mul_pow, yN, Real.sq_sqrt hin]
  field_simp
  linear_combination h

/-! ### `Q` as a function of the wavenumber -/

/-- `Q(ξ) = p(c²y² − ξ²) − 2icxy`. -/
noncomputable def qQk (c y x ξ : ℝ) : ℂ :=
  ((pP x * (c ^ 2 * y ^ 2 - ξ ^ 2) : ℝ) : ℂ) - ((2 * c * x * y : ℝ) : ℂ) * I

theorem qQk_neg (c y x ξ : ℝ) : qQk c y x (-ξ) = qQk c y x ξ := by
  unfold qQk; push_cast; ring

/-- At `ξ = ±k`, `Q(ξ)` is the rung's `Q`. -/
theorem qQk_kP {c χ y x : ℝ} (hx : 1 < x) (hc : 0 < c) (hχc : χ < c ^ 2) :
    qQk c y x (kP c χ x) = qQ c χ y x := by
  have h := pP_mul_kP_sq hx hc hχc
  unfold pP qP at h
  apply Complex.ext
  · rw [qQ_re]
    simp only [qQk, pP, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im]
    linear_combination -h
  · rw [Cvs.L2a.QIdentityRealWeight.qQ_im]
    simp only [qQk, Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re]
    ring

/-- `|Q(ξ)| ≥ 2cxy`. -/
theorem le_norm_qQk_im {c y x ξ : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * c * x * y ≤ ‖qQk c y x ξ‖ := by
  refine le_trans ?_ (Complex.abs_im_le_norm _)
  have : (qQk c y x ξ).im = -(2 * c * x * y) := by
    simp only [qQk, Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re]
    ring
  rw [this, abs_neg, abs_of_nonneg (by positivity)]

/-- `|Q(ξ)| ≥ p|c²y² − ξ²|`. -/
theorem le_norm_qQk_re {c y x ξ : ℝ} (hx : 1 ≤ x) : pP x * |c ^ 2 * y ^ 2 - ξ ^ 2| ≤ ‖qQk c y x ξ‖ := by
  refine le_trans ?_ (Complex.abs_re_le_norm _)
  have : (qQk c y x ξ).re = pP x * (c ^ 2 * y ^ 2 - ξ ^ 2) := by
    simp only [qQk, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im]
    ring
  have hp : 0 ≤ pP x := by unfold pP; nlinarith
  rw [this, abs_mul, abs_of_nonneg hp]

/-! ### The cut multiplier -/

/-- The phase-free cut multiplier `μ̃(ξ) = p[i(ξ − cy)/Q(ξ) + Q′/Q(ξ)²]`. -/
noncomputable def muQ (c y x ξ : ℝ) : ℂ :=
  ((pP x : ℝ) : ℂ) * (I * ((ξ - c * y : ℝ) : ℂ) / qQk c y x ξ + qQ₁ c y x / qQk c y x ξ ^ 2)

/-- The exact cut multiplier `μ(ξ) = e^{icxy} μ̃(ξ)`. -/
noncomputable def muCut (c y x ξ : ℝ) : ℂ := eF c y x * muQ c y x ξ

/-- `B` at a cut point, where `w = 1` and `w′ = 0`. -/
theorem bBc_cut {w w₁ : ℝ → ℂ} {c χ y x : ℝ} {g : ℝ → ℝ} (h0 : w x = 1) (h1 : w₁ x = 0) :
    bBc w w₁ c χ g y x
      = eF c y x * ((rungU c g x : ℂ) / qQ c χ y x
        + ((pP x : ℝ) : ℂ) * (qQ₁ c y x / qQ c χ y x ^ 2 - I * ((c * y : ℝ) : ℂ) / qQ c χ y x)
          * (psi c g x : ℂ)) := by
  unfold bBc gWc gWc₁
  rw [h0, h1]
  ring

/-- **The cut boundary term in Cauchy-split form**: `B = μ(k)ψ⁺ + μ(−k)ψ⁻`. -/
theorem bBc_cut_split {w w₁ : ℝ → ℂ} {c χ y x : ℝ} {g : ℝ → ℝ} (hx : 1 < x) (hc : 0 < c)
    (hχc : χ < c ^ 2) (h0 : w x = 1) (h1 : w₁ x = 0) :
    bBc w w₁ c χ g y x = Cvs.L2a.BandTransferBandForm.smp (muCut c y x) c χ g x := by
  have hp : ((pP x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (pP_pos hx).ne'
  have ha : ((aP c χ x : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (aP_pos hx (by positivity : (0 : ℝ) < c ^ 2) hχc).ne'
  have hsum : psiP c χ g x + conj (psiP c χ g x) = (psi c g x : ℂ) := split_add_conj
  have hdiff : psiP c χ g x - conj (psiP c χ g x) = -I * ((rungU c g x / aP c χ x : ℝ) : ℂ) :=
    split_sub_conj
  have hU : (rungU c g x : ℂ)
      = ((pP x : ℝ) : ℂ) * I * ((kP c χ x : ℝ) : ℂ) * (psiP c χ g x - conj (psiP c χ g x)) := by
    rw [hdiff, kP]
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [bBc_cut h0 h1, ← hsum]
  unfold Cvs.L2a.BandTransferBandForm.smp muCut muQ
  rw [qQk_neg, qQk_kP hx hc hχc]
  push_cast
  linear_combination (eF c y x / qQ c χ y x) * hU

/-! ### The real part of a sample -/

/-- The symmetrised multiplier `μ_s(ξ) = (μ(ξ) + conj μ(−ξ))/2`. -/
noncomputable def muSym (μ : ℝ → ℂ) (ξ : ℝ) : ℂ := (μ ξ + conj (μ (-ξ))) / 2

/-- **The real part of a sample**: `Re S[μ] = S[μ_s]`. -/
theorem re_smp (μ : ℝ → ℂ) (c χ : ℝ) (g : ℝ → ℝ) (x : ℝ) :
    ((Cvs.L2a.BandTransferBandForm.smp μ c χ g x).re : ℂ) = Cvs.L2a.BandTransferBandForm.smp (muSym μ) c χ g x := by
  have h := Complex.add_conj (Cvs.L2a.BandTransferBandForm.smp μ c χ g x)
  unfold Cvs.L2a.BandTransferBandForm.smp muSym at *
  rw [neg_neg]
  simp only [map_add, map_mul, Complex.conj_conj] at h
  have h2 : (((μ (kP c χ x) * psiP c χ g x + μ (-kP c χ x) * conj (psiP c χ g x)).re : ℝ) : ℂ)
      = ((μ (kP c χ x) * psiP c χ g x + μ (-kP c χ x) * conj (psiP c χ g x))
        + (conj (μ (kP c χ x)) * conj (psiP c χ g x) + conj (μ (-kP c χ x)) * psiP c χ g x)) / 2 := by
    rw [h]; push_cast; ring
  rw [h2]
  ring

/-! ### `L²` membership along `y = t/m` -/

/-- The `L²` membership of the cut multiplier along `y = t/m` on `t > 1`. -/
theorem memLp_muCut_div {c x m : ℝ} (hx : 1 < x) (hc : 0 < c) (hm : 0 < m) (ξ : ℝ) :
    MemLp (fun t => muCut c (t / m) x ξ) 2 (volume.restrict (Ioi 1)) := by
  set f : ℝ → ℂ := fun t => muCut c (t / m) x ξ with hf_def
  have hp : 0 < pP x := pP_pos hx
  have hx0 : 0 < x := by linarith
  -- `Q(ξ) ≠ 0` for `y > 0`
  have hQne : ∀ y, 0 < y → qQk c y x ξ ≠ 0 := by
    intro y hy h
    have := le_norm_qQk_im (ξ := ξ) hc.le hx0.le hy.le
    rw [h, norm_zero] at this
    have : 0 < 2 * c * x * y := by positivity
    linarith
  -- continuity on `t > 0`
  have hcont : ContinuousOn f (Ioi 0) := by
    intro t ht
    have ht0 : 0 < t / m := div_pos ht hm
    have hQc : Continuous fun t : ℝ => qQk c (t / m) x ξ := by unfold qQk; fun_prop
    have hQ₁c : Continuous fun t : ℝ => qQ₁ c (t / m) x := by unfold qQ₁; fun_prop
    have hec : Continuous fun t : ℝ => eF c (t / m) x := by unfold eF; fun_prop
    have hlin : Continuous fun t : ℝ => ((ξ - c * (t / m) : ℝ) : ℂ) := by fun_prop
    have hne := hQne _ ht0
    refine ContinuousAt.continuousWithinAt ?_
    simp only [hf_def, muCut, muQ]
    refine hec.continuousAt.mul (continuousAt_const.mul ?_)
    refine ((continuousAt_const.mul hlin.continuousAt).div hQc.continuousAt hne).add
      (hQ₁c.continuousAt.div (hQc.continuousAt.pow 2) (pow_ne_zero 2 hne))
  -- the tail bound `‖μ̃(y)‖ ≤ K₀/y` for `y ≥ y₁`
  set D : ℝ := pP x * c ^ 2 / 2 with hD
  have hD0 : 0 < D := by positivity
  set y₁ : ℝ := 2 * |ξ| / c + 1 with hy₁
  have hy₁1 : 1 ≤ y₁ := by have : 0 ≤ 2 * |ξ| / c := by positivity
                           linarith
  set K₀ : ℝ := pP x * ((|ξ| + c) / D + (2 * c ^ 2 * x + 2 * c) / D ^ 2) with hK₀
  have htail : ∀ y, y₁ ≤ y → ‖muCut c y x ξ‖ ≤ K₀ / y := by
    intro y hy
    have hy1 : 1 ≤ y := hy₁1.trans hy
    have hy0 : 0 < y := by linarith
    have hcy : 2 * |ξ| ≤ c * y := by
      have : c * y₁ = 2 * |ξ| + c := by rw [hy₁]; field_simp
      nlinarith
    have hξsq : ξ ^ 2 ≤ c ^ 2 * y ^ 2 / 4 := by
      have h1 : |ξ| ^ 2 ≤ (c * y / 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (by linarith) 2
      rw [sq_abs] at h1; nlinarith
    have hQ : D * y ^ 2 ≤ ‖qQk c y x ξ‖ := by
      refine le_trans ?_ (le_norm_qQk_re hx.le)
      rw [abs_of_nonneg (by nlinarith)]
      rw [hD]; nlinarith
    have hQ0 : 0 < D * y ^ 2 := by positivity
    have hnQ0 : 0 < ‖qQk c y x ξ‖ := hQ0.trans_le hQ
    have hA : ‖I * ((ξ - c * y : ℝ) : ℂ)‖ ≤ (|ξ| + c) * y := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |ξ - c * y| ≤ |ξ| + |c * y| := abs_sub _ _
        _ = |ξ| + c * y := by rw [abs_of_nonneg (mul_nonneg hc.le hy0.le)]
        _ ≤ (|ξ| + c) * y := by nlinarith [abs_nonneg ξ]
    have hB : ‖qQ₁ c y x‖ ≤ (2 * c ^ 2 * x + 2 * c) * y ^ 2 := by
      refine (Cvs.L2a.QIdentityIterated.norm_qQ₁_le_far hx0.le hy1 hc.le).trans ?_
      have h1 : 0 ≤ 2 * c ^ 2 * x := by positivity
      have h2 : y ≤ y ^ 2 := by nlinarith
      have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * c)
      nlinarith
    have e1 : ‖I * ((ξ - c * y : ℝ) : ℂ) / qQk c y x ξ‖ ≤ (|ξ| + c) / D / y := by
      rw [norm_div]
      calc ‖I * ((ξ - c * y : ℝ) : ℂ)‖ / ‖qQk c y x ξ‖ ≤ (|ξ| + c) * y / (D * y ^ 2) := by
            gcongr
        _ = (|ξ| + c) / D / y := by field_simp
    have e2 : ‖qQ₁ c y x / qQk c y x ξ ^ 2‖ ≤ (2 * c ^ 2 * x + 2 * c) / D ^ 2 / y := by
      rw [norm_div, norm_pow]
      calc ‖qQ₁ c y x‖ / ‖qQk c y x ξ‖ ^ 2 ≤ (2 * c ^ 2 * x + 2 * c) * y ^ 2 / (D * y ^ 2) ^ 2 := by
            gcongr
        _ = (2 * c ^ 2 * x + 2 * c) / D ^ 2 / y / y := by field_simp
        _ ≤ (2 * c ^ 2 * x + 2 * c) / D ^ 2 / y := by
            apply div_le_self (by positivity) hy1
    unfold muCut muQ
    rw [norm_mul, (continuous_eF c y).2 x, one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hp]
    calc pP x * ‖I * ((ξ - c * y : ℝ) : ℂ) / qQk c y x ξ + qQ₁ c y x / qQk c y x ξ ^ 2‖
        ≤ pP x * ((|ξ| + c) / D / y + (2 * c ^ 2 * x + 2 * c) / D ^ 2 / y) := by
          gcongr; exact (norm_add_le _ _).trans (add_le_add e1 e2)
      _ = K₀ / y := by rw [hK₀]; field_simp
  -- the bound on the compact part
  set T : ℝ := m * y₁ + 1 with hT
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := T)).exists_bound_of_continuousOn
    (hcont.mono fun t ht => lt_of_lt_of_le one_pos ht.1)
  have hK0 : 0 ≤ K₀ := by positivity
  have hB0 : 0 ≤ B := by
    have := hB 1 ⟨le_rfl, by rw [hT]; nlinarith⟩
    exact (norm_nonneg _).trans this
  set K : ℝ := max (B * T) (K₀ * m) with hK
  have hglob : ∀ t, 1 < t → ‖f t‖ ≤ K / t := by
    intro t ht
    have ht0 : 0 < t := by linarith
    by_cases htT : t ≤ T
    · calc ‖f t‖ ≤ B := hB t ⟨ht.le, htT⟩
        _ ≤ B * T / t := by rw [le_div_iff₀ ht0]; gcongr
        _ ≤ K / t := by gcongr; exact le_max_left _ _
    · have hyt : y₁ ≤ t / m := by
        rw [le_div_iff₀ hm]; have htT' := not_le.mp htT; rw [hT] at htT'; nlinarith
      calc ‖f t‖ ≤ K₀ / (t / m) := htail _ hyt
        _ = K₀ * m / t := by field_simp
        _ ≤ K / t := by gcongr; exact le_max_right _ _
  -- `L²` from the `K/t` bound
  have hmeas : AEStronglyMeasurable f (volume.restrict (Ioi 1)) :=
    (hcont.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
    (by norm_num : (0 : ℝ) < 1)).const_mul (K ^ 2)) (hmeas.norm.pow 2) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
  have ht0 : 0 < t := lt_trans one_pos ht
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.rpow_neg ht0.le, Real.rpow_two]
  calc ‖f t‖ ^ 2 ≤ (K / t) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hglob t ht) 2
    _ = K ^ 2 * (t ^ 2)⁻¹ := by field_simp

/-! ### The cut multiplier at complex `y` -/

/-- `Q(ξ)` at complex `η`: `p(c²η² − ξ²) − 2icxη`. -/
noncomputable def qQkC (c x ξ : ℝ) (η : ℂ) : ℂ :=
  ((pP x : ℝ) : ℂ) * ((c : ℂ) ^ 2 * η ^ 2 - (ξ : ℂ) ^ 2) - 2 * I * (c : ℂ) * (x : ℂ) * η

/-- `Q′` at complex `η`: `2c²x(η² − 1) − 2icη`. -/
noncomputable def qQ₁C (c x : ℝ) (η : ℂ) : ℂ := 2 * (c : ℂ) ^ 2 * (x : ℂ) * (η ^ 2 - 1) - 2 * I * (c : ℂ) * η

/-- `μ̃` at complex `η`. -/
noncomputable def muQC (c x ξ : ℝ) (η : ℂ) : ℂ :=
  ((pP x : ℝ) : ℂ) * (I * ((ξ : ℂ) - (c : ℂ) * η) / qQkC c x ξ η + qQ₁C c x η / qQkC c x ξ η ^ 2)

theorem muQC_ofReal (c x ξ y : ℝ) : muQC c x ξ (y : ℂ) = muQ c y x ξ := by
  have h1 : qQkC c x ξ (y : ℂ) = qQk c y x ξ := by unfold qQkC qQk; push_cast; ring
  have h2 : qQ₁C c x (y : ℂ) = qQ₁ c y x := by unfold qQ₁C qQ₁; push_cast; ring
  unfold muQC muQ
  rw [h1, h2]
  push_cast
  ring

/-- `μ̃` is holomorphic off the zeros of `Q(ξ)`. -/
theorem differentiableAt_muQC {c x ξ : ℝ} {η : ℂ} (hQ : qQkC c x ξ η ≠ 0) :
    DifferentiableAt ℂ (muQC c x ξ) η := by
  have hQd : Differentiable ℂ (qQkC c x ξ) := by unfold qQkC; fun_prop
  have hQ₁d : Differentiable ℂ (qQ₁C c x) := by unfold qQ₁C; fun_prop
  have hl : Differentiable ℂ fun η : ℂ => I * ((ξ : ℂ) - (c : ℂ) * η) := by fun_prop
  have hQ2 : qQkC c x ξ η ^ 2 ≠ 0 := pow_ne_zero 2 hQ
  have e1 : DifferentiableAt ℂ (fun η : ℂ => I * ((ξ : ℂ) - (c : ℂ) * η) / qQkC c x ξ η) η :=
    DifferentiableAt.div (c := fun η : ℂ => I * ((ξ : ℂ) - (c : ℂ) * η)) (d := qQkC c x ξ)
      (hl η) (hQd η) hQ
  have e2 : DifferentiableAt ℂ (fun η : ℂ => qQ₁C c x η / qQkC c x ξ η ^ 2) η :=
    DifferentiableAt.div (c := qQ₁C c x) (d := fun η : ℂ => qQkC c x ξ η ^ 2)
      (hQ₁d η) ((hQd η).pow 2) hQ2
  have e3 := (differentiableAt_const (c := ((pP x : ℝ) : ℂ)) (x := η)).mul (e1.add e2)
  exact e3

/-- `Q(ξ) ≠ 0` on a neighbourhood of the positive real axis. -/
theorem qQkC_ne_zero {c x ξ : ℝ} (hc : 0 < c) (hx : 1 < x) {η : ℂ} (hη : 0 < η.re)
    (hηi : pP x * c * |η.im| < x) : qQkC c x ξ η ≠ 0 := by
  intro h
  have him : (qQkC c x ξ η).im = 2 * c * η.re * (pP x * c * η.im - x) := by
    simp only [qQkC, Complex.sub_im, Complex.mul_im, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, sq, Complex.re_ofNat, Complex.im_ofNat]
    ring
  rw [h, Complex.zero_im] at him
  have hp : 0 < pP x := pP_pos hx
  have h1 : pP x * c * η.im ≤ pP x * c * |η.im| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
  have h2 : 0 < 2 * c * η.re := by positivity
  have h3 : 2 * c * η.re * (pP x * c * η.im - x) < 0 := mul_neg_of_pos_of_neg h2 (by linarith)
  linarith

/-! ### The region ratios -/

/-- **Far side, exact**: `c²(x₀² − 1)(y₀² − 1) ≤ Re Q_{c²}` for `x ≥ x₀ ≥ 1`, `y ≥ y₀ ≥ 1`. -/
theorem re_qQ_far_ge {c x₀ y₀ x y : ℝ} (hx₀ : 1 ≤ x₀) (hy₀ : 1 ≤ y₀) (hx : x₀ ≤ x) (hy : y₀ ≤ y) :
    c ^ 2 * ((x₀ ^ 2 - 1) * (y₀ ^ 2 - 1)) ≤ (qQ c (c ^ 2) y x).re := by
  rw [qQ_re]
  have hx' : 0 ≤ x₀ ^ 2 - 1 := by nlinarith
  have hy' : 0 ≤ y₀ ^ 2 - 1 := by nlinarith
  have hxx : x₀ ^ 2 - 1 ≤ x ^ 2 - 1 := by nlinarith
  have hyy : y₀ ^ 2 - 1 ≤ y ^ 2 - 1 := by nlinarith
  have : (x₀ ^ 2 - 1) * (y₀ ^ 2 - 1) ≤ (x ^ 2 - 1) * (y ^ 2 - 1) := mul_le_mul hxx hyy hy' (hx'.trans hxx)
  have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
  nlinarith

/-- The near gap is a square: `(m² − 1)(1 − 4/m²) + 1 = (m − 2/m)²`. -/
theorem near_ratio_eq {m : ℝ} (hm : m ≠ 0) : (m ^ 2 - 1) * (1 - 4 / m ^ 2) + 1 = (m - 2 / m) ^ 2 := by
  field_simp
  ring

/-- The bottom near ratio, `m ≥ 3`, `t ≤ 2`: `(m² − 1)(1 − 4/m²) + 1 ≥ 49/9`. -/
theorem near_ratio {m : ℝ} (hm : 3 ≤ m) : 49 / 9 ≤ (m ^ 2 - 1) * (1 - 4 / m ^ 2) + 1 := by
  rw [near_ratio_eq (by linarith)]
  have h1 : 2 / m ≤ 2 / 3 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hm
  have h2 : (7 / 3 : ℝ) ≤ m - 2 / m := by linarith
  nlinarith

/-- The orbit ratio, `2 ≤ m ≤ M − 1`: `(M² − 1)((M/m)² − 1) ≥ 10`. -/
theorem orbit_ratio (M m : ℕ) (hm : 2 ≤ m) (hmM : m ≤ M - 1) :
    10 ≤ ((M : ℝ) ^ 2 - 1) * (((M : ℝ) / m) ^ 2 - 1) := by
  have hmr : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hMr : (m : ℝ) + 1 ≤ M := by exact_mod_cast (show m + 1 ≤ M by omega)
  have hm0 : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
  have he : ((M : ℝ) / m) ^ 2 - 1 = ((M : ℝ) ^ 2 - (m : ℝ) ^ 2) / (m : ℝ) ^ 2 := by
    field_simp
  rw [he, mul_div_assoc', le_div_iff₀ hm0]
  have h1 : 2 * (M : ℝ) - 1 ≤ (M : ℝ) ^ 2 - (m : ℝ) ^ 2 := by nlinarith
  have h2 : (m : ℝ) ^ 2 ≤ ((M : ℝ) - 1) ^ 2 := by nlinarith
  have h3 : 10 * ((M : ℝ) - 1) ^ 2 ≤ ((M : ℝ) ^ 2 - 1) * (2 * (M : ℝ) - 1) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * M - 3) (by linarith : (0 : ℝ) ≤ M - 3),
      (by linarith : (0 : ℝ) ≤ M - 1)]
  have h4 : 0 ≤ (M : ℝ) ^ 2 - 1 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h1 h4]

end Cvs.L2a.QIdentityCutPoint
