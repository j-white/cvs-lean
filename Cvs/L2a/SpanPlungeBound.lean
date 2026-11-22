import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.MirrorConcentrationHalf
import Cvs.Prolate.CorrectedEnergyPairAngular
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.ForbiddenZoneClosedForm
import Cvs.Prolate.ForbiddenZoneGrowth
import Cvs.Prolate.LiouvilleGreen.AiryTurningPoint
import Cvs.Prolate.LiouvilleGreen.AngularRateAiryUnits
import Cvs.Prolate.PlungeLawIntegral
import Cvs.Prolate.PlungeLawTwoZone
import Cvs.Prolate.RegularSolutionEdge

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The plunge bound P2♭ on the span and `ε_τ(s₀)`

Certificates `(11/20)max{T̄₁, T̄₂} ≤ 8/7` and `C_big ≤ 71/10`; the branch `S > c/4` by the exact
window; the uniform plunge bound `1 − λ ≤ plungeFlat s₀` for `S ≥ s₀ ≥ 5`; and the eigenvalue
bound `1 − ε_τ(s₀) ≤ μ√(c/(2π))` on every even-index rung of the span.
-/

namespace Cvs.L2a.SpanPlungeBound

open Real Set Filter Topology Cvs.L2a.AngularProlateTailPositive Cvs.L2a.MirrorConcentrationHalf Cvs.Prolate.RegularSolutionEdge Cvs.Prolate.EdgeCentreSign Cvs.Prolate.ForbiddenZoneGrowth Cvs.Prolate.PlungeLawIntegral Cvs.Prolate.ForbiddenZoneClosedForm Cvs.Prolate.LiouvilleGreen.AiryTurningPoint Cvs.Prolate.CorrectedEnergyPairAngular Cvs.Prolate.LiouvilleGreen.AngularRateAiryUnits Cvs.Prolate.PlungeLawTwoZone

/-! ### The rational atoms -/

theorem epsMax_pos : 0 < epsMax := cbrt_pos (by norm_num)

theorem epsMax_le : epsMax ≤ 102 / 6250 := by
  unfold epsMax; rw [cbrt_le_iff (by norm_num) (by norm_num)]; norm_num

theorem gMax5_pos : 0 < gMax5 := cbrt_pos (by norm_num)

theorem gMax5_le : gMax5 ≤ 5429 / 10000 := by
  unfold gMax5; rw [cbrt_le_iff (by norm_num) (by norm_num)]; norm_num

/-- `W(g, y) ≤ q` from the rational inequality `4g + 1/(y(1 + gy)) ≤ (2yq)²`. -/
theorem Wair_le_of {g y q : ℝ} (hg : 0 ≤ g) (hy : 0 < y) (hq : 0 ≤ q)
    (h : 4 * g + 1 / (y * (1 + g * y)) ≤ (2 * y * q) ^ 2) : Wair g y ≤ q := by
  rw [Wair_eq hg hy, div_le_iff₀ (by positivity)]
  calc √(4 * g + 1 / (y * (1 + g * y))) ≤ √((2 * y * q) ^ 2) := sqrt_le_sqrt h
    _ = q * (2 * y) := by rw [sqrt_sq (by positivity)]; ring

/-- The transport ratio at the worst rate on the virial cut: `R(W(ḡ, 4(1 − 4ε̄))) ≥ R(0.20104)`. -/
theorem Rcorr_four_ge : Rcorr (20104 / 100000) ≤ Rcorr (Wair gMax5 (4 * (1 - 4 * epsMax))) := by
  have hy : (373888 / 100000 : ℝ) ≤ 4 * (1 - 4 * epsMax) := by linarith [epsMax_le]
  have hW := (Wair_mono gMax5_pos.le gMax5_le (by linarith : (0 : ℝ) < 4 * (1 - 4 * epsMax))).trans
    (Wair_anti (by norm_num) (by norm_num) hy)
  have hq : Wair (5429 / 10000) (373888 / 100000) ≤ 20104 / 100000 :=
    Wair_le_of (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact Rcorr_anti (by linarith [Wair_pos gMax5_pos.le (by linarith : (0 : ℝ) < 4 * (1 - 4 * epsMax))])
    (hW.trans hq)

/-- The transport ratio at the worst rate on the window cut: `R(W(ḡ, 1 − ε̄)) ≥ R(0.85575)`. -/
theorem Rcorr_one_ge : Rcorr (85575 / 100000) ≤ Rcorr (Wair gMax5 (1 - epsMax)) := by
  have hy : (98368 / 100000 : ℝ) ≤ 1 - epsMax := by linarith [epsMax_le]
  have hW := (Wair_mono gMax5_pos.le gMax5_le (by linarith : (0 : ℝ) < 1 - epsMax)).trans
    (Wair_anti (by norm_num) (by norm_num) hy)
  have hq : Wair (5429 / 10000) (98368 / 100000) ≤ 85575 / 100000 :=
    Wair_le_of (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact Rcorr_anti (by linarith [Wair_pos gMax5_pos.le (by linarith : (0 : ℝ) < 1 - epsMax)])
    (hW.trans hq)

/-! ### The certificates -/

theorem T2bar_le : 11 / 20 * T2bar ≤ 8 / 7 := by
  have hR4 := Rcorr_four_ge
  have hR1 := Rcorr_one_ge
  have hr4 : Rcorr (20104 / 100000 : ℝ) = 179896 / 220104 := by unfold Rcorr; norm_num
  have hr1 : Rcorr (85575 / 100000 : ℝ) = 114425 / 285575 := by unfold Rcorr; norm_num
  rw [hr4] at hR4
  rw [hr1] at hR1
  have hε := epsMax_le
  have hA : (30827 / 10000 : ℝ) ≤ cbrt (1875 / 64) := by
    rw [le_cbrt_iff (by norm_num) (by norm_num)]; norm_num
  have hB : (15205 / 10000 : ℝ) ≤ cbrt (225 / 64) := by
    rw [le_cbrt_iff (by norm_num) (by norm_num)]; norm_num
  have hs : (9918 / 10000 : ℝ) ≤ √(1 - epsMax) := by
    rw [Real.le_sqrt' (by norm_num)]; linarith
  have ht : (21397 / 10000 : ℝ) ≤ √(cbrt (1875 / 64) + cbrt (225 / 64) * (1 - epsMax)) := by
    rw [Real.le_sqrt' (by norm_num)]
    nlinarith [mul_le_mul hB (by linarith : (98368 / 100000 : ℝ) ≤ 1 - epsMax) (by norm_num)
      (by linarith)]
  have hP : (179896 / 220104 : ℝ) * (114425 / 285575) * (9918 / 10000) * (21397 / 10000)
      ≤ Rcorr (Wair gMax5 (4 * (1 - 4 * epsMax))) * Rcorr (Wair gMax5 (1 - epsMax))
        * √(1 - epsMax) * √(cbrt (1875 / 64) + cbrt (225 / 64) * (1 - epsMax)) := by
    apply mul_le_mul (mul_le_mul (mul_le_mul hR4 hR1 (by norm_num) (by linarith)) hs (by norm_num)
      (by positivity)) ht (by norm_num) (by positivity)
  unfold T2bar
  calc 11 / 20 * (36 / 25 / (Rcorr (Wair gMax5 (4 * (1 - 4 * epsMax)))
        * Rcorr (Wair gMax5 (1 - epsMax)) * √(1 - epsMax)
        * √(cbrt (1875 / 64) + cbrt (225 / 64) * (1 - epsMax))))
      ≤ 11 / 20 * (36 / 25 / ((179896 / 220104 : ℝ) * (114425 / 285575) * (9918 / 10000)
          * (21397 / 10000))) := by
        gcongr
    _ ≤ 8 / 7 := by norm_num

theorem T1bar_le : 11 / 20 * T1bar ≤ 8 / 7 := by
  have hR := Rcorr_four_ge
  have hr4 : Rcorr (20104 / 100000 : ℝ) = 179896 / 220104 := by unfold Rcorr; norm_num
  rw [hr4] at hR
  have hε := epsMax_le
  have hε0 := epsMax_pos
  have hg := gMax5_le
  have hg0 := gMax5_pos
  have hm : mth 1 = 58 / 63 := by unfold mth; norm_num
  unfold T1bar T1f D1f betaf
  rw [hm, show epsMax * 4 = 4 * epsMax by ring]
  set R := Rcorr (Wair gMax5 (4 * (1 - 4 * epsMax))) with hRdef
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hκ : (93472 / 100000 : ℝ) ≤ 1 - 4 * epsMax := by linarith
  have h3 : (433 / 500 : ℝ) ≤ √3 / 2 := by
    rw [le_div_iff₀ (by norm_num), Real.le_sqrt' (by norm_num)]; norm_num
  have hsg : √gMax5 ≤ 737 / 1000 := by
    rw [Real.sqrt_le_left (by norm_num)]; linarith
  have hX : √(gMax5 * 4 / (1 - 4 * epsMax)) ≤ 1525 / 1000 := by
    rw [Real.sqrt_le_left (by norm_num), div_le_iff₀ (by linarith)]; nlinarith
  have hA : √(gMax5 * 4 / (1 - 4 * epsMax)) / (√3 / 2) ≤ 1525 / 1000 / (433 / 500) :=
    div_le_div₀ (by norm_num) hX (by norm_num) h3
  have hRR : (1 + R) / R ^ 2 ≤ 45 / 16 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have e : (1 + R) * √gMax5 / (4 * (√3 / 2) * R ^ 2 * (1 - 4 * epsMax) * 4)
      = (1 + R) / R ^ 2 * (√gMax5 / (16 * (√3 / 2) * (1 - 4 * epsMax))) := by
    field_simp; ring
  have hB2 : √gMax5 / (16 * (√3 / 2) * (1 - 4 * epsMax))
      ≤ 737 / 1000 / (16 * (433 / 500) * (93472 / 100000)) :=
    div_le_div₀ (by norm_num) hsg (by norm_num) (by gcongr)
  have hB : (1 + R) * √gMax5 / (4 * (√3 / 2) * R ^ 2 * (1 - 4 * epsMax) * 4)
      ≤ 45 / 16 * (737 / 1000 / (16 * (433 / 500) * (93472 / 100000))) := by
    rw [e]; exact mul_le_mul hRR hB2 (by positivity) (by norm_num)
  have hsum0 : 0 ≤ 1 / (2 * 5) + (√(gMax5 * 4 / (1 - 4 * epsMax)) / (√3 / 2)
      + (1 + R) * √gMax5 / (4 * (√3 / 2) * R ^ 2 * (1 - 4 * epsMax) * 4)) := by
    have : 0 < 1 - 4 * epsMax := by linarith
    positivity
  rw [div_div_eq_mul_div]
  calc 11 / 20 * ((1 / (2 * 5) + (√(gMax5 * 4 / (1 - 4 * epsMax)) / (√3 / 2)
        + (1 + R) * √gMax5 / (4 * (√3 / 2) * R ^ 2 * (1 - 4 * epsMax) * 4))) * √gMax5 / (58 / 63))
      ≤ 11 / 20 * ((1 / (2 * 5) + (1525 / 1000 / (433 / 500)
        + 45 / 16 * (737 / 1000 / (16 * (433 / 500) * (93472 / 100000))))) * (737 / 1000)
          / (58 / 63)) := by
        gcongr
    _ ≤ 8 / 7 := by norm_num

theorem Tbar_le : 11 / 20 * max T1bar T2bar ≤ 8 / 7 := by
  rw [mul_max_of_nonneg _ _ (by norm_num)]
  exact max_le T1bar_le T2bar_le

/-- **P2♭ with the certificate**: for `c ≥ 80` and `5c ≤ c² − χ ≤ c²/4`,
`1 − λ ≤ (8/7)e^{−2Φ_C(π(c² − χ)/(4c))}`. -/
theorem plunge_P2flat {g g₁ g₂ : ℝ → ℝ} {c χ μ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 80 ≤ c) (hD : 5 * c ≤ c ^ 2 - χ) (hD4 : 4 * (c ^ 2 - χ) ≤ c ^ 2)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0)
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) :
    1 - c / (2 * π) * μ ^ 2 ≤ 8 / 7 * Real.exp (-(2 * PhiC (π * (c ^ 2 - χ) / (4 * c)))) :=
  (plunge_P2flat_Tbar hg hg₁ hg₂c hang hc hD hD4 heven hg0 hμ).trans
    (mul_le_mul_of_nonneg_right Tbar_le (Real.exp_pos _).le)

/-- The constant of the branch `S > c/4`: `(11/20)(π + 1/40)e²/(45(2 − √3)/2)^{1/3}`. -/
noncomputable def Cbig : ℝ := 11 / 20 * (π + 1 / 40) * Real.exp 2 / cbrt (45 / 2 * (2 - √3))

theorem sqrt_three_le : √3 ≤ 17320509 / 10000000 := by
  rw [Real.sqrt_le_left (by norm_num)]; norm_num

theorem Cbig_den_ge : (182 / 100 : ℝ) ≤ cbrt (45 / 2 * (2 - √3)) := by
  have h3 := sqrt_three_le
  rw [le_cbrt_iff (by norm_num) (by linarith)]
  linarith

theorem Cbig_pos : 0 < Cbig := by
  unfold Cbig
  exact div_pos (by positivity) (lt_of_lt_of_le (by norm_num) Cbig_den_ge)

theorem Cbig_le : Cbig ≤ 71 / 10 := by
  have hden := Cbig_den_ge
  have he : Real.exp 2 < 2.7182818286 ^ 2 := by
    rw [show Real.exp 2 = Real.exp 1 ^ 2 by rw [← Real.exp_nat_mul]; norm_num]
    exact pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
  have hπ := Real.pi_lt_d4
  unfold Cbig
  rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) hden)]
  have h1 : 11 / 20 * (π + 1 / 40) * Real.exp 2 ≤ 11 / 20 * (3.1416 + 1 / 40) * 2.7182818286 ^ 2 := by
    gcongr
  have h2 : 71 / 10 * (182 / 100 : ℝ) ≤ 71 / 10 * cbrt (45 / 2 * (2 - √3)) := by gcongr
  have h3 : 11 / 20 * (3.1416 + 1 / 40) * (2.7182818286 : ℝ) ^ 2 ≤ 71 / 10 * (182 / 100) := by
    norm_num
  linarith

/-- **The branch `S > c/4`**: for `c ≥ 80` and `c² < 4(c² − χ)`, the window
`d = (9(1 − a)/(16c²))^{1/3}` gives `1 − λ ≤ C_big e^{−2Φ_C(π(c² − χ)/(4c))}`. -/
theorem plunge_large {g g₁ g₂ : ℝ → ℝ} {c χ μ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 80 ≤ c) (hχ0 : 0 ≤ χ) (hD4 : c ^ 2 < 4 * (c ^ 2 - χ))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0)
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) :
    1 - c / (2 * π) * μ ^ 2 ≤ Cbig * Real.exp (-(2 * PhiC (π * (c ^ 2 - χ) / (4 * c)))) := by
  have hc0 : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have hS : 0 < c ^ 2 - χ := by nlinarith
  have hχc : χ < c ^ 2 := by linarith
  have hD : 5 * c ≤ c ^ 2 - χ := by nlinarith
  have hP1 := plunge_P1 hg hg₁ hg₂c hang hc hχ0 hD heven hg0 hμ
  -- `K + c/(2(c² − χ)) ≤ π + 1/40`
  have hsq : c / 2 < √(c ^ 2 - χ) := by
    rw [Real.lt_sqrt (by positivity)]; nlinarith
  have hK : ellK c χ ≤ π := by
    refine (ellK_le hc0 hχ0 hχc).trans ?_
    have : c / √(c ^ 2 - χ) ≤ 2 := by rw [div_le_iff₀ (by positivity)]; linarith
    nlinarith [Real.pi_pos]
  have hα : c / (2 * (c ^ 2 - χ)) ≤ 1 / 40 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  -- the window `d`
  set a := √χ / c with hadef
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hc0.le
  have ha2 : a ^ 2 = χ / c ^ 2 := by rw [hadef, div_pow, sq_sqrt hχ0]
  have h32 : 0 < √3 / 2 := by positivity
  have hac : a < √3 / 2 := by
    rw [← pow_lt_pow_iff_left₀ ha0 h32.le two_ne_zero, ha2, div_pow, sq_sqrt (by norm_num),
      div_lt_iff₀ hc2]
    linarith
  have h3 := sqrt_three_le
  have h1a : 1 / 8 < 1 - a := by linarith
  have hca : 40 * (2 - √3) ≤ c * (1 - a) := by nlinarith
  set X := 9 * (1 - a) / (16 * c ^ 2) with hXdef
  have hX0 : 0 < X := by positivity
  set d := cbrt X with hddef
  have hd3 : d ^ 3 = X := cbrt_pow_three hX0.le
  have hd : 0 < d := cbrt_pos hX0
  have hdrop : 16 * c ^ 2 * d ^ 3 ≤ 9 * (1 - a) := by
    rw [hd3, hXdef]; field_simp; rfl
  have hd1 : d ≤ (1 - a) / 2 := by
    rw [hddef, cbrt_le_iff (by linarith) hX0.le, hXdef, div_le_iff₀ (by positivity)]
    have h10 : 10 ≤ c * (1 - a) := by nlinarith
    have : 9 * (1 - a) ≤ 2 * (c * (1 - a)) ^ 2 * (1 - a) := by nlinarith
    nlinarith
  have hJ := forbJ_ge_window hc0 hχ0 hχc hd hd1 hdrop
  set C₀ := cbrt (45 / 2 * (2 - √3)) with hC₀def
  have hC₀ : C₀ ≤ c * d := by
    rw [hC₀def, cbrt_le_iff (by positivity) (by linarith), mul_pow, hd3, hXdef]
    have e : c ^ 3 * (9 * (1 - a) / (16 * c ^ 2)) = 9 / 16 * (c * (1 - a)) := by
      field_simp
    rw [e]; linarith
  have hC₀0 : 0 < C₀ := lt_of_lt_of_le (by norm_num) Cbig_den_ge
  set Φ := PhiC (forbZ c χ a) with hΦdef
  set E := Real.exp (2 * Φ - 2) with hEdef
  have hE0 : 0 < E := Real.exp_pos _
  have hcJ : C₀ * E ≤ c * forbJ c χ := by
    calc C₀ * E ≤ c * d * E := mul_le_mul_of_nonneg_right hC₀ hE0.le
      _ = c * (d * E) := by ring
      _ ≤ c * forbJ c χ := mul_le_mul_of_nonneg_left hJ hc0.le
  have hstep : 1 - c / (2 * π) * μ ^ 2 ≤ 11 / 20 * (π + 1 / 40) / (C₀ * E) := by
    refine hP1.trans ?_
    rw [show 11 / 10 / 2 * (ellK c χ + c / (2 * (c ^ 2 - χ))) / (c * forbJ c χ)
      = 11 / 20 * (ellK c χ + c / (2 * (c ^ 2 - χ))) / (c * forbJ c χ) by ring]
    exact div_le_div₀ (by positivity) (by linarith) (by positivity) hcJ
  have heq : 11 / 20 * (π + 1 / 40) / (C₀ * E) = Cbig * Real.exp (-(2 * Φ)) := by
    have hEe : E * (Real.exp 2 * Real.exp (-(2 * Φ))) = 1 := by
      rw [hEdef, ← Real.exp_add, ← Real.exp_add]; ring_nf; exact Real.exp_zero
    have hE' : 1 / E = Real.exp 2 * Real.exp (-(2 * Φ)) := by
      rw [div_eq_iff hE0.ne']; linarith
    calc 11 / 20 * (π + 1 / 40) / (C₀ * E) = 11 / 20 * (π + 1 / 40) / C₀ * (1 / E) := by
          rw [mul_one_div, div_div]
      _ = Cbig * Real.exp (-(2 * Φ)) := by rw [hE']; unfold Cbig; rw [← hC₀def]; ring
  have hfz := exp_neg_two_PhiC_forbZ_le hc0 hχ0 hχc
  rw [← hadef, ← hΦdef] at hfz
  rw [heq] at hstep
  exact hstep.trans (mul_le_mul_of_nonneg_left hfz Cbig_pos.le)

/-! ### The uniform plunge bound on `S ≥ s₀` -/

/-- The plunge majorant for `S = (c² − χ)/c ≥ s₀`:
`max((8/7)e^{−2Φ_C(πs₀/4)}, C_big e^{−2Φ_C(π max(s₀, 20)/4)})`. -/
noncomputable def plungeFlat (s₀ : ℝ) : ℝ :=
  max (8 / 7 * Real.exp (-(2 * PhiC (π * s₀ / 4)))) (Cbig * Real.exp (-(2 * PhiC (π * max s₀ 20 / 4))))

theorem plungeFlat_nonneg (s₀ : ℝ) : 0 ≤ plungeFlat s₀ :=
  le_max_of_le_left (by positivity)

/-- **The uniform plunge bound**: for `c ≥ 80`, `s₀ ≥ 5` and `s₀c ≤ c² − χ`,
`1 − λ ≤ plungeFlat s₀`. -/
theorem plunge_flat {g g₁ g₂ : ℝ → ℝ} {c χ μ s₀ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 80 ≤ c) (hχ0 : 0 ≤ χ) (hs₀ : 5 ≤ s₀) (hσ : s₀ * c ≤ c ^ 2 - χ)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0)
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) :
    1 - c / (2 * π) * μ ^ 2 ≤ plungeFlat s₀ := by
  have hc0 : 0 < c := by linarith
  have hS : s₀ ≤ (c ^ 2 - χ) / c := by rw [le_div_iff₀ hc0]; linarith
  have hZ : ∀ t : ℝ, t ≤ (c ^ 2 - χ) / c → π * t / 4 ≤ π * (c ^ 2 - χ) / (4 * c) := by
    intro t ht
    rw [show π * (c ^ 2 - χ) / (4 * c) = π * ((c ^ 2 - χ) / c) / 4 by field_simp]
    gcongr
  rcases le_or_gt (4 * (c ^ 2 - χ)) (c ^ 2) with h4 | h4
  · have hD : 5 * c ≤ c ^ 2 - χ := by nlinarith
    refine (plunge_P2flat hg hg₁ hg₂c hang hc hD h4 heven hg0 hμ).trans (le_max_of_le_left ?_)
    exact mul_le_mul_of_nonneg_left
      (exp_neg_two_PhiC_anti (by positivity) (hZ s₀ hS)) (by norm_num)
  · refine (plunge_large hg hg₁ hg₂c hang hc hχ0 h4 heven hg0 hμ).trans (le_max_of_le_right ?_)
    have h20 : 20 ≤ (c ^ 2 - χ) / c := by rw [le_div_iff₀ hc0]; nlinarith
    exact mul_le_mul_of_nonneg_left
      (exp_neg_two_PhiC_anti (by positivity) (hZ _ (max_le hS h20))) Cbig_pos.le

/-! ### `ε_τ(s₀)` -/

/-- `ε_τ(s₀) = plungeFlat(s₀)/(1 + √(20/(11π)))`. -/
noncomputable def epsTauFlat (s₀ : ℝ) : ℝ := plungeFlat s₀ / (1 + √(20 / (11 * π)))

theorem epsTauFlat_nonneg (s₀ : ℝ) : 0 ≤ epsTauFlat s₀ :=
  div_nonneg (plungeFlat_nonneg s₀) (by positivity)

/-- **The eigenvalue bound**: an even rung with `ψ(1)g(1) > 0` and `S ≥ s₀ ≥ 5` has
`1 − ε_τ(s₀) ≤ μ√(c/(2π))`. -/
theorem tau_flat {g g₁ g₂ : ℝ → ℝ} {c χ μ s₀ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 80 ≤ c) (hχ0 : 0 ≤ χ) (hs₀ : 5 ≤ s₀) (hσ : s₀ * c ≤ c ^ 2 - χ)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0)
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) (hsign : 0 < psi c g 1 * g 1) :
    1 - epsTauFlat s₀ ≤ μ * √(c / (2 * π)) := by
  have hc0 : 0 < c := by linarith
  have hD : 5 * c ≤ c ^ 2 - χ := by nlinarith
  have hμ1 := hμ 1 ⟨by norm_num, le_rfl⟩
  have hμpos : 0 < μ := by
    rw [hμ1] at hsign
    by_contra h
    push Not at h
    nlinarith [mul_nonneg (neg_nonneg.2 h) (sq_nonneg (g 1))]
  obtain ⟨-, hlam, -⟩ := htau_concentration hg hg₁ hg₂c hang hc hχ0 hD heven hg0 hμ
  have hP := plunge_flat hg hg₁ hg₂c hang hc hχ0 hs₀ hσ heven hg0 hμ
  set τ := μ * √(c / (2 * π)) with hτdef
  have hτ0 : 0 ≤ τ := mul_nonneg hμpos.le (Real.sqrt_nonneg _)
  have hτ2 : τ ^ 2 = c / (2 * π) * μ ^ 2 := by
    rw [hτdef, mul_pow, sq_sqrt (by positivity)]; ring
  have hk : √(20 / (11 * π)) ≤ τ := by
    rw [← sqrt_sq hτ0]; exact sqrt_le_sqrt (by rw [hτ2]; exact hlam)
  have hk0 : 0 < 1 + √(20 / (11 * π)) := by positivity
  unfold epsTauFlat
  rcases le_total 1 τ with h | h
  · have := div_nonneg (plungeFlat_nonneg s₀) hk0.le
    linarith
  · have f1 : (1 - τ) * (1 + √(20 / (11 * π))) ≤ (1 - τ) * (1 + τ) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have f2 : (1 - τ) * (1 + τ) = 1 - c / (2 * π) * μ ^ 2 := by rw [← hτ2]; ring
    have f3 : 1 - τ ≤ plungeFlat s₀ / (1 + √(20 / (11 * π))) := by
      rw [le_div_iff₀ hk0]; linarith
    linarith

/-- **`ParametricFloorSqrtN`'s `hτ` on the span with `ε = ε_τ(s₀)`**: every even-index rung with `S ≥ s₀ ≥ 5`
has `1 − ε_τ(s₀) ≤ μ√(c/(2π))`. -/
theorem epsTau_P2flat {ι : Type*} {g g₁ g₂ : ι → ℝ → ℝ} {c s₀ : ℝ} {χ μ : ι → ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hs₀ : 5 ≤ s₀) (hχ0 : ∀ i, 0 ≤ χ i) (hσ : ∀ i, s₀ * c ≤ c ^ 2 - χ i)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s) (hg0 : ∀ i, ∃ s ∈ Icc (-1 : ℝ) 1, g i s ≠ 0)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (g i) s = μ i * g i s)
    (hidx : ∀ i, Even (evenSpec (sqC c) ∩ Iio (χ i)).ncard) :
    ∀ i, 1 - epsTauFlat s₀ ≤ μ i * √(c / (2 * π)) := by
  have hsign := hsign_of_even_index (by linarith) hχ0 hg hg₁ hg₂c hang heven hg0 hμ hidx
  intro i
  exact tau_flat (hg i) (hg₁ i) (hg₂c i) (hang i) hc (hχ0 i) hs₀ (hσ i) (heven i) (hg0 i) (hμ i)
    (hsign i)

theorem one_add_sqrt_ge : (176 / 100 : ℝ) ≤ 1 + √(20 / (11 * π)) := by
  have hπ := Real.pi_lt_d4
  have h : (76 / 100 : ℝ) ≤ √(20 / (11 * π)) := by
    rw [Real.le_sqrt' (by norm_num), le_div_iff₀ (by positivity)]; nlinarith
  linarith

/-- At `s₀ = 5`: `ε_τ(5) ≤ 7/1000`. -/
theorem epsTauFlat_five_le : epsTauFlat 5 ≤ 7 / 1000 := by
  have hk := one_add_sqrt_ge
  have hπl := Real.pi_gt_d4
  have hπu := Real.pi_lt_d4
  have he1 := Real.exp_one_gt_d9
  have he0 : (0 : ℝ) < 2.7182818283 := by norm_num
  -- the window term at `Z = 5π/4`
  set r := √((π * 5 / 4) ^ 2 + 9 / 4) with hrdef
  have hr1 : (42036 / 10000 : ℝ) ≤ r := by
    rw [hrdef, Real.le_sqrt' (by norm_num)]; nlinarith
  have hr2 : r ≤ 42038 / 10000 := by
    rw [hrdef, Real.sqrt_le_left (by norm_num)]; nlinarith [Real.pi_pos]
  have hL : (2.7182818283 : ℝ) ^ 5 * (1 + 4072 / 10000 + (4072 / 10000) ^ 2 / 2)
      ≤ Real.exp (5 + 4072 / 10000) := by
    rw [Real.exp_add, show Real.exp 5 = Real.exp 1 ^ 5 by rw [← Real.exp_nat_mul]; norm_num]
    exact mul_le_mul (pow_le_pow_left₀ he0.le he1.le 5)
      (Real.quadratic_le_exp_of_nonneg (by norm_num)) (by norm_num) (by positivity)
  have hX0 : Real.exp (3 - 2 * r) ≤ 1 / ((2.7182818283 : ℝ) ^ 5 * (1 + 4072 / 10000 + (4072 / 10000) ^ 2 / 2)) := by
    calc Real.exp (3 - 2 * r) ≤ Real.exp (-(5 + 4072 / 10000)) := Real.exp_le_exp.2 (by linarith)
      _ = 1 / Real.exp (5 + 4072 / 10000) := by rw [Real.exp_neg, one_div]
      _ ≤ _ := one_div_le_one_div_of_le (by positivity) hL
  have hX : Real.exp (-(2 * PhiC (π * 5 / 4)))
      ≤ 1 / ((2.7182818283 : ℝ) ^ 5 * (1 + 4072 / 10000 + (4072 / 10000) ^ 2 / 2))
        * (42038 / 10000 + 1 / 2) / 2 := by
    rw [exp_neg_two_PhiC, ← hrdef]
    gcongr
  -- the large-`S` term at `Z = 5π`
  have hY0 := exp_neg_two_PhiC_le (Z := π * max 5 20 / 4) (by positivity)
  rw [show max (5 : ℝ) 20 = 20 by norm_num] at hY0
  have hE : Real.exp 3 * Real.exp (-(2 * (π * 20 / 4))) ≤ 1 / (2.7182818283 : ℝ) ^ 28 := by
    rw [← Real.exp_add]
    calc Real.exp (3 + -(2 * (π * 20 / 4))) ≤ Real.exp (-28) := Real.exp_le_exp.2 (by linarith)
      _ = 1 / Real.exp 1 ^ 28 := by
          rw [Real.exp_neg, ← Real.exp_nat_mul, one_div]; norm_num
      _ ≤ _ := one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ he0.le he1.le 28)
  have hY : Real.exp (-(2 * PhiC (π * 20 / 4))) ≤ (5 * 31416 / 10000 + 2) / 2 / (2.7182818283 : ℝ) ^ 28 := by
    refine hY0.trans ?_
    have h1 : 0 ≤ π * 20 / 4 + 2 := by positivity
    calc Real.exp 3 / 2 * (π * 20 / 4 + 2) * Real.exp (-(2 * (π * 20 / 4)))
        = (π * 20 / 4 + 2) / 2 * (Real.exp 3 * Real.exp (-(2 * (π * 20 / 4)))) := by ring
      _ ≤ (5 * 31416 / 10000 + 2) / 2 * (1 / (2.7182818283 : ℝ) ^ 28) := by
          apply mul_le_mul (by linarith) hE (by positivity) (by positivity)
      _ = _ := by ring
  have hC := Cbig_le
  have hC0 := Cbig_pos
  unfold epsTauFlat plungeFlat
  rw [show max (5 : ℝ) 20 = 20 by norm_num, div_le_iff₀ (by positivity)]
  apply max_le
  · have : 8 / 7 * Real.exp (-(2 * PhiC (π * 5 / 4)))
        ≤ 8 / 7 * (1 / ((2.7182818283 : ℝ) ^ 5 * (1 + 4072 / 10000 + (4072 / 10000) ^ 2 / 2))
          * (42038 / 10000 + 1 / 2) / 2) := by gcongr
    have h2 : 8 / 7 * (1 / ((2.7182818283 : ℝ) ^ 5 * (1 + 4072 / 10000 + (4072 / 10000) ^ 2 / 2))
          * (42038 / 10000 + 1 / 2) / 2) ≤ 7 / 1000 * (176 / 100) := by norm_num
    nlinarith
  · have : Cbig * Real.exp (-(2 * PhiC (π * 20 / 4)))
        ≤ 71 / 10 * ((5 * 31416 / 10000 + 2) / 2 / (2.7182818283 : ℝ) ^ 28) :=
      mul_le_mul hC hY (Real.exp_pos _).le (by norm_num)
    have h2 : 71 / 10 * ((5 * 31416 / 10000 + 2) / 2 / (2.7182818283 : ℝ) ^ 28)
        ≤ 7 / 1000 * (176 / 100) := by norm_num
    nlinarith

end Cvs.L2a.SpanPlungeBound
