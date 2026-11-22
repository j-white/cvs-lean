import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.PositionTailSpanAdapters
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.SoninFunction
import Cvs.Prolate.PlungeLawIntegral
import Cvs.Prolate.RungConnectionIdentity
import Cvs.Prolate.RungExactOrthogonality
import Cvs.Prolate.SlepianCommutingRelation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The edge Bessel count

`ellK ≤ K̄(s) = ½ log(12c/s) + s/(12c) + 2/3` at `s = (c² − χ)/c`. Sonin (Cvs.Prolate.LiouvilleGreen.SoninFunction) and the integrated flux give
`|ψ − ψ(1)| ≤ |ψ(1)|(σ²v/2 + c²v²/4)`, `v = ξ − 1`. With `PlungeLawIntegral`'s mass law and Bessel's inequality for the orthogonal
rungs (Cvs.Prolate.RungExactOrthogonality) against `1_(1, 1+δ]`, `δ = 4/(3Sc)`: `#{i : s_i ≤ S} ≤ A_c S` for `S ≥ 5`.
-/

namespace Cvs.Prolate.EdgeBesselCount

open Real Set MeasureTheory intervalIntegral Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.Prolate.PlungeLawIntegral

/-- `K̄(s) = ½ log(12c/s) + s/(12c) + 2/3`, the majorant of `ellK` at `s = (c² − χ)/c`. -/
noncomputable def Kbar (c s : ℝ) : ℝ := Real.log (12 * c / s) / 2 + s / (12 * c) + 2 / 3

/-- The edge Taylor constant `β = 2/3 − 4/675` at `θ = 4/3`, `S ≥ 5`. -/
noncomputable def betaEdge : ℝ := 2 / 3 - 4 / 675

/-- The count constant `A_c = (33/40)(K̄(5)/2 + 1/20)/β²`. -/
noncomputable def Ac (c : ℝ) : ℝ := 33 / 40 * (Kbar c 5 / 2 + 1 / 20) / betaEdge ^ 2

/-- `|f(b) − f(a)| ≤ F(b) − F(a)` when `|f'| ≤ F'` on `(a, b)`. -/
theorem abs_sub_le_of_abs_deriv_le {f F f' F' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x) (hF : ∀ x ∈ Icc a b, HasDerivAt F (F' x) x)
    (h : ∀ x ∈ Ioo a b, |f' x| ≤ F' x) : |f b - f a| ≤ F b - F a := by
  have hm : ∀ s : ℝ, s = 1 ∨ s = -1 → MonotoneOn (fun x => F x - s * f x) (Icc a b) := by
    intro s hs
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun x => F' x - s * f' x) (convex_Icc a b)
      (fun x hx => ((hF x hx).sub ((hf x hx).const_mul s)).continuousAt.continuousWithinAt) ?_ ?_
    · rw [interior_Icc]; intro x hx
      exact ((hF x (Ioo_subset_Icc_self hx)).sub ((hf x (Ioo_subset_Icc_self hx)).const_mul s)).hasDerivWithinAt
    · rw [interior_Icc]; intro x hx
      have := h x hx
      rcases hs with rfl | rfl
      · have := le_abs_self (f' x); linarith
      · have := neg_abs_le (f' x); linarith
  have h1 := hm 1 (Or.inl rfl) (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  have h2 := hm (-1) (Or.inr rfl) (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  simp only at h1 h2
  rw [abs_le]; constructor <;> linarith

/-- The edge part of `ellK`: `c ∫₁² 1/a ≤ ½ log(12c/s) + s/(12c)`, `s = (c² − χ)/c`, through the antiderivative
`log(c√(ξ² − 1) + √(c²ξ² − χ))/c` of `ξ/a`. -/
theorem mul_integral_inv_aP_edge_le {c χ : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) :
    c * ∫ ξ in (1 : ℝ)..2, 1 / aP c χ ξ
      ≤ Real.log (12 * c / ((c ^ 2 - χ) / c)) / 2 + (c ^ 2 - χ) / c / (12 * c) := by
  have hσ : 0 < c ^ 2 - χ := by linarith
  set G : ℝ → ℝ := fun ξ => Real.log (c * √(ξ ^ 2 - 1) + √(c ^ 2 * ξ ^ 2 - χ)) / c with hG
  have hin : ∀ ξ, 1 ≤ ξ → 0 < c * √(ξ ^ 2 - 1) + √(c ^ 2 * ξ ^ 2 - χ) := fun ξ hξ => by
    have h1 : 1 ≤ ξ ^ 2 := by nlinarith
    have h2 : c ^ 2 * 1 ≤ c ^ 2 * ξ ^ 2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg c)
    have : 0 < √(c ^ 2 * ξ ^ 2 - χ) := Real.sqrt_pos.mpr (by linarith)
    have : 0 ≤ c * √(ξ ^ 2 - 1) := mul_nonneg hc.le (Real.sqrt_nonneg _)
    linarith
  have hcont : ContinuousOn G (Icc 1 2) := by
    refine ContinuousOn.div_const (ContinuousOn.log (by fun_prop) fun ξ (hξ : ξ ∈ Icc (1:ℝ) 2) => (hin ξ hξ.1).ne') c
  have hderiv : ∀ ξ ∈ Ioo (1 : ℝ) 2, HasDerivAt G (ξ / aP c χ ξ) ξ := by
    intro ξ hξ
    have hp : 0 < ξ ^ 2 - 1 := by nlinarith [hξ.1]
    have hq : 0 < c ^ 2 * ξ ^ 2 - χ := by nlinarith [hξ.1]
    have h1 : HasDerivAt (fun ξ => √(ξ ^ 2 - 1)) (2 * ξ / (2 * √(ξ ^ 2 - 1))) ξ := by
      have := ((hasDerivAt_pow 2 ξ).sub_const 1).sqrt hp.ne'
      simpa using this
    have h2 : HasDerivAt (fun ξ => √(c ^ 2 * ξ ^ 2 - χ)) (c ^ 2 * (2 * ξ) / (2 * √(c ^ 2 * ξ ^ 2 - χ))) ξ := by
      have := (((hasDerivAt_pow 2 ξ).const_mul (c ^ 2)).sub_const χ).sqrt hq.ne'
      simpa using this
    have h3 := ((h1.const_mul c).fun_add h2).log (hin ξ hξ.1.le).ne'
    refine (h3.div_const c).congr_deriv ?_
    have ha : aP c χ ξ = √(ξ ^ 2 - 1) * √(c ^ 2 * ξ ^ 2 - χ) := by
      unfold aP pP qP; rw [Real.sqrt_mul hp.le]
    rw [ha]
    have hsp : 0 < √(ξ ^ 2 - 1) := Real.sqrt_pos.mpr hp
    have hsq : 0 < √(c ^ 2 * ξ ^ 2 - χ) := Real.sqrt_pos.mpr hq
    have := hin ξ hξ.1.le
    field_simp
    ring
  have hint : IntegrableOn (fun ξ => 1 / aP c χ ξ) (Icc 1 2) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (integrableOn_inv_aP hc hχ0 hχ).mono_set Ioc_subset_Ioi_self
  have hle := integral_le_sub_of_hasDeriv_right_of_le (by norm_num : (1 : ℝ) ≤ 2) hcont
    (fun ξ hξ => (hderiv ξ hξ).hasDerivWithinAt) hint fun ξ hξ => by
      have ha : 0 < aP c χ ξ := aP_pos hξ.1 (by positivity) hχ
      exact div_le_div_of_nonneg_right hξ.1.le ha.le
  have hG1 : G 1 = Real.log (√(c ^ 2 - χ)) / c := by simp [hG]
  have hG2 : G 2 = Real.log (c * √3 + √(3 * c ^ 2 + (c ^ 2 - χ))) / c := by
    simp only [hG]; congr 2; norm_num; ring_nf
  -- the logarithmic bound
  set σ2 := c ^ 2 - χ with hσ2
  have h3 : 0 < √3 := by positivity
  have h33 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsσ : 0 < √σ2 := Real.sqrt_pos.mpr hσ
  have hsσ2 : √σ2 ^ 2 = σ2 := Real.sq_sqrt hσ.le
  set X := 2 * √3 * c / √σ2 with hX
  have hX0 : 0 < X := by positivity
  set t := σ2 / (12 * c ^ 2) with ht
  have ht0 : 0 ≤ t := by positivity
  have hroot : √(3 * c ^ 2 + σ2) ≤ √3 * c + σ2 / (2 * √3 * c) := by
    rw [Real.sqrt_le_left (by positivity)]
    have e : (√3 * c + σ2 / (2 * √3 * c)) ^ 2 = 3 * c ^ 2 + σ2 + σ2 ^ 2 / (12 * c ^ 2) := by
      field_simp; rw [h33]; ring
    rw [e]; have : 0 ≤ σ2 ^ 2 / (12 * c ^ 2) := by positivity
    linarith
  have hA : (c * √3 + √(3 * c ^ 2 + σ2)) / √σ2 ≤ X * (1 + t) := by
    rw [div_le_iff₀ hsσ]
    have e : X * (1 + t) * √σ2 = 2 * √3 * c + σ2 / (2 * √3 * c) := by
      rw [hX, ht]; field_simp; rw [h33]; ring
    rw [e]; linarith
  have hApos : 0 < (c * √3 + √(3 * c ^ 2 + σ2)) / √σ2 := by
    have : 0 ≤ √(3 * c ^ 2 + σ2) := Real.sqrt_nonneg _
    positivity
  have hlog : Real.log ((c * √3 + √(3 * c ^ 2 + σ2)) / √σ2) ≤ Real.log X + t := by
    calc Real.log ((c * √3 + √(3 * c ^ 2 + σ2)) / √σ2) ≤ Real.log (X * (1 + t)) :=
          Real.log_le_log hApos hA
      _ = Real.log X + Real.log (1 + t) := Real.log_mul hX0.ne' (by positivity)
      _ ≤ Real.log X + t := by
          have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + t); linarith
  have hXsq : 12 * c / (σ2 / c) = X ^ 2 := by
    rw [hX]; field_simp; rw [h33, hsσ2]; ring
  have hlogX : Real.log X = Real.log (12 * c / (σ2 / c)) / 2 := by
    rw [hXsq, Real.log_pow]; push_cast; ring
  have hts : t = σ2 / c / (12 * c) := by rw [ht]; field_simp
  have hnum : 0 < c * √3 + √(3 * c ^ 2 + σ2) := by
    have : 0 ≤ √(3 * c ^ 2 + σ2) := Real.sqrt_nonneg _
    positivity
  calc c * ∫ ξ in (1 : ℝ)..2, 1 / aP c χ ξ ≤ c * (G 2 - G 1) := mul_le_mul_of_nonneg_left hle hc.le
    _ = Real.log ((c * √3 + √(3 * c ^ 2 + σ2)) / √σ2) := by
        rw [hG1, hG2, Real.log_div hnum.ne' hsσ.ne']; field_simp
    _ ≤ Real.log X + t := hlog
    _ = Real.log (12 * c / (σ2 / c)) / 2 + σ2 / c / (12 * c) := by rw [hlogX, hts]

/-- The tail of `ellK`: `c ∫₂^∞ 1/a ≤ 2/3`, since `a ≥ c(ξ² − 1) ≥ (3/4)cξ²` beyond `2`. -/
theorem mul_integral_inv_aP_tail_le {c χ : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) :
    c * ∫ ξ in Ioi (2 : ℝ), 1 / aP c χ ξ ≤ 2 / 3 := by
  have hpow : IntegrableOn (fun ξ : ℝ => ξ ^ (-2 : ℝ)) (Ioi 2) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have hle : ∫ ξ in Ioi (2 : ℝ), 1 / aP c χ ξ ≤ ∫ ξ in Ioi (2 : ℝ), 4 / (3 * c) * ξ ^ (-2 : ℝ) := by
    refine setIntegral_mono_on ((integrableOn_inv_aP hc hχ0 hχ).mono_set (Ioi_subset_Ioi (by norm_num)))
      (hpow.const_mul _) measurableSet_Ioi fun ξ hξ => ?_
    have hξ2 : (2 : ℝ) < ξ := hξ
    have hξ0 : 0 < ξ := by linarith
    have hfar := Cvs.Prolate.RungConnectionIdentity.le_aP_far hχ.le (by linarith : (1 : ℝ) ≤ ξ)
    have h4 : 0 ≤ c * (ξ ^ 2 / 4 - 1) := mul_nonneg hc.le (by nlinarith)
    have h34 : 3 / 4 * c * ξ ^ 2 ≤ aP c χ ξ := by linarith
    rw [Real.rpow_neg hξ0.le, Real.rpow_two]
    calc 1 / aP c χ ξ ≤ 1 / (3 / 4 * c * ξ ^ 2) := one_div_le_one_div_of_le (by positivity) h34
      _ = 4 / (3 * c) * (ξ ^ 2)⁻¹ := by field_simp
  have hI : ∫ ξ in Ioi (2 : ℝ), 4 / (3 * c) * ξ ^ (-2 : ℝ) = 2 / (3 * c) := by
    rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) (by norm_num)]
    norm_num; field_simp; norm_num
  calc c * ∫ ξ in Ioi (2 : ℝ), 1 / aP c χ ξ ≤ c * (2 / (3 * c)) := by
        rw [← hI]; exact mul_le_mul_of_nonneg_left hle hc.le
    _ = 2 / 3 := by field_simp

/-- **`ellK ≤ K̄`**: `ellK c χ ≤ ½ log(12c/s) + s/(12c) + 2/3` at `s = (c² − χ)/c`. -/
theorem ellK_le_Kbar {c χ : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) :
    ellK c χ ≤ Kbar c ((c ^ 2 - χ) / c) := by
  have hint := integrableOn_inv_aP hc hχ0 hχ
  have hsplit : ∫ ξ in Ioi (1 : ℝ), 1 / aP c χ ξ
      = (∫ ξ in (1 : ℝ)..2, 1 / aP c χ ξ) + ∫ ξ in Ioi (2 : ℝ), 1 / aP c χ ξ := by
    rw [intervalIntegral.integral_of_le (by norm_num), ← setIntegral_union (Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi (by norm_num))),
      Ioc_union_Ioi_eq_Ioi (by norm_num)]
  have h1 := mul_integral_inv_aP_edge_le hc hχ0 hχ
  have h2 := mul_integral_inv_aP_tail_le hc hχ0 hχ
  unfold ellK Kbar
  rw [hsplit, mul_add]
  linarith

/-- `K̄(s) ≤ K̄(5)` for `5 ≤ s ≤ 6c`. -/
theorem Kbar_le_Kbar_five {c s : ℝ} (hc : 0 < c) (hs5 : 5 ≤ s) (hs : s ≤ 6 * c) : Kbar c s ≤ Kbar c 5 := by
  have hs0 : 0 < s := by linarith
  have hl : Real.log (12 * c / s) = Real.log (12 * c / 5) + Real.log (5 / s) := by
    rw [← Real.log_mul (by positivity) (by positivity)]; congr 1; field_simp
  have hlog := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 5 / s)
  have key : (s - 5) * (1 / (12 * c) - 1 / (2 * s)) ≤ 0 := by
    refine mul_nonpos_of_nonneg_of_nonpos (by linarith) ?_
    rw [sub_nonpos]; exact one_div_le_one_div_of_le (by positivity) (by linarith)
  unfold Kbar
  rw [hl]
  have e : 5 / s - 1 = -(s - 5) / s := by field_simp; ring
  have e2 : (s - 5) * (1 / (12 * c) - 1 / (2 * s)) = s / (12 * c) - 5 / (12 * c) + (-(s - 5) / s) / 2 := by
    field_simp; ring
  linarith

/-- **The edge Taylor bound**: `|ψ(ξ) − ψ(1)| ≤ |ψ(1)|(σ²(ξ − 1)/2 + c²(ξ − 1)²/4)`, `σ² = c² − χ`, for `ξ ≥ 1`. -/
theorem abs_psi_sub_psi_one_le {g g₁ g₂ : ℝ → ℝ} {c χ ξ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hχ : χ < c ^ 2) (hξ : 1 ≤ ξ) :
    |psi c g ξ - psi c g 1| ≤ |psi c g 1| * ((c ^ 2 - χ) * (ξ - 1) / 2 + c ^ 2 * (ξ - 1) ^ 2 / 4) := by
  obtain ⟨hψ, hv, hode⟩ := psi_system hg hg₁ hg₂c hang
  obtain ⟨-, hu, -, -⟩ := rung_system hg hg₁ hg₂c hang
  set v := Cvs.Prolate.SlepianCommutingRelation.kint g (fun ξ s => -(c * s * sin (c * ξ * s))) with hvdef
  set P := |psi c g 1| with hP
  have hP0 : 0 ≤ P := abs_nonneg _
  have hq : ∀ η, 1 ≤ η → 0 < qP c χ η := fun η hη => by
    have h1 : 1 ≤ η ^ 2 := by nlinarith
    have h2 : c ^ 2 * 1 ≤ c ^ 2 * η ^ 2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg c)
    unfold qP; linarith
  -- the integrated flux
  have hflux : ∀ η ∈ Icc 1 ξ, |rungU c g η| ≤ P * (c ^ 2 * (η ^ 3 - 1) / 3 - χ * (η - 1)) := by
    intro η hη
    have h := abs_sub_le_of_abs_deriv_le (f := rungU c g) (F := fun x => P * (c ^ 2 * (x ^ 3 - 1) / 3 - χ * (x - 1)))
      (f' := fun x => -(qP c χ x * psi c g x)) (F' := fun x => P * qP c χ x) hη.1 (fun x _ => hu x)
      (fun x _ => by
        have := ((((hasDerivAt_pow 3 x).sub_const 1).const_mul (c ^ 2)).div_const 3).fun_sub
          (((hasDerivAt_id' x).sub_const 1).const_mul χ)
        refine (this.const_mul P).congr_deriv ?_
        rw [mul_eq_mul_left_iff]; left; unfold qP; norm_num; ring)
      (fun x hx => by
        have hx1 : 1 ≤ x := hx.1.le
        have hS := Cvs.Prolate.LiouvilleGreen.SoninFunction.prolate_sq_le_edge hχ (⟨hx1, hx.2.le.trans hη.2⟩ : x ∈ Icc 1 ξ)
          (fun r _ => hψ r) (fun r _ => hv r) (fun r _ => hode r)
        have hb : |psi c g x| ≤ P := sq_le_sq.mp hS
        rw [abs_neg, abs_mul, abs_of_pos (hq x hx1)]
        exact mul_le_mul_of_nonneg_left hb (hq x hx1).le |>.trans_eq (mul_comm _ _))
    simpa [Cvs.L2a.PositionTailSpanAdapters.rungU_one] using h
  have h := abs_sub_le_of_abs_deriv_le (f := psi c g)
    (F := fun x => P * ((c ^ 2 - χ) * (x - 1) / 2 + c ^ 2 * (x - 1) ^ 2 / 4))
    (f' := v) (F' := fun x => P * ((c ^ 2 - χ) / 2 + c ^ 2 * (x - 1) / 2)) hξ (fun x _ => hψ x)
    (fun x _ => by
      have := ((((hasDerivAt_id' x).sub_const 1).const_mul (c ^ 2 - χ)).div_const 2).fun_add
        (((((hasDerivAt_id' x).sub_const 1).fun_pow 2).const_mul (c ^ 2)).div_const 4)
      refine (this.const_mul P).congr_deriv ?_
      rw [mul_eq_mul_left_iff]; left; norm_num; ring)
    (fun x hx => by
      have hx1 : 1 < x := hx.1
      have hp : 0 < pP x := pP_pos hx1
      have hf := hflux x ⟨hx1.le, hx.2.le⟩
      have hu : rungU c g x = pP x * v x := rfl
      rw [hu, abs_mul, abs_of_pos hp] at hf
      set y := x - 1 with hy
      have hy0 : 0 ≤ y := by linarith
      have hσ : 0 ≤ c ^ 2 - χ := by linarith
      have hQ : c ^ 2 * (x ^ 3 - 1) / 3 - χ * (x - 1) ≤ pP x * ((c ^ 2 - χ) / 2 + c ^ 2 * (x - 1) / 2) := by
        have e : pP x * ((c ^ 2 - χ) / 2 + c ^ 2 * (x - 1) / 2) - (c ^ 2 * (x ^ 3 - 1) / 3 - χ * (x - 1))
            = (c ^ 2 - χ) * y ^ 2 / 2 + c ^ 2 * y ^ 3 / 6 := by rw [hy]; unfold pP; ring
        have : 0 ≤ (c ^ 2 - χ) * y ^ 2 / 2 + c ^ 2 * y ^ 3 / 6 := by positivity
        linarith
      have : pP x * |v x| ≤ pP x * (P * ((c ^ 2 - χ) / 2 + c ^ 2 * (x - 1) / 2)) := by
        calc pP x * |v x| ≤ P * (c ^ 2 * (x ^ 3 - 1) / 3 - χ * (x - 1)) := hf
          _ ≤ P * (pP x * ((c ^ 2 - χ) / 2 + c ^ 2 * (x - 1) / 2)) := mul_le_mul_of_nonneg_left hQ hP0
          _ = pP x * (P * ((c ^ 2 - χ) / 2 + c ^ 2 * (x - 1) / 2)) := by ring
      exact le_of_mul_le_mul_left this hp)
  simpa using h

/-- **The edge integral**: `|∫₁^{1+δ} ψ| ≥ |ψ(1)|(δ − σ²δ²/4 − c²δ³/12)`, `σ² = c² − χ`, for `δ ≥ 0`. -/
theorem abs_integral_psi_edge_ge {g g₁ g₂ : ℝ → ℝ} {c χ δ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hχ : χ < c ^ 2) (hδ : 0 ≤ δ) :
    |psi c g 1| * (δ - (c ^ 2 - χ) * δ ^ 2 / 4 - c ^ 2 * δ ^ 3 / 12) ≤ |∫ ξ in (1 : ℝ)..1 + δ, psi c g ξ| := by
  have hψc := (rung_system hg hg₁ hg₂c hang).2.2.1
  set P := |psi c g 1| with hP
  have h := abs_sub_le_of_abs_deriv_le (f := fun x => (∫ ξ in (1 : ℝ)..x, psi c g ξ) - (x - 1) * psi c g 1)
    (F := fun x => P * ((c ^ 2 - χ) * (x - 1) ^ 2 / 4 + c ^ 2 * (x - 1) ^ 3 / 12))
    (f' := fun x => psi c g x - psi c g 1)
    (F' := fun x => P * ((c ^ 2 - χ) * (x - 1) / 2 + c ^ 2 * (x - 1) ^ 2 / 4))
    (by linarith : (1 : ℝ) ≤ 1 + δ)
    (fun x _ => by
      have := (hψc.integral_hasStrictDerivAt 1 x).hasDerivAt.sub
        (((hasDerivAt_id' x).sub_const 1).mul_const (psi c g 1))
      exact this.congr_deriv (by ring))
    (fun x _ => by
      have := (((((hasDerivAt_id' x).sub_const 1).fun_pow 2).const_mul (c ^ 2 - χ)).div_const 4).fun_add
        (((((hasDerivAt_id' x).sub_const 1).fun_pow 3).const_mul (c ^ 2)).div_const 12)
      refine (this.const_mul P).congr_deriv ?_
      rw [mul_eq_mul_left_iff]; left; norm_num; ring)
    (fun x hx => abs_psi_sub_psi_one_le hg hg₁ hg₂c hang hχ hx.1.le)
  simp only [integral_same, sub_self, zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, zero_div, add_zero, sub_zero, add_sub_cancel_left] at h
  have h2 := abs_sub_abs_le_abs_sub (δ * psi c g 1) (∫ ξ in (1 : ℝ)..1 + δ, psi c g ξ)
  rw [abs_sub_comm (δ * psi c g 1), abs_mul, abs_of_nonneg hδ] at h2
  nlinarith

/-- A rung with positive mass on `[1, X]` has `ψ(1) ≠ 0`: by Sonin, `ψ(1) = 0` forces `ψ = 0` on `[1, X]`. -/
theorem psi_one_ne_zero_of_mass_pos {g g₁ g₂ : ℝ → ℝ} {c χ X : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hχ : χ < c ^ 2) (hX : 1 ≤ X) (hM : 0 < ∫ ξ in (1 : ℝ)..X, psi c g ξ ^ 2) : psi c g 1 ≠ 0 := by
  intro h0
  obtain ⟨hψ, hv, hode⟩ := psi_system hg hg₁ hg₂c hang
  have hz : ∫ ξ in (1 : ℝ)..X, psi c g ξ ^ 2 = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun ξ hξ => ?_]
    · simp
    · rw [uIcc_of_le hX] at hξ
      have := Cvs.Prolate.LiouvilleGreen.SoninFunction.prolate_sq_le_edge hχ hξ (fun r _ => hψ r) (fun r _ => hv r)
        (fun r _ => hode r)
      rw [h0] at this
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at this
      exact le_antisymm this (sq_nonneg _)
  linarith

/-- **The mass law at the edge**: `∫₁^∞ ψ² ≤ (11/10)ψ(1)²(K̄(5) + 1/10)/(2c)` for `c ≥ 80`, `χ ≥ 0`, `c² − χ ≥ 5c`. -/
theorem mass_le_edge {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 80 ≤ c) (hχ0 : 0 ≤ χ) (hσ : 5 * c ≤ c ^ 2 - χ) :
    ∫ ξ in Ioi 1, psi c g ξ ^ 2 ≤ 11 / 10 * psi c g 1 ^ 2 * (Kbar c 5 + 1 / 10) / (2 * c) := by
  have hc0 : 0 < c := by linarith
  have hχc : χ < c ^ 2 := by nlinarith
  obtain ⟨hψ, hu, hψc, -⟩ := rung_system hg hg₁ hg₂c hang
  obtain ⟨-, hM⟩ := radial_mass_le hc0 hχ0 hχc hψ hu hψc (Cvs.L2a.PositionTailSpanAdapters.rungU_one c g)
    fun ξ hξ => energy_le_sup hg hg₁ hg₂c hang hc hχ0 hσ hξ
  set E := 11 / 10 * psi c g 1 ^ 2 with hE
  have hE0 : 0 ≤ E := by positivity
  have hs5 : 5 ≤ (c ^ 2 - χ) / c := by rw [le_div_iff₀ hc0]; linarith
  have hs6 : (c ^ 2 - χ) / c ≤ 6 * c := by rw [div_le_iff₀ hc0]; nlinarith
  have hK : c * ∫ ξ in Ioi (1 : ℝ), 1 / aP c χ ξ ≤ Kbar c 5 :=
    (ellK_le_Kbar hc0 hχ0 hχc).trans (Kbar_le_Kbar_five hc0 hs5 hs6)
  have h1 : E / 2 * ∫ ξ in Ioi (1 : ℝ), 1 / aP c χ ξ ≤ E / (2 * c) * Kbar c 5 := by
    rw [show E / 2 * ∫ ξ in Ioi (1 : ℝ), 1 / aP c χ ξ = E / (2 * c) * (c * ∫ ξ in Ioi (1 : ℝ), 1 / aP c χ ξ) by
      field_simp]
    exact mul_le_mul_of_nonneg_left hK (by positivity)
  have h2 : E / (4 * (c ^ 2 - χ)) ≤ E / (20 * c) :=
    div_le_div_of_nonneg_left hE0 (by positivity) (by linarith)
  have e : 11 / 10 * psi c g 1 ^ 2 * (Kbar c 5 + 1 / 10) / (2 * c) = E / (2 * c) * Kbar c 5 + E / (20 * c) := by
    rw [hE]; field_simp; ring
  rw [e]; linarith

/-- **Bessel's inequality against `1_(1, 1+δ]`**: rungs with pairwise distinct `χ_i` satisfy
`Σ_i (∫₁^{1+δ} ψ_i)²/∫₁^∞ ψ_i² ≤ δ`. -/
theorem sum_sq_integral_edge_div_le {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχinj : Function.Injective χ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∑ i, (∫ ξ in (1 : ℝ)..1 + δ, psi c (g i) ξ) ^ 2 / (∫ ξ in Ioi 1, psi c (g i) ξ ^ 2) ≤ δ := by
  set A : ι → ℝ := fun i => ∫ ξ in (1 : ℝ)..1 + δ, psi c (g i) ξ with hA
  set M : ι → ℝ := fun i => ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2 with hMdef
  show ∑ i, A i ^ 2 / M i ≤ δ
  set b : ι → ℝ := fun i => A i / M i with hb
  set φ : ℝ → ℝ := (Ioc 1 (1 + δ)).indicator (fun _ => (1 : ℝ)) with hφ
  set F : ℝ → ℝ := fun ξ => ∑ i, b i * psi c (g i) ξ with hF
  have hψc : ∀ i, Continuous (psi c (g i)) := fun i => (rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)).2.2.1
  have hFc : Continuous F := continuous_finsetSum _ fun i _ => continuous_const.mul (hψc i)
  have hsub : Ioi (1 : ℝ) ∩ Ioc 1 (1 + δ) = Ioc 1 (1 + δ) := inter_eq_right.mpr Ioc_subset_Ioi_self
  have hφint : IntegrableOn φ (Ioi 1) :=
    (((continuous_const (y := (1 : ℝ))).integrableOn_Icc (a := 1) (b := 1 + δ)).mono_set
      Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc |>.integrableOn
  have hφF : (fun ξ => φ ξ * F ξ) = (Ioc 1 (1 + δ)).indicator F := by
    funext ξ; by_cases h : ξ ∈ Ioc 1 (1 + δ) <;> simp [hφ, h]
  have hφFint : IntegrableOn (fun ξ => φ ξ * F ξ) (Ioi 1) := by
    rw [hφF]
    exact ((hFc.integrableOn_Icc).mono_set Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc
      |>.integrableOn
  have hF2 : (fun ξ => F ξ ^ 2) = fun ξ => ∑ i, ∑ j, b i * b j * (psi c (g i) ξ * psi c (g j) ξ) := by
    funext ξ; rw [hF, sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hF2int : IntegrableOn (fun ξ => F ξ ^ 2) (Ioi 1) := by
    rw [hF2]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (Cvs.Prolate.RungExactOrthogonality.integrableOn_psi_mul (hg i) (hg₁ i) (hg₂c i) (hang i) (hg j) (hg₁ j) (hg₂c j)
        (hang j) hc).const_mul _
  have hexp : ∀ ξ, (φ ξ - F ξ) ^ 2 = φ ξ - 2 * (φ ξ * F ξ) + F ξ ^ 2 := by
    intro ξ
    have : φ ξ ^ 2 = φ ξ := by by_cases h : ξ ∈ Ioc 1 (1 + δ) <;> simp [hφ, h]
    linear_combination this
  have h0 : 0 ≤ ∫ ξ in Ioi 1, (φ ξ - F ξ) ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have hsplit : ∫ ξ in Ioi 1, (φ ξ - F ξ) ^ 2
      = (∫ ξ in Ioi 1, φ ξ) - 2 * (∫ ξ in Ioi 1, φ ξ * F ξ) + ∫ ξ in Ioi 1, F ξ ^ 2 := by
    simp_rw [hexp]
    rw [integral_add (by exact hφint.sub (hφFint.const_mul 2)) hF2int,
      integral_sub hφint (by exact hφFint.const_mul 2), MeasureTheory.integral_const_mul]
  have hI1 : ∫ ξ in Ioi 1, φ ξ = δ := by
    rw [hφ, setIntegral_indicator measurableSet_Ioc, hsub, ← intervalIntegral.integral_of_le (by linarith)]
    simp
  have hI2 : ∫ ξ in Ioi 1, φ ξ * F ξ = ∑ i, b i * A i := by
    rw [hφF, setIntegral_indicator measurableSet_Ioc, hsub, ← intervalIntegral.integral_of_le (by linarith), hF,
      intervalIntegral.integral_finsetSum fun i _ => ((hψc i).intervalIntegrable _ _).const_mul _]
    exact Finset.sum_congr rfl fun i _ => intervalIntegral.integral_const_mul _ _
  have hI3 : ∫ ξ in Ioi 1, F ξ ^ 2 = ∑ i, b i ^ 2 * M i :=
    Cvs.Prolate.RungExactOrthogonality.integral_span_sq b hg hg₁ hg₂c hang hc hχinj
  have hterm : ∀ i, b i * A i = A i ^ 2 / M i ∧ b i ^ 2 * M i = A i ^ 2 / M i := by
    intro i
    rcases eq_or_ne (M i) 0 with h | h
    · simp [hb, h]
    · constructor
      · simp only [hb]; field_simp
      · simp only [hb]; field_simp
  have e1 : ∑ i, b i * A i = ∑ i, A i ^ 2 / M i := Finset.sum_congr rfl fun i _ => (hterm i).1
  have e2 : ∑ i, b i ^ 2 * M i = ∑ i, A i ^ 2 / M i := Finset.sum_congr rfl fun i _ => (hterm i).2
  rw [hsplit, hI1, hI2, hI3, e1, e2] at h0
  linarith

/-- **The edge Bessel count**: for rungs with pairwise distinct `χ_i ≥ 0`, `c² − χ_i ≥ 5c`, `ψ_i(1) ≠ 0` and
`c ≥ 80`, `#{i : (c² − χ_i)/c ≤ S} ≤ A_c S` for every `S ≥ 5`. -/
theorem edge_count_le {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hσ : ∀ i, 5 * c ≤ c ^ 2 - χ i) (hχinj : Function.Injective χ)
    (hψ1 : ∀ i, psi c (g i) 1 ≠ 0) {S : ℝ} (hS : 5 ≤ S) :
    ((Finset.univ.filter fun i => (c ^ 2 - χ i) / c ≤ S).card : ℝ) ≤ Ac c * S := by
  have hc0 : 0 < c := by linarith
  have hS0 : 0 < S := by linarith
  set δ := 4 / (3 * S * c) with hδ
  have hδ0 : 0 < δ := by positivity
  set β := betaEdge with hβ
  have hβ0 : 0 < β := by rw [hβ, betaEdge]; norm_num
  set K := Kbar c 5 with hK
  have hK0 : 0 < K + 1 / 10 := by
    have : 0 < Real.log (12 * c / 5) := Real.log_pos (by rw [one_lt_div (by norm_num)]; linarith)
    rw [hK, Kbar]; positivity
  set L := δ ^ 2 * β ^ 2 * (2 * c) / (11 / 10 * (K + 1 / 10)) with hL
  have hL0 : 0 < L := by positivity
  set A : ι → ℝ := fun i => ∫ ξ in (1 : ℝ)..1 + δ, psi c (g i) ξ with hA
  set M : ι → ℝ := fun i => ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2 with hMdef
  have hBessel : ∑ i, A i ^ 2 / M i ≤ δ := sum_sq_integral_edge_div_le hg hg₁ hg₂c hang hc0 hχinj hδ0.le
  have hM0 : ∀ i, 0 ≤ M i := fun i => setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have hcδ : c * δ = 4 / (3 * S) := by rw [hδ]; field_simp
  have hterm : ∀ i ∈ Finset.univ.filter (fun i => (c ^ 2 - χ i) / c ≤ S), L ≤ A i ^ 2 / M i := by
    intro i hi
    rw [Finset.mem_filter] at hi
    have hsS : c ^ 2 - χ i ≤ S * c := (div_le_iff₀ hc0).1 hi.2
    have hχc : χ i < c ^ 2 := by nlinarith [hσ i]
    have hP : 0 < psi c (g i) 1 ^ 2 := lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 (hψ1 i)).symm
    have hedge := abs_integral_psi_edge_ge (hg i) (hg₁ i) (hg₂c i) (hang i) hχc hδ0.le
    have hfac : δ * β ≤ δ - (c ^ 2 - χ i) * δ ^ 2 / 4 - c ^ 2 * δ ^ 3 / 12 := by
      have h1 : (c ^ 2 - χ i) * δ ≤ 4 / 3 := by
        calc (c ^ 2 - χ i) * δ ≤ S * c * δ := mul_le_mul_of_nonneg_right hsS hδ0.le
          _ = S * (c * δ) := by ring
          _ = 4 / 3 := by rw [hcδ]; field_simp
      have h2 : (c * δ) ^ 2 ≤ 16 / 225 := by
        rw [hcδ]
        have h3 : 4 / (3 * S) ≤ 4 / 15 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
        have h4 : 0 ≤ 4 / (3 * S) := by positivity
        nlinarith
      have e : δ - (c ^ 2 - χ i) * δ ^ 2 / 4 - c ^ 2 * δ ^ 3 / 12
          = δ * (1 - (c ^ 2 - χ i) * δ / 4 - (c * δ) ^ 2 / 12) := by ring
      rw [e]
      refine mul_le_mul_of_nonneg_left ?_ hδ0.le
      rw [hβ, betaEdge]; linarith
    have hAi : |psi c (g i) 1| * (δ * β) ≤ |A i| :=
      (mul_le_mul_of_nonneg_left hfac (abs_nonneg _)).trans hedge
    have hA2 : psi c (g i) 1 ^ 2 * (δ ^ 2 * β ^ 2) ≤ A i ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hAi 2
      rwa [mul_pow, sq_abs, sq_abs, mul_pow] at this
    have hMle := mass_le_edge (hg i) (hg₁ i) (hg₂c i) (hang i) hc (hχ0 i) (hσ i)
    have hApos : 0 < A i ^ 2 := lt_of_lt_of_le (by positivity) hA2
    have hMpos : 0 < M i := by
      rcases (hM0 i).lt_or_eq with h | h
      · exact h
      exfalso
      have hint : IntegrableOn (fun ξ => psi c (g i) ξ ^ 2) (Ioi 1) := by
        have := Cvs.Prolate.RungExactOrthogonality.integrableOn_psi_mul (hg i) (hg₁ i) (hg₂c i) (hang i) (hg i) (hg₁ i)
          (hg₂c i) (hang i) hc0
        exact (integrableOn_congr_fun (fun ξ _ => by ring) measurableSet_Ioi).mp this
      have hae := (setIntegral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun ξ => sq_nonneg _) hint).1 h.symm
      have hA0 : A i = 0 := by
        show ∫ ξ in (1 : ℝ)..1 + δ, psi c (g i) ξ = 0
        rw [intervalIntegral.integral_of_le (by linarith)]
        apply integral_eq_zero_of_ae
        filter_upwards [ae_restrict_of_ae_restrict_of_subset Ioc_subset_Ioi_self hae] with ξ hξ
        simpa using hξ
      rw [hA0] at hApos
      simp at hApos
    calc L = psi c (g i) 1 ^ 2 * (δ ^ 2 * β ^ 2) / (11 / 10 * psi c (g i) 1 ^ 2 * (K + 1 / 10) / (2 * c)) := by
          have := hψ1 i; rw [hL]; field_simp
      _ ≤ A i ^ 2 / M i := div_le_div₀ (sq_nonneg _) hA2 hMpos hMle
  have hsum : ((Finset.univ.filter fun i => (c ^ 2 - χ i) / c ≤ S).card : ℝ) * L ≤ δ := by
    calc ((Finset.univ.filter fun i => (c ^ 2 - χ i) / c ≤ S).card : ℝ) * L
        = ∑ i ∈ Finset.univ.filter (fun i => (c ^ 2 - χ i) / c ≤ S), L := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ Finset.univ.filter (fun i => (c ^ 2 - χ i) / c ≤ S), A i ^ 2 / M i := Finset.sum_le_sum hterm
      _ ≤ ∑ i, A i ^ 2 / M i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun i _ _ => div_nonneg (sq_nonneg _) (hM0 i)
      _ ≤ δ := hBessel
  have e : δ / L = Ac c * S := by
    rw [hL, hδ, Ac, ← hK, ← hβ]; field_simp; ring
  rw [← e, le_div_iff₀ hL0]
  exact hsum

end Cvs.Prolate.EdgeBesselCount
