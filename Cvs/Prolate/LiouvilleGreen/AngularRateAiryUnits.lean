import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.Compact
import Cvs.Prolate.CorrectedEnergyPairAngular
import Cvs.Prolate.LiouvilleGreen.AiryTurningPoint
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Angular_K in Airy units: the rate majorant `W(y)` and the worst-case ratios

In the units `l, g, ε` of Cvs.Prolate.LiouvilleGreen.AiryTurningPoint with `y = x(1 − εx)`: `w(a − xl) ≤ W(y) = (1 + 2gy)/(2y^{3/2}√(1 + gy))`,
`a(a − θl) = (2a/g)√(y(1 + gy))`, and the top-window length and `c/Q` are closed forms in `Θ`. For
`c ≥ 80`, `5 ≤ S = c(1 − a²) ≤ c/4`: `T₁ ≤ T̄₁`, `T₂ ≤ T̄₂`, the ratios at `S = 5`, `a = √3/2`.
-/

namespace Cvs.Prolate.LiouvilleGreen.AngularRateAiryUnits

open Real Set Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.LiouvilleGreen.AiryTurningPoint Cvs.Prolate.CorrectedEnergyPairAngular

/-- The Airy rate majorant `W(y) = (1 + 2gy)/(2y^{3/2}√(1 + gy))`. -/
noncomputable def Wair (g y : ℝ) : ℝ := (1 + 2 * g * y) / (2 * y * √y * √(1 + g * y))

theorem Wair_eq {g y : ℝ} (hg : 0 ≤ g) (hy : 0 < y) :
    Wair g y = √(4 * g + 1 / (y * (1 + g * y))) / (2 * y) := by
  have h1 : 0 < 1 + g * y := by positivity
  have e : 4 * g + 1 / (y * (1 + g * y)) = (1 + 2 * g * y) ^ 2 / (y * (1 + g * y)) := by
    field_simp; ring
  have hsy := sqrt_pos.mpr hy
  have hs1 := sqrt_pos.mpr h1
  rw [e, sqrt_div' _ (by positivity), sqrt_sq (by positivity), sqrt_mul hy.le]
  unfold Wair
  field_simp

theorem Wair_pos {g y : ℝ} (hg : 0 ≤ g) (hy : 0 < y) : 0 < Wair g y := by
  have h1 : 0 < 1 + g * y := by positivity
  have hsy := sqrt_pos.mpr hy
  have hs1 := sqrt_pos.mpr h1
  unfold Wair; positivity

theorem Wair_anti {g y y' : ℝ} (hg : 0 ≤ g) (hy : 0 < y) (hyy' : y ≤ y') : Wair g y' ≤ Wair g y := by
  have hy' : 0 < y' := hy.trans_le hyy'
  rw [Wair_eq hg hy, Wair_eq hg hy']
  apply div_le_div₀ (sqrt_nonneg _) _ (by positivity) (by linarith)
  apply sqrt_le_sqrt
  have h1 : y * (1 + g * y) ≤ y' * (1 + g * y') := by
    have : g * y ≤ g * y' := mul_le_mul_of_nonneg_left hyy' hg
    nlinarith
  have := one_div_le_one_div_of_le (by positivity) h1
  linarith

theorem Wair_mono {g g' y : ℝ} (hg : 0 ≤ g) (hgg' : g ≤ g') (hy : 0 < y) : Wair g y ≤ Wair g' y := by
  have hg' : 0 ≤ g' := hg.trans hgg'
  have h1 : 0 < 1 + g * y := by positivity
  have h1' : 0 < 1 + g' * y := by positivity
  have hsy := sqrt_pos.mpr hy
  have hs1 := sqrt_pos.mpr h1
  have hs1' := sqrt_pos.mpr h1'
  have key : (1 + 2 * g * y) * √(1 + g' * y) ≤ (1 + 2 * g' * y) * √(1 + g * y) := by
    rw [show (1 + 2 * g * y) * √(1 + g' * y) = √((1 + 2 * g * y) ^ 2 * (1 + g' * y)) by
        rw [sqrt_mul (by positivity), sqrt_sq (by positivity)],
      show (1 + 2 * g' * y) * √(1 + g * y) = √((1 + 2 * g' * y) ^ 2 * (1 + g * y)) by
        rw [sqrt_mul (by positivity), sqrt_sq (by positivity)]]
    apply sqrt_le_sqrt
    have hz : 0 ≤ g * y := by positivity
    have hzz : g * y ≤ g' * y := mul_le_mul_of_nonneg_right hgg' hy.le
    nlinarith [mul_nonneg (sub_nonneg.2 hzz) (by positivity : (0 : ℝ) ≤ 3 + 4 * (g * y) + 4 * (g' * y)
      + 4 * (g * y) * (g' * y))]
  unfold Wair
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ 2 * y * √y)
  nlinarith [h2]

/-- `a² − (a − xl)² = 2al·x(1 − εx)`. -/
theorem airy_D {c a x : ℝ} (ha : 0 < a) :
    a ^ 2 - (a - x * airyL c a) ^ 2 = 2 * a * airyL c a * (x * (1 - airyEps c a * x)) := by
  unfold airyEps
  field_simp
  ring

/-- `1 − (a − xl)² = (1 − a²)(1 + g·x(1 − εx))`. -/
theorem airy_one_sub {c a x : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    1 - (a - x * airyL c a) ^ 2 = (1 - a ^ 2) * (1 + airyG c a * (x * (1 - airyEps c a * x))) := by
  have hA : 0 < 1 - a ^ 2 := by nlinarith
  unfold airyG airyEps
  field_simp
  ring

theorem wP_le_Wair {c χ a x : ℝ} (hc : 0 < c) (ha : 0 < a) (ha1 : a < 1) (hχ : χ = c ^ 2 * a ^ 2)
    (hx : 0 < x) (hxa : x * airyL c a < a) :
    wP c χ (a - x * airyL c a) ≤ Wair (airyG c a) (x * (1 - airyEps c a * x)) := by
  have hA : 0 < 1 - a ^ 2 := by nlinarith
  have hl := airyL_pos hc ha ha1
  have hg := airyG_pos hc ha ha1
  set l := airyL c a with hldef
  set g := airyG c a with hgdef
  set y := x * (1 - airyEps c a * x) with hydef
  set s := a - x * l with hsdef
  have hs0 : 0 < s := by rw [hsdef]; linarith
  have hsa : s < a := by rw [hsdef]; nlinarith
  have hD : a ^ 2 - s ^ 2 = 2 * a * l * y := airy_D ha
  have hy : 0 < y := by
    have : 0 < a ^ 2 - s ^ 2 := by nlinarith
    rw [hD] at this
    exact pos_of_mul_pos_right this (by positivity)
  have h1s : 1 - s ^ 2 = (1 - a ^ 2) * (1 + g * y) := airy_one_sub ha ha1
  have hDpos : 0 < a ^ 2 - s ^ 2 := by nlinarith
  have h1spos : 0 < 1 - s ^ 2 := by nlinarith
  rw [wP_eq_angular hc ha1 hχ hs0.le hsa]
  calc s * (2 * (a ^ 2 - s ^ 2) + (1 - a ^ 2)) / (c * (a ^ 2 - s ^ 2) * √(a ^ 2 - s ^ 2) * √(1 - s ^ 2))
      ≤ a * (2 * (a ^ 2 - s ^ 2) + (1 - a ^ 2))
          / (c * (a ^ 2 - s ^ 2) * √(a ^ 2 - s ^ 2) * √(1 - s ^ 2)) := by
        have := sqrt_pos.mpr hDpos
        have := sqrt_pos.mpr h1spos
        gcongr
    _ = Wair g y := by
        set r := √(2 * a * l) with hrdef
        have hr : 0 < r := sqrt_pos.mpr (by positivity)
        have hr2 : r ^ 2 = 2 * a * l := sq_sqrt (by positivity)
        have hk : √(1 - a ^ 2) = c * l * r := by
          rw [← airyL_cube hc ha ha1, show 2 * a * c ^ 2 * l ^ 3 = (c * l) ^ 2 * (2 * a * l) by ring,
            sqrt_mul (sq_nonneg _), sqrt_sq (by positivity)]
        have hgy : 0 < 1 + g * y := by positivity
        have hsy := sqrt_pos.mpr hy
        have hs1 := sqrt_pos.mpr hgy
        have e3 : 2 * (a ^ 2 - s ^ 2) + (1 - a ^ 2) = (c * l * r) ^ 2 * (1 + 2 * g * y) := by
          rw [← hk, sq_sqrt hA.le, hD]
          unfold g airyG
          field_simp
          rw [← hldef]
          ring
        have e1 : √(1 - s ^ 2) = c * l * r * √(1 + g * y) := by
          rw [h1s, sqrt_mul hA.le, hk]
        have e2 : √(a ^ 2 - s ^ 2) = r * √y := by
          rw [hD, sqrt_mul (by positivity)]
        have e4 : a ^ 2 - s ^ 2 = r ^ 2 * y := by rw [hD, hr2]
        rw [e3, e2, e4, e1]
        unfold Wair
        field_simp
        ring_nf
        linarith [hr2]

set_option linter.unusedVariables false in
theorem aP_airy {c χ a θ : ℝ} (hc : 0 < c) (ha : 0 < a) (ha1 : a < 1) (hχ : χ = c ^ 2 * a ^ 2)
    (hθ : 0 ≤ θ) (hθa : θ * airyL c a ≤ a) :
    aP c χ (a - θ * airyL c a)
      = 2 * a / airyG c a * √(θ * (1 - airyEps c a * θ) * (1 + airyG c a * (θ * (1 - airyEps c a * θ)))) := by
  have hl := airyL_pos hc ha ha1
  have hg := airyG_pos hc ha ha1
  have hD := airy_D (c := c) (x := θ) ha
  have h1s := airy_one_sub (c := c) (x := θ) ha ha1
  have hg' : 2 * a / airyG c a = 2 * a * c ^ 2 * airyL c a ^ 2 := by
    have := airyG_mul hc ha ha1
    rw [div_eq_iff hg.ne']
    linear_combination (-(2 * a)) * this
  set l := airyL c a
  set g := airyG c a
  set y := θ * (1 - airyEps c a * θ)
  have hinner : pP (a - θ * l) * qP c χ (a - θ * l) = (2 * a / g) ^ 2 * (y * (1 + g * y)) := by
    rw [hg']
    unfold pP qP
    rw [hχ]
    calc ((a - θ * l) ^ 2 - 1) * (c ^ 2 * (a - θ * l) ^ 2 - c ^ 2 * a ^ 2)
        = c ^ 2 * (1 - (a - θ * l) ^ 2) * (a ^ 2 - (a - θ * l) ^ 2) := by ring
      _ = c ^ 2 * ((1 - a ^ 2) * (1 + g * y)) * (2 * a * l * y) := by rw [h1s, hD]
      _ = _ := by rw [← airyL_cube hc ha ha1]; ring
  unfold aP
  rw [hinner, sqrt_mul (sq_nonneg _), sqrt_sq (by positivity)]

theorem Lambda_airy {c a Θ : ℝ} (hc : 0 < c) (ha : 0 < a) (ha1 : a < 1) (hΘ : 0 < Θ)
    (hΘε : airyEps c a * Θ < 1) :
    2 * √(Θ * airyL c a) / (√(1 - a ^ 2) * √(2 * a - Θ * airyL c a))
      = √(airyG c a * Θ / (1 - airyEps c a * Θ)) / a := by
  have hA : 0 < 1 - a ^ 2 := by nlinarith
  have hl := airyL_pos hc ha ha1
  have hκ : 0 < 2 * a - Θ * airyL c a := by
    unfold airyEps at hΘε
    rw [div_mul_eq_mul_div, div_lt_one (by positivity)] at hΘε
    linarith
  have hκ' : 0 < 1 - airyEps c a * Θ := by linarith
  have hg := airyG_pos hc ha ha1
  have h1 := sqrt_pos.mpr hA
  have h2 := sqrt_pos.mpr hκ
  rw [← pow_left_inj₀ (by positivity) (by positivity) two_ne_zero]
  rw [div_pow, div_pow, mul_pow, mul_pow, sq_sqrt (by positivity), sq_sqrt hA.le, sq_sqrt hκ.le,
    sq_sqrt (by positivity)]
  unfold airyG airyEps
  field_simp

theorem cQ_airy {c χ a Θ : ℝ} (hc : 0 < c) (ha : 0 < a) (ha1 : a < 1) (hχ : χ = c ^ 2 * a ^ 2)
    (hΘ : 0 < Θ) (hΘε : airyEps c a * Θ < 1) :
    c / (χ - c ^ 2 * (a - Θ * airyL c a) ^ 2) = √(airyG c a) / (2 * a * (1 - airyEps c a * Θ) * Θ) := by
  have hl := airyL_pos hc ha ha1
  have hg := airyG_pos hc ha ha1
  have hκ' : 0 < 1 - airyEps c a * Θ := by linarith
  have hD := airy_D (c := c) (x := Θ) ha
  have hsg : √(airyG c a) * (c * airyL c a) = 1 := by
    rw [← sqrt_sq (by positivity : 0 ≤ c * airyL c a), ← sqrt_mul hg.le,
      show airyG c a * (c * airyL c a) ^ 2 = c ^ 2 * airyL c a ^ 2 * airyG c a by ring,
      airyG_mul hc ha ha1, sqrt_one]
  have e : χ - c ^ 2 * (a - Θ * airyL c a) ^ 2
      = c ^ 2 * (2 * a * airyL c a * (Θ * (1 - airyEps c a * Θ))) := by
    rw [hχ, ← hD]; ring
  rw [e, div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (-(2 * a * c * Θ * (1 - airyEps c a * Θ))) * hsg

/-- The top-window bracket `β(Θ) = Λ_v + (1 + R)/(2R²)·c/Q_v`, `R = R(W(Θ(1 − εΘ)))`, in Airy units
(`Lambda_airy`, `cQ_airy`). -/
noncomputable def betaf (g a ε Θ : ℝ) : ℝ :=
  √(g * Θ / (1 - ε * Θ)) / a
    + (1 + Rcorr (Wair g (Θ * (1 - ε * Θ)))) * √g
      / (4 * a * Rcorr (Wair g (Θ * (1 - ε * Θ))) ^ 2 * (1 - ε * Θ) * Θ)

/-- The crossing-window denominator `m(θ)/√g`. -/
noncomputable def D1f (g θ : ℝ) : ℝ := mth θ / √g

/-- The transported-energy denominator `R(W(Θ))R(W(θ))(1 − θ³/6)²·a(a − θl)/(2c)` in Airy units. -/
noncomputable def D2f (g a ε θ Θ : ℝ) : ℝ :=
  Rcorr (Wair g (Θ * (1 - ε * Θ))) * Rcorr (Wair g (θ * (1 - ε * θ))) * (1 - θ ^ 3 / 6) ^ 2
    * (a / g * √(θ * (1 - ε * θ) * (1 + g * (θ * (1 - ε * θ)))))

/-- The ratio `T₁ = (1/(2S) + β)/D₁`. -/
noncomputable def T1f (S g a ε θ Θ : ℝ) : ℝ := (1 / (2 * S) + betaf g a ε Θ) / D1f g θ

/-- The ratio `T₂ = 1/D₂`. -/
noncomputable def T2f (g a ε θ Θ : ℝ) : ℝ := 1 / D2f g a ε θ Θ

/-- The largest relative Airy width for `c ≥ 80`, `S ≤ c/4`: `(1/230400)^{1/3}`. -/
noncomputable def epsMax : ℝ := cbrt (1 / 230400)

/-- The largest Airy rate for `S ≥ 5`: `(4/25)^{1/3}`. -/
noncomputable def gMax5 : ℝ := cbrt (4 / 25)

/-- The worst-case value of `T₁`. -/
noncomputable def T1bar : ℝ := T1f 5 gMax5 (√3 / 2) epsMax 1 4

/-- The worst-case value of `T₂`. -/
noncomputable def T2bar : ℝ :=
  36 / 25 / (Rcorr (Wair gMax5 (4 * (1 - 4 * epsMax))) * Rcorr (Wair gMax5 (1 - epsMax))
    * √(1 - epsMax) * √(cbrt (1875 / 64) + cbrt (225 / 64) * (1 - epsMax)))

/-- `W < 2` once `g ≤ 1` and `y ≥ 7/8`. -/
theorem Wair_lt_two {g y : ℝ} (hg : 0 ≤ g) (hg1 : g ≤ 1) (hy : 7 / 8 ≤ y) : Wair g y < 2 := by
  have hy0 : 0 < y := by linarith
  refine lt_of_le_of_lt ((Wair_mono hg hg1 hy0).trans (Wair_anti zero_le_one (by norm_num) hy)) ?_
  have h1 : (9 / 10 : ℝ) ≤ √(7 / 8) := by
    rw [show (9 / 10 : ℝ) = √((9 / 10) ^ 2) by rw [sqrt_sq]; norm_num]
    exact sqrt_le_sqrt (by norm_num)
  have h2 : (1 : ℝ) ≤ √(1 + 1 * (7 / 8)) := by
    rw [show (1 : ℝ) = √1 from sqrt_one.symm]
    exact sqrt_le_sqrt (by norm_num)
  have h3 : 0 < √(7 / 8 : ℝ) := by positivity
  unfold Wair
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [mul_le_mul h1 h2 zero_le_one h3.le]

/-- The transport ratio at the rate majorant is antitone in `g` and in `−y`. -/
theorem Rcorr_Wair_le {g g' y y' : ℝ} (hg : 0 ≤ g) (hgg' : g ≤ g') (hy' : 0 < y') (hyy' : y' ≤ y) :
    Rcorr (Wair g' y') ≤ Rcorr (Wair g y) := by
  have hy : 0 < y := hy'.trans_le hyy'
  exact Rcorr_anti (by linarith [Wair_pos hg hy])
    ((Wair_mono hg hgg' hy).trans (Wair_anti (hg.trans hgg') hy' hyy'))

theorem betaf_mono {g g' a a' ε ε' Θ : ℝ} (hg : 0 ≤ g) (hgg' : g ≤ g') (ha' : 0 < a') (haa' : a' ≤ a)
    (hεε' : ε ≤ ε') (hΘ : 0 < Θ) (hε'Θ : ε' * Θ < 1)
    (hW : Wair g' (Θ * (1 - ε' * Θ)) < 2) :
    betaf g a ε Θ ≤ betaf g' a' ε' Θ := by
  have hκ' : 0 < 1 - ε' * Θ := by linarith
  have hκκ : 1 - ε' * Θ ≤ 1 - ε * Θ := by nlinarith
  have hκ : 0 < 1 - ε * Θ := hκ'.trans_le hκκ
  have hy' : 0 < Θ * (1 - ε' * Θ) := by positivity
  have hyy : Θ * (1 - ε' * Θ) ≤ Θ * (1 - ε * Θ) := mul_le_mul_of_nonneg_left hκκ hΘ.le
  have hRR := Rcorr_Wair_le hg hgg' hy' hyy
  have hR' : 0 < Rcorr (Wair g' (Θ * (1 - ε' * Θ))) :=
    Rcorr_pos (by linarith [Wair_pos (hg.trans hgg') hy']) hW
  set R := Rcorr (Wair g (Θ * (1 - ε * Θ)))
  set R' := Rcorr (Wair g' (Θ * (1 - ε' * Θ)))
  have hR : 0 < R := hR'.trans_le hRR
  have hfR : (1 + R) / R ^ 2 ≤ (1 + R') / R' ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hR'.le hR.le) (sub_nonneg.2 hRR),
      mul_nonneg (add_pos hR' hR).le (sub_nonneg.2 hRR)]
  have e : ∀ (R a ε g : ℝ), (1 + R) * √g / (4 * a * R ^ 2 * (1 - ε * Θ) * Θ)
      = (1 + R) / R ^ 2 * (√g / (4 * a * (1 - ε * Θ) * Θ)) := by
    intro R a ε g
    rw [div_mul_div_comm]
    ring
  unfold betaf
  rw [e R a ε g, e R' a' ε' g']
  have ha : 0 < a := ha'.trans_le haa'
  have hgg : √g ≤ √g' := sqrt_le_sqrt hgg'
  apply add_le_add
  · apply div_le_div₀ (sqrt_nonneg _) _ ha' haa'
    apply sqrt_le_sqrt
    apply div_le_div₀ (mul_nonneg (hg.trans hgg') hΘ.le) (mul_le_mul_of_nonneg_right hgg' hΘ.le) hκ' hκκ
  · apply mul_le_mul hfR _ (div_nonneg (sqrt_nonneg _)
      (mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) ha) hκ) hΘ).le)
      (div_nonneg (by linarith) (sq_nonneg _))
    apply div_le_div₀ (sqrt_nonneg _) hgg
      (mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) ha') hκ') hΘ)
    have : 4 * a' * (1 - ε' * Θ) ≤ 4 * a * (1 - ε * Θ) := by
      have := mul_le_mul haa' hκκ hκ'.le ha.le
      linarith
    exact mul_le_mul_of_nonneg_right this hΘ.le

theorem betaf_nonneg {g a ε Θ : ℝ} (hg : 0 ≤ g) (ha : 0 < a) (hΘ : 0 < Θ) (hεΘ : ε * Θ < 1)
    (hW : Wair g (Θ * (1 - ε * Θ)) < 2) : 0 ≤ betaf g a ε Θ := by
  have hκ : 0 < 1 - ε * Θ := by linarith
  have hR : 0 < Rcorr (Wair g (Θ * (1 - ε * Θ))) :=
    Rcorr_pos (by linarith [Wair_pos hg (by positivity : 0 < Θ * (1 - ε * Θ))]) hW
  unfold betaf
  apply add_nonneg (div_nonneg (sqrt_nonneg _) ha.le)
  apply div_nonneg (mul_nonneg (by linarith) (sqrt_nonneg _))
  exact (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) ha) (pow_pos hR 2)) hκ) hΘ).le

theorem airy_worst_case {c a : ℝ} (hc : 80 ≤ c) (ha : 0 < a) (ha1 : a < 1)
    (hS5 : 5 ≤ c * (1 - a ^ 2)) (hS4 : 4 * (1 - a ^ 2) ≤ 1) :
    airyEps c a * 4 < 1 / 2 ∧ Wair (airyG c a) (1 * (1 - airyEps c a * 1)) < 2 ∧
      T1f (c * (1 - a ^ 2)) (airyG c a) a (airyEps c a) 1 4 ≤ T1bar ∧
      T2f (airyG c a) a (airyEps c a) 1 4 ≤ T2bar := by
  have hc0 : 0 < c := by linarith
  have hA : 0 < 1 - a ^ 2 := by nlinarith
  have hg0 := airyG_pos hc0 ha ha1
  have hε0 := airyEps_pos hc0 ha ha1
  have hcube := airyG_cube hc0 ha ha1
  have hεcube := airyEps_cube hc0 ha ha1
  set g := airyG c a
  set ε := airyEps c a
  set S := c * (1 - a ^ 2) with hSdef
  have ha2 : 3 / 4 ≤ a ^ 2 := by linarith
  have haq : √3 / 2 ≤ a := by
    rw [← pow_le_pow_iff_left₀ (by positivity) ha.le (two_ne_zero), div_pow, sq_sqrt (by norm_num)]
    linarith
  have haq0 : 0 < √3 / 2 := by positivity
  -- the Airy rate and width at their worst
  have hg5 : g ≤ gMax5 := by
    unfold gMax5
    rw [le_cbrt_iff hg0.le (by norm_num)]
    have hS2 : 25 ≤ S ^ 2 := by nlinarith
    have : g ^ 3 * 25 ≤ g ^ 3 * S ^ 2 := mul_le_mul_of_nonneg_left hS2 (by positivity)
    nlinarith
  have hεM : ε ≤ epsMax := by
    unfold epsMax
    rw [le_cbrt_iff hε0.le (by norm_num)]
    have hc2 : 6400 ≤ c ^ 2 := by nlinarith
    have ha4 : 9 / 16 ≤ a ^ 4 := by nlinarith
    have h16 : 57600 ≤ 16 * a ^ 4 * c ^ 2 := by nlinarith
    have : ε ^ 3 * 57600 ≤ ε ^ 3 * (16 * a ^ 4 * c ^ 2) := mul_le_mul_of_nonneg_left h16 (by positivity)
    nlinarith
  have hgM0 : 0 < gMax5 := cbrt_pos (by norm_num)
  have hgM1 : gMax5 ≤ 1 := by
    unfold gMax5; rw [cbrt_le_iff zero_le_one (by norm_num)]; norm_num
  have hεM0 : 0 < epsMax := cbrt_pos (by norm_num)
  have hεM40 : epsMax ≤ 1 / 40 := by
    unfold epsMax; rw [cbrt_le_iff (by norm_num) (by norm_num)]; norm_num
  have hW4 : Wair gMax5 (4 * (1 - epsMax * 4)) < 2 := Wair_lt_two hgM0.le hgM1 (by linarith)
  have hW1 : Wair gMax5 (1 - epsMax) < 2 := Wair_lt_two hgM0.le hgM1 (by linarith)
  refine ⟨by linarith, Wair_lt_two hg0.le (hg5.trans hgM1) (by linarith), ?_, ?_⟩
  · -- T₁
    unfold T1bar T1f D1f
    rw [div_div_eq_mul_div, div_div_eq_mul_div]
    have hm : 0 < mth 1 := by unfold mth; norm_num
    apply div_le_div_of_nonneg_right _ hm.le
    apply mul_le_mul _ (sqrt_le_sqrt hg5) (sqrt_nonneg _)
    · exact add_nonneg (by norm_num) (betaf_nonneg hgM0.le haq0 (by norm_num) (by linarith) hW4)
    apply add_le_add
    · apply one_div_le_one_div_of_le (by norm_num); linarith
    · exact betaf_mono hg0.le hg5 haq0 haq hεM (by norm_num) (by linarith) hW4
  · -- T₂
    have hR4 := Rcorr_Wair_le (g := g) (y := 4 * (1 - ε * 4)) hg0.le hg5
      (by linarith : 0 < 4 * (1 - 4 * epsMax)) (by linarith)
    have hR1 := Rcorr_Wair_le (g := g) (y := 1 * (1 - ε * 1)) hg0.le hg5
      (by linarith : 0 < 1 - epsMax) (by linarith)
    have hR4p : 0 < Rcorr (Wair gMax5 (4 * (1 - 4 * epsMax))) :=
      Rcorr_pos (by linarith [Wair_pos hgM0.le (by linarith : 0 < 4 * (1 - 4 * epsMax))])
        (Wair_lt_two hgM0.le hgM1 (by linarith))
    have hR1p : 0 < Rcorr (Wair gMax5 (1 - epsMax)) :=
      Rcorr_pos (by linarith [Wair_pos hgM0.le (by linarith : 0 < 1 - epsMax)]) hW1
    -- the amplitude factor `(a/g)√(y(1 + gy))`
    set y := 1 * (1 - ε * 1) with hydef
    have hy0 : 0 < y := by rw [hydef]; linarith
    have hyM : 1 - epsMax ≤ y := by rw [hydef]; linarith
    have hP : a / g * √(y * (1 + g * y)) = √y * √(a ^ 2 / g ^ 2 + a ^ 2 / g * y) := by
      rw [show a / g = √((a / g) ^ 2) from (sqrt_sq (by positivity)).symm, ← sqrt_mul (sq_nonneg _),
        ← sqrt_mul hy0.le]
      congr 1
      field_simp
    have hAc : cbrt (1875 / 64) ≤ a ^ 2 / g ^ 2 := by
      rw [cbrt_le_iff (by positivity) (by norm_num)]
      have e : (a ^ 2 / g ^ 2) ^ 3 = a ^ 2 * S ^ 4 / 16 := by
        rw [div_pow, div_eq_div_iff (by positivity) (by norm_num)]
        linear_combination (-(a ^ 2 * (g ^ 3 * S ^ 2 + 4 * a ^ 2))) * hcube
      rw [e]
      have hS4' : 625 ≤ S ^ 4 := by
        have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5) hS5 4
        norm_num at this; linarith
      have := mul_le_mul ha2 hS4' (by norm_num) (sq_nonneg a)
      linarith
    have hBc : cbrt (225 / 64) ≤ a ^ 2 / g := by
      rw [cbrt_le_iff (by positivity) (by norm_num)]
      have e : (a ^ 2 / g) ^ 3 = a ^ 4 * S ^ 2 / 4 := by
        rw [div_pow, div_eq_div_iff (by positivity) (by norm_num)]
        linear_combination (-(a ^ 4)) * hcube
      rw [e]
      have hS2 : 25 ≤ S ^ 2 := by
        have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5) hS5 2
        norm_num at this; linarith
      have ha4 : 9 / 16 ≤ a ^ 4 := by
        have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 4) ha2 2
        rw [← pow_mul] at this; norm_num at this; linarith
      have := mul_le_mul ha4 hS2 (by norm_num) (by positivity)
      linarith
    have hPb : √(1 - epsMax) * √(cbrt (1875 / 64) + cbrt (225 / 64) * (1 - epsMax))
        ≤ a / g * √(y * (1 + g * y)) := by
      rw [hP]
      apply mul_le_mul (sqrt_le_sqrt hyM) _ (sqrt_nonneg _) (sqrt_nonneg _)
      apply sqrt_le_sqrt
      exact add_le_add hAc (mul_le_mul hBc hyM (by linarith) (by positivity))
    have hPb0 : 0 < √(1 - epsMax) * √(cbrt (1875 / 64) + cbrt (225 / 64) * (1 - epsMax)) := by
      have : 0 < cbrt (1875 / 64 : ℝ) := cbrt_pos (by norm_num)
      have : 0 < cbrt (225 / 64 : ℝ) := cbrt_pos (by norm_num)
      have : 0 < 1 - epsMax := by linarith
      positivity
    have hD2 : Rcorr (Wair gMax5 (4 * (1 - 4 * epsMax))) * Rcorr (Wair gMax5 (1 - epsMax)) * (25 / 36)
        * (√(1 - epsMax) * √(cbrt (1875 / 64) + cbrt (225 / 64) * (1 - epsMax)))
        ≤ D2f g a ε 1 4 := by
      unfold D2f
      rw [show (1 - (1 : ℝ) ^ 3 / 6) ^ 2 = 25 / 36 by norm_num]
      apply mul_le_mul _ hPb hPb0.le
        (mul_nonneg (mul_nonneg (hR4p.le.trans hR4) (hR1p.le.trans hR1)) (by norm_num))
      apply mul_le_mul_of_nonneg_right _ (by norm_num)
      exact mul_le_mul hR4 hR1 hR1p.le (hR4p.le.trans hR4)
    unfold T2f
    refine (one_div_le_one_div_of_le (by positivity) hD2).trans (le_of_eq ?_)
    unfold T2bar
    field_simp

end Cvs.Prolate.LiouvilleGreen.AngularRateAiryUnits
