import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.CutEstimateFrameFloor
import Cvs.L2a.CutPointCountForm
import Cvs.L2a.EdgeCountSSums
import Cvs.L2a.FirstStepRemainderCount
import Cvs.L2a.PerLevelFarLeak
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.RungSpanLowMass
import Cvs.L2a.TailLogScaleTest
import Cvs.Prolate.EdgeBesselCount
import Cvs.Prolate.Mellin.EdgeGreenIdentity
import Cvs.Prolate.Mellin.EdgeRemainderClosedForm
import Cvs.Prolate.Mellin.FarPartLevelBound
import Cvs.Prolate.Mellin.GreenBoundaryBound
import Cvs.Prolate.Mellin.GreenBulkBound
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.GradedArchFloor
import Cvs.WeilForm.SelfConvolutionFunctional

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The low constant uniformly in `c`

For `K0 = κ(1 + log c)`, `κ ≥ 1`, `c ≥ 80` and `J ≤ c/4 + 1`: `ℛ ≤ R̄₀ + R̄₁ log c` and `η_P ≤ Ē/κ`, with
`Ē = ((√F̄ + √W̄ + √R̄₀)/√(1 + log 80) + √R̄₁)²/π` and `F̄`, `W̄`, `R̄₀`, `R̄₁` closed forms at `c = 80`; the full-tail
L2a of Cvs.L2a.RungSpanLowMass then holds with `η = Ē/(κκ_F)`.
-/

namespace Cvs.L2a.LowConstantUniform

open MeasureTheory Real Set Cvs.L2a.TailLogScaleTest Cvs.L2a.AngularProlateTailPositive Cvs.L2a.PositionTruncatedTail Cvs.L2a.SpectralMassLevelLeak Cvs.L2a.CutPointCountForm Cvs.L2a.FirstStepRemainderCount Cvs.L2a.CutEstimateFrameFloor Cvs.Prolate.Mellin.FarPartLevelBound Cvs.L2a.PerLevelFarLeak Cvs.Prolate.Mellin.EdgeGreenIdentity Cvs.Prolate.Mellin.EdgeRemainderClosedForm Cvs.Prolate.EdgeBesselCount Cvs.L2a.EdgeCountSSums Cvs.L2a.RungSpanLowMass
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)

/-- `r̄ = (1 + log 80)⁻² + 1/(4·80²)`. -/
noncomputable def rBar : ℝ := 1 / (1 + Real.log 80) ^ 2 + 1 / (4 * 80 ^ 2)

/-- `r̄_f = (1 + log 80)⁻²/4 + 1/(16·80²)`. -/
noncomputable def rBarF : ℝ := 1 / (4 * (1 + Real.log 80) ^ 2) + 1 / (16 * 80 ^ 2)

/-- `a₁ = 33/(160β²)`, the `log c` coefficient of `A_c`. -/
noncomputable def a1 : ℝ := 33 / (160 * betaEdge ^ 2)

/-- `a₀ = (33/(40β²))(log(12/5)/4 + 23/60 + 5/(24·80))`. -/
noncomputable def a0 : ℝ := 33 / (40 * betaEdge ^ 2) * (Real.log (12 / 5) / 4 + 23 / 60 + 5 / (24 * 80))

/-- `S̄₁(80) = (a₀ + a₁ log 80) log 16 + 21/80`. -/
noncomputable def S1at80 : ℝ := (a0 + a1 * Real.log 80) * Real.log 16 + 21 / 80

/-- `F̄ = (3/2)(21/80)C̄(80, r̄_f)²`. -/
noncomputable def Fbar : ℝ := 3 / 2 * (21 / 80) * Cbar 80 rBarF ^ 2

/-- `W̄ = (21/80)ω₂(80, r̄)²`. -/
noncomputable def Wbar : ℝ := 21 / 80 * omega2Sq 80 rBar

/-- `R̄₁ = (16/15)(3/50)a₁`. -/
noncomputable def R1bar : ℝ := 16 / 15 * (3 / 50) * a1

/-- `R̄₀`, the `c`-free part of `ℛ ≤ R̄₀ + R̄₁ log c`. -/
noncomputable def R0bar : ℝ :=
  16 / 15 * (3 / 50) * a0 + 2 / (3 * (1 - rBar)) * (max a0 a1 + 21 / 80 / (1 + Real.log 80) ^ 2
    + S1at80 / (4 * 80 ^ 2)) + √(32 / 15) * e1 rBar * (2 * (a0 + a1 * Real.log 80) / 5) / 80
    + e1 rBar ^ 2 / 2 * S1at80 / 80 ^ 2
    + 2 * rBar * (21 / 80) * (2 * (2 + rBar) * Lc 80 + (2 + rBar) ^ 2 / 2) / (1 - rBar) ^ 4
    + √(I1bar rBar * I2bar rBar) * (2 * (a0 + a1 * Real.log 80) / 5) / 80

/-- `Ē = ((√F̄ + √W̄ + √R̄₀)/√(1 + log 80) + √R̄₁)²/π`. -/
noncomputable def Ebar : ℝ := ((√Fbar + √Wbar + √R0bar) / √(1 + Real.log 80) + √R1bar) ^ 2 / π

/-- `1 + 2 log 5 ≤ log 80`, from `25e < 80`. -/
theorem one_add_two_log_five_le : 1 + 2 * Real.log 5 ≤ Real.log 80 := by
  have h1 : (1 : ℝ) ≤ Real.log (16 / 5) :=
    (Real.le_log_iff_exp_le (by norm_num)).mpr (by linarith [Real.exp_one_lt_three])
  have e : Real.log 80 = Real.log (16 / 5) + 2 * Real.log 5 := by
    rw [show (80 : ℝ) = 16 / 5 * 5 ^ 2 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  have : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  linarith

/-- `1 ≤ log 80`. -/
theorem one_le_log_80 : 1 ≤ Real.log 80 := by
  have := one_add_two_log_five_le
  have : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  linarith

/-- `0 ≤ r̄ < 1`. -/
theorem rBar_mem : 0 ≤ rBar ∧ rBar < 1 := by
  have h := one_le_log_80
  refine ⟨by unfold rBar; positivity, ?_⟩
  unfold rBar
  have : 1 / (1 + Real.log 80) ^ 2 ≤ 1 / 4 :=
    one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  norm_num at this ⊢
  linarith

/-- `0 ≤ r̄_f < 1`. -/
theorem rBarF_mem : 0 ≤ rBarF ∧ rBarF < 1 := by
  have h := one_le_log_80
  refine ⟨by unfold rBarF; positivity, ?_⟩
  unfold rBarF
  have : 1 / (4 * (1 + Real.log 80) ^ 2) ≤ 1 / 16 :=
    one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  norm_num at this ⊢
  linarith

/-- `log y / y ≤ log x / x` for `3 ≤ x ≤ y` (`log t / t` decreases past `e < 3`). -/
theorem log_div_le {x y : ℝ} (hx : 3 ≤ x) (hxy : x ≤ y) : Real.log y / y ≤ Real.log x / x :=
  Real.log_div_self_antitoneOn (mem_Ici.mpr (by linarith [Real.exp_one_lt_three]))
    (mem_Ici.mpr (by linarith [Real.exp_one_lt_three])) hxy

/-- `A_c ≤ a₀ + a₁ log c` and `0 ≤ A_c` for `c ≥ 80`. -/
theorem Ac_le {c : ℝ} (hc : 80 ≤ c) : 0 ≤ Ac c ∧ Ac c ≤ a0 + a1 * Real.log c := by
  have hc0 : 0 < c := by linarith
  have hb : 0 < betaEdge := by unfold betaEdge; norm_num
  have hlog : Real.log (12 * c / 5) = Real.log (12 / 5) + Real.log c := by
    rw [mul_div_right_comm, Real.log_mul (by norm_num) hc0.ne']
  have hl0 : 0 ≤ Real.log (12 * c / 5) := Real.log_nonneg (by linarith)
  refine ⟨by unfold Ac Kbar; positivity, ?_⟩
  have e : Ac c = 33 / (40 * betaEdge ^ 2) * (Real.log (12 / 5) / 4 + 23 / 60 + 5 / (24 * c))
      + a1 * Real.log c := by
    unfold Ac Kbar a1
    rw [hlog]
    field_simp
    ring
  rw [e]
  unfold a0
  have : 5 / (24 * c) ≤ 5 / (24 * 80) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hk : 0 ≤ 33 / (40 * betaEdge ^ 2) := by positivity
  nlinarith

/-- `(a₀ + a₁ log c)/c ≤ (a₀ + a₁ log 80)/80` for `c ≥ 80`. -/
theorem lin_div_le {c : ℝ} (hc : 80 ≤ c) : (a0 + a1 * Real.log c) / c ≤ (a0 + a1 * Real.log 80) / 80 := by
  have hc0 : 0 < c := by linarith
  have hb : 0 < betaEdge := by unfold betaEdge; norm_num
  have ha0 : 0 ≤ a0 := by
    unfold a0; have : 0 ≤ Real.log (12 / 5) := Real.log_nonneg (by norm_num); positivity
  have ha1 : 0 ≤ a1 := by unfold a1; positivity
  have hL := log_div_le (by norm_num : (3 : ℝ) ≤ 80) hc
  rw [add_div, add_div, mul_div_assoc, mul_div_assoc]
  have : a0 / c ≤ a0 / 80 := div_le_div_of_nonneg_left ha0 (by norm_num) hc
  nlinarith

/-- `0 ≤ r ≤ ρ(c) ≤ r̄` for `r = rLow c (κ(1 + log c))`, `ρ(c) = (1 + log c)⁻² + 1/(4c²)`, `κ ≥ 1`, `c ≥ 80`. -/
theorem rLow_le {c κ : ℝ} (hc : 80 ≤ c) (hκ : 1 ≤ κ) :
    0 ≤ rLow c (κ * (1 + Real.log c)) ∧ rLow c (κ * (1 + Real.log c)) ≤ 1 / (1 + Real.log c) ^ 2 + 1 / (4 * c ^ 2)
      ∧ 1 / (1 + Real.log c) ^ 2 + 1 / (4 * c ^ 2) ≤ rBar := by
  have hL80 : Real.log 80 ≤ Real.log c := Real.log_le_log (by norm_num) hc
  have h1 := one_le_log_80
  have hu : 0 < 1 + Real.log c := by linarith
  refine ⟨by unfold rLow; positivity, ?_, ?_⟩
  · unfold rLow
    have : 1 / (κ * (1 + Real.log c)) ^ 2 ≤ 1 / (1 + Real.log c) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hu.le (by nlinarith) 2)
    linarith
  · unfold rBar
    have e1 : 1 / (1 + Real.log c) ^ 2 ≤ 1 / (1 + Real.log 80) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by linarith) (by linarith) 2)
    have e2 : 1 / (4 * c ^ 2) ≤ 1 / (4 * 80 ^ 2) :=
      one_div_le_one_div_of_le (by norm_num) (by nlinarith)
    linarith

/-- `0 ≤ r_f ≤ r̄_f` for `r_f = 1/(4K0²) + 1/(16c²)`, `K0 = κ(1 + log c)`, `κ ≥ 1`, `c ≥ 80`. -/
theorem rf_le {c κ : ℝ} (hc : 80 ≤ c) (hκ : 1 ≤ κ) :
    0 ≤ 1 / (4 * (κ * (1 + Real.log c)) ^ 2) + 1 / (16 * c ^ 2)
      ∧ 1 / (4 * (κ * (1 + Real.log c)) ^ 2) + 1 / (16 * c ^ 2) ≤ rBarF := by
  have hL80 : Real.log 80 ≤ Real.log c := Real.log_le_log (by norm_num) hc
  have h1 := one_le_log_80
  refine ⟨by positivity, ?_⟩
  unfold rBarF
  have e1 : 1 / (4 * (κ * (1 + Real.log c)) ^ 2) ≤ 1 / (4 * (1 + Real.log 80) ^ 2) :=
    one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by nlinarith) 2) (by norm_num))
  have e2 : 1 / (16 * c ^ 2) ≤ 1 / (16 * 80 ^ 2) :=
    one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  linarith

/-- `e₁`, `Ī₁`, `Ī₂` at `r ∈ [0, r̄]` are at most their values at `r̄`, and `e₁ r ≥ 0`. -/
theorem consts_le {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ rBar) :
    0 ≤ e1 r ∧ e1 r ≤ e1 rBar ∧ I1bar r ≤ I1bar rBar ∧ I2bar r ≤ I2bar rBar := by
  have hb := rBar_mem.2
  have h1 : 0 < 1 - rBar := by linarith
  have he0 := e1_nonneg hr0 (hr.trans_lt hb)
  have he : e1 r ≤ e1 rBar := e1_mono hr0 hr hb
  refine ⟨he0, he, ?_, ?_⟩
  · unfold I1bar
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  · unfold I2bar
    have : 0 ≤ rBar := hr0.trans hr
    gcongr

/-- `0 ≤ L_c` for `c ≥ 80`. -/
theorem Lc_nonneg {c : ℝ} (hc : 80 ≤ c) : 0 ≤ Lc c := by
  unfold Lc
  have : 0 ≤ Real.log (c / 5) := Real.log_nonneg (by rw [le_div_iff₀ (by norm_num)]; linarith)
  have : 5 / c ≤ 1 / 16 := by rw [div_le_iff₀ (by linarith)]; linarith
  exact div_nonneg (by assumption) (by linarith)

/-- `(u − b)/u² ≤ (u₀ − b)/u₀²` for `2b ≤ u₀ ≤ u`, `b ≥ 0`. -/
theorem sub_div_sq_le {u u₀ b : ℝ} (hb : 0 ≤ b) (h2b : 2 * b ≤ u₀) (hu : u₀ ≤ u) (hu0 : 0 < u₀) :
    (u - b) / u ^ 2 ≤ (u₀ - b) / u₀ ^ 2 := by
  have hupos : 0 < u := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : 0 ≤ u - u₀ := by linarith
  have h2 : 0 ≤ u * u₀ - b * (u + u₀) := by nlinarith
  nlinarith [mul_nonneg h1 h2]

/-- `r·L_c ≤ r̄·L_80` for `r ≤ (1 + log c)⁻² + 1/(4c²)`, `c ≥ 80`. -/
theorem mul_Lc_le {c r : ℝ} (hc : 80 ≤ c) (hr : r ≤ 1 / (1 + Real.log c) ^ 2 + 1 / (4 * c ^ 2)) :
    r * Lc c ≤ rBar * Lc 80 := by
  have hc0 : 0 < c := by linarith
  have hc5 : 0 < c - 5 := by linarith
  have hL80 : Real.log 80 ≤ Real.log c := Real.log_le_log (by norm_num) hc
  have h1 := one_le_log_80
  have h5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  have hlc : Real.log (c / 5) = Real.log c - Real.log 5 := Real.log_div hc0.ne' (by norm_num)
  have hl16 : Real.log 16 = Real.log 80 - Real.log 5 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  have hlc0 : 0 ≤ Real.log (c / 5) := Real.log_nonneg (by rw [le_div_iff₀ (by norm_num)]; linarith)
  have hu : 0 < 1 + Real.log c := by linarith
  -- `ρ(c)·L_c = [log(c/5)/(1 + log c)²]·[c/(c − 5)] + [log(c/5)/(c/5)]·[1/(20(c − 5))]`
  have key : ∀ x : ℝ, 80 ≤ x → (1 / (1 + Real.log x) ^ 2 + 1 / (4 * x ^ 2)) * Lc x
      = Real.log (x / 5) / (1 + Real.log x) ^ 2 * (x / (x - 5))
        + Real.log (x / 5) / (x / 5) * (1 / (20 * (x - 5))) := fun x hx => by
    have hx0 : 0 < x := by linarith
    have hx5 : x - 5 ≠ 0 := by linarith
    have hu' : 1 + Real.log x ≠ 0 := by
      have := Real.log_le_log (by norm_num : (0 : ℝ) < 80) hx; linarith
    unfold Lc
    have : 1 - 5 / x = (x - 5) / x := by field_simp
    rw [this]
    field_simp
    ring
  have hA : Real.log (c / 5) / (1 + Real.log c) ^ 2 ≤ Real.log (80 / 5) / (1 + Real.log 80) ^ 2 := by
    rw [hlc, show (80 : ℝ) / 5 = 16 by norm_num, hl16,
      show Real.log c - Real.log 5 = (1 + Real.log c) - (1 + Real.log 5) by ring,
      show Real.log 80 - Real.log 5 = (1 + Real.log 80) - (1 + Real.log 5) by ring]
    exact sub_div_sq_le (by linarith) (by linarith [one_add_two_log_five_le]) (by linarith) (by linarith)
  have hB : c / (c - 5) ≤ 80 / (80 - 5) := by
    rw [div_le_div_iff₀ hc5 (by norm_num)]; nlinarith
  have hC : Real.log (c / 5) / (c / 5) ≤ Real.log (80 / 5) / (80 / 5) :=
    log_div_le (by norm_num) (by linarith)
  have hD : 1 / (20 * (c - 5)) ≤ 1 / (20 * (80 - 5)) :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hLc := Lc_nonneg hc
  calc r * Lc c ≤ (1 / (1 + Real.log c) ^ 2 + 1 / (4 * c ^ 2)) * Lc c := mul_le_mul_of_nonneg_right hr hLc
    _ = _ := key c hc
    _ ≤ Real.log (80 / 5) / (1 + Real.log 80) ^ 2 * (80 / (80 - 5))
        + Real.log (80 / 5) / (80 / 5) * (1 / (20 * (80 - 5))) := by
      have hA0 : 0 ≤ Real.log (c / 5) / (1 + Real.log c) ^ 2 := by positivity
      have hC0 : 0 ≤ Real.log (c / 5) / (c / 5) := by positivity
      have hl80 : 0 ≤ Real.log (80 / 5) := Real.log_nonneg (by norm_num)
      gcongr
    _ = rBar * Lc 80 := by unfold rBar; rw [key 80 le_rfl]

/-- `J/c ≤ 21/80` for `J ≤ c/4 + 1`, `c ≥ 80`. -/
theorem J_div_le {c J : ℝ} (hc : 80 ≤ c) (hJ : J ≤ c / 4 + 1) : J / c ≤ 21 / 80 := by
  rw [div_le_iff₀ (by linarith)]; linarith

/-- The `S̄₁ = A_c log(c/5) + J/c` bounds: `S̄₁ ≥ 0`, `S̄₁/c² ≤ S̄₁(80)/80²` and
`S̄₁/(1 + log c)² ≤ max a₀ a₁ + (21/80)/(1 + log 80)²`. -/
theorem S1_le {c J : ℝ} (hc : 80 ≤ c) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1) :
    0 ≤ Ac c * Real.log (c / 5) + J / c
      ∧ (Ac c * Real.log (c / 5) + J / c) / c ^ 2 ≤ S1at80 / 80 ^ 2
      ∧ (Ac c * Real.log (c / 5) + J / c) / (1 + Real.log c) ^ 2
        ≤ max a0 a1 + 21 / 80 / (1 + Real.log 80) ^ 2 := by
  have hc0 : 0 < c := by linarith
  obtain ⟨hA0, hA⟩ := Ac_le hc
  have hJc := J_div_le hc hJ
  have hJc0 : 0 ≤ J / c := by positivity
  have hlc0 : 0 ≤ Real.log (c / 5) := Real.log_nonneg (by rw [le_div_iff₀ (by norm_num)]; linarith)
  have hlc : Real.log (c / 5) ≤ Real.log c := Real.log_le_log (by positivity) (by linarith)
  have hL80 : Real.log 80 ≤ Real.log c := Real.log_le_log (by norm_num) hc
  have h1 := one_le_log_80
  have hb : 0 < betaEdge := by unfold betaEdge; norm_num
  have ha0 : 0 ≤ a0 := by
    unfold a0; have : 0 ≤ Real.log (12 / 5) := Real.log_nonneg (by norm_num); positivity
  have ha1 : 0 ≤ a1 := by unfold a1; positivity
  refine ⟨by positivity, ?_, ?_⟩
  · have e : (Ac c * Real.log (c / 5) + J / c) / c ^ 2
        = Ac c / c * (Real.log (c / 5) / (c / 5) / 5) + J / c / c ^ 2 := by field_simp
    rw [e]
    have hAc : Ac c / c ≤ (a0 + a1 * Real.log 80) / 80 :=
      (div_le_div_of_nonneg_right hA hc0.le).trans (lin_div_le hc)
    have hl : Real.log (c / 5) / (c / 5) / 5 ≤ Real.log (80 / 5) / (80 / 5) / 5 :=
      div_le_div_of_nonneg_right (log_div_le (by norm_num) (by linarith)) (by norm_num)
    have hj : J / c / c ^ 2 ≤ 21 / 80 / 80 ^ 2 :=
      div_le_div₀ (by norm_num) hJc (by norm_num) (by nlinarith)
    have hl0 : 0 ≤ Real.log (c / 5) / (c / 5) / 5 := by positivity
    have hm := mul_le_mul hAc hl hl0 (by positivity)
    unfold S1at80
    rw [show (80 : ℝ) / 5 = 16 by norm_num] at hm
    have : (a0 + a1 * Real.log 80) / 80 * (Real.log 16 / 16 / 5) + 21 / 80 / 80 ^ 2
        = ((a0 + a1 * Real.log 80) * Real.log 16 + 21 / 80) / 80 ^ 2 := by ring
    linarith
  · have hu : 0 < 1 + Real.log c := by linarith
    have hm : Ac c * Real.log (c / 5) ≤ max a0 a1 * (1 + Real.log c) ^ 2 := by
      have hL0 : 0 ≤ Real.log c := by linarith
      calc Ac c * Real.log (c / 5) ≤ (a0 + a1 * Real.log c) * Real.log c :=
            mul_le_mul hA hlc hlc0 (by positivity)
        _ ≤ (max a0 a1 + max a0 a1 * Real.log c) * Real.log c := by
            gcongr
            · exact le_max_left _ _
            · exact le_max_right _ _
        _ ≤ max a0 a1 * (1 + Real.log c) ^ 2 := by
            have : 0 ≤ max a0 a1 := ha0.trans (le_max_left _ _)
            nlinarith
    have hj : J / c / (1 + Real.log c) ^ 2 ≤ 21 / 80 / (1 + Real.log 80) ^ 2 :=
      div_le_div₀ (by norm_num) hJc (by positivity) (pow_le_pow_left₀ (by linarith) (by linarith) 2)
    rw [add_div]
    have : Ac c * Real.log (c / 5) / (1 + Real.log c) ^ 2 ≤ max a0 a1 := by
      rw [div_le_iff₀ (by positivity)]; exact hm
    linarith

/-- **ℛ uniformly in `c`**: `ℛ(c, rLow c (κ(1 + log c)), J) ≤ R̄₀ + R̄₁ log c` for `c ≥ 80`, `κ ≥ 1`,
`0 ≤ J ≤ c/4 + 1`. -/
theorem Rcal_le {c κ J : ℝ} (hc : 80 ≤ c) (hκ : 1 ≤ κ) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1) :
    Rcal c (rLow c (κ * (1 + Real.log c))) J ≤ R0bar + R1bar * Real.log c := by
  have hc0 : 0 < c := by linarith
  obtain ⟨hr0, hrρ, hρb⟩ := rLow_le hc hκ
  set r := rLow c (κ * (1 + Real.log c)) with hrd
  have hrb : r ≤ rBar := hrρ.trans hρb
  obtain ⟨hbar0, hbar1⟩ := rBar_mem
  have h1r : 0 < 1 - r := by linarith
  have h1b : 0 < 1 - rBar := by linarith
  obtain ⟨he0, he, hI1, hI2⟩ := consts_le hr0 hrb
  obtain ⟨hA0, hA⟩ := Ac_le hc
  obtain ⟨hS0, hSc, hSL⟩ := S1_le hc hJ0 hJ
  have hJc := J_div_le hc hJ
  have hJc0 : 0 ≤ J / c := by positivity
  have hAc : Ac c / c ≤ (a0 + a1 * Real.log 80) / 80 :=
    (div_le_div_of_nonneg_right hA hc0.le).trans (lin_div_le hc)
  have hAc0 : 0 ≤ Ac c / c := by positivity
  have hL80 : Real.log 80 ≤ Real.log c := Real.log_le_log (by norm_num) hc
  have hlog1 := one_le_log_80
  unfold Rcal RcalS
  have t1 : 16 / 15 * (3 * Ac c / 50) ≤ 16 / 15 * (3 / 50) * a0 + R1bar * Real.log c := by
    unfold R1bar; nlinarith
  have t2 : 2 * r / (3 * (1 - r)) * (Ac c * Real.log (c / 5) + J / c)
      ≤ 2 / (3 * (1 - rBar)) * (max a0 a1 + 21 / 80 / (1 + Real.log 80) ^ 2 + S1at80 / (4 * 80 ^ 2)) := by
    have hk : 2 / (3 * (1 - r)) ≤ 2 / (3 * (1 - rBar)) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
    have e : 2 * r / (3 * (1 - r)) * (Ac c * Real.log (c / 5) + J / c)
        = 2 / (3 * (1 - r)) * (r * (Ac c * Real.log (c / 5) + J / c)) := by ring
    have hρS : r * (Ac c * Real.log (c / 5) + J / c)
        ≤ max a0 a1 + 21 / 80 / (1 + Real.log 80) ^ 2 + S1at80 / (4 * 80 ^ 2) := by
      calc r * (Ac c * Real.log (c / 5) + J / c)
          ≤ (1 / (1 + Real.log c) ^ 2 + 1 / (4 * c ^ 2)) * (Ac c * Real.log (c / 5) + J / c) :=
            mul_le_mul_of_nonneg_right hrρ hS0
        _ = (Ac c * Real.log (c / 5) + J / c) / (1 + Real.log c) ^ 2
            + (Ac c * Real.log (c / 5) + J / c) / c ^ 2 / 4 := by ring
        _ ≤ _ := by
            have : S1at80 / (4 * 80 ^ 2) = S1at80 / 80 ^ 2 / 4 := by ring
            rw [this]
            linarith
    rw [e]
    exact mul_le_mul hk hρS (by positivity) (by positivity)
  have t3 : √(32 / 15) * e1 r * (2 * Ac c / 5) / c
      ≤ √(32 / 15) * e1 rBar * (2 * (a0 + a1 * Real.log 80) / 5) / 80 := by
    have e : √(32 / 15) * e1 r * (2 * Ac c / 5) / c = √(32 / 15) * e1 r * (2 / 5 * (Ac c / c)) := by ring
    have e' : √(32 / 15) * e1 rBar * (2 * (a0 + a1 * Real.log 80) / 5) / 80
        = √(32 / 15) * e1 rBar * (2 / 5 * ((a0 + a1 * Real.log 80) / 80)) := by ring
    have : 0 ≤ e1 rBar := he0.trans he
    rw [e, e']
    gcongr
  have t4 : e1 r ^ 2 / 2 * (Ac c * Real.log (c / 5) + J / c) / c ^ 2 ≤ e1 rBar ^ 2 / 2 * S1at80 / 80 ^ 2 := by
    have e : e1 r ^ 2 / 2 * (Ac c * Real.log (c / 5) + J / c) / c ^ 2
        = e1 r ^ 2 / 2 * ((Ac c * Real.log (c / 5) + J / c) / c ^ 2) := by ring
    have e' : e1 rBar ^ 2 / 2 * S1at80 / 80 ^ 2 = e1 rBar ^ 2 / 2 * (S1at80 / 80 ^ 2) := by ring
    rw [e, e']
    gcongr
  have t5 : 2 * r * (J / c) * (2 * (2 + r) * Lc c + (2 + r) ^ 2 / 2) / (1 - r) ^ 4
      ≤ 2 * rBar * (21 / 80) * (2 * (2 + rBar) * Lc 80 + (2 + rBar) ^ 2 / 2) / (1 - rBar) ^ 4 := by
    have hLc := mul_Lc_le hc hrρ
    have hLc0 : 0 ≤ r * Lc c := mul_nonneg hr0 (Lc_nonneg hc)
    have e : ∀ x y z : ℝ, 2 * x * z * (2 * (2 + x) * y + (2 + x) ^ 2 / 2) / (1 - x) ^ 4
        = z * (4 * (2 + x) * (x * y) + x * (2 + x) ^ 2) / (1 - x) ^ 4 := fun x y z => by ring
    rw [e r (Lc c) (J / c), e rBar (Lc 80) (21 / 80)]
    have hn : 4 * (2 + r) * (r * Lc c) + r * (2 + r) ^ 2 ≤ 4 * (2 + rBar) * (rBar * Lc 80) + rBar * (2 + rBar) ^ 2 := by
      have a : 4 * (2 + r) * (r * Lc c) ≤ 4 * (2 + rBar) * (rBar * Lc 80) :=
        mul_le_mul (by linarith) hLc hLc0 (by linarith)
      have b : r * (2 + r) ^ 2 ≤ rBar * (2 + rBar) ^ 2 :=
        mul_le_mul hrb (pow_le_pow_left₀ (by linarith) (by linarith) 2) (by positivity) hbar0
      linarith
    have := Lc_nonneg hc
    have := Lc_nonneg (le_refl (80 : ℝ))
    have hn0 : 0 ≤ 4 * (2 + r) * (r * Lc c) + r * (2 + r) ^ 2 := by positivity
    have hd : (1 - rBar) ^ 4 ≤ (1 - r) ^ 4 := pow_le_pow_left₀ h1b.le (by linarith) 4
    exact div_le_div₀ (by positivity) (mul_le_mul hJc hn hn0 (by norm_num)) (pow_pos h1b 4) hd
  have t6 : √(I1bar r * I2bar r) * (2 * Ac c / 5) / c
      ≤ √(I1bar rBar * I2bar rBar) * (2 * (a0 + a1 * Real.log 80) / 5) / 80 := by
    have hI20 : 0 ≤ I2bar r := by unfold I2bar; positivity
    have hI1b : 0 ≤ I1bar rBar := by unfold I1bar; positivity
    have hs : √(I1bar r * I2bar r) ≤ √(I1bar rBar * I2bar rBar) :=
      Real.sqrt_le_sqrt (mul_le_mul hI1 hI2 hI20 hI1b)
    have e : √(I1bar r * I2bar r) * (2 * Ac c / 5) / c = √(I1bar r * I2bar r) * (2 / 5 * (Ac c / c)) := by ring
    have e' : √(I1bar rBar * I2bar rBar) * (2 * (a0 + a1 * Real.log 80) / 5) / 80
        = √(I1bar rBar * I2bar rBar) * (2 / 5 * ((a0 + a1 * Real.log 80) / 80)) := by ring
    rw [e, e']
    exact mul_le_mul hs (by linarith) (by positivity) (Real.sqrt_nonneg _)
  unfold R0bar
  linarith

/-- `0 ≤ C̄(c, r) ≤ C̄(80, r̄_f)` for `c ≥ 80`, `r ≤ r̄_f`. -/
theorem Cbar_le {c r : ℝ} (hc : 80 ≤ c) (hr : r ≤ rBarF) : 0 ≤ Cbar c r ∧ Cbar c r ≤ Cbar 80 rBarF := by
  have h1 : 0 < 1 - rBarF := by linarith [rBarF_mem.2]
  have := rBarF_mem.1
  refine ⟨by unfold Cbar; positivity, ?_⟩
  unfold Cbar Cvs.Prolate.Mellin.GreenBoundaryBound.betaSq Cvs.Prolate.Mellin.GreenBulkBound.rhoSq
  gcongr

/-- `0 ≤ ω₂(c, r)² ≤ ω₂(80, r̄)²` for `c ≥ 80`, `r ≤ r̄`. -/
theorem omega2Sq_le {c r : ℝ} (hc : 80 ≤ c) (hr : r ≤ rBar) :
    0 ≤ omega2Sq c r ∧ omega2Sq c r ≤ omega2Sq 80 rBar := by
  have h4 : 0 < 4 - rBar := by linarith [rBar_mem.2]
  have h4' : 0 < 4 - r := by linarith
  refine ⟨by unfold omega2Sq; positivity, ?_⟩
  unfold omega2Sq
  gcongr

/-- `√(x + y) ≤ √x + √y` for `y ≥ 0`. -/
theorem sqrt_add_le_add {x y : ℝ} (hy : 0 ≤ y) : √(x + y) ≤ √x + √y := by
  rcases le_or_gt 0 x with hx | hx
  · refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, Real.sqrt_nonneg x, Real.sqrt_nonneg y,
      mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]
  · rw [Real.sqrt_eq_zero_of_nonpos hx.le, zero_add]
    exact Real.sqrt_le_sqrt (by linarith)

/-- **η_P uniformly in `c`**: `η_P(c, κ(1 + log c), J) ≤ Ē/κ` for `c ≥ 80`, `κ ≥ 1`, `0 ≤ J ≤ c/4 + 1`. -/
theorem etaP_le_Ebar {c κ J : ℝ} (hc : 80 ≤ c) (hκ : 1 ≤ κ) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1) :
    etaP c (κ * (1 + Real.log c)) J ≤ Ebar / κ := by
  have hc0 : 0 < c := by linarith
  have hL80 : Real.log 80 ≤ Real.log c := Real.log_le_log (by norm_num) hc
  have hlog1 := one_le_log_80
  have hL0 : 0 ≤ Real.log c := by linarith
  obtain ⟨hr0, hrρ, hρb⟩ := rLow_le hc hκ
  have hfb := (rf_le hc hκ).2
  have hJc := J_div_le hc hJ
  have hJc0 : 0 ≤ J / c := by positivity
  have hFar : Far c (κ * (1 + Real.log c)) J ≤ Fbar := by
    obtain ⟨hC0, hC⟩ := Cbar_le hc hfb
    unfold Far Fbar
    gcongr
  have hWb : Wb c (κ * (1 + Real.log c)) J ≤ Wbar := by
    obtain ⟨hω0, hω⟩ := omega2Sq_le hc (hrρ.trans hρb)
    unfold Wb Wbar
    exact mul_le_mul hJc hω hω0 (by norm_num)
  have hR := Rcal_le hc hκ hJ0 hJ
  have hR1 : 0 ≤ R1bar := by
    unfold R1bar a1; have : 0 < betaEdge := by unfold betaEdge; norm_num
    positivity
  set A := √Fbar + √Wbar + √R0bar with hAd
  set S := √(Far c (κ * (1 + Real.log c)) J) + √(Wb c (κ * (1 + Real.log c)) J)
    + √(Rcal c (rLow c (κ * (1 + Real.log c))) J) with hSd
  have hS : S ≤ A + √R1bar * √(Real.log c) := by
    have h3 : √(Rcal c (rLow c (κ * (1 + Real.log c))) J) ≤ √R0bar + √R1bar * √(Real.log c) := by
      rw [← Real.sqrt_mul hR1]
      exact (Real.sqrt_le_sqrt hR).trans (sqrt_add_le_add (by positivity))
    have h1 := Real.sqrt_le_sqrt hFar
    have h2 := Real.sqrt_le_sqrt hWb
    rw [hSd, hAd]
    linarith
  have hS0 : 0 ≤ S := by positivity
  have hu0 : 0 < √(1 + Real.log 80) := Real.sqrt_pos.mpr (by linarith)
  have hu : √(1 + Real.log 80) ≤ √(1 + Real.log c) := Real.sqrt_le_sqrt (by linarith)
  have hupos : 0 < √(1 + Real.log c) := hu0.trans_le hu
  have hLu : √(Real.log c) ≤ √(1 + Real.log c) := Real.sqrt_le_sqrt (by linarith)
  have hA0 : 0 ≤ A := by positivity
  have hSu : S / √(1 + Real.log c) ≤ A / √(1 + Real.log 80) + √R1bar := by
    rw [div_le_iff₀ hupos]
    have : A ≤ A / √(1 + Real.log 80) * √(1 + Real.log c) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hu0]
      exact mul_le_mul_of_nonneg_left hu hA0
    have : √R1bar * √(Real.log c) ≤ √R1bar * √(1 + Real.log c) :=
      mul_le_mul_of_nonneg_left hLu (Real.sqrt_nonneg _)
    nlinarith
  have hκ0 : 0 < κ := by linarith
  have e : etaP c (κ * (1 + Real.log c)) J = (S / √(1 + Real.log c)) ^ 2 / π / κ := by
    unfold etaP
    rw [div_pow, Real.sq_sqrt (by linarith)]
    field_simp
    rw [hSd]
  rw [e]
  unfold Ebar
  gcongr

variable {ι : Type} [Fintype ι]

/-- **The full-tail L2a, uniformly in `c`**: `RungSpanLowMass`'s `L2a_span_fulltail_ff` at `K0 = κ(1 + log c)`, `κ ≥ 1`, with
`η = Ē/(κκ_F)` in place of `η_P/κ_F`. -/
theorem L2a_span_fulltail_ff_unif {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) {X κ κF : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hX : 2 ≤ X) (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hσ : ∀ i, 5 * c ≤ c ^ 2 - χ i)
    (hχinj : Function.Injective χ) (hM : ∀ i, 0 < ∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)
    (hJ : (Fintype.card ι : ℝ) ≤ c / 4 + 1) (hκ1 : 1 ≤ κ) (hT : 2 ≤ c / (κ * (1 + Real.log c)))
    (hκ : 0 < κF)
    (hFF : κF * ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)
      ≤ ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2) :
    (archSymbol (c / (κ * (1 + Real.log c))) - 114 / (c / (κ * (1 + Real.log c)))
        - (archSymbol (c / (κ * (1 + Real.log c))) - archSymbol 0) * (Ebar / (κ * κF))
        - (Real.log 2 + 4 * √(ALoc (Fintype.card ι) c (((c / (κ * (1 + Real.log c))) ^ 2 + 1 / 16) / c ^ 2)
          (c / (κ * (1 + Real.log c))) κF / 2))
        - 6 * (Fintype.card ι : ℝ) / c * (lamCount nsRamp (5 / 4) X + kapCount nsRamp nsRamp' (5 / 4) X) / κF
        - 49 * (c / 4 + 1) / (2 * c ^ 2 * κF))
        * (∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2)
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm ⌊X⌋₊ ⌊X⌋₊
          (logScale (posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X)) := by
  obtain ⟨-, hrρ, hρb⟩ := rLow_le hc hκ1
  have hr : rLow c (κ * (1 + Real.log c)) < 1 := (hrρ.trans hρb).trans_lt rBar_mem.2
  have h := L2a_span_fulltail_ff a hg hg₁ hg₂c hang hX hc hχ0 hσ hχinj hM hJ hr hT hκ hFF
  refine le_trans (mul_le_mul_of_nonneg_right ?_ (setIntegral_nonneg measurableSet_Ioi fun θ _ => sq_nonneg _)) h
  have hη : etaP c (κ * (1 + Real.log c)) (Fintype.card ι) / κF ≤ Ebar / (κ * κF) := by
    rw [← div_div]
    exact div_le_div_of_nonneg_right (etaP_le_Ebar hc hκ1 (Nat.cast_nonneg _) hJ) hκ.le
  have hD := mul_le_mul_of_nonneg_left hη (Cvs.WeilForm.Archimedean.GradedArchFloor.archSymbol_sub_zero_nonneg (c / (κ * (1 + Real.log c))))
  linarith

end Cvs.L2a.LowConstantUniform
