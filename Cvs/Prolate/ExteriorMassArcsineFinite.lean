import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.ZetaValues
import Cvs.L2a.LeakageEnergyScaling
import Cvs.Prolate.ExteriorMassEdgeLayer
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The arcsine law of the exterior mass at finite `c`

For a radial solution on `[1, ∞)` with `ψ² ∈ L¹(1, ∞)`, `0 ≤ χ < c²`, a base point `ξ_b ≤ ξ₀` and `w(ξ_b), w(ξ₀) < 2`:
`|∫_Y^∞ ψ² − (2/π) arcsin(1/Y) ∫_1^∞ ψ²| ≤ errR · ∫_1^∞ ψ² / Y` for every `Y ≥ 1`, with `errR c χ ξ_b ξ₀` in closed form
from `fac(ξ₀)`, `c/√(c²−χ)`, `c/(c²−χ)`, `c(ξ₀ − 1) K_b` and `arcsin(1/ξ₀)`.
-/

noncomputable section

open MeasureTheory Real Set Filter Topology Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.ExteriorMassEdgeLayer

namespace Cvs.Prolate.ExteriorMassArcsineFinite

/-- `ℓ = (2/π) arcsin(1/ξ₀)`, the share of the arcsine law beyond `ξ₀`. -/
def ellA (ξ₀ : ℝ) : ℝ := 2 / π * arcsin (1 / ξ₀)

/-- The lower energy coefficient `L = ℓ/fac(ξ₀)`. -/
def lowL (c χ ξ₀ : ℝ) : ℝ := ellA ξ₀ / Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀

/-- The upper coefficient `U = fac(ξ₀) c/√(c²−χ) + (4/π) c (ξ₀ − 1) K_b`. -/
def upU (c χ ξb ξ₀ : ℝ) : ℝ :=
  Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀ * (c / √(c ^ 2 - χ)) + 4 / π * (c * (ξ₀ - 1)) * kEdge c χ ξb

/-- The edge-term coefficient `e = fac(ξ₀) c/(c² − χ)`. -/
def errE (c χ ξ₀ : ℝ) : ℝ := Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀ * (c / (c ^ 2 - χ))

/-- The relative error `ξ₀((π/2)(U − ℓL) + 2e)/((π/2)L − e)`. -/
def errR (c χ ξb ξ₀ : ℝ) : ℝ :=
  ξ₀ * (π / 2 * (upU c χ ξb ξ₀ - ellA ξ₀ * lowL c χ ξ₀) + 2 * errE c χ ξ₀)
    / (π / 2 * lowL c χ ξ₀ - errE c χ ξ₀)

/-- `q(Y) ≥ (c² − χ) Y` for `Y ≥ 1`, `0 ≤ χ`. -/
theorem qP_ge {c χ Y : ℝ} (hχ0 : 0 ≤ χ) (hY : 1 ≤ Y) : (c ^ 2 - χ) * Y ≤ qP c χ Y := by
  unfold qP
  nlinarith [sq_nonneg c, mul_nonneg (sq_nonneg c) (mul_nonneg (by linarith : (0 : ℝ) ≤ Y) (by linarith : 0 ≤ Y - 1)),
    mul_nonneg hχ0 (by linarith : 0 ≤ Y - 1)]

/-- `fac c/q(Y) ≤ e/Y`. -/
theorem fac_div_qP_le {c χ ξ₀ Y : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hY : 1 ≤ Y)
    (hF : 0 ≤ Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀) :
    Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀ * (c / qP c χ Y) ≤ errE c χ ξ₀ / Y := by
  have hs : 0 < c ^ 2 - χ := by linarith
  have hq := qP_ge (c := c) hχ0 hY
  have hY0 : 0 < Y := by linarith
  have hqpos : 0 < qP c χ Y := lt_of_lt_of_le (by positivity) hq
  unfold errE
  rw [mul_div_assoc', mul_div_assoc', div_div]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hq

/-- **The comparison step, in real numbers.** If `T₁` lies in `[g((π/2)L − e), g((π/2)U + e)]`, `T_Y` lies in
`[g(sL − e/Y), g(sU + e/Y)]` when `Y ≥ ξ₀` and in `[g((π/2)L − e), T₁]` with `ℓ ≤ (2/π)s` when `Y ≤ ξ₀`, and
`s ≤ (π/2)/Y`, then `|T_Y − (2/π) s T₁| ≤ ξ₀((π/2)(U − ℓL) + 2e)/((π/2)L − e) · T₁/Y`. -/
theorem abs_sub_le_core {g T1 TY s ℓ L U e ξ₀ Y : ℝ} (hg0 : 0 ≤ g) (he0 : 0 ≤ e)
    (hℓ1 : ℓ ≤ 1) (hL0 : 0 ≤ L) (hLU : L ≤ U) (hY : 1 ≤ Y) (hξ : 1 ≤ ξ₀) (hs0 : 0 ≤ s)
    (hsY : s ≤ π / 2 / Y) (hsπ : s ≤ π / 2) (hden : 0 < π / 2 * L - e)
    (hT1lo : g * (π / 2 * L - e) ≤ T1) (hT1hi : T1 ≤ g * (π / 2 * U + e))
    (hfar : ξ₀ ≤ Y → g * (s * L - e / Y) ≤ TY ∧ TY ≤ g * (s * U + e / Y))
    (hnear : Y ≤ ξ₀ → g * (π / 2 * L - e) ≤ TY ∧ TY ≤ T1 ∧ ℓ ≤ 2 / π * s) :
    |TY - 2 / π * s * T1| ≤ ξ₀ * (π / 2 * (U - ℓ * L) + 2 * e) / (π / 2 * L - e) * T1 / Y := by
  have hπ := pi_pos
  have hY0 : 0 < Y := by linarith
  set Bk := π / 2 * (U - ℓ * L) + 2 * e with hBk
  have hℓL : ℓ * L ≤ L := mul_le_of_le_one_left hL0 hℓ1
  have hBk0 : 0 ≤ Bk := by
    have : 0 ≤ U - ℓ * L := by linarith
    rw [hBk]; positivity
  have hT10 : 0 ≤ T1 := le_trans (mul_nonneg hg0 hden.le) hT1lo
  have hmain : |TY - 2 / π * s * T1| ≤ g * (ξ₀ * Bk) / Y := by
    rcases le_total ξ₀ Y with hYξ | hYξ
    · obtain ⟨lo, hi⟩ := hfar hYξ
      have h2s : 2 / π * s ≤ 1 / Y := by
        have : 2 / π * s ≤ 2 / π * (π / 2 / Y) := mul_le_mul_of_nonneg_left hsY (by positivity)
        have e : 2 / π * (π / 2 / Y) = 1 / Y := by field_simp
        linarith
      have h2s0 : 0 ≤ 2 / π * s := by positivity
      have e1 := mul_le_mul_of_nonneg_left hT1lo h2s0
      have e2 := mul_le_mul_of_nonneg_left hT1hi h2s0
      have es : 2 / π * s * (g * (π / 2 * L - e)) = g * (s * L) - g * (2 / π * s * e) := by
        field_simp
      have es' : 2 / π * s * (g * (π / 2 * U + e)) = g * (s * U) + g * (2 / π * s * e) := by
        field_simp
      have a1 : s * (U - L) ≤ π / 2 / Y * (U - ℓ * L) := by
        calc s * (U - L) ≤ π / 2 / Y * (U - L) := mul_le_mul_of_nonneg_right hsY (by linarith)
          _ ≤ π / 2 / Y * (U - ℓ * L) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have a2 : 2 / π * s * e ≤ e / Y := by
        calc 2 / π * s * e ≤ 1 / Y * e := mul_le_mul_of_nonneg_right h2s he0
          _ = e / Y := by ring
      have a3 : Bk / Y ≤ ξ₀ * Bk / Y := by
        apply div_le_div_of_nonneg_right _ hY0.le; nlinarith
      have a4 : π / 2 / Y * (U - ℓ * L) + e / Y + e / Y = Bk / Y := by rw [hBk]; ring
      have hbr : s * (U - L) + e / Y + 2 / π * s * e ≤ ξ₀ * Bk / Y := by linarith
      have hgb := mul_le_mul_of_nonneg_left hbr hg0
      have e3 : g * (ξ₀ * Bk / Y) = g * (ξ₀ * Bk) / Y := by ring
      have e4 : g * (s * (U - L) + e / Y + 2 / π * s * e)
          = g * (s * U) - g * (s * L) + g * (e / Y) + g * (2 / π * s * e) := by ring
      have e5 : g * (s * L - e / Y) = g * (s * L) - g * (e / Y) := by ring
      have e6 : g * (s * U + e / Y) = g * (s * U) + g * (e / Y) := by ring
      rw [abs_le]; constructor <;> linarith
    · obtain ⟨lo, hi, hsℓ⟩ := hnear hYξ
      have hs1 : 2 / π * s ≤ 1 := by
        have : 2 / π * s ≤ 2 / π * (π / 2) := mul_le_mul_of_nonneg_left hsπ (by positivity)
        have e : 2 / π * (π / 2) = 1 := by field_simp
        linarith
      have hm0 : 0 ≤ g * (π / 2 * L - e) := mul_nonneg hg0 hden.le
      have hlo1 : ℓ * (g * (π / 2 * L - e)) ≤ TY := le_trans (mul_le_of_le_one_left hm0 hℓ1) lo
      have hlo2 : ℓ * (g * (π / 2 * L - e)) ≤ 2 / π * s * T1 :=
        mul_le_mul hsℓ hT1lo hm0 (by positivity)
      have hhi2 : 2 / π * s * T1 ≤ T1 := mul_le_of_le_one_left hT10 hs1
      have hb1 : g * (π / 2 * U + e) - ℓ * (g * (π / 2 * L - e)) ≤ g * Bk := by
        have := mul_le_mul_of_nonneg_left hℓ1 (mul_nonneg hg0 he0)
        have e7 : g * Bk = g * (π / 2 * U + e) - g * (π / 2 * (ℓ * L)) + g * e := by rw [hBk]; ring
        have e8 : ℓ * (g * (π / 2 * L - e)) = g * (π / 2 * (ℓ * L)) - ℓ * (g * e) := by ring
        linarith
      have hb2 : g * Bk ≤ g * (ξ₀ * Bk) / Y := by
        rw [le_div_iff₀ hY0]
        have : g * Bk * Y ≤ g * Bk * ξ₀ := mul_le_mul_of_nonneg_left hYξ (mul_nonneg hg0 hBk0)
        linarith
      rw [abs_le]; constructor <;> linarith
  have hgT : g * (ξ₀ * Bk) ≤ ξ₀ * Bk / (π / 2 * L - e) * T1 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hden]
    have := mul_le_mul_of_nonneg_left hT1lo (mul_nonneg (by linarith : (0 : ℝ) ≤ ξ₀) hBk0)
    linarith [mul_comm g (ξ₀ * Bk), mul_assoc (ξ₀ * Bk) g (π / 2 * L - e)]
  calc |TY - 2 / π * s * T1| ≤ g * (ξ₀ * Bk) / Y := hmain
    _ ≤ ξ₀ * Bk / (π / 2 * L - e) * T1 / Y := div_le_div_of_nonneg_right hgT hY0.le

/-- **The arcsine law at finite `c`.** Under the finite-`c` hypotheses, for every `Y ≥ 1`,
`|∫_Y^∞ ψ² − (2/π) arcsin(1/Y) ∫_1^∞ ψ²| ≤ errR · ∫_1^∞ ψ² / Y`. -/
theorem relative_law {ψ v v' : ℝ → ℝ} {c χ ξb ξ₀ : ℝ}
    (hψ : ∀ r ∈ Ici (1 : ℝ), HasDerivAt ψ (v r) r)
    (hv : ∀ r ∈ Ici (1 : ℝ), HasDerivAt v (v' r) r)
    (hode : ∀ r ∈ Ici (1 : ℝ), (r ^ 2 - 1) * v' r + 2 * r * v r + (c ^ 2 * r ^ 2 - χ) * ψ r = 0)
    (hint : IntegrableOn (fun t => ψ t ^ 2) (Ioi 1))
    (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hb : 1 < ξb) (hb0 : ξb ≤ ξ₀)
    (ha4 : pP ξb * qP c χ ξb < 4) (hWb : wP c χ ξb < 2) (hW : wP c χ ξ₀ < 2)
    (hden : errE c χ ξ₀ < π / 2 * lowL c χ ξ₀) {Y : ℝ} (hY : 1 ≤ Y) :
    |(∫ t in Ioi Y, ψ t ^ 2) - 2 / π * arcsin (1 / Y) * ∫ t in Ioi 1, ψ t ^ 2|
      ≤ errR c χ ξb ξ₀ * (∫ t in Ioi 1, ψ t ^ 2) / Y := by
  have hπ := pi_pos
  have h1 : 1 < ξ₀ := lt_of_lt_of_le hb hb0
  set F := Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀ with hFdef
  set G₀ := enG c χ ψ v ξ₀ with hG₀
  set g := G₀ / (2 * c) with hg
  set T1 := ∫ t in Ioi 1, ψ t ^ 2 with hT1
  set TY := ∫ t in Ioi Y, ψ t ^ 2 with hTY
  set T0 := ∫ t in Ioi ξ₀, ψ t ^ 2 with hT0
  set s := arcsin (1 / Y) with hs
  set ℓ := ellA ξ₀ with hℓ
  set L := lowL c χ ξ₀ with hL
  set U := upU c χ ξb ξ₀ with hU
  set e := errE c χ ξ₀ with he
  set σ := √(c ^ 2 - χ) with hσ
  have hF0 : 0 < F := fac_pos h1 hc hχ hW
  have hG0 : 0 ≤ G₀ := enG_nonneg h1 hc hχ
  have hg0 : 0 ≤ g := by positivity
  have hsub : 0 < c ^ 2 - χ := by linarith
  have hσ0 : 0 < σ := Real.sqrt_pos.mpr hsub
  have hσc : σ ≤ c := by
    rw [hσ, Real.sqrt_le_left hc.le]; linarith
  have hY0 : 0 < Y := by linarith
  have hKb0 : 0 ≤ kEdge c χ ξb := by
    have hc2 : 0 < c ^ 2 := by positivity
    have := fac_pos hb hc hχ hWb
    have ha := aP_pos hb hc2 hχ
    unfold kEdge
    have : 0 < 1 - pP ξb * qP c χ ξb / 4 := by linarith
    positivity
  have he0 : 0 ≤ e := by rw [he]; unfold errE; positivity
  -- arcsine facts
  have hs0 : 0 ≤ s := arcsin_nonneg.mpr (by positivity)
  have hsπ : s ≤ π / 2 := arcsin_le_pi_div_two _
  have hsY : s ≤ π / 2 / Y := by
    have := Cvs.L2a.LeakageEnergyScaling.arcsin_le_pi_div_two_mul (y := 1 / Y) (by positivity)
      (by rw [div_le_one hY0]; exact hY)
    rw [hs]; calc arcsin (1 / Y) ≤ π / 2 * (1 / Y) := this
      _ = π / 2 / Y := by ring
  have harc0 : 0 ≤ arcsin (1 / ξ₀) := arcsin_nonneg.mpr (by positivity)
  have harcπ : arcsin (1 / ξ₀) ≤ π / 2 := arcsin_le_pi_div_two _
  have hℓ0 : 0 ≤ ℓ := by rw [hℓ]; unfold ellA; positivity
  have hℓ1 : ℓ ≤ 1 := by
    rw [hℓ]; unfold ellA
    rw [div_mul_eq_mul_div, div_le_one hπ]; linarith
  have hℓarc : π / 2 * ℓ = arcsin (1 / ξ₀) := by rw [hℓ]; unfold ellA; field_simp
  have hL0 : 0 ≤ L := by rw [hL]; unfold lowL; positivity
  have hden' : 0 < π / 2 * L - e := by linarith
  -- the two-sided tail bounds, in units of `g`
  have hcq : ∀ y, 1 ≤ y → G₀ * F / (2 * qP c χ y) ≤ g * (e / y) := by
    intro y hy
    have := fac_div_qP_le hc hχ0 hχ hy hF0.le (ξ₀ := ξ₀)
    have hy0 : 0 < y := by linarith
    have hq : 0 < qP c χ y := lt_of_lt_of_le (by positivity) (qP_ge (c := c) hχ0 hy)
    calc G₀ * F / (2 * qP c χ y) = g * (F * (c / qP c χ y)) := by rw [hg]; field_simp
      _ ≤ g * (e / y) := mul_le_mul_of_nonneg_left this hg0
  have tail : ∀ y, ξ₀ ≤ y →
      g * (arcsin (1 / y) / F - e / y) ≤ ∫ t in Ioi y, ψ t ^ 2 ∧
        ∫ t in Ioi y, ψ t ^ 2 ≤ g * (arcsin (1 / y) * (F * (c / σ)) + e / y) := by
    intro y hy
    have hy1 : 1 ≤ y := h1.le.trans hy
    obtain ⟨lo, hi⟩ := tail_mass_bounds hψ hv hode hint hc hχ0 hχ h1 hy hW
    have hy0 : 0 < y := by linarith
    have ha0 : 0 ≤ arcsin (1 / y) := arcsin_nonneg.mpr (by positivity)
    have hq := hcq y hy1
    have hLle : L ≤ 1 / F := by
      rw [hL]; unfold lowL; exact div_le_div_of_nonneg_right hℓ1 hF0.le
    have hUge : F * (c / σ) ≤ U := by
      rw [hU]; unfold upU
      have : 0 ≤ 4 / π * (c * (ξ₀ - 1)) * kEdge c χ ξb := by
        have : 0 ≤ ξ₀ - 1 := by linarith
        positivity
      linarith
    refine ⟨?_, ?_⟩
    · refine le_trans ?_ lo
      have e1 : G₀ / F * arcsin (1 / y) / (2 * c) = g * (arcsin (1 / y) / F) := by
        rw [hg]; field_simp
      rw [e1, mul_sub]
      linarith [hq]
    · refine le_trans hi ?_
      have e1 : G₀ * F * arcsin (1 / y) / (2 * σ) = g * (arcsin (1 / y) * (F * (c / σ))) := by
        rw [hg]; field_simp
      rw [e1, mul_add]
      linarith [hq]
  -- bounds on `T1`
  obtain ⟨t0lo, t0hi⟩ := tail ξ₀ le_rfl
  have hsplit := integral_Ioi_split hint h1.le
  have hedge := edge_layer_le hψ hv hode hc hχ0 hχ hb hb0 ha4 hWb
  have hedge0 : 0 ≤ ∫ t in (1 : ℝ)..ξ₀, ψ t ^ 2 :=
    intervalIntegral.integral_nonneg h1.le fun t _ => sq_nonneg _
  have he1 : e / ξ₀ ≤ e := div_le_self he0 h1.le
  have hT0lo : g * (π / 2 * L - e) ≤ T0 := by
    refine le_trans ?_ t0lo
    have hA : arcsin (1 / ξ₀) / F = π / 2 * L := by
      rw [← hℓarc, hL]; unfold lowL; rw [← hℓ]; ring
    rw [hA]
    have := mul_le_mul_of_nonneg_left he1 hg0
    linarith [mul_sub g (π / 2 * L) e, mul_sub g (π / 2 * L) (e / ξ₀)]
  have hT1lo : g * (π / 2 * L - e) ≤ T1 := by
    rw [hT1, hsplit]; linarith
  have hT1hi : T1 ≤ g * (π / 2 * U + e) := by
    rw [hT1, hsplit]
    have hed : (ξ₀ - 1) * (kEdge c χ ξb * G₀) = g * (π / 2 * (4 / π * (c * (ξ₀ - 1)) * kEdge c χ ξb)) := by
      rw [hg]; field_simp; ring
    have hFU : arcsin (1 / ξ₀) * (F * (c / σ)) ≤ π / 2 * (F * (c / σ)) :=
      mul_le_mul_of_nonneg_right harcπ (by positivity)
    have hU' : π / 2 * U = π / 2 * (F * (c / σ)) + π / 2 * (4 / π * (c * (ξ₀ - 1)) * kEdge c χ ξb) := by
      rw [hU]; unfold upU; ring
    have h3 := mul_le_mul_of_nonneg_left hFU hg0
    have h4 := mul_le_mul_of_nonneg_left he1 hg0
    rw [hed] at hedge
    have e5 : g * (π / 2 * U + e) = g * (π / 2 * (F * (c / σ))) + g * (π / 2 * (4 / π * (c * (ξ₀ - 1))
        * kEdge c χ ξb)) + g * e := by rw [hU']; ring
    have e6 : g * (arcsin (1 / ξ₀) * (F * (c / σ)) + e / ξ₀)
        = g * (arcsin (1 / ξ₀) * (F * (c / σ))) + g * (e / ξ₀) := by ring
    linarith
  have hLle : L ≤ 1 / F := by
    rw [hL]; unfold lowL; exact div_le_div_of_nonneg_right hℓ1 hF0.le
  have hUge : F * (c / σ) ≤ U := by
    rw [hU]; unfold upU
    have : 0 ≤ 4 / π * (c * (ξ₀ - 1)) * kEdge c χ ξb := by
      have : 0 ≤ ξ₀ - 1 := by linarith
      positivity
    linarith
  have hLU : L ≤ U := by
    have hge1 : 1 ≤ F := by
      have hw := wP_pos h1 (by positivity : 0 < c ^ 2) hχ
      rw [hFdef]; unfold Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac
      have hd : 0 < 1 - wP c χ ξ₀ / 2 := by linarith
      have h1' : 1 ≤ (1 + wP c χ ξ₀ / 2) / (1 - wP c χ ξ₀ / 2) := by
        rw [le_div_iff₀ hd]; linarith
      have h2 : 1 ≤ exp (wP c χ ξ₀ / (2 - wP c χ ξ₀)) := by
        apply one_le_exp; apply div_nonneg hw.le; linarith
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ _ := mul_le_mul h1' h2 zero_le_one (by linarith)
    have hF1 : 1 / F ≤ 1 := by rw [div_le_one hF0]; exact hge1
    have hcσ : 1 ≤ c / σ := by rw [le_div_iff₀ hσ0]; linarith
    have : 1 ≤ F * (c / σ) := by
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ F * (c / σ) := mul_le_mul hge1 hcσ zero_le_one (by linarith)
    linarith
  have hR : errR c χ ξb ξ₀ = ξ₀ * (π / 2 * (U - ℓ * L) + 2 * e) / (π / 2 * L - e) := rfl
  rw [hR]
  refine abs_sub_le_core (TY := ∫ t in Ioi Y, ψ t ^ 2) hg0 he0 hℓ1 hL0 hLU hY h1.le hs0 hsY hsπ hden' hT1lo hT1hi ?_ ?_
  · intro hYξ
    obtain ⟨lo, hi⟩ := tail Y hYξ
    have h1F : s * L ≤ s / F := by
      rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hLle hs0
    have hVU : s * (F * (c / σ)) ≤ s * U := mul_le_mul_of_nonneg_left hUge hs0
    constructor
    · refine le_trans ?_ lo
      exact mul_le_mul_of_nonneg_left (by linarith) hg0
    · refine le_trans hi ?_
      exact mul_le_mul_of_nonneg_left (by linarith) hg0
  · intro hYξ
    have hTY0 : T0 ≤ TY := setIntegral_mono_set (hint.mono_set (Ioi_subset_Ioi hY))
        (ae_of_all _ fun t => sq_nonneg _) (ae_of_all _ (Ioi_subset_Ioi hYξ))
    have hTY1 : TY ≤ T1 := setIntegral_mono_set hint
        (ae_of_all _ fun t => sq_nonneg _) (ae_of_all _ (Ioi_subset_Ioi hY))
    have hsℓ : ℓ ≤ 2 / π * s := by
      rw [hℓ]; unfold ellA
      have : arcsin (1 / ξ₀) ≤ s := arcsin_le_arcsin (one_div_le_one_div_of_le hY0 hYξ)
      exact mul_le_mul_of_nonneg_left this (by positivity)
    exact ⟨hT0lo.trans hTY0, hTY1, hsℓ⟩

end Cvs.Prolate.ExteriorMassArcsineFinite

end
