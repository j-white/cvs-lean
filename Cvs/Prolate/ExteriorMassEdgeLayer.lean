import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.Prolate.Envelope.EdgeValueSoninBound
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyLower
import Cvs.Prolate.LiouvilleGreen.ProlateArcsinMassLaw
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay
import Cvs.Prolate.LiouvilleGreen.SoninFunction

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The exterior mass beyond `Y`, two-sided, and the edge layer

For a solution of `((ξ²−1)ψ')' + (c²ξ² − χ)ψ = 0` on `[1, ∞)` with `ψ² ∈ L¹(1, ∞)`, `0 ≤ χ < c²`, `1 < ξ₀ ≤ Y` and
`w(ξ₀) < 2`: `G₀ arcsin(1/Y)/(2cF) − G₀F/(2q(Y)) ≤ ∫_Y^∞ ψ² ≤ G₀F arcsin(1/Y)/(2√(c²−χ)) + G₀F/(2q(Y))`, with `G₀` the
Liouville–Green energy at `ξ₀` and `F = fac(ξ₀)`; and `∫_1^{ξ₀} ψ² ≤ (ξ₀ − 1) K_b G₀` for any base point `ξ_b ≤ ξ₀`.
-/

noncomputable section

open MeasureTheory Real Set Filter Topology Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

namespace Cvs.Prolate.ExteriorMassEdgeLayer

variable {ψ v v' : ℝ → ℝ} {c χ : ℝ}

/-- The Liouville–Green energy `a ψ² + (pψ')²/a` of a solution `(ψ, v = ψ')`. -/
def enG (c χ : ℝ) (ψ v : ℝ → ℝ) (ξ : ℝ) : ℝ := energy (aP c χ) ψ (fun r => pP r * v r) ξ

/-- The edge constant `K_b = fac(ξ_b)/(a(ξ_b)(1 − a(ξ_b)²/4))`. -/
def kEdge (c χ ξb : ℝ) : ℝ :=
  Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξb / (aP c χ ξb * (1 - pP ξb * qP c χ ξb / 4))

/-- The radial equation on `[1, ∞)` gives the first-order system `ψ' = u/p`, `u' = −qψ`, `u = pψ'`, at `t > 1`. -/
theorem system_of_ode (hψ : ∀ r ∈ Ici (1 : ℝ), HasDerivAt ψ (v r) r)
    (hv : ∀ r ∈ Ici (1 : ℝ), HasDerivAt v (v' r) r)
    (hode : ∀ r ∈ Ici (1 : ℝ), (r ^ 2 - 1) * v' r + 2 * r * v r + (c ^ 2 * r ^ 2 - χ) * ψ r = 0)
    {t : ℝ} (ht : 1 < t) :
    HasDerivAt ψ (pP t * v t / pP t) t ∧ HasDerivAt (fun r => pP r * v r) (-(qP c χ t * ψ t)) t := by
  have hmem : t ∈ Ici (1 : ℝ) := ht.le
  refine ⟨?_, ?_⟩
  · rw [mul_div_cancel_left₀ _ (pP_pos ht).ne']; exact hψ t hmem
  · have hp : HasDerivAt pP (2 * t) t := by
      have := (hasDerivAt_pow 2 t).sub_const 1; unfold pP; simpa using this
    refine (hp.mul (hv t hmem)).congr_deriv ?_
    have := hode t hmem; unfold pP qP; linarith

/-- The energy is nonnegative at `ξ > 1`. -/
theorem enG_nonneg {ξ : ℝ} (h1 : 1 < ξ) (hc : 0 < c) (hχ : χ < c ^ 2) : 0 ≤ enG c χ ψ v ξ := by
  have ha := aP_pos h1 (by positivity : 0 < c ^ 2) hχ
  unfold enG energy; positivity

/-- `fac > 0` when `w < 2`. -/
theorem fac_pos {ξ : ℝ} (h1 : 1 < ξ) (hc : 0 < c) (hχ : χ < c ^ 2) (hW : wP c χ ξ < 2) :
    0 < Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ := by
  have hw := wP_pos h1 (by positivity : 0 < c ^ 2) hχ
  unfold Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac
  have : 0 < 1 - wP c χ ξ / 2 := by linarith
  positivity

/-- **The energy stays within `fac(ξ₀)^{±1}` of `G₀`** on `[ξ₀, ∞)`. -/
theorem enG_bounds (hψ : ∀ r ∈ Ici (1 : ℝ), HasDerivAt ψ (v r) r)
    (hv : ∀ r ∈ Ici (1 : ℝ), HasDerivAt v (v' r) r)
    (hode : ∀ r ∈ Ici (1 : ℝ), (r ^ 2 - 1) * v' r + 2 * r * v r + (c ^ 2 * r ^ 2 - χ) * ψ r = 0)
    (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) {ξ₀ t : ℝ} (h1 : 1 < ξ₀) (ht : ξ₀ ≤ t)
    (hW : wP c χ ξ₀ < 2) :
    enG c χ ψ v ξ₀ / Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀ ≤ enG c χ ψ v t ∧
      enG c χ ψ v t ≤ enG c χ ψ v ξ₀ * Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀ := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hs1 : ∀ s ∈ Icc ξ₀ t, HasDerivAt ψ (pP s * v s / pP s) s := fun s hs =>
    (system_of_ode hψ hv hode (lt_of_lt_of_le h1 hs.1)).1
  have hs2 : ∀ s ∈ Icc ξ₀ t, HasDerivAt (fun r => pP r * v r) (-(qP c χ s * ψ s)) s := fun s hs =>
    (system_of_ode hψ hv hode (lt_of_lt_of_le h1 hs.1)).2
  have hle := prolate_energy_le h1 ht hc2 hχ0 hχ hs1 hs2 hW
  have hge := Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyLower.prolate_energy_ge h1 ht hc2 hχ0 hχ hs1 hs2 hW
  have hw := wP_pos h1 hc2 hχ
  have hd : 0 < 1 - wP c χ ξ₀ / 2 := by linarith
  have hd' : 0 < 1 + wP c χ ξ₀ / 2 := by linarith
  refine ⟨?_, ?_⟩
  · refine le_trans (le_of_eq ?_) hge
    unfold enG Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac
    rw [Real.exp_neg]
    field_simp
  · refine le_trans hle (le_of_eq ?_)
    unfold enG Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac
    ring

/-- **The exterior mass beyond `Y`, two-sided**: for `1 < ξ₀ ≤ Y`, `w(ξ₀) < 2`, with `G₀ = G(ξ₀)` and `F = fac(ξ₀)`,
`G₀ arcsin(1/Y)/(2cF) − G₀F/(2q(Y)) ≤ ∫_Y^∞ ψ² ≤ G₀F arcsin(1/Y)/(2√(c²−χ)) + G₀F/(2q(Y))`. -/
theorem tail_mass_bounds (hψ : ∀ r ∈ Ici (1 : ℝ), HasDerivAt ψ (v r) r)
    (hv : ∀ r ∈ Ici (1 : ℝ), HasDerivAt v (v' r) r)
    (hode : ∀ r ∈ Ici (1 : ℝ), (r ^ 2 - 1) * v' r + 2 * r * v r + (c ^ 2 * r ^ 2 - χ) * ψ r = 0)
    (hint : IntegrableOn (fun t => ψ t ^ 2) (Ioi 1))
    (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) {ξ₀ Y : ℝ} (h1 : 1 < ξ₀) (hY : ξ₀ ≤ Y)
    (hW : wP c χ ξ₀ < 2) :
    enG c χ ψ v ξ₀ / Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀ * arcsin (1 / Y) / (2 * c)
        - enG c χ ψ v ξ₀ * Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀ / (2 * qP c χ Y) ≤ ∫ t in Ioi Y, ψ t ^ 2 ∧
      ∫ t in Ioi Y, ψ t ^ 2 ≤ enG c χ ψ v ξ₀ * Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀ * arcsin (1 / Y)
          / (2 * √(c ^ 2 - χ)) + enG c χ ψ v ξ₀ * Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀ / (2 * qP c χ Y) := by
  set F := Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀ with hF
  set G₀ := enG c χ ψ v ξ₀ with hG₀
  have hY1 : 1 < Y := lt_of_lt_of_le h1 hY
  have hF0 : 0 < F := fac_pos h1 hc hχ hW
  have hG0 : 0 ≤ G₀ := enG_nonneg h1 hc hχ
  -- the bounds on every `[Y, ξ₁]`
  have hfin : ∀ ξ₁, Y ≤ ξ₁ →
      G₀ / F * (arccos (1 / ξ₁) - arccos (1 / Y)) / (2 * c) - G₀ * F / (2 * qP c χ Y)
          ≤ ∫ t in Y..ξ₁, ψ t ^ 2 ∧
        ∫ t in Y..ξ₁, ψ t ^ 2
          ≤ G₀ * F * (arccos (1 / ξ₁) - arccos (1 / Y)) / (2 * √(c ^ 2 - χ)) + G₀ * F / (2 * qP c χ Y) := by
    intro ξ₁ hξ₁
    have hs1 : ∀ s ∈ Icc Y ξ₁, HasDerivAt ψ (pP s * v s / pP s) s := fun s hs =>
      (system_of_ode hψ hv hode (lt_of_lt_of_le hY1 hs.1)).1
    have hs2 : ∀ s ∈ Icc Y ξ₁, HasDerivAt (fun r => pP r * v r) (-(qP c χ s * ψ s)) s := fun s hs =>
      (system_of_ode hψ hv hode (lt_of_lt_of_le hY1 hs.1)).2
    have hGm : ∀ t ∈ Icc Y ξ₁, G₀ / F ≤ energy (aP c χ) ψ (fun r => pP r * v r) t := fun t ht =>
      (enG_bounds hψ hv hode hc hχ0 hχ h1 (hY.trans ht.1) hW).1
    have hGM : ∀ t ∈ Icc Y ξ₁, energy (aP c χ) ψ (fun r => pP r * v r) t ≤ G₀ * F := fun t ht =>
      (enG_bounds hψ hv hode hc hχ0 hχ h1 (hY.trans ht.1) hW).2
    exact Cvs.Prolate.LiouvilleGreen.ProlateArcsinMassLaw.prolate_mass_bounds hY1 hξ₁ hc hχ0 hχ hs1 hs2 hGm hGM (by positivity)
  -- pass to `ξ₁ → ∞`
  have hI : Tendsto (fun ξ₁ => ∫ t in Y..ξ₁, ψ t ^ 2) atTop (𝓝 (∫ t in Ioi Y, ψ t ^ 2)) :=
    intervalIntegral_tendsto_integral_Ioi Y (hint.mono_set (Ioi_subset_Ioi hY1.le)) tendsto_id
  have hA : Tendsto (fun ξ₁ : ℝ => arccos (1 / ξ₁) - arccos (1 / Y)) atTop (𝓝 (arcsin (1 / Y))) := by
    have h0 : Tendsto (fun ξ₁ : ℝ => 1 / ξ₁) atTop (𝓝 0) := by
      simpa only [one_div] using tendsto_inv_atTop_zero
    have h2 := ((Real.continuous_arccos.tendsto 0).comp h0).sub_const (arccos (1 / Y))
    rw [arccos_zero, ← arcsin_eq_pi_div_two_sub_arccos] at h2
    exact h2
  have hev : ∀ᶠ ξ₁ in atTop, Y ≤ ξ₁ := eventually_ge_atTop Y
  refine ⟨?_, ?_⟩
  · have hL : Tendsto (fun ξ₁ : ℝ => G₀ / F * (arccos (1 / ξ₁) - arccos (1 / Y)) / (2 * c)
        - G₀ * F / (2 * qP c χ Y)) atTop
        (𝓝 (G₀ / F * arcsin (1 / Y) / (2 * c) - G₀ * F / (2 * qP c χ Y))) :=
      ((hA.const_mul (G₀ / F)).div_const (2 * c)).sub_const _
    exact le_of_tendsto_of_tendsto hL hI (hev.mono fun ξ₁ h => (hfin ξ₁ h).1)
  · have hU : Tendsto (fun ξ₁ : ℝ => G₀ * F * (arccos (1 / ξ₁) - arccos (1 / Y)) / (2 * √(c ^ 2 - χ))
        + G₀ * F / (2 * qP c χ Y)) atTop
        (𝓝 (G₀ * F * arcsin (1 / Y) / (2 * √(c ^ 2 - χ)) + G₀ * F / (2 * qP c χ Y))) :=
      ((hA.const_mul (G₀ * F)).div_const _).add_const _
    exact le_of_tendsto_of_tendsto hI hU (hev.mono fun ξ₁ h => (hfin ξ₁ h).2)

/-- **The edge layer**: for `1 < ξ_b ≤ ξ₀` with `a(ξ_b)² < 4` and `w(ξ_b) < 2`,
`∫_1^{ξ₀} ψ² ≤ (ξ₀ − 1) K_b G(ξ₀)`, since `ψ² ≤ ψ(1)²` there (Sonin) and `ψ(1)² ≤ K_b G(ξ₀)` (Cvs.Prolate.Envelope.EdgeValueSoninBound). -/
theorem edge_layer_le (hψ : ∀ r ∈ Ici (1 : ℝ), HasDerivAt ψ (v r) r)
    (hv : ∀ r ∈ Ici (1 : ℝ), HasDerivAt v (v' r) r)
    (hode : ∀ r ∈ Ici (1 : ℝ), (r ^ 2 - 1) * v' r + 2 * r * v r + (c ^ 2 * r ^ 2 - χ) * ψ r = 0)
    (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) {ξb ξ₀ : ℝ} (hb : 1 < ξb) (hb0 : ξb ≤ ξ₀)
    (ha4 : pP ξb * qP c χ ξb < 4) (hWb : wP c χ ξb < 2) :
    ∫ t in (1 : ℝ)..ξ₀, ψ t ^ 2 ≤ (ξ₀ - 1) * (kEdge c χ ξb * enG c χ ψ v ξ₀) := by
  have h10 : (1 : ℝ) ≤ ξ₀ := (hb.trans_le hb0).le
  have hψ' : ∀ r ∈ Icc 1 ξ₀, HasDerivAt ψ (v r) r := fun r hr => hψ r hr.1
  have hv' : ∀ r ∈ Icc 1 ξ₀, HasDerivAt v (v' r) r := fun r hr => hv r hr.1
  have hode' : ∀ r ∈ Icc 1 ξ₀, (r ^ 2 - 1) * v' r + 2 * r * v r + (c ^ 2 * r ^ 2 - χ) * ψ r = 0 :=
    fun r hr => hode r hr.1
  have hedge := Cvs.Prolate.Envelope.EdgeValueSoninBound.edge_le_energy hc hχ0 hχ hψ' hv' hode' hb hb0 le_rfl ha4 hWb
  have hcont : ContinuousOn (fun t => ψ t ^ 2) (Icc 1 ξ₀) := fun t ht =>
    ((hψ t ht.1).continuousAt.pow 2).continuousWithinAt
  have hmono := intervalIntegral.integral_mono_on h10 (hcont.intervalIntegrable_of_Icc h10)
    (intervalIntegrable_const (μ := volume) (c := ψ 1 ^ 2))
    (fun t ht => Cvs.Prolate.LiouvilleGreen.SoninFunction.prolate_sq_le_edge hχ ht hψ' hv' hode')
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  calc ∫ t in (1 : ℝ)..ξ₀, ψ t ^ 2 ≤ (ξ₀ - 1) * ψ 1 ^ 2 := hmono
    _ ≤ (ξ₀ - 1) * (kEdge c χ ξb * enG c χ ψ v ξ₀) :=
        mul_le_mul_of_nonneg_left (by unfold kEdge enG; exact hedge) (by linarith)

/-- The mass beyond `1` splits at `ξ₀ ≥ 1`: `∫_1^∞ ψ² = ∫_1^{ξ₀} ψ² + ∫_{ξ₀}^∞ ψ²`. -/
theorem integral_Ioi_split (hint : IntegrableOn (fun t => ψ t ^ 2) (Ioi 1)) {ξ₀ : ℝ} (h1 : 1 ≤ ξ₀) :
    ∫ t in Ioi 1, ψ t ^ 2 = (∫ t in (1 : ℝ)..ξ₀, ψ t ^ 2) + ∫ t in Ioi ξ₀, ψ t ^ 2 := by
  rw [intervalIntegral.integral_of_le h1, ← setIntegral_union (Ioc_disjoint_Ioi le_rfl)
    measurableSet_Ioi (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi h1)),
    Ioc_union_Ioi_eq_Ioi h1]

end Cvs.Prolate.ExteriorMassEdgeLayer

end
