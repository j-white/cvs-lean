import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.LeakageEnergyScaling
import Cvs.Prolate.AngularBesselInequality
import Cvs.Prolate.ArcsineLawErrorSizes
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.ExteriorMassArcsineFinite
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.Mellin.XiLawsRungEight
import Cvs.Prolate.Mellin.XiLawsRungFour
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
# The arcsine law of the mode energies

If `χ/c² → 0`, every radial solution with `ψ² ∈ L¹(1, ∞)` has, uniformly in `Y ≥ 1`,
`|∫_Y^∞ ψ² − (2/π) arcsin(1/Y) ∫_1^∞ ψ²| ≤ η ∫_1^∞ ψ²/Y` for all large `c`, and
`|Σ_{M≥1} (1/M)∫_M^∞ ψ² − (2/π) S₀ ∫_1^∞ ψ²| ≤ η ∫_1^∞ ψ²`, `S₀ = Σ_M arcsin(1/M)/M`. For the rung of index `j` with
`0 ≤ χ_j ≤ Kc`, and so for `h₀, h₄, h₈`: `∫_M^∞ ψ_j² = (2/c)(1 − λ_j) arcsin(1/M) + η(π/c)(1 − λ_j) O(1/M)`.
-/

noncomputable section

open MeasureTheory Real Set Filter Topology Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.ExteriorMassEdgeLayer Cvs.Prolate.ExteriorMassArcsineFinite Cvs.Prolate.ArcsineLawErrorSizes

namespace Cvs.Prolate.ModeEnergyArcsineLaw
open Cvs.ZeroCounting

/-- `S₀ = Σ_{M ≥ 1} arcsin(1/M)/M`. -/
def sZero : ℝ := ∑' M : ℕ, arcsin (1 / ((M : ℝ) + 1)) / ((M : ℝ) + 1)

/-- **The arcsine law, uniformly in `Y ≥ 1`**, for a family of radial solutions with `χ/c² → 0`. -/
theorem arcsine_law {χ : ℝ → ℝ} {ψ v v' : ℝ → ℝ → ℝ}
    (hu : Tendsto (fun c => χ c / c ^ 2) atTop (𝓝 0))
    (hsys : ∀ᶠ c in atTop, 0 ≤ χ c ∧ (∀ r ∈ Ici (1 : ℝ), HasDerivAt (ψ c) (v c r) r) ∧
      (∀ r ∈ Ici (1 : ℝ), HasDerivAt (v c) (v' c r) r) ∧
      (∀ r ∈ Ici (1 : ℝ), (r ^ 2 - 1) * v' c r + 2 * r * v c r + (c ^ 2 * r ^ 2 - χ c) * ψ c r = 0) ∧
      IntegrableOn (fun t => ψ c t ^ 2) (Ioi 1))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ c in atTop, ∀ Y : ℝ, 1 ≤ Y →
      |(∫ t in Ioi Y, ψ c t ^ 2) - 2 / π * arcsin (1 / Y) * ∫ t in Ioi 1, ψ c t ^ 2|
        ≤ η * (∫ t in Ioi 1, ψ c t ^ 2) / Y := by
  have hχ0 : ∀ᶠ c in atTop, 0 ≤ χ c := hsys.mono fun c h => h.1
  filter_upwards [hsys, eventually_hyps hu hχ0, (tendsto_errR hu).eventually (ge_mem_nhds hη)]
    with c ⟨_, hψ, hv, hode, hint⟩ ⟨hc, hχc0, hχc, hb, hb0, ha4, hWb, hW, hden⟩ hR Y hY
  have hT : 0 ≤ ∫ t in Ioi 1, ψ c t ^ 2 := setIntegral_nonneg measurableSet_Ioi fun t _ => sq_nonneg _
  have hY0 : 0 < Y := by linarith
  refine (relative_law hψ hv hode hint hc hχc0 hχc hb hb0 ha4 hWb hW hden hY).trans ?_
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hR hT) hY0.le

theorem summable_inv_sq : Summable (fun M : ℕ => 1 / ((M : ℝ) + 1) ^ 2) := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  simpa [Nat.cast_add, Nat.cast_one] using this

theorem hasSum_inv_sq : HasSum (fun M : ℕ => 1 / ((M : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
  have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  simpa [Nat.cast_add, Nat.cast_one] using this

theorem summable_sZero : Summable (fun M : ℕ => arcsin (1 / ((M : ℝ) + 1)) / ((M : ℝ) + 1)) := by
  refine Summable.of_nonneg_of_le (fun M => div_nonneg (arcsin_nonneg.mpr (by positivity)) (by positivity))
    (fun M => ?_)
    (summable_inv_sq.mul_left (π / 2))
  have hM : (0 : ℝ) < M + 1 := by positivity
  have h := Cvs.L2a.LeakageEnergyScaling.arcsin_le_pi_div_two_mul (y := 1 / ((M : ℝ) + 1)) (by positivity)
    (by rw [div_le_one hM]; linarith [M.cast_nonneg (α := ℝ)])
  have e : π / 2 * (1 / ((M : ℝ) + 1) ^ 2) = π / 2 * (1 / ((M : ℝ) + 1)) / ((M : ℝ) + 1) := by
    field_simp
  rw [e]
  exact div_le_div_of_nonneg_right h hM.le

/-- **The mode sum.** For real numbers `T M`, if `|T(M) − (2/π) arcsin(1/M) T₁| ≤ η T₁/M` for every `M ≥ 1` with
then `Σ_M T(M)/M` converges and is within `η (π²/6) T₁` of `(2/π) S₀ T₁`. -/
theorem modeSum_le {T : ℝ → ℝ} {T1 η : ℝ}
    (hlaw : ∀ M : ℕ, |T ((M : ℝ) + 1) - 2 / π * arcsin (1 / ((M : ℝ) + 1)) * T1| ≤ η * T1 / ((M : ℝ) + 1)) :
    Summable (fun M : ℕ => T ((M : ℝ) + 1) / ((M : ℝ) + 1)) ∧
      |∑' M : ℕ, T ((M : ℝ) + 1) / ((M : ℝ) + 1) - 2 / π * sZero * T1| ≤ η * (π ^ 2 / 6) * T1 := by
  have hdiff : ∀ M : ℕ, |T ((M : ℝ) + 1) / ((M : ℝ) + 1)
      - 2 / π * T1 * (arcsin (1 / ((M : ℝ) + 1)) / ((M : ℝ) + 1))| ≤ η * T1 * (1 / ((M : ℝ) + 1) ^ 2) := by
    intro M
    have hM : (0 : ℝ) < M + 1 := by positivity
    have e : T ((M : ℝ) + 1) / ((M : ℝ) + 1) - 2 / π * T1 * (arcsin (1 / ((M : ℝ) + 1)) / ((M : ℝ) + 1))
        = (T ((M : ℝ) + 1) - 2 / π * arcsin (1 / ((M : ℝ) + 1)) * T1) / ((M : ℝ) + 1) := by ring
    rw [e, abs_div, abs_of_pos hM]
    have e2 : η * T1 * (1 / ((M : ℝ) + 1) ^ 2) = η * T1 / ((M : ℝ) + 1) / ((M : ℝ) + 1) := by
      field_simp
    rw [e2]
    exact div_le_div_of_nonneg_right (hlaw M) hM.le
  have hs2 : Summable (fun M : ℕ => 2 / π * T1 * (arcsin (1 / ((M : ℝ) + 1)) / ((M : ℝ) + 1))) :=
    summable_sZero.mul_left _
  have hsE : Summable (fun M : ℕ => η * T1 * (1 / ((M : ℝ) + 1) ^ 2)) := summable_inv_sq.mul_left _
  have hsd : Summable (fun M : ℕ => T ((M : ℝ) + 1) / ((M : ℝ) + 1)
      - 2 / π * T1 * (arcsin (1 / ((M : ℝ) + 1)) / ((M : ℝ) + 1))) :=
    Summable.of_norm_bounded hsE (fun M => by rw [Real.norm_eq_abs]; exact hdiff M)
  have hsT : Summable (fun M : ℕ => T ((M : ℝ) + 1) / ((M : ℝ) + 1)) := by
    simpa using hsd.add hs2
  refine ⟨hsT, ?_⟩
  have e : ∑' M : ℕ, T ((M : ℝ) + 1) / ((M : ℝ) + 1) - 2 / π * sZero * T1
      = ∑' M : ℕ, (T ((M : ℝ) + 1) / ((M : ℝ) + 1)
        - 2 / π * T1 * (arcsin (1 / ((M : ℝ) + 1)) / ((M : ℝ) + 1))) := by
    rw [hsT.tsum_sub hs2, tsum_mul_left]; unfold sZero; ring
  rw [e]
  calc |∑' M : ℕ, (T ((M : ℝ) + 1) / ((M : ℝ) + 1)
        - 2 / π * T1 * (arcsin (1 / ((M : ℝ) + 1)) / ((M : ℝ) + 1)))|
      ≤ ∑' M : ℕ, η * T1 * (1 / ((M : ℝ) + 1) ^ 2) := by
        rw [← Real.norm_eq_abs]
        exact tsum_of_norm_bounded hsE.hasSum (fun M => by rw [Real.norm_eq_abs]; exact hdiff M)
    _ = η * (π ^ 2 / 6) * T1 := by rw [tsum_mul_left, hasSum_inv_sq.tsum_eq]; ring

/-! ### The rungs -/

open Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.EvenRungsByIndex in
/-- A rung's cosine transform solves the radial equation on `[1, ∞)` and is in `L²(1, ∞)`. -/
theorem rung_sys {c : ℝ} {j : ℕ} (hc : 0 < c) (h : ∃ χ, IsLevelIdx c j χ) :
    (∀ r ∈ Ici (1 : ℝ), HasDerivAt (psi c (rung c j))
        (Cvs.Prolate.SlepianCommutingRelation.kint (rung c j) (fun ξ s => -(c * s * sin (c * ξ * s))) r) r) ∧
      (∀ r ∈ Ici (1 : ℝ), HasDerivAt (Cvs.Prolate.SlepianCommutingRelation.kint (rung c j) (fun ξ s => -(c * s * sin (c * ξ * s))))
        (Cvs.Prolate.SlepianCommutingRelation.kint (rung c j) (fun ξ s => -(c ^ 2 * s ^ 2 * cos (c * ξ * s))) r) r) ∧
      (∀ r ∈ Ici (1 : ℝ), (r ^ 2 - 1) * Cvs.Prolate.SlepianCommutingRelation.kint (rung c j)
          (fun ξ s => -(c ^ 2 * s ^ 2 * cos (c * ξ * s))) r
        + 2 * r * Cvs.Prolate.SlepianCommutingRelation.kint (rung c j) (fun ξ s => -(c * s * sin (c * ξ * s))) r
        + (c ^ 2 * r ^ 2 - lev c j) * psi c (rung c j) r = 0) ∧
      IntegrableOn (fun t => psi c (rung c j) t ^ 2) (Ioi 1) := by
  obtain ⟨hg, hg₁, hg₂c, hang, -, -⟩ := rung_spec h
  obtain ⟨h1, h2, h3⟩ := psi_system hg hg₁ hg₂c hang
  exact ⟨fun r _ => h1 r, fun r _ => h2 r, fun r _ => h3 r,
    (Cvs.Prolate.RungExactOrthogonality.memLp_psi hg hg₁ hg₂c hang hc).integrable_sq⟩

open Cvs.Prolate.EvenRungsByIndex in
/-- `0 ≤ χ ≤ K c` eventually gives `χ/c² → 0`. -/
theorem tendsto_lev_div_sq {j : ℕ} {K : ℝ}
    (hlev : ∀ᶠ c : ℝ in atTop, 0 ≤ lev c j ∧ lev c j ≤ K * c) :
    Tendsto (fun c => lev c j / c ^ 2) atTop (𝓝 0) := by
  have hK : Tendsto (fun c : ℝ => K * c⁻¹) atTop (𝓝 (K * 0)) := tendsto_inv_atTop_zero.const_mul K
  rw [mul_zero] at hK
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hK ?_ ?_
  · filter_upwards [hlev] with c h
    exact div_nonneg h.1 (sq_nonneg c)
  · filter_upwards [hlev, eventually_gt_atTop 0] with c h hc
    rw [div_le_iff₀ (by positivity)]
    calc lev c j ≤ K * c := h.2
      _ = K * c⁻¹ * c ^ 2 := by field_simp

open Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.EvenRungsByIndex in
/-- **The arcsine law for the rung of index `j`**: if `0 ≤ χ_j ≤ Kc` eventually, then for all large `c` and every
`Y ≥ 1`, `|∫_Y^∞ ψ_j² − (2/c)(1 − λ_j) arcsin(1/Y)| ≤ η (π/c)(1 − λ_j)/Y`. -/
theorem arcsine_law_rung {j : ℕ} {K : ℝ}
    (hlev : ∀ᶠ c : ℝ in atTop, (∃ χ, IsLevelIdx c j χ) ∧ 0 ≤ lev c j ∧ lev c j ≤ K * c)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ c : ℝ in atTop, ∀ Y : ℝ, 1 ≤ Y →
      |(∫ t in Ioi Y, psi c (rung c j) t ^ 2) - 2 / c * (1 - lamR c j) * arcsin (1 / Y)|
        ≤ η * (π / c * (1 - lamR c j)) / Y := by
  have hu := tendsto_lev_div_sq (hlev.mono fun c h => h.2)
  have hsys : ∀ᶠ c in atTop, 0 ≤ lev c j ∧
      (∀ r ∈ Ici (1 : ℝ), HasDerivAt (psi c (rung c j))
        (Cvs.Prolate.SlepianCommutingRelation.kint (rung c j) (fun ξ s => -(c * s * sin (c * ξ * s))) r) r) ∧
      (∀ r ∈ Ici (1 : ℝ), HasDerivAt (Cvs.Prolate.SlepianCommutingRelation.kint (rung c j) (fun ξ s => -(c * s * sin (c * ξ * s))))
        (Cvs.Prolate.SlepianCommutingRelation.kint (rung c j) (fun ξ s => -(c ^ 2 * s ^ 2 * cos (c * ξ * s))) r) r) ∧
      (∀ r ∈ Ici (1 : ℝ), (r ^ 2 - 1) * Cvs.Prolate.SlepianCommutingRelation.kint (rung c j)
          (fun ξ s => -(c ^ 2 * s ^ 2 * cos (c * ξ * s))) r
        + 2 * r * Cvs.Prolate.SlepianCommutingRelation.kint (rung c j) (fun ξ s => -(c * s * sin (c * ξ * s))) r
        + (c ^ 2 * r ^ 2 - lev c j) * psi c (rung c j) r = 0) ∧
      IntegrableOn (fun t => psi c (rung c j) t ^ 2) (Ioi 1) := by
    filter_upwards [hlev, eventually_gt_atTop 0] with c h hc
    exact ⟨h.2.1, rung_sys hc h.1⟩
  filter_upwards [arcsine_law (ψ := fun c => psi c (rung c j)) hu hsys hη, hlev, eventually_gt_atTop 0]
    with c hA h hc Y hY
  obtain ⟨-, -, -, -, heven, hnorm⟩ := rung_spec h.1
  have hmass : ∫ t in Ioi 1, psi c (rung c j) t ^ 2 = π / c * (1 - lamR c j) :=
    Cvs.Prolate.AngularBesselInequality.mass_eq hc (continuousOn_rung h.1) heven (psi_rung h.1) hnorm
  have := hA Y hY
  rw [hmass] at this
  have e : 2 / π * arcsin (1 / Y) * (π / c * (1 - lamR c j)) = 2 / c * (1 - lamR c j) * arcsin (1 / Y) := by
    field_simp
  rwa [e] at this

open Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.EvenRungsByIndex in
/-- **The m-mode energy of the rung of index `j`**: `Σ_{M≥1} (1/M)∫_M^∞ ψ_j² = (2/c)(1 − λ_j) S₀ + o((1 − λ_j)/c)`. -/
theorem modeSum_law_rung {j : ℕ} {K : ℝ}
    (hlev : ∀ᶠ c : ℝ in atTop, (∃ χ, IsLevelIdx c j χ) ∧ 0 ≤ lev c j ∧ lev c j ≤ K * c)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ c : ℝ in atTop,
      |∑' M : ℕ, (∫ t in Ioi ((M : ℝ) + 1), psi c (rung c j) t ^ 2) / ((M : ℝ) + 1)
        - 2 / c * (1 - lamR c j) * sZero| ≤ η * (π / c * (1 - lamR c j)) := by
  have hπ6 : 0 < π ^ 2 / 6 := by have := pi_pos; positivity
  filter_upwards [arcsine_law_rung hlev (div_pos hη hπ6), eventually_gt_atTop 0] with c hA hc
  have hlaw : ∀ M : ℕ, |(∫ t in Ioi ((M : ℝ) + 1), psi c (rung c j) t ^ 2)
      - 2 / π * arcsin (1 / ((M : ℝ) + 1)) * (π / c * (1 - lamR c j))|
        ≤ η / (π ^ 2 / 6) * (π / c * (1 - lamR c j)) / ((M : ℝ) + 1) := by
    intro M
    have e : 2 / π * arcsin (1 / ((M : ℝ) + 1)) * (π / c * (1 - lamR c j))
        = 2 / c * (1 - lamR c j) * arcsin (1 / ((M : ℝ) + 1)) := by field_simp
    rw [e]; exact hA _ (by linarith [M.cast_nonneg (α := ℝ)])
  have h2 := (modeSum_le (T := fun Y => ∫ t in Ioi Y, psi c (rung c j) t ^ 2) hlaw).2
  have e : 2 / π * sZero * (π / c * (1 - lamR c j)) = 2 / c * (1 - lamR c j) * sZero := by field_simp
  have e2 : η / (π ^ 2 / 6) * (π ^ 2 / 6) * (π / c * (1 - lamR c j)) = η * (π / c * (1 - lamR c j)) := by
    field_simp
  rw [e, e2] at h2
  exact h2

open Cvs.Prolate.EvenRungsByIndex in
/-- `χ_j/c → κ > 0` gives `0 ≤ χ_j ≤ (κ + 1)c` eventually. -/
theorem hlev_of_tendsto {j : ℕ} {κ : ℝ} (hκ : 0 < κ) (hex : ∀ᶠ c : ℝ in atTop, ∃ χ, IsLevelIdx c j χ)
    (ht : Tendsto (fun c => lev c j / c) atTop (𝓝 κ)) :
    ∀ᶠ c : ℝ in atTop, (∃ χ, IsLevelIdx c j χ) ∧ 0 ≤ lev c j ∧ lev c j ≤ (κ + 1) * c := by
  filter_upwards [hex, eventually_gt_atTop 0, ht.eventually (lt_mem_nhds (by linarith : (0 : ℝ) < κ)),
    ht.eventually (gt_mem_nhds (by linarith : κ < κ + 1))] with c he hc h0 h1
  refine ⟨he, ?_, ?_⟩
  · have := (lt_div_iff₀ hc).mp h0; linarith
  · exact ((div_lt_iff₀ hc).mp h1).le

open Cvs.Prolate.EvenRungsByIndex in
/-- The rungs `h₀`, `h₄`, `h₈` (indices `0, 2, 4`) satisfy the level hypothesis with `K = 2, 10, 18`. -/
theorem hlev_even {j : ℕ} (hj : j = 0 ∨ j = 2 ∨ j = 4) :
    ∃ K : ℝ, ∀ᶠ c : ℝ in atTop, (∃ χ, IsLevelIdx c j χ) ∧ 0 ≤ lev c j ∧ lev c j ≤ K * c := by
  rcases hj with rfl | rfl | rfl
  · exact ⟨_, hlev_of_tendsto one_pos (Eventually.of_forall fun c => exists_isLevelIdx_zero c)
      Cvs.Prolate.Mellin.XiLawsRungEight.tendsto_lev_zero_div⟩
  · exact ⟨_, hlev_of_tendsto (by norm_num) ((eventually_ge_atTop 256).mono fun c hc =>
      (Cvs.Prolate.Mellin.XiLawsRungFour.lev_two_bounds hc).1) Cvs.Prolate.Mellin.XiLawsRungEight.tendsto_lev_two_div⟩
  · exact ⟨_, hlev_of_tendsto (by norm_num) ((eventually_ge_atTop 1024).mono fun c hc =>
      (Cvs.Prolate.Mellin.XiLawsRungEight.lev_four_bounds hc).1) Cvs.Prolate.Mellin.XiLawsRungEight.tendsto_lev_four_div⟩

open Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.EvenRungsByIndex in
/-- **The arcsine law for `h₀`, `h₄`, `h₈`**, with no hypotheses. -/
theorem arcsine_law_even {j : ℕ} (hj : j = 0 ∨ j = 2 ∨ j = 4) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ c : ℝ in atTop, ∀ Y : ℝ, 1 ≤ Y →
      |(∫ t in Ioi Y, psi c (rung c j) t ^ 2) - 2 / c * (1 - lamR c j) * arcsin (1 / Y)|
        ≤ η * (π / c * (1 - lamR c j)) / Y :=
  arcsine_law_rung (hlev_even hj).choose_spec hη

open Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.EvenRungsByIndex in
/-- **The m-mode energy of `h₀`, `h₄`, `h₈`**, with no hypotheses:
`Σ_{M≥1} (1/M)∫_M^∞ ψ_j² = (2/c)(1 − λ_j) S₀ + o((1 − λ_j)/c)`. -/
theorem modeSum_law_even {j : ℕ} (hj : j = 0 ∨ j = 2 ∨ j = 4) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ c : ℝ in atTop,
      |∑' M : ℕ, (∫ t in Ioi ((M : ℝ) + 1), psi c (rung c j) t ^ 2) / ((M : ℝ) + 1)
        - 2 / c * (1 - lamR c j) * sZero| ≤ η * (π / c * (1 - lamR c j)) :=
  modeSum_law_rung (hlev_even hj).choose_spec hη

end Cvs.Prolate.ModeEnergyArcsineLaw

end
