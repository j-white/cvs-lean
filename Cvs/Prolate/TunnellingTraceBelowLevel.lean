import Mathlib
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.ForbiddenZoneGrowth
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.SlepianEvenOrdering
import Cvs.Prolate.TopPlungeFloor
import Cvs.Prolate.TunnellingExponentSharpPlunge
import Cvs.Prolate.TunnellingIntegralMargin
import Cvs.Prolate.TunnellingIntegralsAgree
import Cvs.Route.Visibility.LayerFloorDeepRemainderB

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The tunnelling trace of the rungs below a level

The plunge exponent `W(T) = ∫_{√T}^1 √((u² − T)/(1 − u²)) du` is antitone in `T`, so every rung with `T_j ≤ T*`
has `1 − λ_j ≤ (33/40)e⁵c(c + 2)e^{−2cW(T*)}` at `c = 2πx`. Hence for `β < 2W(T*)` the trace
`Σ_{T_j ≤ T*} (1 − λ_j)e^{βc}` tends to `0`: polynomially many rungs against the rate `2W(T*) − β`.
-/

noncomputable section

open Real Filter Finset Set
open scoped Topology
open Cvs.ZeroCounting
open Cvs.Prolate.Gram.ProlateCellGramHalfUnit (lam levT)

namespace Cvs.Prolate.TunnellingTraceBelowLevel
open Cvs.ZeroCounting

/-- **The plunge exponent is antitone**: `W(T′) ≤ W(T)` for `T ≤ T′`. -/
theorem tunW_anti {T T' : ℝ} (h : T ≤ T') : Cvs.Prolate.TunnellingExponentSharpPlunge.tunW T' ≤ Cvs.Prolate.TunnellingExponentSharpPlunge.tunW T := by
  unfold Cvs.Prolate.TunnellingExponentSharpPlunge.tunW Cvs.Prolate.ForbiddenZoneGrowth.forbZ
  have hs : √T ≤ √T' := Real.sqrt_le_sqrt h
  have hb : √(1 - √T) ∈ Ioo (-√2) (√2) := Cvs.Prolate.ForbiddenZoneGrowth.sqrt_one_sub_mem (by linarith [Real.sqrt_nonneg T])
  have hb' : √(1 - √T') ∈ Ioo (-√2) (√2) := Cvs.Prolate.ForbiddenZoneGrowth.sqrt_one_sub_mem (by linarith [Real.sqrt_nonneg T'])
  have hbb : √(1 - √T') ≤ √(1 - √T) := Real.sqrt_le_sqrt (by linarith)
  have hI := Cvs.Prolate.ForbiddenZoneGrowth.intervalIntegrable_forbInt 1 T hb (Real.sqrt_nonneg _)
  calc (∫ r in (0 : ℝ)..√(1 - √T'), 2 * √(Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.qP 1 T' (1 - r ^ 2)) / √(2 - r ^ 2))
      ≤ ∫ r in (0 : ℝ)..√(1 - √T'), 2 * √(Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.qP 1 T (1 - r ^ 2)) / √(2 - r ^ 2) := by
        refine intervalIntegral.integral_mono_on (Real.sqrt_nonneg _)
          (Cvs.Prolate.ForbiddenZoneGrowth.intervalIntegrable_forbInt 1 T' hb' (Real.sqrt_nonneg _))
          (Cvs.Prolate.ForbiddenZoneGrowth.intervalIntegrable_forbInt 1 T hb' (Real.sqrt_nonneg _)) fun r _ => ?_
        have hq : Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.qP 1 T' (1 - r ^ 2) ≤ Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.qP 1 T (1 - r ^ 2) := by unfold Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.qP; linarith
        gcongr
    _ ≤ ∫ r in (0 : ℝ)..√(1 - √T), 2 * √(Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.qP 1 T (1 - r ^ 2)) / √(2 - r ^ 2) :=
        intervalIntegral.integral_mono_interval le_rfl (Real.sqrt_nonneg _) hbb
          (Filter.Eventually.of_forall fun r => by positivity) hI

/-- `0 ≤ T_j`. -/
theorem levT_nonneg {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Fin x) : 0 ≤ levT x j :=
  div_nonneg (Cvs.Prolate.SlepianEvenOrdering.nonneg_of_mem_evenSpec _ (Cvs.Prolate.EvenRungsByIndex.lev_spec (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.exists_level hx j)).1) (sq_nonneg _)

/-- **The tunnelling bound below a level**: at `c = 2πx ≥ 80` with `c(1 − T*) ≥ 5`, every rung with `T_j ≤ T*`
has `1 − λ_j ≤ (33/40)e⁵c(c + 2)e^{−2cW(T*)}`. -/
theorem one_sub_lam_le_tun {x : ℕ} (hx : 80 ≤ 2 * π * x) {T : ℝ} (hD : 5 ≤ 2 * π * x * (1 - T)) (j : Fin x)
    (hj : levT x j ≤ T) :
    1 - lam x j ≤ 33 / 40 * Real.exp 5 * (2 * π * x) * (2 * π * x + 2)
      * Real.exp (-(2 * (2 * π * x * Cvs.Prolate.TunnellingExponentSharpPlunge.tunW T))) := by
  set c := 2 * π * (x : ℝ)
  have hc0 : 0 < c := by linarith
  have hlev : Cvs.Prolate.EvenRungsByIndex.lev c (2 * (j : ℕ)) / c ^ 2 = levT x j := rfl
  have hle : Cvs.Prolate.EvenRungsByIndex.lev c (2 * (j : ℕ)) ≤ c ^ 2 * T := by
    have := hj; rw [← hlev, div_le_iff₀ (by positivity)] at this; linarith
  have hD' : 5 * c ≤ c ^ 2 - Cvs.Prolate.EvenRungsByIndex.lev c (2 * (j : ℕ)) := by nlinarith
  have h := Cvs.Prolate.TunnellingExponentSharpPlunge.one_sub_lamR_le_tunW hx (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.exists_level hx j) hD'
  rw [hlev] at h
  have hT0 := levT_nonneg hx j
  have hW1 : Cvs.Prolate.TunnellingExponentSharpPlunge.tunW (levT x j) ≤ 1 := by rw [← Cvs.Prolate.TunnellingIntegralsAgree.tunW_eq]; exact Cvs.Prolate.TunnellingIntegralsAgree.tunW_le_one hT0
  have hW0 := Cvs.Prolate.TunnellingExponentSharpPlunge.tunW_nonneg (levT x j)
  have hWa := tunW_anti hj
  have hK : 0 ≤ 33 / 40 * Real.exp 5 * c := by positivity
  refine h.trans ?_
  have h1 : c * Cvs.Prolate.TunnellingExponentSharpPlunge.tunW (levT x j) + 2 ≤ c + 2 := by nlinarith
  have h2 : Real.exp (-(2 * (c * Cvs.Prolate.TunnellingExponentSharpPlunge.tunW (levT x j)))) ≤ Real.exp (-(2 * (c * Cvs.Prolate.TunnellingExponentSharpPlunge.tunW T))) :=
    Real.exp_le_exp.2 (by nlinarith)
  have h3 : 0 ≤ c * Cvs.Prolate.TunnellingExponentSharpPlunge.tunW (levT x j) + 2 := by positivity
  calc 33 / 40 * Real.exp 5 * c * (c * Cvs.Prolate.TunnellingExponentSharpPlunge.tunW (levT x j) + 2) * Real.exp (-(2 * (c * Cvs.Prolate.TunnellingExponentSharpPlunge.tunW (levT x j))))
      ≤ 33 / 40 * Real.exp 5 * c * (c + 2) * Real.exp (-(2 * (c * Cvs.Prolate.TunnellingExponentSharpPlunge.tunW (levT x j)))) := by
        gcongr
    _ ≤ 33 / 40 * Real.exp 5 * c * (c + 2) * Real.exp (-(2 * (c * Cvs.Prolate.TunnellingExponentSharpPlunge.tunW T))) := by
        gcongr

/-- **The tunnelling trace below `T* < 1` vanishes**: for `β < 2W(T*)` and `ρ > 0`, eventually
`Σ_{T_j ≤ T*} (1 − λ_j)e^{βc} ≤ ρ` at `c = 2πx`. -/
theorem trace_eventually_le {T β ρ : ℝ} (hT : T < 1) (hβ : β < 2 * Cvs.Prolate.TunnellingExponentSharpPlunge.tunW T) (hρ : 0 < ρ) :
    ∀ᶠ x : ℕ in atTop,
      ∑ j ∈ univ.filter (fun j : Fin x => levT x j ≤ T), (1 - lam x j) * Real.exp (β * (2 * π * x)) ≤ ρ := by
  set K := 33 / 40 * Real.exp 5
  have hε : 0 < 2 * Cvs.Prolate.TunnellingExponentSharpPlunge.tunW T - β := by linarith
  have hlim := Cvs.Prolate.TopPlungeFloor.tendsto_pow_six_exp hε (2 * K)
  have hc : Tendsto (fun x : ℕ => 2 * π * (x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  have h5 : ∀ᶠ x : ℕ in atTop, 5 ≤ 2 * π * x * (1 - T) :=
    (hc.atTop_mul_const (by linarith : 0 < 1 - T)).eventually_ge_atTop 5
  filter_upwards [hlim.eventually (gt_mem_nhds hρ), Cvs.Route.Visibility.LayerFloorDeepRemainderB.eventually_scale, h5] with x hlt hx hD
  set c := 2 * π * (x : ℝ)
  have hc80 : 80 ≤ c := hx
  have hxc : (x : ℝ) ≤ c := by
    have : (1 : ℝ) ≤ 2 * π := by linarith [Real.pi_gt_three]
    have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
    nlinarith
  have hK : 0 ≤ K := by positivity
  set E := Real.exp (-(2 * (c * Cvs.Prolate.TunnellingExponentSharpPlunge.tunW T)))
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hterm : ∀ j ∈ univ.filter (fun j : Fin x => levT x j ≤ T),
      (1 - lam x j) * Real.exp (β * c) ≤ K * c * (c + 2) * E * Real.exp (β * c) := fun j hj =>
    mul_le_mul_of_nonneg_right (one_sub_lam_le_tun hx hD j (Finset.mem_filter.1 hj).2) (Real.exp_pos _).le
  refine (Finset.sum_le_sum hterm).trans ?_
  have hcard : ((univ.filter fun j : Fin x => levT x j ≤ T).card : ℝ) ≤ x := by
    exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
  rw [Finset.sum_const, nsmul_eq_mul]
  have hP : 0 ≤ K * c * (c + 2) * E * Real.exp (β * c) := by positivity
  have hexp : E * Real.exp (β * c) = Real.exp (-((2 * Cvs.Prolate.TunnellingExponentSharpPlunge.tunW T - β) * c)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc ((univ.filter fun j : Fin x => levT x j ≤ T).card : ℝ) * (K * c * (c + 2) * E * Real.exp (β * c))
      ≤ c * (K * c * (c + 2) * E * Real.exp (β * c)) := mul_le_mul_of_nonneg_right (hcard.trans hxc) hP
    _ = K * (c * c * (c + 2)) * Real.exp (-((2 * Cvs.Prolate.TunnellingExponentSharpPlunge.tunW T - β) * c)) := by rw [← hexp]; ring
    _ ≤ 2 * K * c ^ 6 * Real.exp (-((2 * Cvs.Prolate.TunnellingExponentSharpPlunge.tunW T - β) * c)) := by
        have hc6 : c * c * (c + 2) ≤ 2 * c ^ 6 := by
          have h1 : (1 : ℝ) ≤ c := by linarith
          have h3 : c ^ 3 ≤ c ^ 6 := pow_le_pow_right₀ h1 (by norm_num)
          nlinarith
        have := (Real.exp_pos (-((2 * Cvs.Prolate.TunnellingExponentSharpPlunge.tunW T - β) * c))).le
        nlinarith [mul_le_mul_of_nonneg_left hc6 hK]
    _ ≤ ρ := hlt.le

/-- **The plunge exponent at `½`**: `W(½) > ¼`, since `√(sin²φ − ½) ≥ ½` on `[π/3, π/2]`. -/
theorem quarter_lt_tunW_half : 1 / 4 < Cvs.Prolate.TunnellingExponentSharpPlunge.tunW (1 / 2) := by
  rw [← Cvs.Prolate.TunnellingIntegralsAgree.tunW_eq]
  unfold Cvs.Prolate.TunnellingIntegralMargin.tunW
  have hpi := Real.pi_gt_three
  have hs3 : √3 / 2 = sin (π / 3) := Real.sin_pi_div_three.symm
  have ha : arcsin √(1 / 2) ≤ π / 3 := by
    rw [Real.arcsin_le_iff_le_sin ⟨by linarith [Real.sqrt_nonneg (1 / 2 : ℝ)],
      Real.sqrt_le_one.2 (by norm_num)⟩ ⟨by linarith, by linarith⟩, ← hs3]
    rw [show √3 / 2 = √(3 / 4) by
      rw [show (3 / 4 : ℝ) = 3 / 2 ^ 2 by norm_num, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2 ^ 2),
        Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have ha0 : 0 ≤ arcsin √(1 / 2) := arcsin_nonneg.2 (Real.sqrt_nonneg _)
  have hnn : ∀ φ, 0 ≤ Cvs.Prolate.TunnellingIntegralMargin.tunF (1 / 2) φ := fun φ => Real.sqrt_nonneg _
  have h1 : (∫ φ in π / 3..π / 2, Cvs.Prolate.TunnellingIntegralMargin.tunF (1 / 2) φ) ≤ ∫ φ in arcsin √(1 / 2)..π / 2, Cvs.Prolate.TunnellingIntegralMargin.tunF (1 / 2) φ :=
    intervalIntegral.integral_mono_interval ha (by linarith) le_rfl (Filter.Eventually.of_forall hnn)
      ((Cvs.Prolate.TunnellingIntegralMargin.continuous_tunF _).intervalIntegrable _ _)
  have h2 : (∫ φ in π / 3..π / 2, (1 / 2 : ℝ)) ≤ ∫ φ in π / 3..π / 2, Cvs.Prolate.TunnellingIntegralMargin.tunF (1 / 2) φ := by
    refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
      ((Cvs.Prolate.TunnellingIntegralMargin.continuous_tunF _).intervalIntegrable _ _) fun φ hφ => ?_
    have hsφ : sin (π / 3) ≤ sin φ :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hφ.2 hφ.1
    have hs0 : 0 ≤ sin (π / 3) := by rw [← hs3]; positivity
    have hsq : 3 / 4 ≤ sin φ ^ 2 := by
      have : sin (π / 3) ^ 2 = 3 / 4 := by rw [← hs3, div_pow, Real.sq_sqrt (by norm_num)]; norm_num
      nlinarith
    unfold Cvs.Prolate.TunnellingIntegralMargin.tunF
    rw [show (1 / 2 : ℝ) = √((1 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  rw [intervalIntegral.integral_const, smul_eq_mul] at h2
  nlinarith

end Cvs.Prolate.TunnellingTraceBelowLevel

end
