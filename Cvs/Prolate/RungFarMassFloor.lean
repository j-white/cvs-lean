import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullSpanIndexFloor
import Cvs.Prolate.EdgeBesselCount
import Cvs.Prolate.EvenLevelIndexLemma
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RungEdgeCorrectedEnergy
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
# The far mass of a rung: `cJ₀ ≥ F(d)` with `F(d) = ∫₀^{κ*}(1 − dκ/2 − κ²/4)²`

For a rung with `χ < c²`, `D = c² − χ`, `d = D/c`, the edge Taylor bound `Cvs.Prolate.EdgeBesselCount.abs_psi_sub_psi_one_le` gives
`|ψ(ξ)| ≥ |ψ(1)|(1 − D(ξ − 1)/2 − c²(ξ − 1)²/4)`, so `c∫₁^∞ψ² ≥ ψ(1)² F(d)`, `κ* = √(d² + 4) − d`, with
`F(d) > 0` for every `d`. Also `∫₁^∞ψ² ≥ ψ(1)²/(8(D + 2c))`, and at `c = 2πx` every rung of index `2j < 2x` has
`D ≥ 4c/log c > 0`, with `ψ(1)² ≤ 8c∫₁^∞ψ²` when `D ≤ 5c`.
-/

noncomputable section

namespace Cvs.Prolate.RungFarMassFloor

open Real Set MeasureTheory Filter Topology
open Cvs.L2a.AngularProlateTailPositive (psi psi_system)
open Cvs.Prolate.SlepianCommutingRelation (kint)
open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval (pP qP)
open Cvs.Prolate.Gram.RungGramFloorAtInfinity (rungU)

/-! ### The edge-mass function -/

/-- `F(d, k) = ∫₀^k (1 − dκ/2 − κ²/4)² dκ`. -/
def Fk (d k : ℝ) : ℝ := ∫ κ in (0 : ℝ)..k, (1 - d * κ / 2 - κ ^ 2 / 4) ^ 2

/-- The positive root `κ* = √(d² + 4) − d` of `κ² + 2dκ = 4`. -/
def kStar (d : ℝ) : ℝ := √(d ^ 2 + 4) - d

/-- The edge-mass law `F(d) = F(d, κ*(d))`. -/
def edgeF (d : ℝ) : ℝ := Fk d (kStar d)

/-- `F(d, k) = k − dk²/2 + (d²/4 − 1/2)k³/3 + dk⁴/16 + k⁵/80`. -/
theorem Fk_eq (d k : ℝ) :
    Fk d k = k - d * k ^ 2 / 2 + (d ^ 2 / 4 - 1 / 2) * k ^ 3 / 3 + d * k ^ 4 / 16 + k ^ 5 / 80 := by
  unfold Fk
  have hd : ∀ x ∈ uIcc (0 : ℝ) k, HasDerivAt
      (fun κ : ℝ => κ - d * κ ^ 2 / 2 + (d ^ 2 / 4 - 1 / 2) * κ ^ 3 / 3 + d * κ ^ 4 / 16 + κ ^ 5 / 80)
      ((1 - d * x / 2 - x ^ 2 / 4) ^ 2) x := by
    intro x _
    have h := ((((((hasDerivAt_id x).sub (((hasDerivAt_pow 2 x).const_mul d).div_const 2)).add
      (((hasDerivAt_pow 3 x).const_mul (d ^ 2 / 4 - 1 / 2)).div_const 3)).add
      (((hasDerivAt_pow 4 x).const_mul d).div_const 16)).add ((hasDerivAt_pow 5 x).div_const 80)))
    exact h.congr_deriv (by
      ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((by fun_prop : Continuous fun κ : ℝ =>
    (1 - d * κ / 2 - κ ^ 2 / 4) ^ 2).intervalIntegrable 0 k)]
  ring

/-- `κ* > 0` and `2dκ* + κ*² = 4`. -/
theorem kStar_spec (d : ℝ) : 0 < kStar d ∧ 2 * d * kStar d + kStar d ^ 2 = 4 := by
  have h4 : (0 : ℝ) ≤ d ^ 2 + 4 := by positivity
  have hs := Real.sq_sqrt h4
  have hs0 := Real.sqrt_nonneg (d ^ 2 + 4)
  have hgt : d < √(d ^ 2 + 4) := by
    rcases lt_or_ge d 0 with h | h
    · linarith
    · nlinarith
  refine ⟨by unfold kStar; linarith, ?_⟩
  unfold kStar; nlinarith

/-- `F(5, 1/3) = 317/2430`. -/
theorem Fk_five_third : Fk 5 (1 / 3) = 317 / 2430 := by
  rw [Fk_eq]; norm_num

variable {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}

/-! ### The pointwise edge floor -/

/-- **The edge floor**: `|ψ(1)|(1 − (c² − χ)(ξ − 1)/2 − c²(ξ − 1)²/4) ≤ |ψ(ξ)|` for `ξ ≥ 1`. -/
theorem abs_psi_ge (hχc : χ < c ^ 2)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    {ξ : ℝ} (hξ : 1 ≤ ξ) :
    |psi c g 1| * (1 - (c ^ 2 - χ) * (ξ - 1) / 2 - c ^ 2 * (ξ - 1) ^ 2 / 4) ≤ |psi c g ξ| := by
  have h := Cvs.Prolate.EdgeBesselCount.abs_psi_sub_psi_one_le hg hg₁ hg₂c hang hχc hξ
  have := abs_sub_abs_le_abs_sub (psi c g 1) (psi c g ξ)
  rw [abs_sub_comm (psi c g 1) (psi c g ξ)] at this
  nlinarith

/-! ### The far mass -/

/-- **The windowed edge mass**: for `c² − χ ≤ d₀c`, `0 ≤ κ` and `2d₀κ + κ² ≤ 4`,
`ψ(1)² F(d₀, κ) ≤ c ∫₁^∞ ψ²`. -/
theorem edge_mass_window (hc : 0 < c) (hχc : χ < c ^ 2)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    {d₀ κ : ℝ} (hκ : 0 ≤ κ) (hd : c ^ 2 - χ ≤ d₀ * c) (hκ2 : 2 * d₀ * κ + κ ^ 2 ≤ 4) :
    psi c g 1 ^ 2 * Fk d₀ κ ≤ c * ∫ ξ in Ioi 1, psi c g ξ ^ 2 := by
  set a := |psi c g 1| with had
  have ha0 : 0 ≤ a := abs_nonneg _
  have hD : 0 < c ^ 2 - χ := by linarith
  have hd0 : 0 ≤ d₀ := by
    by_contra h; push Not at h; nlinarith
  set f : ℝ → ℝ := fun t => 1 - d₀ * t / 2 - t ^ 2 / 4 with hf
  set r := κ / c with hr
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hsq : ∀ ξ ∈ Ioc (1 : ℝ) (1 + r), a ^ 2 * f (c * ξ - c) ^ 2 ≤ psi c g ξ ^ 2 := by
    intro ξ hξ
    set t := c * ξ - c with ht
    have ht0 : 0 ≤ t := by rw [ht]; nlinarith [hξ.1]
    have htκ : t ≤ κ := by
      have : c * ξ ≤ c * (1 + r) := mul_le_mul_of_nonneg_left hξ.2 hc.le
      rw [hr, mul_add, mul_div_cancel₀ _ hc.ne'] at this; rw [ht]; linarith
    have hfκ : 0 ≤ f t := by
      simp only [hf]; nlinarith [mul_le_mul_of_nonneg_left htκ hd0]
    have hcmp : f t ≤ 1 - (c ^ 2 - χ) * (ξ - 1) / 2 - c ^ 2 * (ξ - 1) ^ 2 / 4 := by
      have e1 : c ^ 2 * (ξ - 1) ^ 2 = t ^ 2 := by rw [ht]; ring
      have e2 : (c ^ 2 - χ) * (ξ - 1) ≤ d₀ * t := by
        have hx1 : 0 ≤ ξ - 1 := by linarith [hξ.1]
        have := mul_le_mul_of_nonneg_right hd hx1
        rw [ht]; nlinarith
      simp only [hf]; rw [e1]; linarith
    have hlow := abs_psi_ge hχc hg hg₁ hg₂c hang hξ.1.le
    have h1 : a * f t ≤ |psi c g ξ| := (mul_le_mul_of_nonneg_left hcmp ha0).trans hlow
    have h2 := pow_le_pow_left₀ (mul_nonneg ha0 hfκ) h1 2
    rw [sq_abs, mul_pow] at h2; exact h2
  have hint : IntegrableOn (fun ξ => psi c g ξ ^ 2) (Ioi 1) :=
    (Cvs.Prolate.RungExactOrthogonality.memLp_psi hg hg₁ hg₂c hang hc).integrable_sq
  have ha2 : a ^ 2 = psi c g 1 ^ 2 := by rw [had, sq_abs]
  have hcont : Continuous fun ξ : ℝ => a ^ 2 * f (c * ξ - c) ^ 2 := by simp only [hf]; fun_prop
  have hchange : ∫ ξ in (1 : ℝ)..(1 + r), a ^ 2 * f (c * ξ - c) ^ 2 = a ^ 2 * (c⁻¹ * Fk d₀ κ) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_sub (fun t => f t ^ 2) hc.ne' c, smul_eq_mul]
    have e0 : c * 1 - c = 0 := by ring
    have e1 : c * (1 + r) - c = κ := by rw [hr]; field_simp; ring
    rw [e0, e1]; rfl
  have hle : ∫ ξ in Ioc (1 : ℝ) (1 + r), a ^ 2 * f (c * ξ - c) ^ 2 ≤ ∫ ξ in Ioi 1, psi c g ξ ^ 2 :=
    (setIntegral_mono_on (hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      (hint.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc hsq).trans
      (setIntegral_mono_set hint (Eventually.of_forall fun _ => sq_nonneg _)
        (Eventually.of_forall fun _ hx => Ioc_subset_Ioi_self hx))
  rw [← intervalIntegral.integral_of_le (by linarith), hchange] at hle
  rw [← ha2]
  have := mul_le_mul_of_nonneg_left hle hc.le
  calc a ^ 2 * Fk d₀ κ = c * (a ^ 2 * (c⁻¹ * Fk d₀ κ)) := by field_simp
    _ ≤ _ := this

/-- **The edge-mass law**: `ψ(1)² F((c² − χ)/c) ≤ c ∫₁^∞ ψ²`. -/
theorem edge_mass_F (hc : 0 < c) (hχc : χ < c ^ 2)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0) :
    psi c g 1 ^ 2 * edgeF ((c ^ 2 - χ) / c) ≤ c * ∫ ξ in Ioi 1, psi c g ξ ^ 2 := by
  obtain ⟨hk0, hk⟩ := kStar_spec ((c ^ 2 - χ) / c)
  exact edge_mass_window hc hχc hg hg₁ hg₂c hang hk0.le (by rw [div_mul_cancel₀ _ hc.ne']) hk.le

/-- **The edge mass at `d ≤ 5`**: for `c² − χ ≤ 5c`, `ψ(1)² ≤ 8c ∫₁^∞ ψ²`. -/
theorem edge_mass_five (hc : 0 < c) (hχc : χ < c ^ 2)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (h5 : c ^ 2 - χ ≤ 5 * c) :
    psi c g 1 ^ 2 ≤ 8 * c * ∫ ξ in Ioi 1, psi c g ξ ^ 2 := by
  have h := edge_mass_window hc hχc hg hg₁ hg₂c hang (d₀ := 5) (κ := 1 / 3) (by norm_num) h5 (by norm_num)
  rw [Fk_five_third] at h
  nlinarith [sq_nonneg (psi c g 1)]
/-- **The edge mass**: `ψ(1)²/(8(c² − χ + 2c)) ≤ ∫₁^∞ ψ²` for `1 ≤ c` and `χ < c²`. -/
theorem edge_mass_ge (hc1 : 1 ≤ c) (hχc : χ < c ^ 2)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0) :
    psi c g 1 ^ 2 / (8 * (c ^ 2 - χ + 2 * c)) ≤ ∫ ξ in Ioi 1, psi c g ξ ^ 2 := by
  have hc : 0 < c := by linarith
  obtain ⟨hψ, -, hode⟩ := psi_system hg hg₁ hg₂c hang
  set ψ₁ := kint g (fun ξ s => -(c * s * sin (c * ξ * s))) with hψ₁
  set D := c ^ 2 - χ with hDdef
  have hD : 0 < D := by rw [hDdef]; linarith
  set a := |psi c g 1| with had
  have ha0 : 0 ≤ a := abs_nonneg _
  set ℓ := 1 / (2 * D + 4 * c) with hℓd
  have hden : 0 < 2 * D + 4 * c := by linarith
  have hℓ0 : 0 < ℓ := by rw [hℓd]; positivity
  have hℓD : D * ℓ ≤ 1 / 2 := by
    rw [hℓd, mul_one_div, div_le_iff₀ hden]; linarith
  have hℓc : 3 * c ^ 2 * ℓ ^ 2 ≤ 3 / 16 := by
    have h4 : 4 * c ≤ 2 * D + 4 * c := by linarith
    have : c * ℓ ≤ 1 / 4 := by
      rw [hℓd, mul_one_div, div_le_iff₀ hden]; linarith
    have hcl0 : 0 ≤ c * ℓ := by positivity
    nlinarith
  have hℓ1 : ℓ ≤ 1 := by
    have : c * ℓ ≤ 1 / 4 := by rw [hℓd, mul_one_div, div_le_iff₀ hden]; linarith
    nlinarith [hℓ0]
  set L := (D + 3 * c ^ 2 * ℓ) / 2 with hLd
  have hL0 : 0 ≤ L := by rw [hLd]; positivity
  have hder : ∀ x ∈ Icc (1 : ℝ) (1 + ℓ), |ψ₁ x| ≤ L * a := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with h1 | h1
    · subst h1
      have h := hode 1
      have e : ψ₁ 1 = -(D * psi c g 1) / 2 := by
        simp only [hψ₁, hDdef] at h ⊢; nlinarith [h]
      rw [e, abs_div, abs_neg, abs_mul, abs_of_pos hD, abs_two]
      rw [hLd]
      have : D * a ≤ (D + 3 * c ^ 2 * ℓ) * a :=
        mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg c, hℓ0]) ha0
      linarith
    · have hx1 : 0 < x - 1 := by linarith
      have hp : pP x = (x - 1) * (x + 1) := by unfold pP; ring
      have hpp : 0 < pP x := by rw [hp]; nlinarith
      have hb := (Cvs.Prolate.RungEdgeCorrectedEnergy.rung_edge_bounds hχc hg hg₁ hg₂c hang hx.1).2
      have hu : rungU c g x = pP x * ψ₁ x := rfl
      rw [hu, abs_mul, abs_of_pos hpp, hp] at hb
      have hq : qP c χ x ≤ D + 3 * c ^ 2 * ℓ := by
        unfold qP; rw [hDdef]
        have : x ^ 2 - 1 ≤ 3 * ℓ := by nlinarith [hx.2, hℓ1]
        nlinarith [sq_nonneg c]
      have hq0 : 0 ≤ qP c χ x := by unfold qP; nlinarith
      have h2 : (x + 1) * |ψ₁ x| ≤ qP c χ x * a := by
        have := hb; nlinarith [abs_nonneg (ψ₁ x)]
      have h3 : 2 * |ψ₁ x| ≤ (x + 1) * |ψ₁ x| := by nlinarith [abs_nonneg (ψ₁ x)]
      have h4 : qP c χ x * a ≤ (D + 3 * c ^ 2 * ℓ) * a := mul_le_mul_of_nonneg_right hq ha0
      rw [hLd]; linarith
  have hlow : ∀ ξ ∈ Icc (1 : ℝ) (1 + ℓ), a / 2 ≤ |psi c g ξ| := by
    intro ξ hξ
    have hsub : Icc (1 : ℝ) ξ ⊆ Icc 1 (1 + ℓ) := Icc_subset_Icc le_rfl hξ.2
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := psi c g) (f' := ψ₁)
      (s := Icc (1 : ℝ) ξ) (fun x _ => (hψ x).hasDerivWithinAt) (fun x hx => by
        rw [Real.norm_eq_abs]; exact hder x (hsub hx)) (convex_Icc 1 ξ) ⟨le_rfl, hξ.1⟩ ⟨hξ.1, le_rfl⟩
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ ξ - 1 by linarith [hξ.1])] at hmvt
    have hLℓ : L * ℓ ≤ 1 / 2 := by rw [hLd]; nlinarith [hℓD, hℓc]
    have hstep : L * a * (ξ - 1) ≤ a / 2 := by
      have : L * a * (ξ - 1) ≤ L * a * ℓ :=
        mul_le_mul_of_nonneg_left (by linarith [hξ.2]) (mul_nonneg hL0 ha0)
      nlinarith [hLℓ, ha0]
    have := abs_sub_abs_le_abs_sub (psi c g 1) (psi c g ξ)
    rw [abs_sub_comm (psi c g 1) (psi c g ξ)] at this
    linarith
  have hsq : ∀ ξ ∈ Ioc (1 : ℝ) (1 + ℓ), a ^ 2 / 4 ≤ psi c g ξ ^ 2 := fun ξ hξ => by
    have h := hlow ξ ⟨hξ.1.le, hξ.2⟩
    have := pow_le_pow_left₀ (by positivity) h 2
    rw [sq_abs] at this; nlinarith
  have hint : IntegrableOn (fun ξ => psi c g ξ ^ 2) (Ioi 1) :=
    (Cvs.Prolate.RungExactOrthogonality.memLp_psi hg hg₁ hg₂c hang hc).integrable_sq
  have ha2 : a ^ 2 = psi c g 1 ^ 2 := by rw [had, sq_abs]
  calc psi c g 1 ^ 2 / (8 * (c ^ 2 - χ + 2 * c)) = (a ^ 2 / 4) * ℓ := by
        rw [ha2, hℓd, ← hDdef]; field_simp; ring
    _ = ∫ ξ in Ioc (1 : ℝ) (1 + ℓ), a ^ 2 / 4 := by
        rw [setIntegral_const, Real.volume_real_Ioc_of_le (by linarith), smul_eq_mul]; ring
    _ ≤ ∫ ξ in Ioc (1 : ℝ) (1 + ℓ), psi c g ξ ^ 2 :=
        setIntegral_mono_on (integrableOn_const (by simp)) (hint.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc hsq
    _ ≤ ∫ ξ in Ioi 1, psi c g ξ ^ 2 :=
        setIntegral_mono_set hint (Eventually.of_forall fun _ => sq_nonneg _) (Eventually.of_forall fun _ hx => Ioc_subset_Ioi_self hx)

/-! ### The rungs at `c = 2πx` -/

open Cvs.Prolate.EvenRungsByIndex (lev rung)

/-- **The rung edge mass at `c = 2πx`**: for `2πx ≥ 80` and `j < x`, with `c = 2πx`, `D = c² − lev c (2j)` and
`ψ = psi c (rung c (2j))`: `4c/log c ≤ D`, `ψ(1)²/(8(D + 2c)) ≤ ∫₁^∞ψ²`, `ψ(1)² F(D/c) ≤ c∫₁^∞ψ²`, and
`ψ(1)² ≤ 8c∫₁^∞ψ²` when `D ≤ 5c`. -/
theorem rung_edge_mass {x : ℕ} (hx : 80 ≤ 2 * π * x) {j : ℕ} (hj : j < x) :
    4 * (2 * π * x) / Real.log (2 * π * x) ≤ (2 * π * x) ^ 2 - lev (2 * π * x) (2 * j) ∧
    psi (2 * π * x) (rung (2 * π * x) (2 * j)) 1 ^ 2 /
        (8 * ((2 * π * x) ^ 2 - lev (2 * π * x) (2 * j) + 2 * (2 * π * x))) ≤
      ∫ ξ in Ioi 1, psi (2 * π * x) (rung (2 * π * x) (2 * j)) ξ ^ 2 ∧
    psi (2 * π * x) (rung (2 * π * x) (2 * j)) 1 ^ 2 *
        edgeF (((2 * π * x) ^ 2 - lev (2 * π * x) (2 * j)) / (2 * π * x)) ≤
      2 * π * x * ∫ ξ in Ioi 1, psi (2 * π * x) (rung (2 * π * x) (2 * j)) ξ ^ 2 ∧
    ((2 * π * x) ^ 2 - lev (2 * π * x) (2 * j) ≤ 5 * (2 * π * x) →
      psi (2 * π * x) (rung (2 * π * x) (2 * j)) 1 ^ 2 ≤
        8 * (2 * π * x) * ∫ ξ in Ioi 1, psi (2 * π * x) (rung (2 * π * x) (2 * j)) ξ ^ 2) := by
  obtain ⟨hex, hlow⟩ := Cvs.L2a.FullSpanIndexFloor.full_index x hx hj
  have hσ := (Cvs.Prolate.EvenLevelIndexLemma.sigmaLow_pos_le hx).1
  have hχc : lev (2 * π * x) (2 * j) < (2 * π * x) ^ 2 := by linarith
  have hc : 0 < 2 * π * (x : ℝ) := by linarith
  obtain ⟨hg, hg₁, hg₂c, hang, -, -⟩ := Cvs.Prolate.EvenRungsByIndex.rung_spec hex
  exact ⟨hlow, edge_mass_ge (by linarith) hχc hg hg₁ hg₂c hang, edge_mass_F hc hχc hg hg₁ hg₂c hang,
    edge_mass_five hc hχc hg hg₁ hg₂c hang⟩

/-- **The top rung at `c = 2πx`**: for `2πx ≥ 80` and `c² − lev c (2(x − 1)) ≤ 5c`, `ψ(1)² ≤ 8c∫₁^∞ψ²`. -/
theorem top_edge_mass {x : ℕ} (hx : 80 ≤ 2 * π * x)
    (h5 : (2 * π * x) ^ 2 - lev (2 * π * x) (2 * (x - 1)) ≤ 5 * (2 * π * x)) :
    psi (2 * π * x) (rung (2 * π * x) (2 * (x - 1))) 1 ^ 2 ≤
      8 * (2 * π * x) * ∫ ξ in Ioi 1, psi (2 * π * x) (rung (2 * π * x) (2 * (x - 1))) ξ ^ 2 := by
  have hx0 : 0 < x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · subst h; simp at hx; linarith
    · exact h
  exact (rung_edge_mass hx (Nat.sub_lt hx0 one_pos)).2.2.2 h5

end Cvs.Prolate.RungFarMassFloor
