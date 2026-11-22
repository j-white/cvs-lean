import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.FullSpanIndexFloor
import Cvs.L2a.WindowChainInputsProlate
import Cvs.Prolate.Envelope.RungExteriorLaw
import Cvs.Prolate.Envelope.RungProfileEdgePlunge
import Cvs.Prolate.EvenLevelIndexLemma
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Mellin.RungTransformUnitCircle
import Cvs.Prolate.Mellin.RungUnitCircleLaw
import Cvs.Prolate.Mellin.RungWindowLawCircleEdge
import Cvs.Prolate.RungWindowProfileCells
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.Visibility.ExtPairingRatesSubpoly
import Cvs.Route.Visibility.ExteriorFactorMTwo
import Cvs.Route.Visibility.WindowLaplaceUPairing
import Cvs.Route.Visibility.WindowLogEnergyCellFloor
import Cvs.Upstream.DirichletWeightedMeanValue
import Cvs.Upstream.LogTailFromDecay

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The per-rung window law from the right-edge law alone

`RungWindowLawCircleEdge`'s fixed-scale window bound holds with any edge quantity `G` in place of `G_j(1)`. With
`E_j = |h_{4j}(1)| + |α_j||h₀(1)|`, the unit-circle bound of Cvs.Prolate.Mellin.RungUnitCircleLaw holds unconditionally, `EdgeLaw` implies the same
bound for `B` since `|G_j(1)| ≤ E_j`, and `E_j² ≤ 2h_{4j}(1)² + 2α_j²h₀(1)² ≤ P(x)x(1 − λ_{4j})^{3/4}` (Cvs.Prolate.Envelope.RungProfileEdgePlunge).
-/

noncomputable section

open Real Set MeasureTheory Filter Complex
open Cvs.Route.L1FloorFromBulkD0 (rung)
open Cvs.Route.Visibility.WindowLaplaceUPairing (winLaplace)
open Cvs.Prolate.EvenRungsByIndex (lamR)
open Cvs.Route.Visibility.ExtPairingRatesSubpoly (SubPoly)
open Cvs.Prolate.RungWindowProfileCells (Gr tn Ff)
open Cvs.Prolate.Mellin.RungTransformUnitCircle (Aw Bw Jw)
open Cvs.Upstream.DirichletWeightedMeanValue (expSum)
open Cvs.Prolate.Mellin.RungWindowLawCircleEdge (bco Jw_eq sum_bco_sq_le norm_exp_half winLaplace_eq_conj arith_sq edge_term_sq_le norm_winLaplace_neg log_div_le_rpow subPoly_max winQ fixed_rhs_eq)

namespace Cvs.Prolate.Mellin.RungWindowLawRightEdge
open Cvs.ZeroCounting

/-- **The one-sided transform beyond `8πx`**: from the two laws at `(σ, g)`,
`g‖F_f(σ + ig)‖ ≤ C₁|G|‖J(σ + ig)‖ + e^{σL/2} C₂|G|/√x`. -/
theorem g_norm_Ff_le {x : ℕ} (hx : 80 ≤ 2 * π * x) {j : ℕ} (hj : j < x) (σ : ℝ) {G g C₁ C₂ : ℝ} (hg : 0 < g)
    (hA : g * ‖Aw x j (σ + g * I)‖ ≤ C₁ * |G|) (hB : g * ‖Bw x j (σ + g * I)‖ ≤ C₂ * |G| / √(x : ℝ)) :
    g * ‖Ff x j (σ + g * I)‖
      ≤ C₁ * |G| * ‖Jw x (σ + g * I)‖ + Real.exp (σ * (Real.log x / 2)) * (C₂ * |G| / √(x : ℝ)) := by
  have hwi : 0 < ((σ : ℂ) + g * I).im := by simp [hg]
  rw [Cvs.Prolate.Mellin.RungTransformUnitCircle.Ff_eq hx hj hwi]
  have h1 : ‖I * Aw x j (σ + g * I) * Jw x (σ + g * I)
      - I * Complex.exp (((σ : ℂ) + g * I) * (Real.log x / 2 : ℝ)) * Bw x j (σ + g * I)‖
      ≤ ‖Aw x j (σ + g * I)‖ * ‖Jw x (σ + g * I)‖ + Real.exp (σ * (Real.log x / 2)) * ‖Bw x j (σ + g * I)‖ := by
    refine (norm_sub_le _ _).trans (le_of_eq ?_)
    rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul, norm_exp_half]
  have hE : 0 ≤ Real.exp (σ * (Real.log x / 2)) := (Real.exp_pos _).le
  calc g * ‖I * Aw x j (σ + g * I) * Jw x (σ + g * I)
        - I * Complex.exp (((σ : ℂ) + g * I) * (Real.log x / 2 : ℝ)) * Bw x j (σ + g * I)‖
      ≤ g * (‖Aw x j (σ + g * I)‖ * ‖Jw x (σ + g * I)‖ + Real.exp (σ * (Real.log x / 2)) * ‖Bw x j (σ + g * I)‖) :=
        mul_le_mul_of_nonneg_left h1 hg.le
    _ = (g * ‖Aw x j (σ + g * I)‖) * ‖Jw x (σ + g * I)‖
          + Real.exp (σ * (Real.log x / 2)) * (g * ‖Bw x j (σ + g * I)‖) := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hA (norm_nonneg _)) (mul_le_mul_of_nonneg_left hB hE)

/-- **The pointwise bound beyond `8πx`**: with the laws at `(±σ, g)`, `g²‖F_{r_j}(σ + ig)‖² ≤
C₁²G²(‖J(σ + ig)‖² + ‖J(−σ + ig)‖²) + 2x^{|σ|}C₂²G²/x`. -/
theorem g_sq_norm_sq_le {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Cvs.Approximant.SpineSubspace.SF x) (σ : ℝ) {G g C₁ C₂ : ℝ} (hg : 0 < g)
    (hA₁ : g * ‖Aw x j (σ + g * I)‖ ≤ C₁ * |G|) (hB₁ : g * ‖Bw x j (σ + g * I)‖ ≤ C₂ * |G| / √(x : ℝ))
    (hA₂ : g * ‖Aw x j (((-σ : ℝ) : ℂ) + g * I)‖ ≤ C₁ * |G|)
    (hB₂ : g * ‖Bw x j (((-σ : ℝ) : ℂ) + g * I)‖ ≤ C₂ * |G| / √(x : ℝ)) :
    g ^ 2 * ‖winLaplace (rung x j) (σ + g * I)‖ ^ 2
      ≤ C₁ ^ 2 * G ^ 2 * (‖Jw x (σ + g * I)‖ ^ 2 + ‖Jw x (((-σ : ℝ) : ℂ) + g * I)‖ ^ 2)
        + 2 * (x : ℝ) ^ |σ| * C₂ ^ 2 * G ^ 2 / x := by
  have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have hj : (j : ℕ) < x := Cvs.Approximant.SpineSubspace.SF_lt x j j.2
  have h1 := g_norm_Ff_le hx hj σ hg hA₁ hB₁
  have h2 := g_norm_Ff_le hx hj (-σ) hg hA₂ hB₂
  have hF : ‖(Ff x j (σ + g * I) + (starRingEnd ℂ) (Ff x j (((-σ : ℝ) : ℂ) + g * I))) / 2‖
      ≤ (‖Ff x j (σ + g * I)‖ + ‖Ff x j (((-σ : ℝ) : ℂ) + g * I)‖) / 2 := by
    rw [norm_div, Complex.norm_ofNat]
    gcongr
    exact (norm_add_le _ _).trans (le_of_eq (by rw [Complex.norm_conj]))
  have key := arith_sq hg.le (norm_nonneg _) hF (norm_nonneg _) (norm_nonneg _) h1 h2
  rw [winLaplace_eq_conj hx j]
  refine key.trans ?_
  have hv1 := edge_term_sq_le hx0 (s := σ) rfl C₂ (G)
  have hv2 := edge_term_sq_le hx0 (s := -σ) (abs_neg σ) C₂ (G)
  have hu : ∀ z : ℂ, (C₁ * |G| * ‖Jw x z‖) ^ 2 = C₁ ^ 2 * G ^ 2 * ‖Jw x z‖ ^ 2 := fun z => by
    rw [mul_pow, mul_pow, sq_abs]
  rw [hu, hu]
  have e : C₁ ^ 2 * G ^ 2 * (‖Jw x (σ + g * I)‖ ^ 2 + ‖Jw x (((-σ : ℝ) : ℂ) + g * I)‖ ^ 2)
      + 2 * (x : ℝ) ^ |σ| * C₂ ^ 2 * G ^ 2 / x
      = C₁ ^ 2 * G ^ 2 * ‖Jw x (σ + g * I)‖ ^ 2 + C₁ ^ 2 * G ^ 2 * ‖Jw x (((-σ : ℝ) : ℂ) + g * I)‖ ^ 2
        + (x : ℝ) ^ |σ| * C₂ ^ 2 * G ^ 2 / x + (x : ℝ) ^ |σ| * C₂ ^ 2 * G ^ 2 / x := by ring
  rw [e]
  linarith

/-- **The window log tail at a fixed scale**: the two laws at `±σ` beyond `T = 8πx` with constants `C₁, C₂ ≥ 0`
give an integrable log tail with `winTail ≤ 4T^{−1/2}(C₁²G²·2S(4T^{−1/2} + 2MT^{−3/2}) + K₂·2T^{−1/2})`,
`S = x^{|σ|}(1 + log x)/x`, `M = 4x(1 + log x)`, `K₂ = 2x^{|σ|}C₂²G²/x`, `G` any real. -/
theorem winTail_le_fixed {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Cvs.Approximant.SpineSubspace.SF x) (σ : ℝ) {G C₁ C₂ : ℝ}
    (hA₁ : ∀ g : ℝ, 8 * π * x ≤ g → g * ‖Aw x j (σ + g * I)‖ ≤ C₁ * |G|)
    (hB₁ : ∀ g : ℝ, 8 * π * x ≤ g → g * ‖Bw x j (σ + g * I)‖ ≤ C₂ * |G| / √(x : ℝ))
    (hA₂ : ∀ g : ℝ, 8 * π * x ≤ g → g * ‖Aw x j (((-σ : ℝ) : ℂ) + g * I)‖ ≤ C₁ * |G|)
    (hB₂ : ∀ g : ℝ, 8 * π * x ≤ g → g * ‖Bw x j (((-σ : ℝ) : ℂ) + g * I)‖ ≤ C₂ * |G| / √(x : ℝ)) :
    (Integrable fun g : ℝ => ‖winLaplace (rung x j) (σ + g * I)‖ ^ 2 * max (Real.log (|g| / (8 * π * x))) 0)
      ∧ Cvs.Route.Visibility.WindowLogEnergyCellFloor.winTail (rung x j) σ (8 * π * x)
        ≤ 4 * (8 * π * x) ^ (-(1 / 2) : ℝ) * (C₁ ^ 2 * G ^ 2 * (2 * ((x : ℝ) ^ |σ| * (1 + Real.log x) / x)
            * (4 * (8 * π * x) ^ (-(1 / 2) : ℝ) + 2 * (4 * x * (1 + Real.log x)) * (8 * π * x) ^ (-(3 / 2) : ℝ)))
          + 2 * (x : ℝ) ^ |σ| * C₂ ^ 2 * G ^ 2 / x * (2 * (8 * π * x) ^ (-(1 / 2) : ℝ))) := by
  have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have hxn : 0 < x := by exact_mod_cast hx0
  set T := 8 * π * (x : ℝ) with hTdef
  have hT : 0 < T := by positivity
  set K₂ := 2 * (x : ℝ) ^ |σ| * C₂ ^ 2 * G ^ 2 / x with hK₂
  set F : ℝ → ℂ := fun g => winLaplace (rung x j) (σ + g * I) with hFdef
  set Jp : ℝ → ℂ := expSum x (bco x σ) (Real.log x / 2) with hJp
  set Jm : ℝ → ℂ := expSum x (bco x (-σ)) (Real.log x / 2) with hJm
  -- the pointwise bound beyond `T`
  have hpt : ∀ g : ℝ, T ≤ g → g ^ 2 * ‖F g‖ ^ 2 ≤ C₁ ^ 2 * G ^ 2 * (‖Jp g‖ ^ 2 + ‖Jm g‖ ^ 2) + K₂ := fun g hg => by
    have h := g_sq_norm_sq_le hx j σ (hT.trans_le hg) (hA₁ g hg) (hB₁ g hg) (hA₂ g hg) (hB₂ g hg)
    rw [Jw_eq, Jw_eq] at h
    exact h
  -- the modulus is even
  have hev : ∀ g : ℝ, ‖F g‖ = ‖F |g|‖ := fun g => by
    rcases le_total 0 g with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h]
      have := norm_winLaplace_neg (rung x j) σ (-g)
      simp only [neg_neg] at this
      simpa [hFdef] using this
  -- integrability from the crude bound
  set Bp := ∑ n ∈ Finset.Icc 1 x, |bco x σ n|
  set Bm := ∑ n ∈ Finset.Icc 1 x, |bco x (-σ) n|
  have hcrude : ∀ g : ℝ, T ≤ |g| → ‖F g‖ ^ 2 * g ^ 2 ≤ C₁ ^ 2 * G ^ 2 * (Bp ^ 2 + Bm ^ 2) + K₂ := fun g hg => by
    rw [hev g, ← sq_abs g, mul_comm]
    refine (hpt |g| hg).trans ?_
    have h1 : ‖Jp |g|‖ ^ 2 ≤ Bp ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (Cvs.Upstream.DirichletWeightedMeanValue.norm_expSum_le _ _ _ _) 2
    have h2 : ‖Jm |g|‖ ^ 2 ≤ Bm ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (Cvs.Upstream.DirichletWeightedMeanValue.norm_expSum_le _ _ _ _) 2
    have : 0 ≤ C₁ ^ 2 * G ^ 2 := by positivity
    nlinarith
  obtain ⟨hI, -⟩ := Cvs.Upstream.LogTailFromDecay.logTail_le_of_decay (Cvs.Route.Visibility.WindowLogEnergyCellFloor.continuous_winLaplace_line (rung x j) σ) hT hcrude
  refine ⟨hI, ?_⟩
  -- the even integral
  set φ : ℝ → ℝ := fun y => ‖F y‖ ^ 2 * max (Real.log (y / T)) 0 with hφ
  have hh : (fun g : ℝ => ‖F g‖ ^ 2 * max (Real.log (|g| / T)) 0) = fun g => φ |g| := by
    funext g; simp only [hφ]; rw [hev g]
  have hwt : Cvs.Route.Visibility.WindowLogEnergyCellFloor.winTail (rung x j) σ T = 2 * ∫ y in Ioi (0 : ℝ), φ y := by
    rw [Cvs.Route.Visibility.WindowLogEnergyCellFloor.winTail]
    change ∫ g : ℝ, ‖F g‖ ^ 2 * max (Real.log (|g| / T)) 0 = _
    rw [hh, integral_comp_abs (f := φ)]
  -- the majorant on `(T, ∞)`
  set Ψ : ℝ → ℝ := fun y => 2 * T ^ (-(1 / 2) : ℝ) * (C₁ ^ 2 * G ^ 2) * (‖Jp y‖ ^ 2 * y ^ (-(3 / 2) : ℝ))
    + 2 * T ^ (-(1 / 2) : ℝ) * (C₁ ^ 2 * G ^ 2) * (‖Jm y‖ ^ 2 * y ^ (-(3 / 2) : ℝ))
    + 2 * T ^ (-(1 / 2) : ℝ) * K₂ * y ^ (-(3 / 2) : ℝ) with hΨ
  have hT12 : 0 ≤ T ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hT.le _
  have hK0 : 0 ≤ K₂ := by rw [hK₂]; positivity
  have hle : ∀ y ∈ Ioi (0 : ℝ), φ y ≤ (Ioi T).indicator Ψ y := fun y hy => by
    by_cases hyT : T < y
    · rw [indicator_of_mem (mem_Ioi.2 hyT)]
      have hy0 : 0 < y := hT.trans hyT
      have hlog : 0 ≤ Real.log (y / T) := Real.log_nonneg (by rw [le_div_iff₀ hT]; linarith)
      simp only [hφ, max_eq_left hlog]
      have hl := log_div_le_rpow hT hyT.le
      have hp := hpt y hyT.le
      have hr : 0 ≤ y ^ (-(3 / 2) : ℝ) := Real.rpow_nonneg hy0.le _
      calc ‖F y‖ ^ 2 * Real.log (y / T) ≤ ‖F y‖ ^ 2 * (2 * T ^ (-(1 / 2) : ℝ) * y ^ (-(3 / 2) : ℝ) * y ^ 2) :=
            mul_le_mul_of_nonneg_left hl (sq_nonneg _)
        _ = (y ^ 2 * ‖F y‖ ^ 2) * (2 * T ^ (-(1 / 2) : ℝ) * y ^ (-(3 / 2) : ℝ)) := by ring
        _ ≤ (C₁ ^ 2 * G ^ 2 * (‖Jp y‖ ^ 2 + ‖Jm y‖ ^ 2) + K₂) * (2 * T ^ (-(1 / 2) : ℝ) * y ^ (-(3 / 2) : ℝ)) :=
            mul_le_mul_of_nonneg_right hp (by positivity)
        _ = Ψ y := by simp only [hΨ]; ring
    · rw [indicator_of_notMem (fun h => hyT (mem_Ioi.1 h))]
      have hy0 : 0 < y := hy
      have hle1 : y / T ≤ 1 := by rw [div_le_one hT]; linarith
      simp only [hφ, max_eq_right (Real.log_nonpos (by positivity) hle1), mul_zero, le_refl]
  -- integrability on the half line
  have hIφ : IntegrableOn φ (Ioi 0) := by
    have := hI.integrableOn (s := Ioi (0 : ℝ))
    refine this.congr_fun (fun y hy => ?_) measurableSet_Ioi
    simp only [hφ]; rw [hev y, abs_of_pos (mem_Ioi.1 hy)]
  have hJp := Cvs.Upstream.DirichletWeightedMeanValue.integrableOn_expSum (x := x) (bco x σ) (Real.log x / 2) hT
  have hJm := Cvs.Upstream.DirichletWeightedMeanValue.integrableOn_expSum (x := x) (bco x (-σ)) (Real.log x / 2) hT
  have hR := integrableOn_Ioi_rpow_of_lt (by norm_num : (-(3 / 2) : ℝ) < -1) hT
  have hIΨ : IntegrableOn Ψ (Ioi T) :=
    ((hJp.const_mul _).add (hJm.const_mul _)).add (hR.const_mul _)
  have hIind : IntegrableOn ((Ioi T).indicator Ψ) (Ioi 0) :=
    ((integrable_indicator_iff measurableSet_Ioi).2 hIΨ).integrableOn
  have hsub : Ioi T ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi hT.le
  have hφle : ∫ y in Ioi (0 : ℝ), φ y ≤ ∫ y in Ioi T, Ψ y := by
    refine (setIntegral_mono_on hIφ hIind measurableSet_Ioi hle).trans (le_of_eq ?_)
    rw [setIntegral_indicator measurableSet_Ioi, inter_eq_right.2 hsub]
  -- evaluate the majorant
  have hΨeq : ∫ y in Ioi T, Ψ y = 2 * T ^ (-(1 / 2) : ℝ) * (C₁ ^ 2 * G ^ 2)
        * ((∫ y in Ioi T, ‖Jp y‖ ^ 2 * y ^ (-(3 / 2) : ℝ)) + ∫ y in Ioi T, ‖Jm y‖ ^ 2 * y ^ (-(3 / 2) : ℝ))
      + 2 * T ^ (-(1 / 2) : ℝ) * K₂ * (2 * T ^ (-(1 / 2) : ℝ)) := by
    have i1 : IntegrableOn (fun y : ℝ => 2 * T ^ (-(1 / 2) : ℝ) * (C₁ ^ 2 * G ^ 2) * (‖Jp y‖ ^ 2
        * y ^ (-(3 / 2) : ℝ))) (Ioi T) := hJp.const_mul _
    have i2 : IntegrableOn (fun y : ℝ => 2 * T ^ (-(1 / 2) : ℝ) * (C₁ ^ 2 * G ^ 2) * (‖Jm y‖ ^ 2
        * y ^ (-(3 / 2) : ℝ))) (Ioi T) := hJm.const_mul _
    have i3 : IntegrableOn (fun y : ℝ => 2 * T ^ (-(1 / 2) : ℝ) * K₂ * y ^ (-(3 / 2) : ℝ)) (Ioi T) :=
      hR.const_mul _
    have i12 : IntegrableOn (fun y : ℝ => 2 * T ^ (-(1 / 2) : ℝ) * (C₁ ^ 2 * G ^ 2) * (‖Jp y‖ ^ 2
        * y ^ (-(3 / 2) : ℝ)) + 2 * T ^ (-(1 / 2) : ℝ) * (C₁ ^ 2 * G ^ 2) * (‖Jm y‖ ^ 2
        * y ^ (-(3 / 2) : ℝ))) (Ioi T) := i1.add i2
    simp only [hΨ]
    rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hT]
    have : -T ^ (-(3 / 2) + 1 : ℝ) / (-(3 / 2) + 1) = 2 * T ^ (-(1 / 2) : ℝ) := by norm_num; ring
    rw [this]; ring
  have hIp := Cvs.Upstream.DirichletWeightedMeanValue.integral_expSum_le (x := x) (bco x σ) (Real.log x / 2) hT
  have hIm := Cvs.Upstream.DirichletWeightedMeanValue.integral_expSum_le (x := x) (bco x (-σ)) (Real.log x / 2) hT
  have hSp := sum_bco_sq_le hxn σ
  have hSm := sum_bco_sq_le hxn (-σ)
  rw [abs_neg] at hSm
  set Sb := (x : ℝ) ^ |σ| * (1 + Real.log x) / x
  set W := 4 * T ^ (-(1 / 2) : ℝ) + 2 * (4 * x * (1 + Real.log x)) * T ^ (-(3 / 2) : ℝ)
  have hW : 0 ≤ W := by
    have := Real.log_natCast_nonneg x
    have : 0 ≤ T ^ (-(3 / 2) : ℝ) := Real.rpow_nonneg hT.le _
    positivity
  have hIp' : ∫ y in Ioi T, ‖Jp y‖ ^ 2 * y ^ (-(3 / 2) : ℝ) ≤ Sb * W := hIp.trans (mul_le_mul_of_nonneg_right hSp hW)
  have hIm' : ∫ y in Ioi T, ‖Jm y‖ ^ 2 * y ^ (-(3 / 2) : ℝ) ≤ Sb * W := hIm.trans (mul_le_mul_of_nonneg_right hSm hW)
  rw [hwt]
  have hc : 0 ≤ 2 * T ^ (-(1 / 2) : ℝ) * (C₁ ^ 2 * G ^ 2) := by positivity
  calc 2 * ∫ y in Ioi (0 : ℝ), φ y ≤ 2 * ∫ y in Ioi T, Ψ y := by linarith
    _ = 2 * (2 * T ^ (-(1 / 2) : ℝ) * (C₁ ^ 2 * G ^ 2)
          * ((∫ y in Ioi T, ‖Jp y‖ ^ 2 * y ^ (-(3 / 2) : ℝ)) + ∫ y in Ioi T, ‖Jm y‖ ^ 2 * y ^ (-(3 / 2) : ℝ))
        + 2 * T ^ (-(1 / 2) : ℝ) * K₂ * (2 * T ^ (-(1 / 2) : ℝ))) := by rw [hΨeq]
    _ ≤ 2 * (2 * T ^ (-(1 / 2) : ℝ) * (C₁ ^ 2 * G ^ 2) * (Sb * W + Sb * W)
        + 2 * T ^ (-(1 / 2) : ℝ) * K₂ * (2 * T ^ (-(1 / 2) : ℝ))) := by
        gcongr
    _ = _ := by ring

/-- The edge quantity `E_j = |h_{4j}(1)| + |α_j||h₀(1)|` at `c = 2πx`. -/
def edgeE (x j : ℕ) : ℝ :=
  |Cvs.Prolate.EvenRungsByIndex.rung (2 * π * x) (2 * j) 1|
    + |Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j| * |Cvs.Prolate.EvenRungsByIndex.rung (2 * π * x) 0 1|

theorem edgeE_nonneg (x j : ℕ) : 0 ≤ edgeE x j := by unfold edgeE; positivity

/-- **The edge value of the two rungs**: eventually, for `j < x`, `E_j² ≤ P(x)·x·(1 − λ_{4j})^{3/4}`. -/
theorem edgeE_sq_le : ∀ᶠ x : ℕ in atTop, ∀ j : ℕ, j < x →
    edgeE x j ^ 2 ≤ Cvs.Prolate.Envelope.RungProfileEdgePlunge.edgeP x * x * (1 - lamR (2 * π * x) (2 * j)) ^ (3 / 4 : ℝ) := by
  filter_upwards [Cvs.Route.Visibility.ExteriorFactorMTwo.eventually_scale] with x hx j hj
  set c := 2 * π * (x : ℝ) with hcdef
  have hc0 : 0 < c := by linarith
  have h1 := (Cvs.L2a.FullSpanIndexFloor.full_index x hx hj)
  have hl := Cvs.L2a.WindowChainInputsProlate.half_le_lamR hx hj
  have hsl := Cvs.L2a.FullSpanIndexFloor.sigmaLow_pos (by linarith : 1 < c)
  have hχc : Cvs.Prolate.EvenRungsByIndex.lev c (2 * j) < c ^ 2 := by linarith [h1.2]
  have hr := Cvs.Prolate.Envelope.RungProfileEdgePlunge.rung_one_sq_le (by linarith) h1.1 hχc hl
  have hg := Cvs.Prolate.Envelope.RungProfileEdgePlunge.alpha_sq_ground_le hx hj
  have hω : 0 ≤ (1 - lamR c (2 * j)) ^ (3 / 4 : ℝ) :=
    Real.rpow_nonneg (by linarith [Cvs.Prolate.Envelope.RungExteriorLaw.lamR_le_one hc0 h1.1]) _
  have hE : edgeE x j ^ 2 ≤ 2 * Cvs.Prolate.EvenRungsByIndex.rung c (2 * j) 1 ^ 2
      + 2 * (Cvs.Approximant.DeepIndexSpineSpan.alpha c j ^ 2 * Cvs.Prolate.EvenRungsByIndex.rung c 0 1 ^ 2) := by
    unfold edgeE
    rw [← hcdef]
    have ha := sq_abs (Cvs.Prolate.EvenRungsByIndex.rung c (2 * j) 1)
    have hb := sq_abs (Cvs.Approximant.DeepIndexSpineSpan.alpha c j)
    have hc := sq_abs (Cvs.Prolate.EvenRungsByIndex.rung c 0 1)
    nlinarith [sq_nonneg (|Cvs.Prolate.EvenRungsByIndex.rung c (2 * j) 1|
      - |Cvs.Approximant.DeepIndexSpineSpan.alpha c j| * |Cvs.Prolate.EvenRungsByIndex.rung c 0 1|)]
  refine hE.trans ?_
  unfold Cvs.Prolate.Envelope.RungProfileEdgePlunge.edgeP
  rw [← hcdef]
  calc 2 * Cvs.Prolate.EvenRungsByIndex.rung c (2 * j) 1 ^ 2
        + 2 * (Cvs.Approximant.DeepIndexSpineSpan.alpha c j ^ 2 * Cvs.Prolate.EvenRungsByIndex.rung c 0 1 ^ 2)
      ≤ 2 * (144 / 49 * (c * Cvs.Prolate.Envelope.RungProfileEdgePlunge.depthQ c) * (1 - lamR c (2 * j)) ^ (3 / 4 : ℝ))
        + 2 * (64 * Cvs.Prolate.Envelope.RungProfileEdgePlunge.K₁ * c * (120 / π) ^ 5 * (1 - lamR c (2 * j)) ^ (3 / 4 : ℝ)) := by
        gcongr
    _ = _ := by rw [hcdef]; ring

/-- **The right-edge law with the two edge values**: some subpolynomial `C` has, at all large `x`, for every rung,
`|σ| ≤ 1` and `g ≥ 8πx`, `g‖B(σ + ig)‖ ≤ C(x)E_j/√x`. -/
def EdgeLawSum : Prop :=
  ∃ C : ℕ → ℝ, SubPoly C ∧ ∀ᶠ x : ℕ in atTop, ∀ j : Cvs.Approximant.SpineSubspace.SF x, ∀ σ : ℝ, |σ| ≤ 1 → ∀ g : ℝ, 8 * π * x ≤ g →
    g * ‖Bw x j (σ + g * I)‖ ≤ C x * edgeE x j / √(x : ℝ)

/-- **The per-rung window log-tail law from the right-edge law with the two edge values**: `EdgeLawSum` gives
`WinTailProfile (1/4)`; the unit-circle input is `RungUnitCircleLaw`'s unconditional bound with `E_j` in place of `|G_j(1)|`. -/
theorem winTailProfile_of_edgeLawSum (hB : EdgeLawSum) : Cvs.Route.Visibility.WindowLogEnergyCellFloor.WinTailProfile (1 / 4) := by
  obtain ⟨CB, hCB, hB⟩ := hB
  set C₁ : ℕ → ℝ := fun _ => 4 * Real.exp 6 with hC₁
  set C₂ : ℕ → ℝ := fun x => max (CB x) 0 with hC₂
  have hC₁s : SubPoly C₁ := Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const _
  have hC₂s : SubPoly C₂ := subPoly_max hCB
  refine ⟨fun x => Cvs.Prolate.Envelope.RungProfileEdgePlunge.edgeP x * winQ (C₁ x) (C₂ x) (Real.log x), ?_, ?_⟩
  · -- the factor is subpolynomial
    have hL : SubPoly fun x : ℕ => 1 + Real.log x := (Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const 1).add Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_log
    have hL0 : ∀ᶠ x : ℕ in atTop, 0 ≤ 1 + Real.log x :=
      Eventually.of_forall fun x => by have := Real.log_natCast_nonneg x; linarith
    have hsq : ∀ {C : ℕ → ℝ}, SubPoly C → (∀ x, 0 ≤ C x) → SubPoly fun x => C x ^ 2 := fun hC h0 => by
      have := hC.mul hC (Eventually.of_forall h0) (Eventually.of_forall h0)
      simpa [sq] using this
    have hC₁0 : ∀ x, 0 ≤ C₁ x := fun x => by simp only [hC₁]; positivity
    have h1 : SubPoly fun x : ℕ => 1 / (2 * π) + (1 + Real.log x) / (8 * π ^ 2) := by
      refine (Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const _).add ?_
      have := (Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const (1 / (8 * π ^ 2))).mul hL (Eventually.of_forall fun _ => by positivity) hL0
      simpa [div_eq_inv_mul, mul_comm] using this
    have hQ : SubPoly fun x : ℕ => winQ (C₁ x) (C₂ x) (Real.log x) := by
      unfold winQ
      refine ((((Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const 8).mul (hsq hC₁s hC₁0)
        (Eventually.of_forall fun _ => by norm_num) (Eventually.of_forall fun _ => sq_nonneg _)).mul hL
        (Eventually.of_forall fun _ => by positivity) hL0).mul h1
        (Eventually.of_forall fun x => by have := sq_nonneg (C₁ x); positivity)
        (Eventually.of_forall fun x => by have := Real.log_natCast_nonneg x; positivity)).add
        ((Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const (2 / π)).mul (hsq hC₂s fun _ => le_max_right _ _)
          (Eventually.of_forall fun _ => by positivity) (Eventually.of_forall fun _ => sq_nonneg _))
    exact Cvs.Prolate.Envelope.RungProfileEdgePlunge.subPoly_edgeP.mul hQ
      (by filter_upwards [eventually_ge_atTop 1] with x hx
          have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
          unfold Cvs.Prolate.Envelope.RungProfileEdgePlunge.edgeP Cvs.Prolate.Envelope.RungProfileEdgePlunge.depthQ
          have : 1 ≤ Cvs.Prolate.Envelope.RungProfileEdgePlunge.K₁ * (2 * π * x) :=
            one_le_mul_of_one_le_of_one_le Cvs.Prolate.Envelope.RungProfileEdgePlunge.one_le_K₁ (by nlinarith [Real.pi_gt_three])
          have := Real.log_nonneg this
          have := Cvs.Prolate.Envelope.RungProfileEdgePlunge.one_le_K₁
          positivity)
      (Eventually.of_forall fun x => by
        unfold winQ; have := Real.log_natCast_nonneg x; positivity)
  · filter_upwards [hB, edgeE_sq_le, Cvs.Route.Visibility.ExteriorFactorMTwo.eventually_scale] with x hBx hGx hx σ hσ j
    have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
    have hσ' : |-σ| ≤ 1 := by rwa [abs_neg]
    have hj : (j : ℕ) < x := Cvs.Approximant.SpineSubspace.SF_lt x j j.2
    have hE0 := edgeE_nonneg x j
    have habs : |edgeE x j| = edgeE x j := abs_of_nonneg hE0
    have upA : ∀ s : ℝ, |s| ≤ 1 → ∀ g : ℝ, 8 * π * x ≤ g → g * ‖Aw x j (s + g * I)‖ ≤ C₁ x * |edgeE x j| :=
      fun s hs g hg => by
        rw [habs]; exact Cvs.Prolate.Mellin.RungUnitCircleLaw.g_norm_Aw_le hx hj hs hg
    have upB : ∀ s : ℝ, |s| ≤ 1 → ∀ g : ℝ, 8 * π * x ≤ g →
        g * ‖Bw x j (s + g * I)‖ ≤ C₂ x * |edgeE x j| / √(x : ℝ) :=
      fun s hs g hg => (hBx j s hs g hg).trans (by
        rw [habs]
        have h1 : CB x ≤ C₂ x := le_max_left _ _
        have hs : 0 < √(x : ℝ) := Real.sqrt_pos.2 hx0
        rw [div_le_div_iff_of_pos_right hs]
        exact mul_le_mul_of_nonneg_right h1 hE0)
    obtain ⟨hI, hle⟩ := winTail_le_fixed hx j σ (upA σ hσ) (upB σ hσ) (upA (-σ) hσ') (upB (-σ) hσ')
    refine ⟨hI, hle.trans ?_⟩
    rw [fixed_rhs_eq hx0]
    have hG := hGx j hj
    have hQ0 : 0 ≤ winQ (C₁ x) (C₂ x) (Real.log x) := by
      unfold winQ; have := Real.log_natCast_nonneg x; positivity
    have he : (1 / 2 + 1 / 4 : ℝ) = 3 / 4 := by norm_num
    rw [he]
    have hxs : 0 ≤ (x : ℝ) ^ |σ| := Real.rpow_nonneg hx0.le _
    calc (x : ℝ) ^ |σ| * edgeE x j ^ 2 / x ^ 2 * winQ (C₁ x) (C₂ x) (Real.log x)
        ≤ (x : ℝ) ^ |σ| * (Cvs.Prolate.Envelope.RungProfileEdgePlunge.edgeP x * x * (1 - lamR (2 * π * x) (2 * j)) ^ (3 / 4 : ℝ)) / x ^ 2
            * winQ (C₁ x) (C₂ x) (Real.log x) := by gcongr
      _ = _ := by field_simp

end Cvs.Prolate.Mellin.RungWindowLawRightEdge

end
