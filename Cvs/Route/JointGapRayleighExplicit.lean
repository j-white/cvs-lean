import Mathlib
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.EvenConnesPartLower
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BandInputsFromCutMultipliers
import Cvs.L2a.FullSpanThreshold
import Cvs.L2a.FullTailUpperFrame
import Cvs.L2a.L1ConnesFactorPolynomial
import Cvs.L2a.PlaneCorrelationL2
import Cvs.L2a.ProlateFamilySpine
import Cvs.L2a.RungSpanProfilePowers
import Cvs.L2a.RungSpanTailHighMass
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowChainInputsProlate
import Cvs.Limit.ZeroFreeApproximantsRH
import Cvs.Prolate.AngularBesselInequality
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.LowLevelsTwoFifths
import Cvs.Prolate.LowRungEndpointSmall
import Cvs.Prolate.LowRungRadialTailEdge
import Cvs.Route.JointGapConnesFromL1
import Cvs.WeilForm.Archimedean.ArchFormIntegrable
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowReflectionSymmetry
import Cvs.Xi.EImageWindowPoisson
import Cvs.Xi.XiValueAtOrigin

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The joint gap's Rayleigh side is an explicit function of `x`

`1 − λ₄ ≤ 8h₄(1)² ≤ 800c⁴e^{−c/16}` (Cvs.Prolate.LowLevelsTwoFifths–Cvs.Prolate.LowRungEndpointSmall with `AngularBesselInequality`'s mass identity) and `‖o‖² ≤ ‖k‖² ≤ 4c⁵` (the window
energy Cvs.Xi.EImageWindowPoisson with `|G| ≤ 2c²`), so with Cvs.Approximant.EvenConnesPartLower the Rayleigh side of the joint gap at Connes' vector is at most
`K(Q(x) + s⁺R(x))`, `Q(x) = C1poly(x)·800c⁴e^{−c/16}`, `R(x) = 25c⁵x log x/‖Ξ(0)‖²`, `c = 2πx`: no spectral datum left.
-/

noncomputable section

open MeasureTheory Set Real Filter Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.RegularSolutionEdge Cvs.Prolate.EdgeCentreSign Cvs.Prolate.SlepianEvenOrdering Cvs.Prolate.EvenSpectrumGroundLevel Cvs.Prolate.EvenRungsByIndex Cvs.Approximant.DeepIndexSpineSpan
open scoped InnerProductSpace

namespace Cvs.Route.JointGapRayleighExplicit
open Cvs.ZeroCounting

open Cvs.L2a.ProlateFamilySpine (kOf bOf)
open Cvs.L2a.WindowChainInputsProlate (c0W)
open Cvs.Route.JointGapConnesFromL1 (one₁ connesEven connesOdd)
open Cvs.L2a.L1ConnesFactorPolynomial (C1poly L1poly)

/-- The spine scale is at least `100` past `c₀^W`. -/
theorem hundred_le {x : ℕ} (hx : c0W ≤ 2 * π * x) : 100 ≤ 2 * π * (x : ℝ) := by
  have h := (Cvs.L2a.BandInputsFromCutMultipliers.scale_ge (le_trans Cvs.L2a.WindowChainInputsProlate.c0F_le_c0W hx)).1
  have := Real.add_one_le_exp (1360 : ℝ)
  linarith

/-- A rung with `μ ≥ 1/c` is bounded by `2c` on `[−1, 1]`. -/
theorem abs_rung_le {g : ℝ → ℝ} {c μ : ℝ} (hgc : ContinuousOn g (uIcc (-1) 1))
    (hI : (∫ s in (-1 : ℝ)..1, |g s|) ≤ 2) (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) (hc0 : 0 < c)
    (hμc : 1 / c ≤ μ) {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) : |g s| ≤ 2 * c := by
  have hμ0 : 0 < μ := lt_of_lt_of_le (by positivity) hμc
  have hinv : 1 / μ ≤ c := by
    rw [div_le_iff₀ hμ0]; have := mul_le_mul_of_nonneg_left hμc hc0.le
    rw [mul_one_div_cancel hc0.ne'] at this; linarith
  have h := Cvs.L2a.RungSpanTailHighMass.abs_psi_le_L1 (c := c) (ξ := s) hgc
  rw [hμ s hs, abs_mul, abs_of_pos hμ0, one_mul] at h
  have hI0 : 0 ≤ ∫ s in (-1 : ℝ)..1, |g s| := intervalIntegral.integral_nonneg (by norm_num) fun _ _ => abs_nonneg _
  calc |g s| ≤ (∫ s in (-1 : ℝ)..1, |g s|) * (1 / μ) := by
        rw [mul_one_div, le_div_iff₀ hμ0]; linarith
    _ ≤ 2 * c := mul_le_mul hI hinv (by positivity) (by norm_num)

/-- **`1 − λ₄` is exponentially small**: `1 − λ₄ ≤ 800c⁴e^{−c/16}` at `c = 2πx`, `c₀^W ≤ 2πx`. -/
theorem one_sub_lamR_two_le (x : ℕ) (hx : c0W ≤ 2 * π * x) :
    1 - lamR (2 * π * x) 2 ≤ 800 * (2 * π * x) ^ 4 * exp (-(2 * π * x / 16)) := by
  have H := Cvs.L2a.L1ConnesFactorPolynomial.connes_spanHyp x hx
  set c : ℝ := 2 * π * x with hcdef
  have hc100 : 100 ≤ c := hundred_le hx
  have hc0 : 0 < c := by linarith
  set i₁ : Option ({1} : Finset ℕ) := some ⟨1, Finset.mem_singleton_self 1⟩
  have hk : kOf i₁ = 2 := rfl
  have hlev := (Cvs.Prolate.LowLevelsTwoFifths.lev_two_lt (c := c) (by nlinarith [Real.pi_lt_four])).1
  have hg := H.hg i₁; have hg₁ := H.hg₁ i₁; have hg₂c := H.hg₂c i₁; have hang := H.hang i₁
  have heven := H.heven i₁; have hnorm := H.hnorm i₁; have hμ := H.hμ i₁
  have hχ0 := H.hχ0 i₁; have hμc := H.hμc i₁
  simp only [hk] at hg hg₁ hg₂c hang heven hnorm hμ hχ0 hμc
  have hend := Cvs.Prolate.LowRungEndpointSmall.endpoint_sq_le hg hg₁ hg₂c hang heven hnorm hμ hc100 hχ0 hlev.le hμc
  have htail := Cvs.Prolate.LowRungRadialTailEdge.tail_le_edge hg hg₁ hg₂c hang hc100 hχ0 hlev.le
  have hgc : ContinuousOn (rung c 2) (Icc (-1) 1) := fun s hs =>
    (hg s (by rw [uIcc_of_le (by norm_num)]; exact hs)).continuousAt.continuousWithinAt
  have hmass := Cvs.Prolate.AngularBesselInequality.mass_eq hc0 hgc heven hμ hnorm
  have hψ1 : psi c (rung c 2) 1 = muR c 2 * rung c 2 1 := hμ 1 ⟨by norm_num, le_rfl⟩
  have hlam : lamR c 2 = muR c 2 ^ 2 * (c / (2 * π)) := by
    unfold lamR; rw [mul_pow, Real.sq_sqrt (by positivity)]
  rw [hmass, hψ1] at htail
  change π / c * (1 - lamR c 2) ≤ 4 * (muR c 2 * rung c 2 1) ^ 2 at htail
  have hkey : 1 - lamR c 2 ≤ 8 * lamR c 2 * rung c 2 1 ^ 2 := by
    have e : 4 * (muR c 2 * rung c 2 1) ^ 2 = π / c * (8 * lamR c 2 * rung c 2 1 ^ 2) := by
      rw [hlam]; field_simp; ring
    rw [e] at htail
    exact le_of_mul_le_mul_left htail (by positivity)
  have hE : 0 ≤ 800 * c ^ 4 * exp (-(c / 16)) := by positivity
  by_cases hl : lamR c 2 ≤ 1
  · have hl0 : 0 ≤ lamR c 2 := by rw [hlam]; positivity
    calc 1 - lamR c 2 ≤ 8 * lamR c 2 * rung c 2 1 ^ 2 := hkey
      _ ≤ 8 * 1 * (100 * c ^ 4 * exp (-(c / 16))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hl (by norm_num)) hend (sq_nonneg _) (by norm_num)
      _ = 800 * c ^ 4 * exp (-(c / 16)) := by ring
  · push Not at hl; linarith

/-- **The odd Connes part is polynomially bounded**: `‖o‖² ≤ 4c⁵`. -/
theorem norm_connesOdd_sq_le (x : ℕ) (hx : c0W ≤ 2 * π * x) :
    ‖connesOdd (Cvs.Approximant.SpineSubspace.scale80_of_c0W hx)‖ ^ 2 ≤ 4 * (2 * π * x) ^ 5 := by
  have H := Cvs.L2a.L1ConnesFactorPolynomial.connes_spanHyp x hx
  set c : ℝ := 2 * π * x with hcdef
  have hc100 : 100 ≤ c := hundred_le hx
  have hc0 : 0 < c := by linarith
  have h80 := Cvs.Approximant.SpineSubspace.scale80_of_c0W hx
  have hx1 := Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale h80
  have hx0 : (0 : ℝ) < x := by linarith
  set L := Real.log x with hL
  set G := spineG c one₁ with hG
  set a : ℝ := 2 * π / c with ha
  have ha0 : 0 < a := by positivity
  have hax : a = 1 / x := by rw [ha, hcdef]; field_simp
  set W := Cvs.Xi.EImageWindowPoisson.window a G with hW
  -- `‖o‖² ≤ ‖k‖²`
  have hsplit := Cvs.WeilForm.EvenOddSplitForm.norm_sq_split (Real.log_natCast_nonneg x) (Cvs.Approximant.CosineColumnTailPairing.connesClass h80)
  have hok : ‖connesOdd h80‖ ^ 2 ≤ ‖Cvs.Approximant.CosineColumnTailPairing.connesClass h80‖ ^ 2 := by
    unfold connesOdd; rw [hsplit]; nlinarith [sq_nonneg ‖Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x)
      (Cvs.Approximant.CosineColumnTailPairing.connesClass h80)‖]
  -- `‖k‖² = ∫ W²`
  have hk : ‖Cvs.Approximant.CosineColumnTailPairing.connesClass h80‖ ^ 2 = ∫ θ, W θ ^ 2 := by
    have e1 : ‖Cvs.Approximant.CosineColumnTailPairing.connesClass h80‖ ^ 2 = ‖((Cvs.Approximant.CosineColumnTailPairing.connesClass h80).val.val : Lp ℝ 2 volume)‖ ^ 2 := rfl
    rw [e1, Cvs.L2a.PlaneCorrelationL2.norm_sq_eq_integral]
    rw [integral_congr_ae ((Cvs.Approximant.CosineColumnTailPairing.coe_connesClass_ae h80).mono fun s hs => congrArg (fun z : ℝ => z ^ 2) hs)]
    rw [Cvs.Approximant.ConnesVectorRealScale.connesK_natCast]
    change ∫ s, Cvs.L2a.TailLogScaleTest.logScale W (s - L) ^ 2 = _
    rw [integral_sub_right_eq_self (fun u => Cvs.L2a.TailLogScaleTest.logScale W u ^ 2) L]
    have e : (fun u => Cvs.L2a.TailLogScaleTest.logScale W u ^ 2) = fun u => exp u • (fun θ => W θ ^ 2) (exp u) := by
      funext u; unfold Cvs.L2a.TailLogScaleTest.logScale
      rw [smul_eq_mul, ← Cvs.L2a.TailLogScaleTest.exp_half_sq]; ring
    rw [e]
    have hz : ∀ θ ≤ a / 2, W θ ^ 2 = 0 := fun θ hθ => by
      rw [hW, Cvs.Xi.EImageWindowPoisson.window_of_notMem G (fun h => by linarith [h.1])]; ring
    have h1 : ∫ u, exp u • (fun θ => W θ ^ 2) (exp u) = ∫ u in Ioi (Real.log (a / 2)), exp u • (fun θ => W θ ^ 2) (exp u) := by
      symm; apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro u hu
      simp only [mem_Ioi, not_lt] at hu
      have : exp u ≤ a / 2 := by
        calc exp u ≤ exp (Real.log (a / 2)) := exp_le_exp.mpr hu
          _ = a / 2 := exp_log (by positivity)
      simp only [hz _ this, smul_zero]
    rw [h1, integral_comp_exp_Ioi (fun θ => W θ ^ 2) (Real.log (a / 2)), exp_log (by positivity)]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro θ hθ
    simp only [mem_Ioi, not_lt] at hθ
    exact hz θ hθ
  -- `∫ W² ≤ (H/2)∫G²`
  have hr : ∀ k, ContinuousOn (rung c k) (Icc (-1 : ℝ) 1) := fun k =>
    (Cvs.Approximant.DeepIndexSpineSpan.continuousOn_rawRung c (lev c k)).div_const _
  have hGc : ContinuousOn G (Icc (-1 : ℝ) 1) :=
    continuousOn_finsetSum _ fun j _ => continuousOn_const.mul ((hr _).sub (continuousOn_const.mul (hr 0)))
  have hGeven : ∀ s ∈ Icc (-1 : ℝ) 1, G (-s) = G s := by
    intro s hs
    rw [hG, ← Cvs.L2a.ProlateFamilySpine.sum_option_eq_spineG]
    exact Finset.sum_congr rfl fun i _ => by rw [H.heven i s hs]
  have hwin := Cvs.Xi.EImageWindowPoisson.integral_window_sq_le_half ha0 hGc hGeven
  -- `|G| ≤ 2c²`
  have hGsup : ∀ s ∈ Icc (-1 : ℝ) 1, |G s| ≤ 2 * c ^ 2 := fun s hs => by
    rw [hG, ← Cvs.L2a.ProlateFamilySpine.sum_option_eq_spineG]
    calc |∑ i, bOf c one₁ i * rung c (kOf i) s| ≤ ∑ i, |bOf c one₁ i| * (2 * c) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          rw [abs_mul]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          exact abs_rung_le (fun s hs => (H.hg i s hs).continuousAt.continuousWithinAt) (H.data i).1 (H.hμ i)
            hc0 (H.hμc i) hs
      _ = (∑ i, |bOf c one₁ i|) * (2 * c) := by rw [Finset.sum_mul]
      _ ≤ c * (2 * c) := mul_le_mul_of_nonneg_right H.hS (by positivity)
      _ = 2 * c ^ 2 := by ring
  have hG2 : ∫ s in (-1 : ℝ)..1, G s ^ 2 ≤ 8 * c ^ 4 := by
    calc ∫ s in (-1 : ℝ)..1, G s ^ 2 ≤ ∫ s in (-1 : ℝ)..1, (2 * c ^ 2) ^ 2 := by
          refine intervalIntegral.integral_mono_on (by norm_num) ?_ intervalIntegrable_const fun s hs => ?_
          · exact (hGc.pow 2).intervalIntegrable_of_Icc (by norm_num)
          · have := hGsup s hs
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = 8 * c ^ 4 := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have hH : (harmonic ⌊1 / a⌋₊ : ℝ) ≤ c := by
    have h1 := harmonic_le_one_add_log ⌊1 / a⌋₊
    have hfl : (⌊1 / a⌋₊ : ℝ) ≤ c := by
      have := Nat.floor_le (show 0 ≤ 1 / a by positivity)
      have h1a : 1 / a ≤ c := by rw [ha, one_div_div, div_le_iff₀ (by positivity)]; nlinarith [Real.pi_gt_three]
      linarith
    have hlog : Real.log (⌊1 / a⌋₊ : ℝ) ≤ c - 1 := by
      rcases Nat.eq_zero_or_pos ⌊1 / a⌋₊ with h0 | h0
      · rw [h0]; simp; linarith
      · have hpos : (0 : ℝ) < ⌊1 / a⌋₊ := by exact_mod_cast h0
        have := Real.log_le_sub_one_of_pos hpos
        linarith
    push_cast at h1
    linarith
  have hH0 : (0 : ℝ) ≤ harmonic ⌊1 / a⌋₊ := by
    rw [harmonic_eq_sum_Icc]; push_cast; exact Finset.sum_nonneg fun i _ => by positivity
  calc ‖connesOdd h80‖ ^ 2 ≤ ‖Cvs.Approximant.CosineColumnTailPairing.connesClass h80‖ ^ 2 := hok
    _ = ∫ θ, W θ ^ 2 := hk
    _ ≤ (harmonic ⌊1 / a⌋₊ : ℝ) / 2 * ∫ s in (-1 : ℝ)..1, G s ^ 2 := hwin
    _ ≤ c / 2 * (8 * c ^ 4) := by
        apply mul_le_mul (by linarith) hG2 (intervalIntegral.integral_nonneg (by norm_num) fun _ _ => sq_nonneg _)
          (by positivity)
    _ = 4 * c ^ 5 := by ring

/-- The explicit Rayleigh term `Q(x) = C1poly(x)·800c⁴e^{−c/16}`. -/
def Qx (x : ℕ) : ℝ := C1poly x * (800 * (2 * π * x) ^ 4 * exp (-(2 * π * x / 16)))

/-- The explicit odd-part ratio `R(x) = 25c⁵x log x/‖Ξ(0)‖²`. -/
def Rx (x : ℕ) : ℝ := 25 * (2 * π * x) ^ 5 * x * Real.log x / ‖Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ ^ 2

/-- **L1's explicit gap at scale `x`**: near-positivity `s` on the whole domain, a continuous even-hyperplane floor
`μ`, and `K(Q(x) + s⁺R(x)) + (K − 1)s < μ` at `K = √x log x`, with `Q, R` explicit functions of `x`. -/
def L1GapE (x : ℕ) : Prop :=
  ∃ (_ : c0W ≤ 2 * π * x) (s μ : ℝ) (η : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x)),
    (∀ φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x),
      -s * ‖φ‖ ^ 2 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) φ) ∧
    (∀ φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x),
      Cvs.WeilForm.WindowReflectionSymmetry.reflD (Real.log_natCast_nonneg x) φ = φ → ⟪η, φ⟫_ℝ = 0 →
        μ * ‖φ‖ ^ 2 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) φ) ∧
    √(x : ℝ) * Real.log x * (Qx x + max s 0 * Rx x) + (√(x : ℝ) * Real.log x - 1) * s < μ

theorem C1poly_nonneg {x : ℕ} (hx : c0W ≤ 2 * π * x) : 0 ≤ C1poly x := by
  have hc100 := hundred_le hx
  have hlc : 0 ≤ Real.log (2 * π * x) := Real.log_nonneg (by linarith)
  have hx1 := Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale (Cvs.Approximant.SpineSubspace.scale80_of_c0W hx)
  have hlx : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg hx1.le
  have := abs_nonneg (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)
  have := Cvs.WeilForm.Archimedean.ArchFormIntegrable.growth_nonneg
  have hL : 0 ≤ L1poly (2 * π * x) := by unfold L1poly; positivity
  have hF : 0 ≤ Cvs.L2a.FullTailUpperFrame.frameC 2 (3 * π * (2 * π * x) + 26 * Real.log (2 * π * x)) :=
    Cvs.L2a.FullTailUpperFrame.frameC_nonneg (by norm_num) (by positivity)
  unfold C1poly
  have : 0 ≤ 4 + π / (2 * π * x) := by positivity
  positivity

/-- **RH from L1's explicit gap**: `L1GapE x` at infinitely many integers `x` gives the Riemann hypothesis. -/
theorem riemannHypothesis_of_L1GapE (h : ∃ᶠ x : ℕ in atTop, L1GapE x) : RiemannHypothesis := by
  refine Cvs.L2a.L1ConnesFactorPolynomial.riemannHypothesis_of_L1GapP ((h.and_eventually
    (Cvs.Approximant.EvenConnesPartLower.eventually_norm_connesEven_sq_ge.and (eventually_ge_atTop 3))).mono
    fun x ⟨⟨hx, s, μ, η, hneg, hfloor, hlt⟩, he, hx3⟩ => ?_)
  refine ⟨hx, s, μ, η, hneg, hfloor, lt_of_le_of_lt ?_ hlt⟩
  have h80 := Cvs.Approximant.SpineSubspace.scale80_of_c0W hx
  have hK : 0 ≤ √(x : ℝ) * Real.log x :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale h80).le)
  have hXi : 0 < ‖Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ := norm_pos_iff.mpr fun h => by
    have hp := Cvs.Xi.XiValueAtOrigin.Xi_zero_re_pos
    rw [h, Complex.zero_re] at hp
    exact lt_irrefl 0 hp
  have hx0 : (0 : ℝ) < x := by have := Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale h80; linarith
  have hlx : 0 < Real.log (x : ℝ) := Real.log_pos (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale h80)
  -- the Rayleigh term
  have hQ : C1poly x * (1 - lamR (2 * π * x) 2) ≤ Qx x :=
    mul_le_mul_of_nonneg_left (one_sub_lamR_two_le x hx) (C1poly_nonneg hx)
  -- the odd term
  set E := ‖connesEven h80‖ ^ 2
  set m := 4 / 25 * ‖Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ ^ 2 / (x * Real.log x) with hm
  have hm0 : 0 < m := by positivity
  have hme := he h80
  have hE : 0 < E := lt_of_lt_of_le hm0 hme
  have ho := norm_connesOdd_sq_le x hx
  have hodd : s * ‖connesOdd h80‖ ^ 2 / E ≤ max s 0 * Rx x := by
    have h1 : s * ‖connesOdd h80‖ ^ 2 ≤ max s 0 * (4 * (2 * π * x) ^ 5) :=
      (mul_le_mul_of_nonneg_right (le_max_left s 0) (sq_nonneg _)).trans
        (mul_le_mul_of_nonneg_left ho (le_max_right s 0))
    have h2 : max s 0 * (4 * (2 * π * x) ^ 5) / E ≤ max s 0 * (4 * (2 * π * x) ^ 5) / m :=
      div_le_div_of_nonneg_left (by positivity) hm0 hme
    have e : max s 0 * (4 * (2 * π * x) ^ 5) / m = max s 0 * Rx x := by
      rw [hm]; unfold Rx; field_simp
    calc s * ‖connesOdd h80‖ ^ 2 / E ≤ max s 0 * (4 * (2 * π * x) ^ 5) / E := div_le_div_of_nonneg_right h1 hE.le
      _ ≤ _ := h2
      _ = _ := e
  have := mul_le_mul_of_nonneg_left (add_le_add hQ hodd) hK
  linarith

end Cvs.Route.JointGapRayleighExplicit
