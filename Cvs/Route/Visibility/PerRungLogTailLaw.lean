import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.FullSpanIndexFloor
import Cvs.L2a.WindowChainInputsProlate
import Cvs.Prolate.Envelope.RungDuhamelRemainder
import Cvs.Prolate.Envelope.RungExteriorLaw
import Cvs.Prolate.EvenLevelIndexLemma
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Mellin.TailMellinPlancherel
import Cvs.Prolate.RungSpanBernsteinNikolskii
import Cvs.Route.Visibility.CaseFiniteCellFloorRates
import Cvs.Route.Visibility.CaseFiniteFromWindowChain
import Cvs.Route.Visibility.ExtPairingRatesSubpoly
import Cvs.Route.Visibility.ExteriorFactorMTwo
import Cvs.Route.Visibility.ExteriorTransformHolomorphy
import Cvs.Route.Visibility.ExteriorTransformPointBound
import Cvs.Route.Visibility.LogTailRateCellFloor
import Cvs.Route.Visibility.ProjectionShareSawtooth
import Cvs.Upstream.LogFourierWeightTranslation
import Cvs.WeilForm.TameWindowZeroSum
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.Xi.EImageMellin
import Cvs.Xi.EImageWindowPoisson
import Cvs.Xi.LogScaleEImageModulus
import Cvs.Xi.WindowTransformExterior

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The per-rung log-tail law `LogTailProfile η` for every `η ∈ (0, ½)`

`X_j(σ + ig) = 𝓕φ_j(−g/2π)` (Cvs.Route.Visibility.ExteriorTransformHolomorphy, Cvs.Prolate.Mellin.TailMellinPlancherel), so `logTail_j = 2π∫|𝓕φ_j|² log⁺(2π|ξ|/8πx)`; Cvs.Upstream.LogFourierWeightTranslation bounds it by the
translation moduli of `φ_j`, Cvs.Xi.LogScaleEImageModulus bounds those by `C(x)h^b` and by `4Ext_j`, and `RungDuhamelRemainder`'s exterior law
`Ext_j ≤ x^ε x⁻¹(1 − λ_{4j})^{1/2+η+δ}` closes the bound with a logarithmic loss.
-/

noncomputable section

open MeasureTheory Set Real Filter Complex
open scoped FourierTransform
open Cvs.Xi.EImageWindowPoisson (eimage)
open Cvs.WeilForm.ThetaSpaceParseval (mellinR)
open Cvs.Xi.WindowTransformExterior (ext)
open Cvs.Prolate.EvenRungsByIndex (lamR rung)
open Cvs.Route.Visibility.ExtPairingRatesSubpoly (SubPoly)
open Cvs.Route.Visibility.CaseFiniteCellFloorRates (logTail)

namespace Cvs.Route.Visibility.PerRungLogTailLaw
open Cvs.ZeroCounting

/-! ### The Riemann-sum bound with explicit constants -/

/-- `|E_G(θ)| ≤ (L + M)a/θ` for `G` continuous on `[0, 1]` with `∫₀¹ G = 0`, `|G| ≤ M` and Lipschitz constant `L`. -/
theorem abs_eimage_le_of {a : ℝ} (ha : 0 < a) {G : ℝ → ℝ} (hGc : ContinuousOn G (Icc 0 1))
    (hGi : ∫ u in (0 : ℝ)..1, G u = 0) {L M : ℝ} (hL0 : 0 ≤ L) (hM0 : 0 ≤ M)
    (hLip : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, |G y - G x| ≤ L * |y - x|)
    (hM : ∀ u ∈ Icc (0 : ℝ) 1, |G u| ≤ M) (θ : ℝ) (hθ : 0 < θ) :
    |eimage a G θ| ≤ (L + M) * a / θ := by
  have hGii : IntervalIntegrable G volume 0 1 := hGc.intervalIntegrable_of_Icc zero_le_one
  have hsub : ∀ c d : ℝ, 0 ≤ c → c ≤ d → d ≤ 1 → IntervalIntegrable G volume c d := fun c d hc hcd hd =>
    hGii.mono_set (by rw [uIcc_of_le hcd, uIcc_of_le zero_le_one]; exact Icc_subset_Icc hc hd)
  rcases lt_or_ge θ a with hθa | hθa
  · rw [Cvs.Xi.EImageWindowPoisson.eimage_of_lt ha hθa, abs_zero]; positivity
  set h := a / θ with hh
  have hh0 : 0 < h := by positivity
  set N := ⌊θ / a⌋₊ with hN
  have hNh : (N : ℝ) * h ≤ 1 := by
    have := Nat.floor_le (div_nonneg hθ.le ha.le)
    rw [hh, ← mul_div_assoc, div_le_one hθ]
    rw [le_div_iff₀ ha] at this; linarith
  have hNh' : 1 < ((N : ℝ) + 1) * h := by
    have := Nat.lt_floor_add_one (θ / a)
    rw [hh, ← mul_div_assoc, one_lt_div hθ]
    rw [div_lt_iff₀ ha] at this; linarith
  have hE : eimage a G θ = ∑ n ∈ Finset.range N, h * G ((n + 1) * h) := by
    rw [Cvs.Xi.EImageMellin.eimage_eq_sum_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hh, mul_div_assoc]
  have hmem : ∀ n ∈ Finset.range N, ∀ x ∈ Icc ((n : ℝ) * h) ((n + 1) * h), x ∈ Icc (0 : ℝ) 1 := by
    intro n hn x hx
    have hn' : (n : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.1 hn
    refine ⟨le_trans (by positivity) hx.1, hx.2.trans ?_⟩
    exact (mul_le_mul_of_nonneg_right hn' hh0.le).trans hNh
  have hpiece : ∀ n ∈ Finset.range N,
      |h * G ((n + 1) * h) - ∫ u in ((n : ℝ) * h)..((n + 1) * h), G u| ≤ L * h * h := by
    intro n hn
    have hnh : (n : ℝ) * h ≤ (n + 1) * h := by nlinarith
    have hint := hsub _ _ (by positivity) hnh (hmem n hn _ (right_mem_Icc.2 hnh)).2
    have e : h * G ((n + 1) * h) - ∫ u in ((n : ℝ) * h)..((n + 1) * h), G u
        = ∫ u in ((n : ℝ) * h)..((n + 1) * h), (G ((n + 1) * h) - G u) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const hint, intervalIntegral.integral_const,
        smul_eq_mul]
      ring_nf
    rw [e]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (n : ℝ) * h) (b := (n + 1) * h)
      (C := L * h) (f := fun u => G ((n + 1) * h) - G u) fun x hx => by
        rw [uIoc_of_le hnh] at hx
        have hx' : x ∈ Icc ((n : ℝ) * h) ((n + 1) * h) := Ioc_subset_Icc_self hx
        rw [Real.norm_eq_abs]
        refine (hLip _ (hmem n hn _ hx') _ (hmem n hn _ (right_mem_Icc.2 hnh))).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ hL0
        rw [abs_of_nonneg (by linarith [hx.2])]
        linarith [hx.1]
    rw [Real.norm_eq_abs] at this
    refine this.trans (le_of_eq ?_)
    rw [show ((n : ℝ) + 1) * h - n * h = h by ring, abs_of_pos hh0]
  have hsplit : ∫ u in (0 : ℝ)..(N * h), G u
      = ∑ n ∈ Finset.range N, ∫ u in ((n : ℝ) * h)..((n + 1) * h), G u := by
    have := intervalIntegral.sum_integral_adjacent_intervals (f := G) (μ := volume)
      (a := fun k : ℕ => (k : ℝ) * h) (n := N) fun k hk => by
        have hkh : (k : ℝ) * h ≤ ((k + 1 : ℕ) : ℝ) * h := by push_cast; nlinarith
        exact hsub _ _ (by positivity) hkh
          (by push_cast; exact (hmem k (Finset.mem_range.2 hk) _ (right_mem_Icc.2 (by
            push_cast at hkh; exact hkh))).2)
    simp only [Nat.cast_zero, zero_mul, Nat.cast_add, Nat.cast_one] at this
    exact this.symm
  have htail : |∫ u in ((N : ℝ) * h)..1, G u| ≤ M * h := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (N : ℝ) * h) (b := 1)
      (C := M) (f := G) fun x hx => by
        rw [uIoc_of_le hNh] at hx
        rw [Real.norm_eq_abs]
        exact hM x ⟨le_trans (by positivity) hx.1.le, hx.2⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ 1 - N * h by linarith)] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hM0)
    nlinarith
  have hadd : (∫ u in (0 : ℝ)..(N * h), G u) + ∫ u in ((N : ℝ) * h)..1, G u = 0 := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hsub _ _ le_rfl (by positivity) hNh)
      (hsub _ _ (by positivity) hNh le_rfl), hGi]
  have hdecomp : eimage a G θ = (∑ n ∈ Finset.range N,
      (h * G ((n + 1) * h) - ∫ u in ((n : ℝ) * h)..((n + 1) * h), G u))
        - ∫ u in ((N : ℝ) * h)..1, G u := by
    rw [hE, Finset.sum_sub_distrib, ← hsplit]; linarith
  have hS : |∑ n ∈ Finset.range N,
      (h * G ((n + 1) * h) - ∫ u in ((n : ℝ) * h)..((n + 1) * h), G u)| ≤ L * h := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hpiece).trans ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have : (N : ℝ) * (L * h * h) = L * h * (N * h) := by ring
    rw [this]
    exact (mul_le_mul_of_nonneg_left hNh (by positivity)).trans_eq (mul_one _)
  rw [hdecomp]
  refine (abs_sub _ _).trans ?_
  have : (L + M) * a / θ = L * h + M * h := by rw [hh]; ring
  rw [this]
  linarith

/-! ### The unit rung's constants -/

/-- `∫₀¹ G_j² ≤ 2 + 2α_j²` for `G_j = h_{4j} − α_j h₀`. -/
theorem integral_single_sq_le {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Cvs.Approximant.SpineSubspace.SF x) :
    ∫ s in (0 : ℝ)..1, Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1) s ^ 2
      ≤ 2 + 2 * Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j ^ 2 := by
  set c := 2 * π * (x : ℝ) with hc
  have hex := (Cvs.L2a.FullSpanIndexFloor.full_index x hx (Cvs.Approximant.SpineSubspace.SF_lt x j j.2)).1
  have hex0 := Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero c
  have hc1 := Cvs.Prolate.EvenRungsByIndex.continuousOn_rung hex
  have hc0 := Cvs.Prolate.EvenRungsByIndex.continuousOn_rung hex0
  have n1 := (Cvs.Prolate.EvenRungsByIndex.rung_spec hex).2.2.2.2.2
  have n0 := (Cvs.Prolate.EvenRungsByIndex.rung_spec hex0).2.2.2.2.2
  rw [Cvs.Route.Visibility.CaseFiniteFromWindowChain.spineG_single]
  set α := Cvs.Approximant.DeepIndexSpineSpan.alpha c j
  have hI : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hcont : ContinuousOn (fun s => (rung c (2 * (j : ℕ)) s - α * rung c 0 s) ^ 2) (uIcc (-1) 1) := by
    rw [hI]; exact (hc1.sub (hc0.const_smul α)).pow 2
  have i1 : IntervalIntegrable (fun s => rung c (2 * (j : ℕ)) s ^ 2) volume (-1) 1 :=
    (by rw [hI]; exact hc1.pow 2 : ContinuousOn _ (uIcc (-1 : ℝ) 1)).intervalIntegrable
  have i0 : IntervalIntegrable (fun s => rung c 0 s ^ 2) volume (-1) 1 :=
    (by rw [hI]; exact hc0.pow 2 : ContinuousOn _ (uIcc (-1 : ℝ) 1)).intervalIntegrable
  calc ∫ s in (0 : ℝ)..1, (rung c (2 * (j : ℕ)) s - α * rung c 0 s) ^ 2
      ≤ ∫ s in (-1 : ℝ)..1, (rung c (2 * (j : ℕ)) s - α * rung c 0 s) ^ 2 :=
        intervalIntegral.integral_mono_interval (by norm_num) zero_le_one le_rfl
          (Eventually.of_forall fun s => sq_nonneg _) hcont.intervalIntegrable
    _ ≤ ∫ s in (-1 : ℝ)..1, (2 * rung c (2 * (j : ℕ)) s ^ 2 + 2 * α ^ 2 * rung c 0 s ^ 2) :=
        intervalIntegral.integral_mono_on (by norm_num) hcont.intervalIntegrable
          ((i1.const_mul 2).add (i0.const_mul (2 * α ^ 2))) fun s _ => by
            nlinarith [sq_nonneg (rung c (2 * (j : ℕ)) s + α * rung c 0 s)]
    _ = 2 + 2 * α ^ 2 := by
        rw [intervalIntegral.integral_add (i1.const_mul 2) (i0.const_mul (2 * α ^ 2)),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, n1, n0]
        ring

/-- **The unit rung's profile constants**: at `c = 2πx ≥ 80`, `G_j` is continuous on `[0, 1]` with `∫₀¹ G_j = 0`,
`|G_j| ≤ 12x` and Lipschitz constant `44x²` there. -/
theorem single_bounds {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Cvs.Approximant.SpineSubspace.SF x) :
    ContinuousOn (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1)) (Icc 0 1)
      ∧ (∫ u in (0 : ℝ)..1, Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1) u = 0)
      ∧ (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          |Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1) t - Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1) s|
            ≤ 44 * (x : ℝ) ^ 2 * |t - s|)
      ∧ ∀ t ∈ Icc (0 : ℝ) 1, |Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1) t| ≤ 12 * x := by
  set G := Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1) with hGdef
  obtain ⟨G₁, -, hG, -, -, -, -⟩ := Cvs.Approximant.SpineCouplingTailPairing.spine_profile_data hx (Cvs.Approximant.SpineSubspace.SF_lt x) (Pi.single j 1)
  obtain ⟨-, -, -, hGi⟩ := Cvs.WeilForm.TameWindowZeroSum.spineG_std hx (Pi.single j 1)
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast Cvs.Prolate.RungSpanBernsteinNikolskii.one_le_of_scale hx
  have hc0 : (0 : ℝ) < 2 * π * x := by linarith
  have hI : ∫ s in (0 : ℝ)..1, G s ^ 2 ≤ 18 * x := by
    have h1 := integral_single_sq_le hx j
    have hex := (Cvs.L2a.FullSpanIndexFloor.full_index x hx (Cvs.Approximant.SpineSubspace.SF_lt x j j.2)).1
    have h2 := Cvs.Prolate.Envelope.RungDuhamelRemainder.alpha_sq_le hc0 hex (Cvs.L2a.WindowChainInputsProlate.half_le_lamR hx (Cvs.Approximant.SpineSubspace.SF_lt x j j.2))
    have : 4 * (2 * π * x) / π = 8 * x := by field_simp; ring
    rw [this] at h2
    linarith
  have hI0 : 0 ≤ ∫ s in (0 : ℝ)..1, G s ^ 2 := intervalIntegral.integral_nonneg zero_le_one fun s _ => sq_nonneg _
  have hIcc : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ Icc (-1 : ℝ) 1 := fun t ht => ⟨by linarith [ht.1], ht.2⟩
  have hGc : ContinuousOn G (Icc 0 1) := fun u hu =>
    (hG u (by rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]; exact hIcc u hu)).continuousAt.continuousWithinAt
  have hM : ∀ t ∈ Icc (0 : ℝ) 1, |G t| ≤ 12 * x := fun t ht => by
    have h := Cvs.Prolate.RungSpanBernsteinNikolskii.spine_nikolskii hx (Pi.single j 1) t (hIcc t ht)
    have : G t ^ 2 ≤ (12 * x) ^ 2 := by nlinarith
    exact abs_le_of_sq_le_sq' this (by positivity) |> fun h => abs_le.2 h
  have hD : ∀ t ∈ Icc (0 : ℝ) 1, ‖G₁ t‖ ≤ 44 * (x : ℝ) ^ 2 := fun t ht => by
    have h := Cvs.Prolate.RungSpanBernsteinNikolskii.spine_deriv_nikolskii hx (Pi.single j 1) hG t (hIcc t ht)
    have hπ : π < 3.15 := Real.pi_lt_d2
    have hπ0 : 0 < π := Real.pi_pos
    have e : 4 * (2 * π * x) ^ 3 / (3 * π) = 32 / 3 * π ^ 2 * (x : ℝ) ^ 3 := by field_simp; ring
    rw [e] at h
    have : G₁ t ^ 2 ≤ (44 * (x : ℝ) ^ 2) ^ 2 := by
      have hx3 : 0 ≤ (x : ℝ) ^ 3 := by positivity
      calc G₁ t ^ 2 ≤ 32 / 3 * π ^ 2 * (x : ℝ) ^ 3 * (18 * x) :=
            h.trans (mul_le_mul_of_nonneg_left hI (by positivity))
        _ = 192 * π ^ 2 * (x : ℝ) ^ 4 := by ring
        _ ≤ 1936 * (x : ℝ) ^ 4 := by
            have : π ^ 2 ≤ 3.15 ^ 2 := pow_le_pow_left₀ hπ0.le hπ.le 2
            gcongr; nlinarith
        _ = (44 * (x : ℝ) ^ 2) ^ 2 := by ring
    rw [Real.norm_eq_abs]
    exact abs_le.2 (abs_le_of_sq_le_sq' this (by positivity))
  refine ⟨hGc, hGi, fun s hs t ht => ?_, hM⟩
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := G) (f' := G₁)
    (fun z hz => (hG z (by rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]; exact hIcc z hz)).hasDerivWithinAt)
    hD (convex_Icc 0 1) hs ht
  simpa [Real.norm_eq_abs] using h

/-! ### The Mellin transform as a Fourier transform -/

/-- **`X(σ + ig) = 𝓕φ(−g/2π)`** for the log-scale E-image `φ = phiE a σ G`. -/
theorem mellinR_ext_eq_fourier (a σ : ℝ) (G : ℝ → ℝ) (g : ℝ) :
    mellinR (ext a G) (σ + g * I) = 𝓕 (Cvs.Xi.LogScaleEImageModulus.phiE a σ G) (-(g / (2 * π))) := by
  rw [Cvs.Xi.WindowTransformExterior.ext, Cvs.Route.Visibility.ExteriorTransformHolomorphy.mellinR_indicator_eq, Cvs.Xi.LogScaleEImageModulus.phiE, ← Cvs.Prolate.Mellin.TailMellinPlancherel.mellin_eq_fourier_logTail]

/-! ### The log tail from the translation moduli -/

/-- `∫₀^{1/T} min(4E, Ch^b)/h dh ≤ Ch₀^b/b + 4E log(1/(Th₀))` for `0 < h₀ ≤ 1/T`, `b > 0`, `C, E ≥ 0`. -/
theorem integral_min_div_le {C E b T h₀ : ℝ} (hC : 0 ≤ C) (hE : 0 ≤ E) (hb : 0 < b) (hT : 0 < T) (hh₀ : 0 < h₀)
    (hh₀T : h₀ ≤ 1 / T) :
    IntegrableOn (fun h => min (4 * E) (C * h ^ b) / h) (Ioc 0 (1 / T))
      ∧ ∫ h in Ioc 0 (1 / T), min (4 * E) (C * h ^ b) / h ≤ C * h₀ ^ b / b + 4 * E * Real.log (1 / (T * h₀)) := by
  have hT1 : 0 ≤ 1 / T := by positivity
  set f : ℝ → ℝ := fun h => min (4 * E) (C * h ^ b) / h with hf
  have hrp : IntervalIntegrable (fun h : ℝ => C * h ^ (b - 1)) volume 0 (1 / T) :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul C
  have hfm : Measurable f :=
    (measurable_const.min (measurable_const.mul (measurable_id.pow_const b))).div measurable_id
  have hf0 : ∀ h, 0 < h → 0 ≤ f h := fun h hh => div_nonneg (le_min (by positivity) (by positivity)) hh.le
  have hfle1 : ∀ h, 0 < h → f h ≤ C * h ^ (b - 1) := fun h hh => by
    rw [hf, div_le_iff₀ hh, mul_assoc, ← Real.rpow_add_one hh.ne', sub_add_cancel]
    exact min_le_right _ _
  have hfle2 : ∀ h, 0 < h → f h ≤ 4 * E / h := fun h hh => div_le_div_of_nonneg_right (min_le_left _ _) hh.le
  have hfI : ∀ α β : ℝ, 0 ≤ α → α ≤ β → β ≤ 1 / T → IntervalIntegrable f volume α β := fun α β hα hαβ hβ => by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hαβ).2 ?_
    have hr : IntegrableOn (fun h : ℝ => C * h ^ (b - 1)) (Ioc α β) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT1).1 hrp).mono_set (Ioc_subset_Ioc hα hβ)
    refine hr.mono' hfm.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioc).2
      (Eventually.of_forall fun h hh => ?_))
    have hh0 : 0 < h := lt_of_le_of_lt hα hh.1
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 h hh0)]
    exact hfle1 h hh0
  have hI := hfI 0 (1 / T) le_rfl hT1 le_rfl
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hT1).1 hI, ?_⟩
  rw [← intervalIntegral.integral_of_le hT1, ← intervalIntegral.integral_add_adjacent_intervals
    (hfI 0 h₀ le_rfl hh₀.le hh₀T) (hfI h₀ (1 / T) hh₀.le hh₀T le_rfl)]
  have h1 : ∫ h in (0 : ℝ)..h₀, f h ≤ C * h₀ ^ b / b := by
    calc ∫ h in (0 : ℝ)..h₀, f h ≤ ∫ h in (0 : ℝ)..h₀, C * h ^ (b - 1) :=
          intervalIntegral.integral_mono_on_of_le_Ioo hh₀.le (hfI 0 h₀ le_rfl hh₀.le hh₀T)
            ((intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul C) fun h hh => hfle1 h hh.1
      _ = C * h₀ ^ b / b := by
          rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)), sub_add_cancel,
            Real.zero_rpow hb.ne']
          ring
  have h2 : ∫ h in h₀..1 / T, f h ≤ 4 * E * Real.log (1 / (T * h₀)) := by
    have hpos : ∀ h ∈ uIcc h₀ (1 / T), 0 < h := fun h hh => by
      rw [uIcc_of_le hh₀T] at hh; linarith [hh.1]
    calc ∫ h in h₀..1 / T, f h ≤ ∫ h in h₀..1 / T, 4 * E * h⁻¹ :=
          intervalIntegral.integral_mono_on hh₀T (hfI h₀ (1 / T) hh₀.le hh₀T le_rfl)
            ((intervalIntegral.intervalIntegrable_inv (fun h hh => (hpos h hh).ne') continuousOn_id).const_mul _)
            fun h hh => by
              have := hfle2 h (lt_of_lt_of_le hh₀ hh.1); rwa [div_eq_mul_inv] at this
      _ = 4 * E * Real.log (1 / (T * h₀)) := by
          rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hh₀ (by positivity)]
          congr 2; field_simp
  linarith

/-- **The log tail from the translation moduli**: under the profile bounds, `‖φ‖₂² ≤ E` and `0 < h₀ ≤ 1/T`,
the log tail of `X = M[1_{(1,∞)}E_G]` on `Re s = σ` is finite and at most `π(Ch₀^b/b + 4E log(1/(Th₀))) + 4πE`,
`C = K²(1 + 5/b) + 4K(L + 4M)/(1 − b)`, `K = (L + M)a`. -/
theorem logTail_le_of_moduli {a σ L M b T E h₀ : ℝ} {G : ℝ → ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hGc : ContinuousOn G (Icc 0 1)) (hGi : ∫ u in (0 : ℝ)..1, G u = 0) (hL0 : 0 ≤ L) (hM0 : 0 ≤ M)
    (hLip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, |G t - G s| ≤ L * |t - s|)
    (hM : ∀ t ∈ Icc (0 : ℝ) 1, |G t| ≤ M) (hb0 : 0 < b) (hb1 : b < 1) (hσ0 : 0 ≤ σ) (hσb : σ ≤ 1 - b)
    (hT : 2 ≤ T) (hE : ∫ u, ‖Cvs.Xi.LogScaleEImageModulus.phiE a σ G u‖ ^ 2 ≤ E) (hh₀ : 0 < h₀) (hh₀T : h₀ ≤ 1 / T) :
    (Integrable fun g : ℝ => ‖mellinR (ext a G) (σ + g * I)‖ ^ 2 * max (Real.log (|g| / T)) 0)
      ∧ ∫ g : ℝ, ‖mellinR (ext a G) (σ + g * I)‖ ^ 2 * max (Real.log (|g| / T)) 0
        ≤ π * (((L + M) * a) ^ 2 * (1 + 5 / b) + 4 * ((L + M) * a) * (L + 4 * M) / (1 - b)) * h₀ ^ b / b
          + 4 * π * E * Real.log (1 / (T * h₀)) + 4 * π * E := by
  set K := (L + M) * a with hKdef
  set C := K ^ 2 * (1 + 5 / b) + 4 * K * (L + 4 * M) / (1 - b) with hCdef
  set φ := Cvs.Xi.LogScaleEImageModulus.phiE a σ G with hφ
  have hK0 : 0 ≤ K := by positivity
  have hC0 : 0 ≤ C := by
    have : 0 < 1 - b := by linarith
    positivity
  have hT0 : 0 < T := by linarith
  have hK : ∀ θ, 0 < θ → |θ * eimage a G θ| ≤ K := fun θ hθ => by
    rw [abs_mul, abs_of_pos hθ]
    have := abs_eimage_le_of ha0 hGc hGi hL0 hM0 hLip hM θ hθ
    calc θ * |eimage a G θ| ≤ θ * (K / θ) := mul_le_mul_of_nonneg_left this hθ.le
      _ = K := by field_simp
  have hσ1 : σ < 1 := by linarith
  have hφi : Integrable φ := Cvs.Xi.LogScaleEImageModulus.integrable_phiE ha0 hGc hσ1 hK
  have hφ2 : MemLp φ 2 volume := Cvs.Xi.LogScaleEImageModulus.memLp_phiE ha0 hGc hσ1 hK
  have hE0 : 0 ≤ E := (integral_nonneg fun u => by positivity).trans hE
  -- the translation moduli
  have hD : ∀ h ∈ Ioc 0 (1 / T), ∫ u, ‖φ (u + h) - φ u‖ ^ 2 ≤ min (4 * E) (C * h ^ b) := fun h hh => by
    refine le_min ?_ ?_
    · have hsq : Integrable fun u => ‖φ u‖ ^ 2 := (memLp_two_iff_integrable_sq_norm hφ2.aestronglyMeasurable).1 hφ2
      have hsqh : Integrable fun u => ‖φ (u + h)‖ ^ 2 := hsq.comp_add_right h
      calc ∫ u, ‖φ (u + h) - φ u‖ ^ 2 ≤ ∫ u, (2 * ‖φ (u + h)‖ ^ 2 + 2 * ‖φ u‖ ^ 2) := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun u => by positivity)
              ((hsqh.const_mul 2).add (hsq.const_mul 2)) (Eventually.of_forall fun u => ?_)
            have h2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (φ (u + h)) (φ u)) 2
            simp only
            nlinarith [sq_nonneg (‖φ (u + h)‖ - ‖φ u‖)]
        _ = 4 * ∫ u, ‖φ u‖ ^ 2 := by
            rw [integral_add (hsqh.const_mul 2) (hsq.const_mul 2), integral_const_mul, integral_const_mul,
              integral_add_right_eq_self (fun u => ‖φ u‖ ^ 2) h]
            ring
        _ ≤ 4 * E := by linarith
    · have hh2 : h ≤ 1 / 2 := hh.2.trans (by rw [div_le_div_iff₀ hT0 two_pos]; linarith)
      exact Cvs.Xi.LogScaleEImageModulus.integral_norm_phiE_sub_sq_le ha0 ha1 hLip hM hK hb0 hb1 hσ0 hσb hh.1 hh2
  obtain ⟨hDi, hDint⟩ := integral_min_div_le hC0 hE0 hb0 hT0 hh₀ hh₀T
  obtain ⟨hFi, hFle⟩ := Cvs.Upstream.LogFourierWeightTranslation.integral_fourier_log_le hφi hφ2 hT0 hD hDi
  -- back to the line variable `g = −2πξ`
  set Fl : ℝ → ℝ := fun ξ => ‖𝓕 φ ξ‖ ^ 2 * max (Real.log (2 * π * |ξ| / T)) 0 with hFl
  have hcv : ∀ g : ℝ, ‖mellinR (ext a G) (σ + g * I)‖ ^ 2 * max (Real.log (|g| / T)) 0
      = Fl ((-(2 * π)⁻¹) * g) := fun g => by
    rw [mellinR_ext_eq_fourier, ← hφ, hFl]
    have h2π : (0 : ℝ) < 2 * π := by positivity
    have e1 : -(g / (2 * π)) = (-(2 * π)⁻¹) * g := by ring
    have e2 : 2 * π * |(-(2 * π)⁻¹) * g| = |g| := by
      rw [abs_mul, abs_neg, abs_inv, abs_of_pos h2π]; field_simp
    simp only [e1, e2]
  have hne : (-(2 * π)⁻¹ : ℝ) ≠ 0 := by
    have : (0 : ℝ) < 2 * π := by positivity
    exact neg_ne_zero.2 (inv_ne_zero this.ne')
  refine ⟨?_, ?_⟩
  · simp only [hcv]; exact hFi.comp_mul_left' hne
  · simp only [hcv]
    rw [Measure.integral_comp_mul_left Fl, inv_neg, inv_inv, abs_neg, abs_of_pos (by positivity), smul_eq_mul]
    have hφE : ∫ u, ‖φ u‖ ^ 2 ≤ E := hE
    calc 2 * π * ∫ ξ, Fl ξ ≤ 2 * π * ((1 / 2) * (∫ h in Ioc 0 (1 / T), min (4 * E) (C * h ^ b) / h)
          + 2 * ∫ u, ‖φ u‖ ^ 2) := mul_le_mul_of_nonneg_left hFle (by positivity)
      _ ≤ 2 * π * ((1 / 2) * (C * h₀ ^ b / b + 4 * E * Real.log (1 / (T * h₀))) + 2 * E) := by gcongr
      _ = π * C * h₀ ^ b / b + 4 * π * E * Real.log (1 / (T * h₀)) + 4 * π * E := by ring

/-! ### The exterior law with a subpolynomial factor -/

/-- The squared `L²` norm of `φ` is the exterior energy `Ext_G(σ)`. -/
theorem integral_norm_sq_phiE (a σ : ℝ) (G : ℝ → ℝ) :
    ∫ u, ‖Cvs.Xi.LogScaleEImageModulus.phiE a σ G u‖ ^ 2 = Cvs.Route.Visibility.ExteriorTransformPointBound.extInt a G σ := by
  rw [Cvs.Xi.LogScaleEImageModulus.phiE, Cvs.Prolate.Mellin.TailMellinPlancherel.integral_norm_sq_logTail, Cvs.Route.Visibility.ExteriorTransformPointBound.extInt]
  refine setIntegral_congr_fun measurableSet_Ioi fun w (hw : 1 < w) => ?_
  have hw0 : (0 : ℝ) ≤ w := (lt_trans one_pos hw).le
  rw [mul_pow, ← Real.rpow_natCast (w ^ (σ - 1 / 2)), ← Real.rpow_mul hw0]
  congr 2; push_cast; ring

/-- **The exterior law with a subpolynomial factor**: for `σ < 1`, `0 < κ < 1` some nonnegative subpolynomial `R`
has, eventually, `Ext_{G_j}(σ) ≤ R(x)·x⁻¹·(1 − λ_{4j})^κ` on every rung. -/
theorem exists_extInt_rate {σ κ : ℝ} (hσ : σ < 1) (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    ∃ R : ℕ → ℝ, SubPoly R ∧ (∀ x, 0 ≤ R x) ∧ ∀ᶠ x : ℕ in atTop, ∀ j : Cvs.Approximant.SpineSubspace.SF x,
      Cvs.Route.Visibility.ExteriorTransformPointBound.extInt (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1)) σ
        ≤ R x * (1 / x) * (1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ κ := by
  have hlaw : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop, ∀ j : Cvs.Approximant.SpineSubspace.SF x,
      Cvs.Route.Visibility.ExteriorTransformPointBound.extInt (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1)) σ
        ≤ (x : ℝ) ^ ε * (1 / x) * (1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ κ := fun ε hε => by
    have h := Cvs.Prolate.Envelope.RungDuhamelRemainder.extInt_profile_le_rpow hσ (η := 1 - κ) (by linarith) (by linarith) ε hε
    rw [show (1 : ℝ) - (1 - κ) = κ by ring] at h
    filter_upwards [h] with x hx j
    rw [Cvs.Route.Visibility.CaseFiniteFromWindowChain.spineG_single]
    exact hx j (Cvs.Approximant.SpineSubspace.SF_lt x j j.2)
  set ratio : (x : ℕ) → Cvs.Approximant.SpineSubspace.SF x → ℝ := fun x j =>
    Cvs.Route.Visibility.ExteriorTransformPointBound.extInt (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1)) σ * x
      / (1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ κ with hratio
  set R : ℕ → ℝ := fun x => max 0 (⨆ j : Cvs.Approximant.SpineSubspace.SF x, ratio x j) with hR
  have hω0 : ∀ᶠ x : ℕ in atTop, ∀ j : Cvs.Approximant.SpineSubspace.SF x, 0 ≤ 1 - lamR (2 * π * x) (2 * (j : ℕ)) := by
    filter_upwards [Cvs.Route.Visibility.ExteriorFactorMTwo.eventually_scale] with x hsc j
    have hc0 : (0 : ℝ) < 2 * π * x := by linarith
    have := Cvs.Prolate.Envelope.RungExteriorLaw.lamR_le_one hc0 (Cvs.L2a.FullSpanIndexFloor.full_index x hsc (Cvs.Approximant.SpineSubspace.SF_lt x j j.2)).1
    linarith
  -- the ratio is below every `x^ε` where the law holds
  have hratio_le : ∀ x : ℕ, ∀ ε : ℝ, 1 ≤ x → (∀ j : Cvs.Approximant.SpineSubspace.SF x, 0 ≤ 1 - lamR (2 * π * x) (2 * (j : ℕ))) →
      (∀ j : Cvs.Approximant.SpineSubspace.SF x, Cvs.Route.Visibility.ExteriorTransformPointBound.extInt (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1)) σ
        ≤ (x : ℝ) ^ ε * (1 / x) * (1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ κ) →
      ∀ j : Cvs.Approximant.SpineSubspace.SF x, ratio x j ≤ (x : ℝ) ^ ε := fun x ε hx1 hω h j => by
    have hx0 : (0 : ℝ) < x := by exact_mod_cast hx1
    rcases (Real.rpow_nonneg (hω j) κ).eq_or_lt with h0 | hpos
    · rw [hratio]; simp only; rw [← h0, div_zero]; exact Real.rpow_nonneg hx0.le _
    · rw [hratio]; simp only
      rw [div_le_iff₀ hpos]
      have := h j
      calc Cvs.Route.Visibility.ExteriorTransformPointBound.extInt (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1)) σ * x
          ≤ (x : ℝ) ^ ε * (1 / x) * (1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ κ * x :=
            mul_le_mul_of_nonneg_right this hx0.le
        _ = (x : ℝ) ^ ε * (1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ κ := by field_simp
  refine ⟨R, fun ε hε => ?_, fun x => le_max_left _ _, ?_⟩
  · filter_upwards [hlaw ε hε, hω0, eventually_ge_atTop 1] with x h hω hx1
    exact max_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Real.iSup_le (hratio_le x ε hx1 hω h) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  · filter_upwards [hlaw 1 one_pos, hω0, eventually_ge_atTop 1] with x h hω hx1 j
    have hx0 : (0 : ℝ) < x := by exact_mod_cast hx1
    rcases (Real.rpow_nonneg (hω j) κ).eq_or_lt with h0 | hpos
    · have := h j
      rw [← h0, mul_zero] at this ⊢
      exact this
    · have hle : ratio x j ≤ R x := (le_ciSup (Finite.bddAbove_range _) j).trans (le_max_right _ _)
      rw [hratio] at hle; simp only at hle
      rw [div_le_iff₀ hpos] at hle
      calc Cvs.Route.Visibility.ExteriorTransformPointBound.extInt (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1)) σ
          = Cvs.Route.Visibility.ExteriorTransformPointBound.extInt (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1)) σ * x * (1 / x) := by field_simp
        _ ≤ R x * (1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ κ * (1 / x) :=
            mul_le_mul_of_nonneg_right hle (by positivity)
        _ = R x * (1 / x) * (1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ κ := by ring

/-! ### The per-rung log-tail law -/

/-- The modulus constant `C(x) = K²(1 + 5/b) + 4K(L + 4M)/(1 − b)` at `L = 44x²`, `M = 12x`, `K = (L + M)/x`. -/
def cRate (x b : ℝ) : ℝ :=
  ((44 * x ^ 2 + 12 * x) * (1 / x)) ^ 2 * (1 + 5 / b)
    + 4 * ((44 * x ^ 2 + 12 * x) * (1 / x)) * (44 * x ^ 2 + 4 * (12 * x)) / (1 - b)

theorem cRate_pos {x b : ℝ} (hx : 1 ≤ x) (hb0 : 0 < b) (hb1 : b < 1) : 0 < cRate x b := by
  have : 0 < 1 - b := by linarith
  have hx0 : 0 < x := by linarith
  unfold cRate; positivity

/-- `ω^δ log(1/ω) ≤ 1/δ` for `0 < ω`, `δ > 0`. -/
theorem rpow_mul_log_inv_le {ω δ : ℝ} (hω : 0 < ω) (hδ : 0 < δ) : ω ^ δ * Real.log (1 / ω) ≤ 1 / δ := by
  have h := Real.log_le_rpow_div (by positivity : (0 : ℝ) ≤ 1 / ω) hδ
  have hωδ : 0 < ω ^ δ := Real.rpow_pos_of_pos hω δ
  calc ω ^ δ * Real.log (1 / ω) ≤ ω ^ δ * ((1 / ω) ^ δ / δ) := mul_le_mul_of_nonneg_left h hωδ.le
    _ = 1 / δ := by
        rw [Real.div_rpow zero_le_one hω.le, Real.one_rpow]; field_simp

/-- **The log tail of one rung**: at `c = 2πx ≥ 80`, for `0 < b < 1`, `0 ≤ σ ≤ 1 − b`, `δ > 0`, `κ = ½ + η + δ`
with `½ + η > 0`, and `Ext_{G_j}(σ) ≤ R·x⁻¹·ω^κ`, `ω = 1 − λ_{4j}`, `R ≥ 0`: the log tail at `T₀ = 8πx` is finite
and at most `(π + 4πR(1 + ℓ/b + (½ + η)/(bδ)))·x⁻¹·ω^{½+η}`, `ℓ = log⁺(xC(x)/b)`. -/
theorem logTail_single_le {x : ℕ} (hsc : 80 ≤ 2 * π * x) (j : Cvs.Approximant.SpineSubspace.SF x) {σ b η δ R : ℝ} (hb0 : 0 < b)
    (hb1 : b < 1) (hσ0 : 0 ≤ σ) (hσb : σ ≤ 1 - b) (hη : 0 < 1 / 2 + η) (hδ : 0 < δ) (hR : 0 ≤ R)
    (hE : Cvs.Route.Visibility.ExteriorTransformPointBound.extInt (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1)) σ
      ≤ R * (1 / x) * (1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ (1 / 2 + η + δ)) :
    (Integrable fun g : ℝ =>
        ‖mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1))) (σ + g * I)‖ ^ 2
          * max (Real.log (|g| / (8 * π * x))) 0)
      ∧ logTail x σ (8 * π * x) (Pi.single j 1)
        ≤ (π + 4 * π * R * (1 + max 0 (Real.log (x * cRate x b / b)) / b + (1 / 2 + η) / (b * δ)))
          * (1 / x) * (1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ (1 / 2 + η) := by
  set G := Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1) with hGdef
  obtain ⟨hGc, hGi, hLip, hM⟩ := single_bounds hsc j
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast Cvs.Prolate.RungSpanBernsteinNikolskii.one_le_of_scale hsc
  have hx0 : (0 : ℝ) < x := by linarith
  have ha0 : (0 : ℝ) < 1 / x := by positivity
  have ha1 : (1 : ℝ) / x ≤ 1 := by rw [div_le_one hx0]; exact hx1
  have hL0 : (0 : ℝ) ≤ 44 * (x : ℝ) ^ 2 := by positivity
  have hM0 : (0 : ℝ) ≤ 12 * (x : ℝ) := by positivity
  have hT : (2 : ℝ) ≤ 8 * π * x := by nlinarith [Real.pi_gt_three]
  have hT0 : (0 : ℝ) < 8 * π * x := by linarith
  set T := 8 * π * (x : ℝ) with hTdef
  set ω := 1 - lamR (2 * π * x) (2 * (j : ℕ)) with hω
  have hc0 : (0 : ℝ) < 2 * π * x := by linarith
  have hex := (Cvs.L2a.FullSpanIndexFloor.full_index x hsc (Cvs.Approximant.SpineSubspace.SF_lt x j j.2)).1
  have hω0 : 0 ≤ ω := by have := Cvs.Prolate.Envelope.RungExteriorLaw.lamR_le_one hc0 hex; rw [hω]; linarith
  have hω1 : ω ≤ 1 := by have := Cvs.L2a.WindowChainInputsProlate.half_le_lamR hsc (Cvs.Approximant.SpineSubspace.SF_lt x j j.2); rw [hω]; linarith
  set E := R * (1 / x) * ω ^ (1 / 2 + η + δ) with hEdef
  have hEφ : ∫ u, ‖Cvs.Xi.LogScaleEImageModulus.phiE (1 / x) σ G u‖ ^ 2 ≤ E := by rw [integral_norm_sq_phiE]; exact hE
  set C := cRate x b with hCdef
  have hC0 : 0 < C := cRate_pos hx1 hb0 hb1
  have hlt := fun h₀ (hh₀ : 0 < h₀) (hh₀T : h₀ ≤ 1 / T) =>
    logTail_le_of_moduli ha0 ha1 hGc hGi hL0 hM0 hLip hM hb0 hb1 hσ0 hσb hT hEφ hh₀ hh₀T
  have hCeq : ((44 * (x : ℝ) ^ 2 + 12 * x) * (1 / x)) ^ 2 * (1 + 5 / b)
      + 4 * ((44 * (x : ℝ) ^ 2 + 12 * x) * (1 / x)) * (44 * (x : ℝ) ^ 2 + 4 * (12 * x)) / (1 - b) = C := rfl
  rcases hω0.eq_or_lt with hωz | hωp
  · -- `ω = 0`: `φ = 0`, so the transform vanishes on the line
    have hint := (hlt (1 / T) (by positivity) le_rfl).1
    refine ⟨hint, ?_⟩
    have hE0 : E = 0 := by
      rw [hEdef, ← hωz, Real.zero_rpow (by linarith)]; ring
    have hφ0 : ∀ᵐ u ∂volume, Cvs.Xi.LogScaleEImageModulus.phiE (1 / x) σ G u = 0 := by
      have hK : ∀ θ, 0 < θ → |θ * eimage (1 / x) G θ| ≤ (44 * (x : ℝ) ^ 2 + 12 * x) * (1 / x) := fun θ hθ => by
        rw [abs_mul, abs_of_pos hθ]
        have := abs_eimage_le_of ha0 hGc hGi hL0 hM0 hLip hM θ hθ
        calc θ * |eimage (1 / x) G θ| ≤ θ * ((44 * (x : ℝ) ^ 2 + 12 * x) * (1 / x) / θ) :=
              mul_le_mul_of_nonneg_left this hθ.le
          _ = _ := by field_simp
      have h2 := Cvs.Xi.LogScaleEImageModulus.memLp_phiE ha0 hGc (by linarith : σ < 1) hK
      have hsq := (memLp_two_iff_integrable_sq_norm h2.aestronglyMeasurable).1 h2
      have hz : ∫ u, ‖Cvs.Xi.LogScaleEImageModulus.phiE (1 / x) σ G u‖ ^ 2 = 0 :=
        le_antisymm (hEφ.trans hE0.le) (integral_nonneg fun u => by positivity)
      have := (integral_eq_zero_iff_of_nonneg (fun u => by positivity) hsq).1 hz
      filter_upwards [this] with u hu
      simpa using hu
    have hzero : ∀ g : ℝ, mellinR (ext (1 / x) G) (σ + g * I) = 0 := fun g => by
      rw [mellinR_ext_eq_fourier, Real.fourier_congr_ae hφ0, Real.fourier_real_eq]
      simp
    have hl : logTail x σ (8 * π * x) (Pi.single j 1) = 0 := by
      have hz : ∀ g : ℝ, ‖mellinR (ext (1 / x) G) (σ + g * I)‖ ^ 2 * max (Real.log (|g| / T)) 0 = 0 :=
        fun g => by rw [hzero g]; simp
      calc logTail x σ (8 * π * x) (Pi.single j 1)
          = ∫ g : ℝ, ‖mellinR (ext (1 / x) G) (σ + g * I)‖ ^ 2 * max (Real.log (|g| / T)) 0 := rfl
        _ = ∫ _ : ℝ, (0 : ℝ) := integral_congr_ae (Eventually.of_forall hz)
        _ = 0 := integral_zero _ _
    rw [hl, ← hωz, Real.zero_rpow (by linarith), mul_zero]
  -- `ω > 0`: the cut `h₀ = min(1/T, (bω^{½+η}/(xC))^{1/b})`
  set w := ω ^ (1 / 2 + η) with hw
  have hw0 : 0 < w := Real.rpow_pos_of_pos hωp _
  set y := (b * w / (x * C)) ^ b⁻¹ with hy
  have hy0 : 0 < y := Real.rpow_pos_of_pos (by positivity) _
  set h₀ := min (1 / T) y with hh₀
  have hh₀0 : 0 < h₀ := lt_min (by positivity) hy0
  have hh₀T : h₀ ≤ 1 / T := min_le_left _ _
  obtain ⟨hint, hle⟩ := hlt h₀ hh₀0 hh₀T
  refine ⟨hint, ?_⟩
  rw [hCeq] at hle
  have hlog : logTail x σ (8 * π * x) (Pi.single j 1)
      = ∫ g : ℝ, ‖mellinR (ext (1 / x) G) (σ + g * I)‖ ^ 2 * max (Real.log (|g| / T)) 0 := rfl
  rw [hlog]
  refine hle.trans ?_
  -- (i) the modulus term
  have hi : π * C * h₀ ^ b / b ≤ π * w / x := by
    have h1 : h₀ ^ b ≤ y ^ b := Real.rpow_le_rpow hh₀0.le (min_le_right _ _) hb0.le
    have h2 : y ^ b = b * w / (x * C) := by rw [hy, Real.rpow_inv_rpow (by positivity) hb0.ne']
    calc π * C * h₀ ^ b / b ≤ π * C * y ^ b / b := by gcongr
      _ = π * w / x := by rw [h2]; field_simp
  -- (ii) the logarithm of the cut
  set ℓ := max 0 (Real.log (x * C / b)) with hℓ
  have hlogω : 0 ≤ Real.log (1 / ω) := Real.log_nonneg (by rw [le_div_iff₀ hωp]; linarith)
  have hii : Real.log (1 / (T * h₀)) ≤ (1 / b) * (ℓ + (1 / 2 + η) * Real.log (1 / ω)) := by
    have hrhs : 0 ≤ (1 / b) * (ℓ + (1 / 2 + η) * Real.log (1 / ω)) :=
      mul_nonneg (by positivity) (add_nonneg (le_max_left _ _) (mul_nonneg hη.le hlogω))
    rcases le_total (1 / T) y with hyT | hyT
    · rw [hh₀, min_eq_left hyT, mul_one_div_cancel hT0.ne', div_one, Real.log_one]; exact hrhs
    · rw [hh₀, min_eq_right hyT]
      have hTy : Real.log (1 / (T * y)) ≤ Real.log (1 / y) := by
        refine Real.log_le_log (by positivity) ?_
        rw [div_le_div_iff₀ (by positivity) hy0]; nlinarith
      have hly : Real.log (1 / y) = (1 / b) * (Real.log (x * C / b) + (1 / 2 + η) * Real.log (1 / ω)) := by
        have e1 : Real.log y = b⁻¹ * Real.log (b * w / (x * C)) := Real.log_rpow (by positivity) _
        have e2 : Real.log (b * w / (x * C)) = Real.log b + Real.log w - (Real.log x + Real.log C) := by
          rw [Real.log_div (by positivity) (by positivity), Real.log_mul hb0.ne' hw0.ne',
            Real.log_mul hx0.ne' hC0.ne']
        have e3 : Real.log w = (1 / 2 + η) * Real.log ω := Real.log_rpow hωp _
        have e4 : Real.log (1 / ω) = -Real.log ω := by rw [one_div, Real.log_inv]
        have e5 : Real.log (x * C / b) = Real.log x + Real.log C - Real.log b := by
          rw [Real.log_div (by positivity) hb0.ne', Real.log_mul hx0.ne' hC0.ne']
        have e6 : Real.log (1 / y) = -Real.log y := by rw [one_div, Real.log_inv]
        rw [e6, e1, e2, e3, e4, e5]
        field_simp
        ring
      rw [hly] at hTy
      refine hTy.trans (mul_le_mul_of_nonneg_left (by linarith [le_max_right 0 (Real.log (x * C / b))])
        (by positivity))
  -- (iii) the exterior factor
  have hsplit : ω ^ (1 / 2 + η + δ) = w * ω ^ δ := by rw [hw, ← Real.rpow_add hωp]
  have hωδ1 : ω ^ δ ≤ 1 := Real.rpow_le_one hωp.le hω1 hδ.le
  have hωδ0 : 0 ≤ ω ^ δ := (Real.rpow_pos_of_pos hωp δ).le
  have hωlog := rpow_mul_log_inv_le hωp hδ
  have hiii : 4 * π * E * Real.log (1 / (T * h₀)) + 4 * π * E
      ≤ 4 * π * R * (1 + ℓ / b + (1 / 2 + η) / (b * δ)) * (1 / x) * w := by
    have hE' : E = R * (1 / x) * w * ω ^ δ := by rw [hEdef, hsplit]; ring
    have hRx : 0 ≤ R * (1 / x) * w := by positivity
    have hℓ0 : 0 ≤ ℓ := le_max_left _ _
    have hlogE : E * Real.log (1 / (T * h₀)) ≤ R * (1 / x) * w * (ℓ / b + (1 / 2 + η) / (b * δ)) := by
      have hEnn : 0 ≤ E := by rw [hE']; positivity
      calc E * Real.log (1 / (T * h₀)) ≤ E * ((1 / b) * (ℓ + (1 / 2 + η) * Real.log (1 / ω))) :=
            mul_le_mul_of_nonneg_left hii hEnn
        _ = R * (1 / x) * w * ((1 / b) * (ω ^ δ * ℓ + (1 / 2 + η) * (ω ^ δ * Real.log (1 / ω)))) := by
            rw [hE']; ring
        _ ≤ R * (1 / x) * w * ((1 / b) * (1 * ℓ + (1 / 2 + η) * (1 / δ))) := by
            gcongr
        _ = R * (1 / x) * w * (ℓ / b + (1 / 2 + η) / (b * δ)) := by field_simp
    have hE1 : E ≤ R * (1 / x) * w := by
      rw [hE']; exact mul_le_of_le_one_right hRx hωδ1
    have h4π : (0 : ℝ) ≤ 4 * π := by positivity
    have k1 := mul_le_mul_of_nonneg_left hlogE h4π
    have k2 := mul_le_mul_of_nonneg_left hE1 h4π
    calc 4 * π * E * Real.log (1 / (T * h₀)) + 4 * π * E
        = 4 * π * (E * Real.log (1 / (T * h₀))) + 4 * π * E := by ring
      _ ≤ 4 * π * (R * (1 / x) * w * (ℓ / b + (1 / 2 + η) / (b * δ))) + 4 * π * (R * (1 / x) * w) :=
          add_le_add k1 k2
      _ = 4 * π * R * (1 + ℓ / b + (1 / 2 + η) / (b * δ)) * (1 / x) * w := by ring
  calc π * C * h₀ ^ b / b + 4 * π * E * Real.log (1 / (T * h₀)) + 4 * π * E
      ≤ π * w / x + 4 * π * R * (1 + ℓ / b + (1 / 2 + η) / (b * δ)) * (1 / x) * w := by linarith
    _ = (π + 4 * π * R * (1 + ℓ / b + (1 / 2 + η) / (b * δ))) * (1 / x) * w := by ring

/-- `x·C(x)/b ≤ A_b x⁴` for `x ≥ 1`, `A_b = (3136(1 + 5/b) + 20608/(1 − b))/b`. -/
theorem mul_cRate_le {x b : ℝ} (hx : 1 ≤ x) (hb0 : 0 < b) (hb1 : b < 1) :
    x * cRate x b / b ≤ (3136 * (1 + 5 / b) + 20608 / (1 - b)) / b * x ^ 4 := by
  have h1b : 0 < 1 - b := by linarith
  have hx0 : 0 < x := by linarith
  have hK : (44 * x ^ 2 + 12 * x) * (1 / x) = 44 * x + 12 := by field_simp
  have hk1 : 44 * x + 12 ≤ 56 * x := by linarith
  have hk2 : 44 * x ^ 2 + 4 * (12 * x) ≤ 92 * x ^ 2 := by nlinarith
  have hc : cRate x b ≤ (3136 * (1 + 5 / b) + 20608 / (1 - b)) * x ^ 3 := by
    unfold cRate
    rw [hK]
    have hp : (44 * x + 12) ^ 2 ≤ 3136 * x ^ 3 := by
      have : (44 * x + 12) ^ 2 ≤ (56 * x) ^ 2 := pow_le_pow_left₀ (by positivity) hk1 2
      nlinarith
    have hq : 4 * (44 * x + 12) * (44 * x ^ 2 + 4 * (12 * x)) ≤ 20608 * x ^ 3 := by
      have := mul_le_mul hk1 hk2 (by positivity) (by positivity)
      nlinarith
    have hb5 : 0 ≤ 1 + 5 / b := by positivity
    calc (44 * x + 12) ^ 2 * (1 + 5 / b) + 4 * (44 * x + 12) * (44 * x ^ 2 + 4 * (12 * x)) / (1 - b)
        ≤ 3136 * x ^ 3 * (1 + 5 / b) + 20608 * x ^ 3 / (1 - b) := by gcongr
      _ = (3136 * (1 + 5 / b) + 20608 / (1 - b)) * x ^ 3 := by ring
  calc x * cRate x b / b ≤ x * ((3136 * (1 + 5 / b) + 20608 / (1 - b)) * x ^ 3) / b := by gcongr
    _ = (3136 * (1 + 5 / b) + 20608 / (1 - b)) / b * x ^ 4 := by ring

/-- `log⁺(xC(x)/b)` is subpolynomial. -/
theorem subPoly_logRate {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    SubPoly fun x : ℕ => max 0 (Real.log (x * cRate x b / b)) := by
  set A := (3136 * (1 + 5 / b) + 20608 / (1 - b)) / b with hA
  have hA0 : 0 < A := by have : 0 < 1 - b := by linarith
                         positivity
  have hg : SubPoly fun x : ℕ => max 0 (Real.log A) + 4 * Real.log x :=
    (Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const _).add (Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly.mul (Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const 4) Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_log
      (Eventually.of_forall fun _ => by norm_num) (by
        filter_upwards [eventually_ge_atTop 1] with x hx
        exact Real.log_nonneg (by exact_mod_cast hx)))
  refine hg.mono ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx1
  refine max_le (by positivity) ?_
  have hpos : 0 < (x : ℝ) * cRate x b / b := by
    have := cRate_pos hx1 hb0 hb1; positivity
  calc Real.log (x * cRate x b / b) ≤ Real.log (A * (x : ℝ) ^ 4) :=
        Real.log_le_log hpos (mul_cRate_le hx1 hb0 hb1)
    _ = Real.log A + 4 * Real.log x := by
        rw [Real.log_mul hA0.ne' (by positivity), Real.log_pow]; push_cast; ring
    _ ≤ max 0 (Real.log A) + 4 * Real.log x := by linarith [le_max_right 0 (Real.log A)]

/-- **The per-rung log-tail law** (caseF-chain Lemma 9 in `H^ε` form): `LogTailProfile η` for every `η ∈ (0, ½)`. -/
theorem logTailProfile {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1 / 2) : Cvs.Route.Visibility.LogTailRateCellFloor.LogTailProfile η := by
  intro σ₁ σ₂ hσ₁ hσ₂
  set b := min (1 - σ₂) (1 / 2) with hb
  have hb0 : 0 < b := lt_min (by linarith) (by norm_num)
  have hb1 : b < 1 := (min_le_right _ _).trans_lt (by norm_num)
  set δ := (1 / 2 - η) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  obtain ⟨R, hRs, hR0, hRx⟩ := exists_extInt_rate (κ := 1 / 2 + η + δ) hσ₂ (by linarith) (by rw [hδ]; linarith)
  set ℓ : ℕ → ℝ := fun x => max 0 (Real.log (x * cRate x b / b)) with hℓ
  have hℓs : SubPoly ℓ := subPoly_logRate hb0 hb1
  have hℓ0 : ∀ x, 0 ≤ ℓ x := fun x => le_max_left _ _
  refine ⟨fun x => π + 4 * π * R x * (1 + ℓ x / b + (1 / 2 + η) / (b * δ)), ?_, ?_⟩
  · have hin : SubPoly fun x => 1 + ℓ x / b + (1 / 2 + η) / (b * δ) := by
      refine ((Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const 1).add ?_).add (Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const _)
      exact Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly.mono (Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly.mul hℓs (Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const b⁻¹) (Eventually.of_forall hℓ0)
        (Eventually.of_forall fun _ => by positivity)) (Eventually.of_forall fun x => le_of_eq (div_eq_mul_inv _ _))
    have hR4 : SubPoly fun x => 4 * π * R x :=
      Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly.mul (Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const (4 * π)) hRs (Eventually.of_forall fun _ => by positivity)
        (Eventually.of_forall hR0)
    exact Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly.mono ((Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const π).add (Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly.mul hR4 hin
      (Eventually.of_forall fun x => by have := hR0 x; positivity)
      (Eventually.of_forall fun x => by have := hℓ0 x; positivity)))
      (Eventually.of_forall fun x => le_of_eq (by ring))
  · filter_upwards [hRx, Cvs.Route.Visibility.ExteriorFactorMTwo.eventually_scale] with x hRx hsc σ hσ j
    have hσ0 : 0 ≤ σ := (hσ₁.trans_le hσ.1).le
    have hσb : σ ≤ 1 - b := hσ.2.trans (by linarith [min_le_left (1 - σ₂) (1 / 2)])
    obtain ⟨G₁, hG, hG₁, hGi⟩ := Cvs.WeilForm.TameWindowZeroSum.spineG_std hsc (Pi.single j 1)
    have hx0 : (0 : ℝ) < 1 / x := by
      have := Cvs.Prolate.RungSpanBernsteinNikolskii.one_le_of_scale hsc; positivity
    have hE := (Cvs.Route.Visibility.ExteriorTransformPointBound.extInt_mono hx0 hG hG₁ hGi hσ.2 hσ₂).trans (hRx j)
    exact logTail_single_le hsc j hb0 hb1 hσ0 hσb (by linarith) hδ0 (hR0 x) hE

end Cvs.Route.Visibility.PerRungLogTailLaw

end
