import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FarFarBound
import Cvs.L2a.SpanPoleMellinFromRungs
import Cvs.Prolate.Envelope.RungCountEnvelope
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RungCauchySplit
import Cvs.Upstream.ExpDifferenceBound

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The kernel form of the localised band transfer

For a window `ω` of half-width `d` at `x₀` and a kernel `K` with `∫(1 + |z| + z²)|K| < ∞`,
`∫K(x₀−x)ω(x)ψ(x)dx` is the sample `μ(k)ψ⁺(x₀) + μ(−k)ψ⁻(x₀)`, `μ = K̂`, `k = k(x₀)`, up to `τ_K·R(x₀)`;
over a span, `|Σaₙ Sₙ[μ]| ≤ ‖K‖₂‖ωΦ‖₂ + τ_K √(6J/(x₀²−1)) √P` by the count envelope (Cvs.Prolate.Envelope.RungCountEnvelope).
-/

namespace Cvs.L2a.BandTransferKernelForm

open Complex Set MeasureTheory Cvs.L2a.AngularProlateTailPositive Cvs.L2a.SpanPoleMellinFromRungs Cvs.Prolate.Envelope.RungCountEnvelope Cvs.Prolate.RungCauchySplit Cvs.Upstream.ExpDifferenceBound
open scoped ComplexConjugate

/-- The kernel's Fourier transform `μ(ξ) = ∫ e^{−iξz} K(z) dz`. -/
noncomputable def ft (K : ℝ → ℂ) (ξ : ℝ) : ℂ := ∫ z, exp (((-(ξ * z) : ℝ) : ℂ) * I) * K z

/-- The rung sample `S[μ] = μ(k)ψ⁺(x₀) + μ(−k)ψ⁻(x₀)` with `k = k(x₀)` and `ψ⁻ = conj ψ⁺`. -/
noncomputable def sample (K : ℝ → ℂ) (c χ : ℝ) (g : ℝ → ℝ) (x₀ : ℝ) : ℂ :=
  ft K (kP c χ x₀) * psiP c χ g x₀ + ft K (-kP c χ x₀) * conj (psiP c χ g x₀)

/-- The window coupling bound `β_W = (x₀−d)/((x₀−d)²−1)`. -/
noncomputable def betaW (x₀ d : ℝ) : ℝ := (x₀ - d) / ((x₀ - d) ^ 2 - 1)

/-- The window chirp bound `Y'_W = (x₀−d/2)/((x₀−d/2)²−1)²`. -/
noncomputable def chirpW (x₀ d : ℝ) : ℝ := (x₀ - d / 2) / ((x₀ - d / 2) ^ 2 - 1) ^ 2

/-- The transfer constant `τ_K = 2β_W e^{β_W d}∫|z||K| + (c/2)Y'_W∫z²|K| + (e^{2β_W d}+1)∫_{|z|>d/2}|K|`. -/
noncomputable def tauK (K : ℝ → ℂ) (c x₀ d : ℝ) : ℝ :=
  2 * betaW x₀ d * Real.exp (betaW x₀ d * d) * (∫ z, |z| * ‖K z‖)
    + c / 2 * chirpW x₀ d * (∫ z, z ^ 2 * ‖K z‖)
    + (Real.exp (2 * betaW x₀ d * d) + 1) * ∫ z in {z : ℝ | d / 2 < |z|}, ‖K z‖

/-- A window at `x₀` of half-width `d`: measurable, valued in `[0,1]`, `1` on `|x−x₀| ≤ d/2`, `0` off `|x−x₀| ≤ d`. -/
structure IsWindow (ω : ℝ → ℝ) (x₀ d : ℝ) : Prop where
  meas : Measurable ω
  nonneg : ∀ x, 0 ≤ ω x
  le_one : ∀ x, ω x ≤ 1
  eq_one : ∀ x, |x - x₀| ≤ d / 2 → ω x = 1
  eq_zero : ∀ x, d < |x - x₀| → ω x = 0

theorem betaW_nonneg {x₀ d : ℝ} (hxd : 1 < x₀ - d) : 0 ≤ betaW x₀ d := by
  have : 0 < (x₀ - d) ^ 2 - 1 := by nlinarith
  unfold betaW; positivity

theorem chirpW_nonneg {x₀ d : ℝ} (hd : 0 ≤ d) (hxd : 1 < x₀ - d) : 0 ≤ chirpW x₀ d := by
  have : 0 < x₀ - d / 2 := by linarith
  unfold chirpW; positivity

theorem tauK_nonneg (K : ℝ → ℂ) {c x₀ d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (hxd : 1 < x₀ - d) :
    0 ≤ tauK K c x₀ d := by
  have hb := betaW_nonneg hxd
  have hy := chirpW_nonneg hd hxd
  have h1 : 0 ≤ ∫ z, |z| * ‖K z‖ := integral_nonneg fun z => by positivity
  have h2 : 0 ≤ ∫ z, z ^ 2 * ‖K z‖ := integral_nonneg fun z => by positivity
  have h3 : 0 ≤ ∫ z in {z : ℝ | d / 2 < |z|}, ‖K z‖ := integral_nonneg fun z => norm_nonneg _
  unfold tauK; positivity

/-- **Complex mass Cauchy–Schwarz**: `‖Σ aᵢXᵢ‖ ≤ √(Σ aᵢ²mᵢ)·√(Σ vᵢ²/mᵢ)` for `‖Xᵢ‖ ≤ vᵢ`. -/
theorem norm_sum_le_mass {ι : Type} [Fintype ι] (a : ι → ℝ) (X : ι → ℂ) (v m : ι → ℝ)
    (hm : ∀ i, 0 < m i) (hX : ∀ i, ‖X i‖ ≤ v i) :
    ‖∑ i, (a i : ℂ) * X i‖ ≤ √(∑ i, a i ^ 2 * m i) * √(massSum v m) := by
  have h := abs_sum_le_mass (fun i => |a i|) (fun i => ‖X i‖) v m hm
    (fun i => by rw [abs_of_nonneg (norm_nonneg _)]; exact hX i)
  have e : ∑ i, |a i| ^ 2 * m i = ∑ i, a i ^ 2 * m i := by simp only [sq_abs]
  rw [e] at h
  calc ‖∑ i, (a i : ℂ) * X i‖ ≤ ∑ i, ‖(a i : ℂ) * X i‖ := norm_sum_le _ _
    _ = ∑ i, |a i| * ‖X i‖ := by simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ |∑ i, |a i| * ‖X i‖| := le_abs_self _
    _ ≤ _ := h

theorem massSum_const_mul {ι : Type} [Fintype ι] (τ : ℝ) (v m : ι → ℝ) :
    massSum (fun i => τ * v i) m = τ ^ 2 * massSum v m := by
  unfold massSum; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring

theorem integrable_exp_mul {K : ℝ → ℂ} (hK : Integrable K) (ξ : ℝ) :
    Integrable (fun z => exp (((-(ξ * z) : ℝ) : ℂ) * I) * K z) :=
  hK.bdd_mul (c := 1) (by fun_prop) (Filter.Eventually.of_forall fun z => (norm_exp_ofReal_mul_I _).le)

section rung

variable {c χ x₀ d : ℝ} {g g₁ g₂ ω : ℝ → ℝ} {K : ℝ → ℂ}

/-- **Envelope on the window**: `|ω(x₀−z)ψ(x₀−z)| ≤ 1_{|z| ≤ d}·e^{2β_W d}R(x₀)`. -/
theorem abs_window_psi_le
    (hg : ∀ s ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (Set.uIcc (-1) 1))
    (hang : ∀ s ∈ Set.uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 0 < c) (hχc : χ < c ^ 2) (hd : 0 ≤ d) (hxd : 1 < x₀ - d) (hω : IsWindow ω x₀ d) (z : ℝ) :
    |ω (x₀ - z) * psi c g (x₀ - z)|
      ≤ (Icc (-d) d).indicator (fun _ => Real.exp (2 * betaW x₀ d * d) * rungAmp c χ g x₀) z := by
  have hzz : x₀ - z - x₀ = -z := by ring
  by_cases hz : |z| ≤ d
  · rw [indicator_of_mem (show z ∈ Icc (-d) d from abs_le.mp hz)]
    have hψ := abs_psi_le_exp hg hg₁ hg₂c hang hc hχc (x₀ := x₀) (x := x₀ - z) (y := x₀ - d) hxd
      (by linarith) (by linarith [le_abs_self z])
    rw [hzz, abs_neg] at hψ
    have hb := betaW_nonneg hxd
    have hR : 0 ≤ rungAmp c χ g x₀ := Real.sqrt_nonneg _
    have hexp : Real.exp (2 * ((x₀ - d) / ((x₀ - d) ^ 2 - 1)) * |z|) ≤ Real.exp (2 * betaW x₀ d * d) :=
      Real.exp_le_exp.mpr (by unfold betaW at hb ⊢; nlinarith)
    rw [abs_mul, abs_of_nonneg (hω.nonneg _)]
    calc ω (x₀ - z) * |psi c g (x₀ - z)| ≤ 1 * |psi c g (x₀ - z)| :=
          mul_le_mul_of_nonneg_right (hω.le_one _) (abs_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hψ.trans (mul_le_mul_of_nonneg_right hexp hR)
  · have h0 : ω (x₀ - z) = 0 := hω.eq_zero _ (by rw [hzz, abs_neg]; linarith)
    rw [h0, zero_mul, abs_zero]
    exact indicator_nonneg (fun _ _ => mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)) z

/-- **Pointwise transfer on the window**: `|ω(x₀−z)ψ(x₀−z) − (e^{−ikz}ψ⁺ + e^{ikz}ψ⁻)|
≤ (2β_W e^{β_W d}|z| + (c/2)Y'_W z²)R(x₀) + 1_{|z|>d/2}(e^{2β_W d}+1)R(x₀)`. -/
theorem norm_window_sub_le
    (hg : ∀ s ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (Set.uIcc (-1) 1))
    (hang : ∀ s ∈ Set.uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 0 < c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2) (hd : 0 ≤ d) (hxd : 1 < x₀ - d) (hω : IsWindow ω x₀ d)
    (z : ℝ) :
    ‖((ω (x₀ - z) * psi c g (x₀ - z) : ℝ) : ℂ)
        - (exp (((-(kP c χ x₀ * z) : ℝ) : ℂ) * I) * psiP c χ g x₀
          + exp (((-(-kP c χ x₀ * z) : ℝ) : ℂ) * I) * conj (psiP c χ g x₀))‖
      ≤ (2 * betaW x₀ d * Real.exp (betaW x₀ d * d) * |z| + c / 2 * chirpW x₀ d * z ^ 2) * rungAmp c χ g x₀
        + {z : ℝ | d / 2 < |z|}.indicator
            (fun _ => (Real.exp (2 * betaW x₀ d * d) + 1) * rungAmp c χ g x₀) z := by
  set t : ℝ := kP c χ x₀ * (x₀ - z - x₀) with ht
  have hzz : x₀ - z - x₀ = -z := by ring
  have e1 : (-(kP c χ x₀ * z) : ℝ) = t := by rw [ht, hzz]; ring
  have e2 : (-(-kP c χ x₀ * z) : ℝ) = -t := by rw [ht, hzz]; ring
  rw [e1, e2, ← two_re_exp_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hx₀ : 1 < x₀ := by linarith
  have hR : 0 ≤ rungAmp c χ g x₀ := Real.sqrt_nonneg _
  have hb := betaW_nonneg hxd
  have hy := chirpW_nonneg hd hxd
  have hfirst : 0 ≤ (2 * betaW x₀ d * Real.exp (betaW x₀ d * d) * |z| + c / 2 * chirpW x₀ d * z ^ 2)
      * rungAmp c χ g x₀ := by positivity
  by_cases hz : |z| ≤ d / 2
  · rw [indicator_of_notMem (show z ∉ {z : ℝ | d / 2 < |z|} from fun h => absurd h (not_lt.mpr hz)),
      add_zero]
    have h1 : ω (x₀ - z) = 1 := hω.eq_one _ (by rw [hzz, abs_neg]; exact hz)
    rw [h1, one_mul]
    have htr := psi_transfer hg hg₁ hg₂c hang hc hχc (x₀ := x₀) (x := x₀ - z) (y := x₀ - d / 2)
      (by linarith) (by linarith) (by linarith [le_abs_self z]) hχ
    rw [← ht] at htr
    rw [hzz, abs_neg, neg_sq] at htr
    -- `β_y ≤ β_W` and `e^{2β_y|z|} − 1 ≤ 2β_W|z| e^{β_W d}`
    set by_ := (x₀ - d / 2) / ((x₀ - d / 2) ^ 2 - 1) with hby
    have hby_le : by_ ≤ betaW x₀ d := div_sq_sub_one_anti hxd (by linarith)
    have hby0 : 0 ≤ by_ := by
      have : 0 < (x₀ - d / 2) ^ 2 - 1 := by nlinarith
      rw [hby]; exact div_nonneg (by linarith) this.le
    have hz0 := abs_nonneg z
    have hgrow : Real.exp (2 * by_ * |z|) - 1 ≤ 2 * betaW x₀ d * Real.exp (betaW x₀ d * d) * |z| := by
      refine exp_sub_one_le_mul_exp.trans ?_
      have hE : Real.exp (2 * by_ * |z|) ≤ Real.exp (betaW x₀ d * d) :=
        Real.exp_le_exp.mpr (by nlinarith [mul_le_mul hby_le (show 2 * |z| ≤ d by linarith) (by positivity) hb])
      have h2 : 2 * by_ * |z| ≤ 2 * betaW x₀ d * |z| := by nlinarith
      calc 2 * by_ * |z| * Real.exp (2 * by_ * |z|) ≤ 2 * betaW x₀ d * |z| * Real.exp (betaW x₀ d * d) :=
            mul_le_mul h2 hE (Real.exp_pos _).le (by positivity)
        _ = _ := by ring
    refine htr.trans (mul_le_mul_of_nonneg_right ?_ hR)
    have hch : c / 2 * ((x₀ - d / 2) / ((x₀ - d / 2) ^ 2 - 1) ^ 2) * z ^ 2 = c / 2 * chirpW x₀ d * z ^ 2 := rfl
    rw [hch]; linarith
  · rw [indicator_of_mem (show z ∈ {z : ℝ | d / 2 < |z|} from lt_of_not_ge hz)]
    have hw := abs_window_psi_le hg hg₁ hg₂c hang hc hχc hd hxd hω z
    have hw' : |ω (x₀ - z) * psi c g (x₀ - z)| ≤ Real.exp (2 * betaW x₀ d * d) * rungAmp c χ g x₀ := by
      refine hw.trans ?_
      by_cases hm : z ∈ Icc (-d) d
      · rw [indicator_of_mem hm]
      · rw [indicator_of_notMem hm]; positivity
    have hre : |2 * (exp ((t : ℂ) * I) * psiP c χ g x₀).re| ≤ rungAmp c χ g x₀ := by
      rw [abs_mul, abs_two]
      have h := Complex.abs_re_le_norm (exp ((t : ℂ) * I) * psiP c χ g x₀)
      rw [norm_mul, norm_exp_ofReal_mul_I, one_mul, norm_psiP hx₀ hc hχc] at h
      linarith
    calc _ ≤ _ := abs_sub (ω (x₀ - z) * psi c g (x₀ - z)) (2 * (exp ((t : ℂ) * I) * psiP c χ g x₀).re)
      _ ≤ _ := add_le_add hw' hre
      _ = (Real.exp (2 * betaW x₀ d * d) + 1) * rungAmp c χ g x₀ := by ring
      _ ≤ _ := le_add_of_nonneg_left hfirst

theorem integrable_window
    (hg : ∀ s ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (Set.uIcc (-1) 1))
    (hang : ∀ s ∈ Set.uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 0 < c) (hχc : χ < c ^ 2) (hd : 0 ≤ d) (hxd : 1 < x₀ - d) (hω : IsWindow ω x₀ d)
    (hK : Integrable K) :
    Integrable (fun z => K z * ((ω (x₀ - z) * psi c g (x₀ - z) : ℝ) : ℂ)) := by
  have hψc : Continuous (psi c g) := (Cvs.Prolate.Gram.RungGramFloorAtInfinity.rung_system hg hg₁ hg₂c hang).2.2.1
  have hm : Measurable fun z => ω (x₀ - z) * psi c g (x₀ - z) :=
    (hω.meas.comp (measurable_id.const_sub x₀)).mul (hψc.measurable.comp (measurable_id.const_sub x₀))
  refine hK.mul_bdd (c := Real.exp (2 * betaW x₀ d * d) * rungAmp c χ g x₀)
    (Complex.measurable_ofReal.comp hm).aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
  rw [Complex.norm_real, Real.norm_eq_abs]
  refine (abs_window_psi_le hg hg₁ hg₂c hang hc hχc hd hxd hω z).trans ?_
  by_cases hz : z ∈ Icc (-d) d
  · rw [indicator_of_mem hz]
  · rw [indicator_of_notMem hz]; exact mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)

theorem memLp_window
    (hg : ∀ s ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (Set.uIcc (-1) 1))
    (hang : ∀ s ∈ Set.uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 0 < c) (hχc : χ < c ^ 2) (hd : 0 ≤ d) (hxd : 1 < x₀ - d) (hω : IsWindow ω x₀ d) :
    MemLp (fun z => ω (x₀ - z) * psi c g (x₀ - z)) 2 := by
  have hψc : Continuous (psi c g) := (Cvs.Prolate.Gram.RungGramFloorAtInfinity.rung_system hg hg₁ hg₂c hang).2.2.1
  have hm : Measurable fun z => ω (x₀ - z) * psi c g (x₀ - z) :=
    (hω.meas.comp (measurable_id.const_sub x₀)).mul (hψc.measurable.comp (measurable_id.const_sub x₀))
  refine MemLp.of_le (memLp_indicator_const (s := Icc (-d) d) 2 measurableSet_Icc.nullMeasurableSet
    (Real.exp (2 * betaW x₀ d * d) * rungAmp c χ g x₀) (Or.inr measure_Icc_lt_top.ne))
    hm.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  exact (abs_window_psi_le hg hg₁ hg₂c hang hc hχc hd hxd hω z).trans (le_abs_self _)

/-- **LBT-h (A), per rung**: `|∫K(z)ω(x₀−z)ψ(x₀−z)dz − (μ(k)ψ⁺(x₀) + μ(−k)ψ⁻(x₀))| ≤ τ_K·R(x₀)`. -/
theorem rung_kernel
    (hg : ∀ s ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (Set.uIcc (-1) 1))
    (hang : ∀ s ∈ Set.uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 0 < c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2) (hd : 0 ≤ d) (hxd : 1 < x₀ - d) (hω : IsWindow ω x₀ d)
    (hK : Integrable K) (hK₁ : Integrable fun z => |z| * ‖K z‖) (hK₂ : Integrable fun z => z ^ 2 * ‖K z‖) :
    ‖(∫ z, K z * ((ω (x₀ - z) * psi c g (x₀ - z) : ℝ) : ℂ)) - sample K c χ g x₀‖
      ≤ tauK K c x₀ d * rungAmp c χ g x₀ := by
  set k := kP c χ x₀
  set ψp := psiP c χ g x₀
  set R := rungAmp c χ g x₀
  set S : Set ℝ := {z : ℝ | d / 2 < |z|}
  have hS : MeasurableSet S := measurableSet_lt measurable_const continuous_abs.measurable
  have hF := integrable_window hg hg₁ hg₂c hang hc hχc hd hxd hω hK
  have h1 := (integrable_exp_mul hK k).mul_const ψp
  have h2 := (integrable_exp_mul hK (-k)).mul_const (conj ψp)
  have e : (∫ z, K z * ((ω (x₀ - z) * psi c g (x₀ - z) : ℝ) : ℂ)) - sample K c χ g x₀
      = ∫ z, (K z * ((ω (x₀ - z) * psi c g (x₀ - z) : ℝ) : ℂ)
          - (exp (((-(k * z)) : ℝ) * I) * K z * ψp + exp (((-(-k * z)) : ℝ) * I) * K z * conj ψp)) := by
    have h12 : Integrable fun z => exp (((-(k * z)) : ℝ) * I) * K z * ψp
        + exp (((-(-k * z)) : ℝ) * I) * K z * conj ψp := h1.add h2
    rw [integral_sub hF h12, integral_add h1 h2, integral_mul_const, integral_mul_const]; rfl
  set A := 2 * betaW x₀ d * Real.exp (betaW x₀ d * d) * R
  set B := c / 2 * chirpW x₀ d * R
  set C := (Real.exp (2 * betaW x₀ d * d) + 1) * R
  have hpt : ∀ z, ‖K z * ((ω (x₀ - z) * psi c g (x₀ - z) : ℝ) : ℂ)
      - (exp (((-(k * z)) : ℝ) * I) * K z * ψp + exp (((-(-k * z)) : ℝ) * I) * K z * conj ψp)‖
      ≤ A * (|z| * ‖K z‖) + B * (z ^ 2 * ‖K z‖) + C * S.indicator (fun z => ‖K z‖) z := by
    intro z
    have h := norm_window_sub_le hg hg₁ hg₂c hang hc hχ hχc hd hxd hω z
    have e' : K z * ((ω (x₀ - z) * psi c g (x₀ - z) : ℝ) : ℂ)
        - (exp (((-(k * z)) : ℝ) * I) * K z * ψp + exp (((-(-k * z)) : ℝ) * I) * K z * conj ψp)
        = K z * (((ω (x₀ - z) * psi c g (x₀ - z) : ℝ) : ℂ)
          - (exp (((-(k * z)) : ℝ) * I) * ψp + exp (((-(-k * z)) : ℝ) * I) * conj ψp)) := by ring
    rw [e', norm_mul]
    refine (mul_le_mul_of_nonneg_left h (norm_nonneg _)).trans (le_of_eq ?_)
    by_cases hz : z ∈ S
    · rw [indicator_of_mem hz, indicator_of_mem hz]; ring
    · rw [indicator_of_notMem hz, indicator_of_notMem hz]; ring
  have hiA := hK₁.const_mul A
  have hiB := hK₂.const_mul B
  have hiC := (hK.norm.indicator hS).const_mul C
  have hiAB : Integrable fun z => A * (|z| * ‖K z‖) + B * (z ^ 2 * ‖K z‖) := hiA.add hiB
  have hiABC : Integrable fun z => A * (|z| * ‖K z‖) + B * (z ^ 2 * ‖K z‖)
      + C * S.indicator (fun z => ‖K z‖) z := hiAB.add hiC
  rw [e]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => norm_nonneg _)
    hiABC (Filter.Eventually.of_forall hpt)).trans (le_of_eq ?_)
  rw [integral_add hiAB hiC, integral_add hiA hiB, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_indicator hS]
  unfold tauK; ring

end rung

/-- **LBT-h (A), span form**: `|Σ aₙSₙ[μ]| ≤ ‖K‖₂‖ωΦ‖₂ + τ_K √(6J/(x₀²−1)) √P`,
`Φ = Σ aₙψₙ`, `P = Σ aₙ² ∫₁^X ψₙ²`, `J = #ι`. -/
theorem lbt_kernel {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    {X x₀ d : ℝ} {ω : ℝ → ℝ} {K : ℝ → ℂ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hX : 2 ≤ X)
    (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2) (hx₀ : x₀ ∈ Icc (6 / 5 : ℝ) X)
    (hd : 0 ≤ d) (hxd : 1 < x₀ - d) (hω : IsWindow ω x₀ d)
    (hK : Integrable K) (hKL2 : MemLp K 2)
    (hK₁ : Integrable fun z => |z| * ‖K z‖) (hK₂ : Integrable fun z => z ^ 2 * ‖K z‖) :
    ‖∑ i, (a i : ℂ) * sample K c (χ i) (g i) x₀‖
      ≤ √(∫ z, ‖K z‖ ^ 2) * √(∫ x, (ω x * ∑ i, a i * psi c (g i) x) ^ 2)
        + tauK K c x₀ d * √(6 * (Fintype.card ι : ℝ) / (x₀ ^ 2 - 1))
          * √(∑ i, a i ^ 2 * ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2) := by
  have hc0 : 0 < c := by linarith
  set m : ι → ℝ := fun i => ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2
  set F : ι → ℝ → ℝ := fun i z => ω (x₀ - z) * psi c (g i) (x₀ - z)
  set Ii : ι → ℂ := fun i => ∫ z, K z * ((F i z : ℝ) : ℂ)
  set G : ℝ → ℝ := fun z => ω (x₀ - z) * ∑ i, a i * psi c (g i) (x₀ - z)
  have hFi : ∀ i, Integrable fun z => K z * ((F i z : ℝ) : ℂ) := fun i =>
    integrable_window (hg i) (hg₁ i) (hg₂c i) (hang i) hc0 (hχc i) hd hxd hω hK
  -- the main term is the windowed span against the kernel
  have hmain : ∑ i, (a i : ℂ) * Ii i = ∫ z, K z * ((G z : ℝ) : ℂ) := by
    simp only [Ii, ← integral_const_mul]
    rw [← integral_finsetSum _ fun i _ => (hFi i).const_mul _]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [G, F, Finset.mul_sum]; push_cast
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have hGL2 : MemLp G 2 := by
    have h := memLp_finsetSum Finset.univ fun i _ =>
      (memLp_window (hg i) (hg₁ i) (hg₂c i) (hang i) hc0 (hχc i) hd hxd hω).const_mul (a i)
    refine h.ae_eq (Filter.Eventually.of_forall fun z => ?_)
    simp only [G, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have hCS : ‖∫ z, K z * ((G z : ℝ) : ℂ)‖
      ≤ √(∫ z, ‖K z‖ ^ 2) * √(∫ x, (ω x * ∑ i, a i * psi c (g i) x) ^ 2) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    have e : ∫ z, ‖K z * ((G z : ℝ) : ℂ)‖ = ∫ z, ‖K z‖ * |G z| := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [e]
    refine (Cvs.L2a.FarFarBound.integral_mul_abs_le (fun z => norm_nonneg _) hKL2.norm hGL2).trans (le_of_eq ?_)
    have hG2 : ∫ z, G z ^ 2 = ∫ x, (ω x * ∑ i, a i * psi c (g i) x) ^ 2 :=
      integral_sub_left_eq_self (fun x => (ω x * ∑ i, a i * psi c (g i) x) ^ 2) volume x₀
    exact congrArg (√(∫ z, ‖K z‖ ^ 2) * √·) hG2
  -- the transfer error, through the count envelope
  have hR : ∀ i, ‖Ii i - sample K c (χ i) (g i) x₀‖ ≤ tauK K c x₀ d * rungAmp c (χ i) (g i) x₀ := fun i =>
    rung_kernel (hg i) (hg₁ i) (hg₂c i) (hang i) hc0 (hχ0 i) (hχc i) hd hxd hω hK hK₁ hK₂
  have hτ := tauK_nonneg K hc0.le hd hxd
  have hJ : 0 ≤ 6 * (Fintype.card ι : ℝ) / (x₀ ^ 2 - 1) := by
    have : 0 < x₀ ^ 2 - 1 := by nlinarith [hx₀.1]
    positivity
  have herr := norm_sum_le_mass a (fun i => Ii i - sample K c (χ i) (g i) x₀)
    (fun i => tauK K c x₀ d * rungAmp c (χ i) (g i) x₀) m hM hR
  rw [massSum_const_mul] at herr
  have henv := count_envelope hg hg₁ hg₂c hang hc hχ0 hχc hX hM hx₀
  have hsq : √(tauK K c x₀ d ^ 2 * massSum (fun i => rungAmp c (χ i) (g i) x₀) m)
      ≤ tauK K c x₀ d * √(6 * (Fintype.card ι : ℝ) / (x₀ ^ 2 - 1)) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hτ]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt henv) hτ
  have hsplit : ∑ i, (a i : ℂ) * sample K c (χ i) (g i) x₀
      = ∑ i, (a i : ℂ) * Ii i - ∑ i, (a i : ℂ) * (Ii i - sample K c (χ i) (g i) x₀) := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit, hmain]
  refine (norm_sub_le _ _).trans (add_le_add hCS (herr.trans ?_))
  rw [mul_comm (√(∑ i, a i ^ 2 * m i))]
  exact mul_le_mul_of_nonneg_right hsq (Real.sqrt_nonneg _)

end Cvs.L2a.BandTransferKernelForm
