import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Lattice sampling of a band-limited transform

For `φ ∈ L²(−a, a]` and a lattice `nD + θ` with `aD ≤ π`, the samples of `F(t) = ∫_{−a}^{a} φ(u) e^{iut} du`
satisfy `∑ₙ |F(nD + θ)|² = (2π/D) ∫_{−a}^{a} |φ|²`, for every phase `θ`: each sample is `2π/D` times a
Fourier coefficient of `φ(u)e^{iuθ}` on the period `[−π/D, π/D]`, and Parseval sums them.
-/

noncomputable section

open MeasureTheory Set Complex

namespace Cvs.Upstream.BandLimitedLatticeSampling

/-- The band-limited transform `F(t) = ∫_{(−a, a]} φ(u) e^{iut} du`. -/
def bandT (a : ℝ) (φ : ℝ → ℂ) (t : ℝ) : ℂ := ∫ u in Ioc (-a) a, φ u * cexp (↑u * ↑t * I)

/-- **Each sample is a Fourier coefficient**: `F(nD + θ) = (2π/D) ĉ_{−n}` for `φ(u)e^{iuθ}` extended by
zero to the period `(−π/D, π/D]`. -/
theorem bandT_eq_fourierCoeffOn {a D : ℝ} (hD : 0 < D) (haD : a * D ≤ Real.pi) (θ : ℝ) (φ : ℝ → ℂ)
    (n : ℤ) :
    bandT a φ (n * D + θ) =
      ((2 * Real.pi / D : ℝ) : ℂ) • fourierCoeffOn (neg_lt_self (by positivity : 0 < Real.pi / D))
        ((Ioc (-a) a).indicator fun u => φ u * cexp (↑u * ↑θ * I)) (-n) := by
  have hpD : 0 < Real.pi / D := by positivity
  have ha : a ≤ Real.pi / D := (le_div_iff₀ hD).2 haD
  have hsub : Ioc (-a) a ⊆ Ioc (-(Real.pi / D)) (Real.pi / D) := Ioc_subset_Ioc (neg_le_neg ha) ha
  have hT : Real.pi / D - -(Real.pi / D) = 2 * Real.pi / D := by ring
  have hind : ∀ x : ℝ, fourier (-(-n)) (x : AddCircle (Real.pi / D - -(Real.pi / D))) •
      (Ioc (-a) a).indicator (fun u => φ u * cexp (↑u * ↑θ * I)) x
      = (Ioc (-a) a).indicator (fun u => φ u * cexp (↑u * ↑(n * D + θ) * I)) x := by
    intro x
    by_cases hx : x ∈ Ioc (-a) a
    · rw [indicator_of_mem hx, indicator_of_mem hx, fourier_coe_apply, smul_eq_mul, hT]
      rw [mul_comm, mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      field_simp
      ring
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, smul_zero]
  have hI : ∫ x : ℝ in -(Real.pi / D)..(Real.pi / D), fourier (-(-n)) (x : AddCircle (Real.pi / D - -(Real.pi / D))) •
      (Ioc (-a) a).indicator (fun u => φ u * cexp (↑u * ↑θ * I)) x = bandT a φ (n * D + θ) := by
    simp_rw [hind]
    rw [intervalIntegral.integral_of_le (neg_lt_self hpD).le, setIntegral_indicator measurableSet_Ioc,
      inter_eq_right.2 hsub]
    rfl
  rw [fourierCoeffOn_eq_integral, hI, hT, Complex.real_smul, smul_eq_mul, ← mul_assoc, ← Complex.ofReal_mul,
    show 2 * Real.pi / D * (1 / (2 * Real.pi / D)) = 1 by field_simp, Complex.ofReal_one, one_mul]

/-- **Lattice sampling identity (Plancherel–Pólya on a lattice)**: for `aD ≤ π` and any phase `θ`,
`∑ₙ |F(nD + θ)|² = (2π/D) ∫_{−a}^{a} |φ|²`. -/
theorem hasSum_sq_bandT {a D : ℝ} (hD : 0 < D) (haD : a * D ≤ Real.pi) (θ : ℝ) {φ : ℝ → ℂ}
    (hφ : MemLp φ 2 (volume.restrict (Ioc (-a) a))) :
    HasSum (fun n : ℤ => ‖bandT a φ (n * D + θ)‖ ^ 2) (2 * Real.pi / D * ∫ u in Ioc (-a) a, ‖φ u‖ ^ 2) := by
  have hpD : 0 < Real.pi / D := by positivity
  have ha : a ≤ Real.pi / D := (le_div_iff₀ hD).2 haD
  have hsub : Ioc (-a) a ⊆ Ioc (-(Real.pi / D)) (Real.pi / D) := Ioc_subset_Ioc (neg_le_neg ha) ha
  have hab := neg_lt_self hpD
  set ψ := (Ioc (-a) a).indicator fun u => φ u * cexp (↑u * ↑θ * I)
  have hnorm : ∀ u : ℝ, ‖φ u * cexp (↑u * ↑θ * I)‖ = ‖φ u‖ := fun u => by
    rw [norm_mul, show (↑u * ↑θ * I : ℂ) = ↑(u * θ) * I by push_cast; ring, Complex.norm_exp_ofReal_mul_I,
      mul_one]
  have hψ : MemLp ψ 2 (volume.restrict (Ioc (-(Real.pi / D)) (Real.pi / D))) := by
    refine ((memLp_indicator_iff_restrict measurableSet_Ioc.nullMeasurableSet).2 ?_).restrict _
    refine hφ.of_le (hφ.aestronglyMeasurable.mul (by fun_prop : Continuous fun u : ℝ => cexp (↑u * ↑θ * I)).aestronglyMeasurable)
      (ae_of_all _ fun u => (hnorm u).le)
  have hP := hasSum_sq_fourierCoeffOn hab hψ
  have hP' := ((Equiv.neg ℤ).hasSum_iff.2 hP).mul_left ((2 * Real.pi / D) ^ 2)
  have hint : ∫ x in -(Real.pi / D)..(Real.pi / D), ‖ψ x‖ ^ 2 = ∫ u in Ioc (-a) a, ‖φ u‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hab.le]
    have : (fun x => ‖ψ x‖ ^ 2) = (Ioc (-a) a).indicator fun u => ‖φ u‖ ^ 2 := by
      funext x
      by_cases hx : x ∈ Ioc (-a) a
      · simp only [ψ, indicator_of_mem hx, hnorm]
      · simp [ψ, indicator_of_notMem hx]
    rw [this, setIntegral_indicator measurableSet_Ioc, inter_eq_right.2 hsub]
  rw [hint, smul_eq_mul, show Real.pi / D - -(Real.pi / D) = 2 * Real.pi / D by ring,
    show (2 * Real.pi / D) ^ 2 * ((2 * Real.pi / D)⁻¹ * ∫ u in Ioc (-a) a, ‖φ u‖ ^ 2)
      = 2 * Real.pi / D * ∫ u in Ioc (-a) a, ‖φ u‖ ^ 2 by field_simp] at hP'
  have hf : (fun n : ℤ => ‖bandT a φ (n * D + θ)‖ ^ 2)
      = fun i => (2 * Real.pi / D) ^ 2 * ((fun i => ‖fourierCoeffOn hab ψ i‖ ^ 2) ∘ Equiv.neg ℤ) i := by
    funext n
    simp only [Function.comp_apply, Equiv.neg_apply]
    rw [bandT_eq_fourierCoeffOn hD haD θ φ n, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      sq_abs]
  rw [hf]
  exact hP'

end Cvs.Upstream.BandLimitedLatticeSampling
