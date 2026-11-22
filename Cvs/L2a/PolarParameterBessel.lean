import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.SpanPlungeBound
import Cvs.Prolate.AngularBesselInequality
import Cvs.Prolate.CosineChristoffelDarboux
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.SlepianEvenOrdering

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# E3: the polar parameter is bounded by Bessel's inequality

For a pole-free span `G = Σ bᵢhᵢ` (`∫ G = 0`) of normalised even angular eigenfunctions with ground `h₀`, `∫ h = μh(0)`
gives `G(0) = Σ_{i≠0} bᵢhᵢ(0)(1 − τᵢ/τ₀)`; ORD gives `(1 − τᵢ/τ₀)² ≤ 1 − λᵢ`; Bessel gives `Σ λᵢhᵢ(0)² ≤ c/π`; and
`∫₁^∞ψᵢ² = (π/c)(1 − λᵢ)`. Hence `(2π/c)²G(0)² ≤ (4/λ_min)∫₁^∞ψ_G²`, and with a floor `κP_∞ ≤ N_∞`,
`(2π/c)|G(0)| ≤ (2/√(κλ_min))√N_∞`. On the deep span (`c ≥ 80`, `c² − χ ≥ 5c`) Cvs.L2a.SpanPlungeBound gives `λ_min = (993/1000)²`.
-/

noncomputable section

open Real Set Filter MeasureTheory Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.RegularSolutionEdge Cvs.Prolate.EdgeCentreSign

namespace Cvs.L2a.PolarParameterBessel

/-! ### The algebra -/

/-- **The centre value of a pole-free span**: if `Σ bᵢμᵢvᵢ = 0` and `μ_{i₀} ≠ 0`, then
`Σ bᵢvᵢ = Σ_{i ≠ i₀} bᵢvᵢ(1 − μᵢ/μ_{i₀})`. -/
theorem centre_eq_of_pole {ι : Type*} [Fintype ι] [DecidableEq ι] (i₀ : ι) (b v μ : ι → ℝ) (hμ₀ : μ i₀ ≠ 0)
    (hpole : ∑ i, b i * (μ i * v i) = 0) :
    ∑ i, b i * v i = ∑ i ∈ Finset.univ.erase i₀, b i * v i * (1 - μ i / μ i₀) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)] at hpole ⊢
  have e : ∑ i ∈ Finset.univ.erase i₀, b i * v i * (1 - μ i / μ i₀)
      = ∑ i ∈ Finset.univ.erase i₀, b i * v i - (∑ i ∈ Finset.univ.erase i₀, b i * (μ i * v i)) / μ i₀ := by
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  rw [e]
  have h0 : b i₀ * v i₀ = -(∑ i ∈ Finset.univ.erase i₀, b i * (μ i * v i)) / μ i₀ := by
    rw [eq_div_iff hμ₀]
    linear_combination hpole
  rw [h0]; ring

/-- **Weighted Cauchy–Schwarz against Bessel**: if `wᵢ² ≤ 1 − λᵢ`, `m ≤ λᵢ` with `m > 0` and `Σ λᵢvᵢ² ≤ K`, then
`(Σ bᵢvᵢwᵢ)² ≤ (Σ bᵢ²(1 − λᵢ))·K/m`. -/
theorem sq_sum_le_of_bessel {ι : Type*} (S : Finset ι) (b v w lam : ι → ℝ) {K m : ℝ} (hm : 0 < m)
    (hw : ∀ i ∈ S, w i ^ 2 ≤ 1 - lam i) (hmin : ∀ i ∈ S, m ≤ lam i)
    (hB : ∑ i ∈ S, lam i * v i ^ 2 ≤ K) :
    (∑ i ∈ S, b i * v i * w i) ^ 2 ≤ (∑ i ∈ S, b i ^ 2 * (1 - lam i)) * (K / m) := by
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq S (fun i => b i * w i) v
  have e : ∑ i ∈ S, b i * v i * w i = ∑ i ∈ S, b i * w i * v i :=
    Finset.sum_congr rfl fun i _ => by ring
  have h1 : ∑ i ∈ S, (b i * w i) ^ 2 ≤ ∑ i ∈ S, b i ^ 2 * (1 - lam i) :=
    Finset.sum_le_sum fun i hi => by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_left (hw i hi) (sq_nonneg _)
  have h2 : ∑ i ∈ S, v i ^ 2 ≤ K / m := by
    rw [le_div_iff₀ hm]
    calc (∑ i ∈ S, v i ^ 2) * m = ∑ i ∈ S, m * v i ^ 2 := by rw [Finset.sum_mul]; simp [mul_comm]
      _ ≤ ∑ i ∈ S, lam i * v i ^ 2 :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hmin i hi) (sq_nonneg _)
      _ ≤ K := hB
  have h0 : 0 ≤ ∑ i ∈ S, (b i * w i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [e]
  calc (∑ i ∈ S, b i * w i * v i) ^ 2 ≤ (∑ i ∈ S, (b i * w i) ^ 2) * ∑ i ∈ S, v i ^ 2 := hCS
    _ ≤ (∑ i ∈ S, b i ^ 2 * (1 - lam i)) * (K / m) :=
      mul_le_mul h1 h2 (Finset.sum_nonneg fun i _ => sq_nonneg _) (h0.trans h1)

/-! ### E3 on the angular spectrum -/

/-- A function with `∫_{−1}^{1} g² = 1` is somewhere nonzero on `[−1, 1]`. -/
theorem exists_ne_zero_of_norm {g : ℝ → ℝ} (hnorm : ∫ s in (-1 : ℝ)..1, g s ^ 2 = 1) :
    ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have : ∫ s in (-1 : ℝ)..1, g s ^ 2 = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun s hs => by
      rw [uIcc_of_le (by norm_num)] at hs; simp [hcon s hs]]
    simp
  linarith

/-- **E3, mass form**: for normalised even angular eigenfunctions `hᵢ` at distinct even-index levels, `h_{i₀}` the
ground state, eigenvalues `λᵢ ≥ λ_min > 0` off `i₀`, and a pole-free span (`Σ bᵢ∫hᵢ = 0`),
`(2π/c)²(Σ bᵢhᵢ(0))² ≤ (4/λ_min) Σ bᵢ² ∫₁^∞ψᵢ²`. -/
theorem centre_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι] (i₀ : ι) {h h₁ h₂ : ι → ℝ → ℝ} {c lmin : ℝ}
    {χ μ : ι → ℝ} (b : ι → ℝ) (hc : 0 < c)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (h i) (h₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (h₁ i) (h₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (h₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * h₂ i s - 2 * s * h₁ i s - c ^ 2 * s ^ 2 * h i s + χ i * h i s = 0)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, h i (-s) = h i s)
    (hnorm : ∀ i, ∫ s in (-1 : ℝ)..1, h i s ^ 2 = 1) (hχ : Function.Injective χ)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (h i) s = μ i * h i s)
    (hground : (evenSpec (sqC c) ∩ Iio (χ i₀)).ncard = 0)
    (hidx : ∀ i, Even (evenSpec (sqC c) ∩ Iio (χ i)).ncard)
    (hlmin : 0 < lmin) (hlam : ∀ i, i ≠ i₀ → lmin ≤ (μ i * √(c / (2 * π))) ^ 2)
    (hpole : ∑ i, b i * ∫ s in (-1 : ℝ)..1, h i s = 0) :
    (2 * π / c) ^ 2 * (∑ i, b i * h i 0) ^ 2 ≤ 4 / lmin * ∑ i, b i ^ 2 * ∫ ξ in Ioi 1, psi c (h i) ξ ^ 2 := by
  classical
  set S := Finset.univ.erase i₀ with hS
  set k := √(c / (2 * π)) with hk
  have hk0 : 0 < k := Real.sqrt_pos.2 (by positivity)
  have hg0 : ∀ i, ∃ s ∈ Icc (-1 : ℝ) 1, h i s ≠ 0 := fun i => exists_ne_zero_of_norm (hnorm i)
  have hgc : ∀ i, ContinuousOn (h i) (Icc (-1 : ℝ) 1) := fun i =>
    Cvs.Prolate.CosineChristoffelDarboux.continuousOn_of_hasDerivAt (hg i)
  have hμ₀ : 0 < μ i₀ := Cvs.Prolate.SlepianEvenOrdering.mu_pos_of_even_index hc (hg i₀) (hg₁ i₀) (hg₂c i₀) (hang i₀)
    (heven i₀) (hg0 i₀) (hμ i₀) (hidx i₀)
  -- the centre value
  have hpole' : ∑ i, b i * (μ i * h i 0) = 0 :=
    (Finset.sum_congr rfl fun i _ => by rw [Cvs.Prolate.AngularBesselInequality.integral_eq_mu_mul (hμ i)]).trans hpole
  have hcentre := centre_eq_of_pole i₀ b (fun i => h i 0) μ hμ₀.ne' hpole'
  -- the ORD weight
  have hw : ∀ i ∈ S, (1 - μ i / μ i₀) ^ 2 ≤ 1 - (μ i * k) ^ 2 := by
    intro i _
    have := Cvs.Prolate.SlepianEvenOrdering.one_sub_tau_div_sq_le hc (hg i₀) (hg₁ i₀) (hg₂c i₀) (hang i₀) (heven i₀)
      (hg0 i₀) (hg i) (hg₁ i) (hg₂c i) (hang i) (heven i) (hg0 i) (hμ i₀) (hμ i) hground (hidx i)
    rwa [mul_div_mul_right _ _ hk0.ne'] at this
  -- Bessel on the span
  have hB := Cvs.Prolate.AngularBesselInequality.sum_lam_mul_sq_le S hc hg hg₁ hang (hχ.injOn) (fun i _ => hnorm i)
    (fun i _ => hμ i)
  have hmin : ∀ i ∈ S, lmin ≤ (μ i * k) ^ 2 := fun i hi => hlam i (Finset.ne_of_mem_erase hi)
  have hsq := sq_sum_le_of_bessel S b (fun i => h i 0) (fun i => 1 - μ i / μ i₀) (fun i => (μ i * k) ^ 2)
    hlmin hw hmin hB
  -- masses
  have hM : ∀ i, ∫ ξ in Ioi 1, psi c (h i) ξ ^ 2 = π / c * (1 - (μ i * k) ^ 2) := fun i =>
    Cvs.Prolate.AngularBesselInequality.mass_eq hc (hgc i) (heven i) (hμ i) (hnorm i)
  have hMnn : ∀ i, 0 ≤ ∫ ξ in Ioi 1, psi c (h i) ξ ^ 2 := fun i =>
    setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have hsumS : ∑ i ∈ S, b i ^ 2 * (1 - (μ i * k) ^ 2)
      = c / π * ∑ i ∈ S, b i ^ 2 * ∫ ξ in Ioi 1, psi c (h i) ξ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hM i]; field_simp
  have hsub : ∑ i ∈ S, b i ^ 2 * ∫ ξ in Ioi 1, psi c (h i) ξ ^ 2
      ≤ ∑ i, b i ^ 2 * ∫ ξ in Ioi 1, psi c (h i) ξ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      fun i _ _ => mul_nonneg (sq_nonneg _) (hMnn i)
  rw [hcentre]
  rw [hsumS] at hsq
  set P := ∑ i, b i ^ 2 * ∫ ξ in Ioi 1, psi c (h i) ξ ^ 2
  set PS := ∑ i ∈ S, b i ^ 2 * ∫ ξ in Ioi 1, psi c (h i) ξ ^ 2
  set G := ∑ i ∈ S, b i * h i 0 * (1 - μ i / μ i₀)
  have hPS0 : 0 ≤ PS := Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hMnn i)
  have hcp : 0 < c / π := by positivity
  have hstep : G ^ 2 ≤ c / π * P * (c / π / lmin) :=
    hsq.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsub hcp.le) (by positivity))
  have ha : 0 ≤ (2 * π / c) ^ 2 := sq_nonneg _
  calc (2 * π / c) ^ 2 * G ^ 2 ≤ (2 * π / c) ^ 2 * (c / π * P * (c / π / lmin)) :=
        mul_le_mul_of_nonneg_left hstep ha
    _ = 4 / lmin * P := by field_simp; ring

/-- **E3 against a frame floor**: if `κ Σ bᵢ²∫₁^∞ψᵢ² ≤ N` with `κ > 0`, then
`(2π/c)|G(0)| ≤ (2/√(κλ_min))√N`, i.e. `ε ≤ 2/√(κλ_min)`. -/
theorem polar_eps_le_of_floor {ι : Type*} [Fintype ι] [DecidableEq ι] (i₀ : ι) {h h₁ h₂ : ι → ℝ → ℝ}
    {c lmin κ N : ℝ} {χ μ : ι → ℝ} (b : ι → ℝ) (hc : 0 < c)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (h i) (h₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (h₁ i) (h₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (h₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * h₂ i s - 2 * s * h₁ i s - c ^ 2 * s ^ 2 * h i s + χ i * h i s = 0)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, h i (-s) = h i s)
    (hnorm : ∀ i, ∫ s in (-1 : ℝ)..1, h i s ^ 2 = 1) (hχ : Function.Injective χ)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (h i) s = μ i * h i s)
    (hground : (evenSpec (sqC c) ∩ Iio (χ i₀)).ncard = 0)
    (hidx : ∀ i, Even (evenSpec (sqC c) ∩ Iio (χ i)).ncard)
    (hlmin : 0 < lmin) (hlam : ∀ i, i ≠ i₀ → lmin ≤ (μ i * √(c / (2 * π))) ^ 2)
    (hpole : ∑ i, b i * ∫ s in (-1 : ℝ)..1, h i s = 0)
    (hκ : 0 < κ) (hfloor : κ * ∑ i, b i ^ 2 * (∫ ξ in Ioi 1, psi c (h i) ξ ^ 2) ≤ N) :
    2 * π / c * |∑ i, b i * h i 0| ≤ 2 / √(κ * lmin) * √N := by
  have hsq := centre_sq_le i₀ b hc hg hg₁ hg₂c hang heven hnorm hχ hμ hground hidx hlmin hlam hpole
  set P := ∑ i, b i ^ 2 * (∫ ξ in Ioi 1, psi c (h i) ξ ^ 2)
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun i _ =>
    mul_nonneg (sq_nonneg _) (setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _)
  have hN0 : 0 ≤ N := (mul_nonneg hκ.le hP0).trans hfloor
  have hPN : P ≤ N / κ := by rw [le_div_iff₀ hκ]; linarith
  have e1 : (2 * π / c * |∑ i, b i * h i 0|) ^ 2 = (2 * π / c) ^ 2 * (∑ i, b i * h i 0) ^ 2 := by
    rw [mul_pow, sq_abs]
  have e2 : (2 / √(κ * lmin) * √N) ^ 2 = 2 ^ 2 / (κ * lmin) * N := by
    rw [mul_pow, div_pow, sq_sqrt (by positivity : (0 : ℝ) ≤ κ * lmin), sq_sqrt hN0]
  have hsq' : (2 * π / c * |∑ i, b i * h i 0|) ^ 2 ≤ (2 / √(κ * lmin) * √N) ^ 2 := by
    rw [e1, e2]
    calc (2 * π / c) ^ 2 * (∑ i, b i * h i 0) ^ 2 ≤ 4 / lmin * P := hsq
      _ ≤ 4 / lmin * (N / κ) := mul_le_mul_of_nonneg_left hPN (by positivity)
      _ = 2 ^ 2 / (κ * lmin) * N := by field_simp; ring
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hsq'

/-! ### The deep span: `λ_min = (993/1000)²` -/

/-- **`λ_min` on the deep span** (Cvs.L2a.SpanPlungeBound): an even-index rung with `c ≥ 80`, `5c ≤ c² − χ` has
`(993/1000)² ≤ (μ√(c/2π))²`. -/
theorem lam_ge_deep {ι : Type*} {h h₁ h₂ : ι → ℝ → ℝ} {c : ℝ} {χ μ : ι → ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (h i) (h₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (h₁ i) (h₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (h₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * h₂ i s - 2 * s * h₁ i s - c ^ 2 * s ^ 2 * h i s + χ i * h i s = 0)
    (hc : 80 ≤ c) (hσ : ∀ i, 5 * c ≤ c ^ 2 - χ i)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, h i (-s) = h i s) (hg0 : ∀ i, ∃ s ∈ Icc (-1 : ℝ) 1, h i s ≠ 0)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (h i) s = μ i * h i s)
    (hidx : ∀ i, Even (evenSpec (sqC c) ∩ Iio (χ i)).ncard) :
    ∀ i, (993 / 1000 : ℝ) ^ 2 ≤ (μ i * √(c / (2 * π))) ^ 2 := by
  have hχ0 : ∀ i, 0 ≤ χ i := fun i => Cvs.Prolate.SlepianEvenOrdering.nonneg_of_mem_evenSpec c
    (mem_evenSpec_of_angular (hg i) (hg₁ i) (hang i) (heven i) (hg0 i))
  have hτ := Cvs.L2a.SpanPlungeBound.epsTau_P2flat hg hg₁ hg₂c hang hc le_rfl hχ0 hσ heven hg0 hμ hidx
  intro i
  have h1 := hτ i
  have h2 := Cvs.L2a.SpanPlungeBound.epsTauFlat_five_le
  exact pow_le_pow_left₀ (by norm_num) (by linarith) 2

end Cvs.L2a.PolarParameterBessel
