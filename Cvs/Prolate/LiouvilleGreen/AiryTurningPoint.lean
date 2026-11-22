import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.Compact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The turning-point crossing in Airy units

For `((ξ² − 1)ψ')' + (c²ξ² − c²a²)ψ = 0` on `[s, a]` with `ψ(a), ψ'(a)·(a² − 1) ≥ 0`,
`ψ(s) ≥ (1 − ac²(a − s)³/(3(1 − a²)))ψ(a)`. In the units `l³ = (1 − a²)/(2ac²)`, `g = 2al/(1 − a²)`,
`ε = l/(2a)` this reads `ψ(a − θl) ≥ (1 − θ³/6)ψ(a)`, with window mass `c∫ψ² ≥ m(θ)ψ(a)²/√g`.
-/

namespace Cvs.Prolate.LiouvilleGreen.AiryTurningPoint

open Real Set Filter Topology intervalIntegral Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-- The real cube root of a nonnegative number, `x^{1/3}`. -/
noncomputable def cbrt (x : ℝ) : ℝ := x ^ ((3 : ℝ)⁻¹)

theorem cbrt_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ cbrt x := rpow_nonneg hx _

theorem cbrt_pos {x : ℝ} (hx : 0 < x) : 0 < cbrt x := rpow_pos_of_pos hx _

theorem cbrt_pow_three {x : ℝ} (hx : 0 ≤ x) : cbrt x ^ 3 = x := by
  have h := Real.rpow_inv_natCast_pow hx (n := 3) (by norm_num)
  simpa [cbrt] using h

theorem le_cbrt_iff {r x : ℝ} (hr : 0 ≤ r) (hx : 0 ≤ x) : r ≤ cbrt x ↔ r ^ 3 ≤ x := by
  rw [← pow_le_pow_iff_left₀ hr (cbrt_nonneg hx) (by norm_num : (3 : ℕ) ≠ 0), cbrt_pow_three hx]

theorem cbrt_le_iff {r x : ℝ} (hr : 0 ≤ r) (hx : 0 ≤ x) : cbrt x ≤ r ↔ x ≤ r ^ 3 := by
  rw [← pow_le_pow_iff_left₀ (cbrt_nonneg hx) hr (by norm_num : (3 : ℕ) ≠ 0), cbrt_pow_three hx]

/-- The Airy length `l = ((1 − a²)/(2ac²))^{1/3}`. -/
noncomputable def airyL (c a : ℝ) : ℝ := cbrt ((1 - a ^ 2) / (2 * a * c ^ 2))

/-- The Airy rate `g = 2al/(1 − a²)`. -/
noncomputable def airyG (c a : ℝ) : ℝ := 2 * a * airyL c a / (1 - a ^ 2)

/-- The relative Airy width `ε = l/(2a)`. -/
noncomputable def airyEps (c a : ℝ) : ℝ := airyL c a / (2 * a)

theorem airyL_pos {c a : ℝ} (hc : 0 < c) (ha : 0 < a) (ha1 : a < 1) : 0 < airyL c a := by
  have : 0 < 1 - a ^ 2 := by nlinarith
  exact cbrt_pos (by positivity)

theorem airyG_pos {c a : ℝ} (hc : 0 < c) (ha : 0 < a) (ha1 : a < 1) : 0 < airyG c a := by
  have : 0 < 1 - a ^ 2 := by nlinarith
  have := airyL_pos hc ha ha1
  unfold airyG; positivity

theorem airyEps_pos {c a : ℝ} (hc : 0 < c) (ha : 0 < a) (ha1 : a < 1) : 0 < airyEps c a := by
  have := airyL_pos hc ha ha1
  unfold airyEps; positivity

theorem airyL_cube {c a : ℝ} (hc : 0 < c) (ha : 0 < a) (ha1 : a < 1) :
    2 * a * c ^ 2 * airyL c a ^ 3 = 1 - a ^ 2 := by
  have : 0 < 1 - a ^ 2 := by nlinarith
  unfold airyL
  rw [cbrt_pow_three (by positivity)]
  field_simp

theorem airyG_mul {c a : ℝ} (hc : 0 < c) (ha : 0 < a) (ha1 : a < 1) :
    c ^ 2 * airyL c a ^ 2 * airyG c a = 1 := by
  have hA : 0 < 1 - a ^ 2 := by nlinarith
  have h := airyL_cube hc ha ha1
  have hl := airyL_pos hc ha ha1
  unfold airyG
  rw [← h]
  field_simp

theorem airyG_cube {c a : ℝ} (hc : 0 < c) (ha : 0 < a) (ha1 : a < 1) :
    airyG c a ^ 3 * (c * (1 - a ^ 2)) ^ 2 = 4 * a ^ 2 := by
  have hA : 0 < 1 - a ^ 2 := by nlinarith
  have h := airyL_cube hc ha ha1
  have hl := airyL_pos hc ha ha1
  unfold airyG
  rw [← h]
  field_simp
  ring

theorem airyEps_cube {c a : ℝ} (hc : 0 < c) (ha : 0 < a) (ha1 : a < 1) :
    airyEps c a ^ 3 * (16 * a ^ 4 * c ^ 2) = 1 - a ^ 2 := by
  have h := airyL_cube hc ha ha1
  have hl := airyL_pos hc ha ha1
  unfold airyEps
  rw [← h]
  field_simp
  ring

/-- The window-mass polynomial `m(θ) = θ − θ⁴/12 + θ⁷/252`, `m(1) = 58/63`. -/
noncomputable def mth (θ : ℝ) : ℝ := θ - θ ^ 4 / 12 + θ ^ 7 / 252

/-- **The turning-point crossing**: below the turning point `a` the solution loses at most the
fraction `ac²(a − s)³/(3(1 − a²))` of `ψ(a)`. -/
theorem turning_crossing {ψ u : ℝ → ℝ} {c χ a s : ℝ} (hc : 0 < c) (ha : 0 < a) (ha1 : a < 1)
    (hχ : χ = c ^ 2 * a ^ 2) (hs0 : 0 ≤ s) (hsa : s ≤ a)
    (hψ : ∀ t ∈ Icc s a, HasDerivAt ψ (u t / pP t) t)
    (hu : ∀ t ∈ Icc s a, HasDerivAt u (-(qP c χ t * ψ t)) t)
    (hψa : 0 ≤ ψ a) (hua : 0 ≤ u a) (hX : a * c ^ 2 * (a - s) ^ 3 ≤ 3 * (1 - a ^ 2)) :
    (1 - a * c ^ 2 * (a - s) ^ 3 / (3 * (1 - a ^ 2))) * ψ a ≤ ψ s := by
  have hA : 0 < 1 - a ^ 2 := by nlinarith
  set X := a * c ^ 2 * (a - s) ^ 3 / (3 * (1 - a ^ 2)) with hXdef
  have hX0 : 0 ≤ X := by
    have : 0 ≤ a - s := by linarith
    positivity
  have hX1 : X ≤ 1 := by rw [hXdef, div_le_one (by positivity)]; exact hX
  -- continuity of ψ and u on [s, a]
  have hψc : ContinuousOn ψ (Icc s a) := fun t ht => (hψ t ht).continuousAt.continuousWithinAt
  have huc : ContinuousOn u (Icc s a) := fun t ht => (hu t ht).continuousAt.continuousWithinAt
  obtain ⟨t₀, ht₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hsa) hψc
  set M := ψ t₀ with hMdef
  have hMa : ψ a ≤ M := hmax (right_mem_Icc.mpr hsa)
  have hM0 : 0 ≤ M := hψa.trans hMa
  rcases eq_or_lt_of_le ht₀.1 with hst | hst
  · -- the maximum sits at `s`
    have hsM : ψ s = M := by rw [hMdef, hst]
    rw [hsM]
    nlinarith
  -- otherwise `u t₀ ≥ 0`
  have hut₀ : 0 ≤ u t₀ := by
    rcases eq_or_lt_of_le ht₀.2 with hta | hta
    · rw [hta]; exact hua
    · have hloc : IsLocalMax ψ t₀ := hmax.isLocalMax (Icc_mem_nhds hst hta)
      have h0 := hloc.hasDerivAt_eq_zero (hψ t₀ ht₀)
      have hp : pP t₀ ≠ 0 := by
        unfold pP; nlinarith [ht₀.1]
      rw [div_eq_zero_iff] at h0
      rcases h0 with h0 | h0
      · rw [h0]
      · exact absurd h0 hp
  have hsub : Icc s t₀ ⊆ Icc s a := Icc_subset_Icc le_rfl ht₀.2
  have hint : interior (Icc s t₀) = Ioo s t₀ := interior_Icc
  -- (1) `u t + M a c² (a − t)²` is antitone on [s, t₀]
  have hF : AntitoneOn (fun t => u t + M * a * c ^ 2 * (a - t) ^ 2) (Icc s t₀) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc s t₀)
      ((huc.mono hsub).add (g := fun t => M * a * c ^ 2 * (a - t) ^ 2)
        (continuous_const.mul ((continuous_const.sub continuous_id).pow 2)).continuousOn) (f' := fun t =>
        -(qP c χ t * ψ t) + M * a * c ^ 2 * (2 * (a - t) * (-1))) ?_ ?_
    · intro t ht
      rw [hint] at ht
      have htI : t ∈ Icc s a := hsub (Ioo_subset_Icc_self ht)
      have h2 : HasDerivAt (fun t => M * a * c ^ 2 * (a - t) ^ 2)
          (M * a * c ^ 2 * (2 * (a - t) * (-1))) t := by
        have := ((hasDerivAt_id t).const_sub a).pow 2
        simpa using this.const_mul (M * a * c ^ 2)
      exact ((hu t htI).add h2).hasDerivWithinAt
    · intro t ht
      rw [hint] at ht
      have htI : t ∈ Icc s a := hsub (Ioo_subset_Icc_self ht)
      have hψt : ψ t ≤ M := hmax htI
      have hq : -qP c χ t = c ^ 2 * (a - t) * (a + t) := by unfold qP; rw [hχ]; ring
      have hat : 0 ≤ a - t := by linarith [htI.2]
      have hat' : 0 ≤ a + t := by linarith [htI.1]
      have hk : 0 ≤ c ^ 2 * (a - t) * (a + t) := by positivity
      have e : -(qP c χ t * ψ t) + M * a * c ^ 2 * (2 * (a - t) * (-1))
          = c ^ 2 * (a - t) * (a + t) * ψ t - 2 * M * a * c ^ 2 * (a - t) := by
        rw [← hq]; ring
      rw [e]
      have h1 : c ^ 2 * (a - t) * (a + t) * ψ t ≤ c ^ 2 * (a - t) * (a + t) * M :=
        mul_le_mul_of_nonneg_left hψt hk
      nlinarith [sq_nonneg (a - t), mul_nonneg hM0 (mul_nonneg (sq_nonneg c) (sq_nonneg (a - t)))]
  have hlow : ∀ t ∈ Icc s t₀, -(M * a * c ^ 2 * (a - t) ^ 2) ≤ u t := by
    intro t ht
    have h := hF ht (right_mem_Icc.mpr (ht.1.trans ht.2)) ht.2
    simp only at h
    have : 0 ≤ M * a * c ^ 2 * (a - t₀) ^ 2 := by positivity
    linarith
  -- (2) `ψ t + M a c² (a − t)³/(3(1 − a²))` is antitone on [s, t₀]
  have hG : AntitoneOn (fun t => ψ t + M * a * c ^ 2 * (a - t) ^ 3 / (3 * (1 - a ^ 2)))
      (Icc s t₀) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc s t₀)
      ((hψc.mono hsub).add (g := fun t => M * a * c ^ 2 * (a - t) ^ 3 / (3 * (1 - a ^ 2)))
        ((continuous_const.mul ((continuous_const.sub continuous_id).pow 3)).div_const
          _).continuousOn) (f' := fun t =>
        u t / pP t + M * a * c ^ 2 * (3 * (a - t) ^ 2 * (-1)) / (3 * (1 - a ^ 2))) ?_ ?_
    · intro t ht
      rw [hint] at ht
      have htI : t ∈ Icc s a := hsub (Ioo_subset_Icc_self ht)
      have h2 : HasDerivAt (fun t => M * a * c ^ 2 * (a - t) ^ 3 / (3 * (1 - a ^ 2)))
          (M * a * c ^ 2 * (3 * (a - t) ^ 2 * (-1)) / (3 * (1 - a ^ 2))) t := by
        have := ((hasDerivAt_id t).const_sub a).pow 3
        simpa using (this.const_mul (M * a * c ^ 2)).div_const (3 * (1 - a ^ 2))
      exact ((hψ t htI).add h2).hasDerivWithinAt
    · intro t ht
      rw [hint] at ht
      have htI : t ∈ Icc s a := hsub (Ioo_subset_Icc_self ht)
      have hut := hlow t (Ioo_subset_Icc_self ht)
      have ht0 : 0 ≤ t := hs0.trans htI.1
      have hat : 0 ≤ a - t := by linarith [htI.2]
      have hT : 1 - a ^ 2 ≤ 1 - t ^ 2 := by nlinarith
      have hT0 : 0 < 1 - t ^ 2 := hA.trans_le hT
      have hp : pP t = -(1 - t ^ 2) := by unfold pP; ring
      have hN : 0 ≤ M * a * c ^ 2 * (a - t) ^ 2 := by positivity
      rw [hp, div_neg]
      have e1 : M * a * c ^ 2 * (3 * (a - t) ^ 2 * (-1)) / (3 * (1 - a ^ 2))
          = -(M * a * c ^ 2 * (a - t) ^ 2 / (1 - a ^ 2)) := by
        field_simp
      rw [e1]
      have h1 : -u t / (1 - t ^ 2) ≤ M * a * c ^ 2 * (a - t) ^ 2 / (1 - t ^ 2) :=
        div_le_div_of_nonneg_right (by linarith) hT0.le
      have h2 : M * a * c ^ 2 * (a - t) ^ 2 / (1 - t ^ 2)
          ≤ M * a * c ^ 2 * (a - t) ^ 2 / (1 - a ^ 2) :=
        div_le_div_of_nonneg_left hN hA hT
      rw [neg_div] at h1
      linarith
  have h := hG (left_mem_Icc.mpr hst.le) (right_mem_Icc.mpr hst.le) hst.le
  simp only at h
  have h3 : 0 ≤ M * a * c ^ 2 * (a - t₀) ^ 3 / (3 * (1 - a ^ 2)) := by
    have : 0 ≤ a - t₀ := by linarith [ht₀.2]
    positivity
  have e : M * a * c ^ 2 * (a - s) ^ 3 / (3 * (1 - a ^ 2)) = M * X := by rw [hXdef]; ring
  rw [e] at h
  have : (1 - X) * ψ a ≤ (1 - X) * M := mul_le_mul_of_nonneg_left hMa (by linarith)
  nlinarith

/-- **The window mass**: `∫_{a−h}^a ψ² ≥ (h − ac²h⁴/(6(1 − a²)) + a²c⁴h⁷/(63(1 − a²)²))ψ(a)²`,
the square of the crossing bound integrated over the window. -/
theorem crossing_window_mass {ψ u : ℝ → ℝ} {c χ a h : ℝ} (hc : 0 < c) (ha : 0 < a) (ha1 : a < 1)
    (hχ : χ = c ^ 2 * a ^ 2) (hh0 : 0 ≤ h) (hha : h ≤ a)
    (hψ : ∀ t ∈ Icc (a - h) a, HasDerivAt ψ (u t / pP t) t)
    (hu : ∀ t ∈ Icc (a - h) a, HasDerivAt u (-(qP c χ t * ψ t)) t)
    (hψa : 0 ≤ ψ a) (hua : 0 ≤ u a) (hX : a * c ^ 2 * h ^ 3 ≤ 3 * (1 - a ^ 2)) :
    (h - a * c ^ 2 * h ^ 4 / (6 * (1 - a ^ 2)) + a ^ 2 * c ^ 4 * h ^ 7 / (63 * (1 - a ^ 2) ^ 2)) * ψ a ^ 2
      ≤ ∫ t in (a - h)..a, ψ t ^ 2 := by
  have hA : 0 < 1 - a ^ 2 := by nlinarith
  set κ := a * c ^ 2 / (3 * (1 - a ^ 2)) with hκ
  have hle : a - h ≤ a := by linarith
  -- pointwise bound
  have hpt : ∀ t ∈ Icc (a - h) a, ((1 - κ * (a - t) ^ 3) * ψ a) ^ 2 ≤ ψ t ^ 2 := by
    intro t ht
    have hat : 0 ≤ a - t := by linarith [ht.2]
    have hth : a - t ≤ h := by linarith [ht.1]
    have hX' : a * c ^ 2 * (a - t) ^ 3 ≤ 3 * (1 - a ^ 2) := by
      have : (a - t) ^ 3 ≤ h ^ 3 := pow_le_pow_left₀ hat hth 3
      have : a * c ^ 2 * (a - t) ^ 3 ≤ a * c ^ 2 * h ^ 3 := by gcongr
      linarith
    have hsub : Icc t a ⊆ Icc (a - h) a := Icc_subset_Icc ht.1 le_rfl
    have hcr := turning_crossing hc ha ha1 hχ (by linarith [ht.1]) ht.2
      (fun x hx => hψ x (hsub hx)) (fun x hx => hu x (hsub hx)) hψa hua hX'
    have e : a * c ^ 2 * (a - t) ^ 3 / (3 * (1 - a ^ 2)) = κ * (a - t) ^ 3 := by
      rw [hκ]; ring
    rw [e] at hcr
    have hk1 : 0 ≤ 1 - κ * (a - t) ^ 3 := by
      have : κ * (a - t) ^ 3 ≤ 1 := by
        rw [hκ, div_mul_eq_mul_div, div_le_one (by positivity)]; linarith
      linarith
    have h0 : 0 ≤ (1 - κ * (a - t) ^ 3) * ψ a := mul_nonneg hk1 hψa
    exact pow_le_pow_left₀ h0 hcr 2
  -- the integral of the square of the bound
  have hF : ∀ t, HasDerivAt
      (fun t => -(ψ a ^ 2 * ((a - t) - κ * (a - t) ^ 4 / 2 + κ ^ 2 * (a - t) ^ 7 / 7)))
      (((1 - κ * (a - t) ^ 3) * ψ a) ^ 2) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => a - t) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub a
    have h4 := h1.fun_pow 4
    have h7 := h1.fun_pow 7
    have := ((h1.sub (h4.const_mul κ |>.div_const 2)).add
      ((h7.const_mul (κ ^ 2)).div_const 7)).const_mul (ψ a ^ 2) |>.neg
    exact this.congr_deriv (by push_cast; ring)
  have hI : ∫ t in (a - h)..a, ((1 - κ * (a - t) ^ 3) * ψ a) ^ 2
      = ψ a ^ 2 * (h - κ * h ^ 4 / 2 + κ ^ 2 * h ^ 7 / 7) := by
    rw [integral_eq_sub_of_hasDerivAt (fun t _ => hF t) (by
      apply Continuous.intervalIntegrable; fun_prop)]
    ring
  have hψc : ContinuousOn ψ (Icc (a - h) a) :=
    fun t ht => (hψ t ht).continuousAt.continuousWithinAt
  have hmono := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hle
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hle]
      exact hψc.pow 2) hpt
  rw [hI] at hmono
  have e : (h - a * c ^ 2 * h ^ 4 / (6 * (1 - a ^ 2)) + a ^ 2 * c ^ 4 * h ^ 7 / (63 * (1 - a ^ 2) ^ 2))
      * ψ a ^ 2 = ψ a ^ 2 * (h - κ * h ^ 4 / 2 + κ ^ 2 * h ^ 7 / 7) := by
    rw [hκ]; field_simp; ring
  rw [e]; exact hmono

/-- **The crossing in Airy units**: `ψ(a − θl) ≥ (1 − θ³/6)ψ(a)` for `θ³ ≤ 6`. -/
theorem turning_crossing_airy {ψ u : ℝ → ℝ} {c χ a θ : ℝ} (hc : 0 < c) (ha : 0 < a) (ha1 : a < 1)
    (hχ : χ = c ^ 2 * a ^ 2) (hθ : 0 ≤ θ) (hθ6 : θ ^ 3 ≤ 6) (hθa : θ * airyL c a ≤ a)
    (hψ : ∀ t ∈ Icc (a - θ * airyL c a) a, HasDerivAt ψ (u t / pP t) t)
    (hu : ∀ t ∈ Icc (a - θ * airyL c a) a, HasDerivAt u (-(qP c χ t * ψ t)) t)
    (hψa : 0 ≤ ψ a) (hua : 0 ≤ u a) :
    (1 - θ ^ 3 / 6) * ψ a ≤ ψ (a - θ * airyL c a) := by
  have hA : 0 < 1 - a ^ 2 := by nlinarith
  have hL := airyL_cube hc ha ha1
  have hl := airyL_pos hc ha ha1
  have e3 : a * c ^ 2 * (a - (a - θ * airyL c a)) ^ 3 = θ ^ 3 * (1 - a ^ 2) / 2 := by
    rw [← hL]; ring
  have hX : a * c ^ 2 * (a - (a - θ * airyL c a)) ^ 3 ≤ 3 * (1 - a ^ 2) := by
    rw [e3]; nlinarith
  have h := turning_crossing hc ha ha1 hχ (by linarith) (by nlinarith) hψ hu hψa hua hX
  rw [e3] at h
  have e : θ ^ 3 * (1 - a ^ 2) / 2 / (3 * (1 - a ^ 2)) = θ ^ 3 / 6 := by
    field_simp; ring
  rwa [e] at h

/-- **The window mass in Airy units**: `c∫_{a−θl}^a ψ² ≥ m(θ)ψ(a)²/√g`. -/
theorem crossing_window_mass_airy {ψ u : ℝ → ℝ} {c χ a θ : ℝ} (hc : 0 < c) (ha : 0 < a) (ha1 : a < 1)
    (hχ : χ = c ^ 2 * a ^ 2) (hθ : 0 ≤ θ) (hθ6 : θ ^ 3 ≤ 6) (hθa : θ * airyL c a ≤ a)
    (hψ : ∀ t ∈ Icc (a - θ * airyL c a) a, HasDerivAt ψ (u t / pP t) t)
    (hu : ∀ t ∈ Icc (a - θ * airyL c a) a, HasDerivAt u (-(qP c χ t * ψ t)) t)
    (hψa : 0 ≤ ψ a) (hua : 0 ≤ u a) :
    mth θ / √(airyG c a) * ψ a ^ 2 ≤ c * ∫ t in (a - θ * airyL c a)..a, ψ t ^ 2 := by
  have hA : 0 < 1 - a ^ 2 := by nlinarith
  have hL := airyL_cube hc ha ha1
  have hl := airyL_pos hc ha ha1
  set l := airyL c a with hldef
  have e3 : a * c ^ 2 * (θ * l) ^ 3 = θ ^ 3 * (1 - a ^ 2) / 2 := by
    rw [← hL]; ring
  have hX : a * c ^ 2 * (θ * l) ^ 3 ≤ 3 * (1 - a ^ 2) := by
    rw [e3]; nlinarith
  have h := crossing_window_mass hc ha ha1 hχ (by positivity) hθa hψ hu hψa hua hX
  -- the bracket is `l · m(θ)`
  have eb : θ * l - a * c ^ 2 * (θ * l) ^ 4 / (6 * (1 - a ^ 2))
      + a ^ 2 * c ^ 4 * (θ * l) ^ 7 / (63 * (1 - a ^ 2) ^ 2) = l * mth θ := by
    have e4 : a * c ^ 2 * (θ * l) ^ 4 = θ ^ 4 * l * (1 - a ^ 2) / 2 := by
      rw [← hL]; ring
    have e7 : a ^ 2 * c ^ 4 * (θ * l) ^ 7 = θ ^ 7 * l * (1 - a ^ 2) ^ 2 / 4 := by
      rw [← hL]; ring
    rw [e4, e7]; unfold mth; field_simp; ring
  rw [eb] at h
  -- `√g = 1/(c l)`
  have hcl : 0 < c * l := mul_pos hc hl
  have hg : airyG c a = ((c * l) ^ 2)⁻¹ := by
    have := airyG_mul hc ha ha1
    rw [← hldef] at this
    field_simp
    linear_combination this
  have hsq : √(airyG c a) = (c * l)⁻¹ := by
    rw [hg, Real.sqrt_inv, Real.sqrt_sq hcl.le]
  rw [hsq, div_inv_eq_mul]
  have := mul_le_mul_of_nonneg_left h hc.le
  calc mth θ * (c * l) * ψ a ^ 2 = c * (l * mth θ * ψ a ^ 2) := by ring
    _ ≤ _ := this

end Cvs.Prolate.LiouvilleGreen.AiryTurningPoint
