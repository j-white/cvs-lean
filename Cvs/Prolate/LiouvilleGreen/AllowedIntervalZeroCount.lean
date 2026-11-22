import Mathlib
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.TopRungDepthBound
import Cvs.Prolate.TopRungZeroSplitHalf
import Cvs.Upstream.SturmLiouvillePrufer

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Liouville–Green zero counts at any level on an allowed interval

On `[α, β] ⊆ [0, 1)` with `q = χ − c²t² > 0`, `χ = c² − Kc`, the Prüfer phase with scale `a = √(pq)` has
`Θ′ = ω(1 − (w/2) sin 2Θ)`, `ω = a/p`, `ωw = (log a)′ ≤ 0`, so its increment is `∫ω ± ½ log(a(α)/a(β))`, and
the regular solution has `(Θ(β) − Θ(α))/π ± 1` zeros there.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory
open Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Upstream.SturmLiouvillePrufer Cvs.Prolate.RegularSolutionEdge Cvs.Prolate.TopRungDepthBound
open Cvs.Prolate.TopRungZeroSplitHalf (ZerosOn)

namespace Cvs.Prolate.LiouvilleGreen.AllowedIntervalZeroCount

variable {c K α β : ℝ}

/-- **The Prüfer phase from `α`**: where `q > 0` on `[α, β] ⊆ [0, 1)`, the regular solution at `c² − Kc` has a phase
`Θ′ = ω(1 − (w/2) sin 2Θ)`, `ω = a/(1 − t²)`, whose cosine vanishes exactly at its zeros. -/
theorem prufer_from (hα0 : 0 ≤ α) (hαβ : α ≤ β) (hβ1 : β < 1) (hq : ∀ t ∈ Icc α β, 0 < qf c K t) :
    ∃ Θ : ℝ → ℝ, (∀ t ∈ Icc α β, HasDerivAt Θ (af c K t / (1 - t ^ 2) * (1 - wf c K t / 2 * sin (2 * Θ t))) t) ∧
      (∀ t ∈ Icc α β, regSol (sqC c) (c ^ 2 - K * c) t = 0 ↔ cos (Θ t) = 0) := by
  set y := regSol (sqC c) (c ^ 2 - K * c) with hydef
  set U := regU (sqC c) (c ^ 2 - K * c) with hUdef
  set V : Set ℝ := {t | -1 < t} ∩ {t | t ^ 2 < 1} ∩ {t | 0 < qf c K t} with hVdef
  have hVo : IsOpen V := by
    refine ((isOpen_lt continuous_const continuous_id).inter (isOpen_lt (by fun_prop) continuous_const)).inter
      (isOpen_lt continuous_const ?_)
    unfold qf; fun_prop
  have hIV : Icc α β ⊆ V := fun t ht => by
    have ht2 : t ^ 2 < 1 := by nlinarith [ht.1, ht.2]
    exact ⟨⟨show -1 < t by linarith [ht.1], ht2⟩, hq t ht⟩
  set p : ℝ → ℝ := fun t => 1 - t ^ 2 with hpdef
  set u : ℝ → ℝ := fun t => -U t with hudef
  have hψd : ∀ t, -1 < t → t ^ 2 < 1 → HasDerivAt y (u t / p t) t := fun t ht1 ht2 => by
    have h := hasDerivAt_regSol (sqC c) (c ^ 2 - K * c) ht1
    have hV := pP_mul_regV (sqC c) (c ^ 2 - K * c) ht1
    have hp : 0 < 1 - t ^ 2 := by linarith
    refine h.congr_deriv ?_
    simp only [u, p, U]
    rw [eq_div_iff hp.ne']
    unfold pP at hV
    linarith
  have hud : ∀ t, -1 < t → HasDerivAt u (-(qf c K t * y t)) t := fun t ht1 => by
    have h := (hasDerivAt_regU (sqC c) (c ^ 2 - K * c) ht1).neg
    refine h.congr_deriv ?_
    rw [sqC_apply]; unfold qf; ring
  have hE : ∀ t, -1 < t → t < 1 → 0 < af c K t → 0 < energy (af c K) y u t := fun t ht1 ht2 ha => by
    unfold energy
    rcases eq_or_ne (y t) 0 with h0 | h0
    · have hU0 := Cvs.Prolate.EdgeCentreSign.regU_ne_zero_of_regSol_eq_zero (sqC c) (c ^ 2 - K * c) ht1 ht2 h0
      have : 0 < u t ^ 2 := lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 (neg_ne_zero.mpr hU0)).symm
      rw [h0]; positivity
    · have : 0 < af c K t * y t ^ 2 := by positivity
      have : 0 ≤ u t ^ 2 / af c K t := by positivity
      linarith
  set rateF := rate p (af c K) (wf c K) (qf c K) y u with hrateF
  have hcont : ∀ t ∈ V, ContinuousAt rateF t := fun t ht => by
    obtain ⟨⟨ht1, ht2⟩, hqt⟩ := ht
    have ht1 : -1 < t := ht1
    have ht2 : t ^ 2 < 1 := ht2
    have hqt : 0 < qf c K t := hqt
    have ha := af_pos ht2 hqt
    have haC := (hasDerivAt_af ht2 hqt).continuousAt
    have hwC := (hasDerivAt_wf ht2 hqt).continuousAt
    have hqC := (hasDerivAt_qf c K t).continuousAt
    have hyC := (hasDerivAt_regSol (sqC c) (c ^ 2 - K * c) ht1).continuousAt
    have huC := (hasDerivAt_regU (sqC c) (c ^ 2 - K * c) ht1).continuousAt.neg
    have hpC : ContinuousAt p t := by simp only [p]; fun_prop
    have hEt := hE t ht1 (by nlinarith) ha
    have hEC : ContinuousAt (energy (af c K) y u) t := by
      unfold energy
      exact (haC.mul (hyC.pow 2)).add ((huC.pow 2).div haC ha.ne')
    have hp0 : p t ≠ 0 := by simp only [p]; linarith
    rw [hrateF]; unfold rate
    exact (haC.div hpC hp0).add (((hwC.mul hqC).mul (huC.mul hyC)).div (haC.mul hEC) (mul_pos ha hEt).ne')
  have hcontOn : ContinuousOn rateF V := fun t ht => (hcont t ht).continuousWithinAt
  have hαI : α ∈ Icc α β := ⟨le_rfl, hαβ⟩
  obtain ⟨⟨hα1, hα2⟩, hqα⟩ := hIV hαI
  have haα := af_pos hα2 hqα
  obtain ⟨Θ₀, hc0, hs0⟩ := exists_angle (X_sq_add_Y_sq (a := af c K) (ψ := y) (u := u) haα
    (hE α hα1 (by nlinarith) haα))
  set Θ : ℝ → ℝ := fun t => Θ₀ + ∫ r in α..t, rateF r with hΘdef
  have hΘ : ∀ t ∈ Icc α β, HasDerivAt Θ (rateF t) t := fun t ht => by
    have hsub : uIcc α t ⊆ V := by
      rw [uIcc_of_le ht.1]; exact (Icc_subset_Icc le_rfl ht.2).trans hIV
    have h := intervalIntegral.integral_hasDerivAt_right ((hcontOn.mono hsub).intervalIntegrable)
      (hcontOn.stronglyMeasurableAtFilter hVo t (hIV ht)) (hcont t (hIV ht))
    exact h.const_add Θ₀
  have hΘ0 : Θ α = Θ₀ := by simp [hΘdef]
  have hfacts : ∀ t ∈ Icc α β, 0 < af c K t ∧ p t ≠ 0 ∧ af c K t ^ 2 = p t * qf c K t ∧
      0 < energy (af c K) y u t ∧ HasDerivAt y (u t / p t) t ∧ HasDerivAt u (-(qf c K t * y t)) t ∧
      HasDerivAt (af c K) (wf c K t * qf c K t) t := fun t ht => by
    obtain ⟨⟨ht1, ht2⟩, hqt⟩ := hIV ht
    have ht1 : -1 < t := ht1
    have ht2 : t ^ 2 < 1 := ht2
    have hqt : 0 < qf c K t := hqt
    have ha := af_pos ht2 hqt
    exact ⟨ha, by simp only [p]; linarith, af_sq ht2 hqt, hE t ht1 (by nlinarith) ha, hψd t ht1 ht2, hud t ht1,
      hasDerivAt_af ht2 hqt⟩
  have hXY := prufer_XY (fun t ht => (hfacts t ht).1) (fun t ht => (hfacts t ht).2.1)
    (fun t ht => (hfacts t ht).2.2.1) (fun t ht => (hfacts t ht).2.2.2.1) (fun t ht => (hfacts t ht).2.2.2.2.1)
    (fun t ht => (hfacts t ht).2.2.2.2.2.1) (fun t ht => (hfacts t ht).2.2.2.2.2.2) hΘ
    (by rw [hΘ0, hc0]) (by rw [hΘ0, hs0])
  have hrate : ∀ t ∈ Icc α β, rateF t = af c K t / (1 - t ^ 2) * (1 - wf c K t / 2 * sin (2 * Θ t)) :=
    fun t ht => by
    obtain ⟨ha, hp, hapq, hEt, -, -, -⟩ := hfacts t ht
    obtain ⟨hX, hY⟩ := hXY t ht
    rw [Real.sin_two_mul, ← hX, ← hY]
    rw [hrateF]; unfold X Y rate
    have hsa := Real.sq_sqrt ha.le
    have hsE := Real.sq_sqrt hEt.le
    have hsa0 : 0 < √(af c K t) := Real.sqrt_pos.mpr ha
    have hsE0 : 0 < √(energy (af c K) y u t) := Real.sqrt_pos.mpr hEt
    have hq' : qf c K t = af c K t ^ 2 / p t := by rw [hapq]; field_simp
    rw [hq']
    simp only [p] at hp ⊢
    field_simp
    rw [hsE]
    ring
  refine ⟨Θ, fun t ht => (hrate t ht) ▸ hΘ t ht, fun t ht => ?_⟩
  obtain ⟨ha, -, -, hEt, -, -, -⟩ := hfacts t ht
  rw [← (hXY t ht).1]
  unfold X
  have hsa0 : 0 < √(af c K t) := Real.sqrt_pos.mpr ha
  have hsE0 : 0 < √(energy (af c K) y u t) := Real.sqrt_pos.mpr hEt
  rw [div_eq_zero_iff, mul_eq_zero]
  constructor
  · intro h; exact Or.inl (Or.inr h)
  · rintro ((h | h) | h)
    · exact absurd h hsa0.ne'
    · exact h
    · exact absurd h hsE0.ne'

/-! ### The phase increment -/

/-- The phase integral `Ω(t) = ∫_α^t a/(1 − s²) ds`. -/
def Omg (c K α t : ℝ) : ℝ := ∫ s in α..t, af c K s / (1 - s ^ 2)

theorem continuousAt_omega {t : ℝ} (ht : t ^ 2 < 1) : ContinuousAt (fun s => af c K s / (1 - s ^ 2)) t := by
  have hne : (1 - t ^ 2) ≠ 0 := by linarith
  have hcont : Continuous (fun s : ℝ => af c K s) := by unfold af qf; fun_prop
  have hden : Continuous (fun s : ℝ => 1 - s ^ 2) := by fun_prop
  exact hcont.continuousAt.div₀ hden.continuousAt hne

theorem hasDerivAt_Omg (hα0 : 0 ≤ α) (hβ1 : β < 1) {t : ℝ} (ht : t ∈ Icc α β) :
    HasDerivAt (Omg c K α) (af c K t / (1 - t ^ 2)) t := by
  have hV : IsOpen {s : ℝ | s ^ 2 < 1} := isOpen_lt (by fun_prop) continuous_const
  have hsub : uIcc α t ⊆ {s : ℝ | s ^ 2 < 1} := by
    rw [uIcc_of_le ht.1]; intro s hs; simp only [mem_ofPred_eq]; nlinarith [hs.1, hs.2, ht.2]
  have hc : ContinuousOn (fun s => af c K s / (1 - s ^ 2)) {s : ℝ | s ^ 2 < 1} :=
    fun s hs => (continuousAt_omega hs).continuousWithinAt
  have ht1 : t ^ 2 < 1 := by nlinarith [ht.1, ht.2]
  exact intervalIntegral.integral_hasDerivAt_right ((hc.mono hsub).intervalIntegrable)
    (hc.stronglyMeasurableAtFilter hV t ht1) (continuousAt_omega ht1)

/-- **The phase increment**: `Θ(t₂) − Θ(t₁) ∈ [Ω(t₂) − Ω(t₁) ± ½(log a(t₂) − log a(t₁))]` on `[α, β]`. -/
theorem phase_bounds (hα0 : 0 ≤ α) (hβ1 : β < 1) (hq : ∀ t ∈ Icc α β, 0 < qf c K t) {Θ : ℝ → ℝ}
    (hΘ : ∀ t ∈ Icc α β, HasDerivAt Θ (af c K t / (1 - t ^ 2) * (1 - wf c K t / 2 * sin (2 * Θ t))) t)
    {t₁ t₂ : ℝ} (h1 : α ≤ t₁) (h12 : t₁ ≤ t₂) (h2 : t₂ ≤ β) :
    Θ t₂ - Θ t₁ ≤ Omg c K α t₂ - Omg c K α t₁ - (log (af c K t₂) - log (af c K t₁)) / 2 ∧
      Omg c K α t₂ - Omg c K α t₁ + (log (af c K t₂) - log (af c K t₁)) / 2 ≤ Θ t₂ - Θ t₁ := by
  have hreg : ∀ t ∈ Icc α β, t ^ 2 < 1 := fun t ht => by nlinarith [ht.1, ht.2]
  have hω0 : ∀ t ∈ Icc α β, 0 ≤ af c K t / (1 - t ^ 2) := fun t ht =>
    div_nonneg (af_pos (hreg t ht) (hq t ht)).le (by linarith [hreg t ht])
  have hw0 : ∀ t ∈ Icc α β, wf c K t ≤ 0 := fun t ht => wf_nonpos (hα0.trans ht.1) (hreg t ht) (hq t ht)
  have hL : ∀ t ∈ Icc α β, HasDerivAt (fun t => log (af c K t)) (af c K t / (1 - t ^ 2) * wf c K t) t :=
    fun t ht => Cvs.Prolate.TopRungZeroSplitHalf.hasDerivAt_log_af (hreg t ht) (hq t ht)
  set G : ℝ → ℝ := fun t => Θ t - Omg c K α t + log (af c K t) / 2 with hG
  set H : ℝ → ℝ := fun t => Θ t - Omg c K α t - log (af c K t) / 2 with hH
  have hGd : ∀ t ∈ Icc α β, HasDerivAt G (af c K t / (1 - t ^ 2) * wf c K t / 2 * (1 - sin (2 * Θ t))) t :=
    fun t ht => by
      refine (((hΘ t ht).sub (hasDerivAt_Omg hα0 hβ1 ht)).add ((hL t ht).div_const 2)).congr_deriv ?_
      ring
  have hHd : ∀ t ∈ Icc α β, HasDerivAt H (-(af c K t / (1 - t ^ 2) * wf c K t / 2 * (1 + sin (2 * Θ t)))) t :=
    fun t ht => by
      refine (((hΘ t ht).sub (hasDerivAt_Omg hα0 hβ1 ht)).sub ((hL t ht).div_const 2)).congr_deriv ?_
      ring
  have hGa : AntitoneOn G (Icc α β) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc α β)
      (fun t ht => (hGd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hGd t (interior_subset ht)).hasDerivWithinAt) (fun t ht => ?_)
    have ht' := interior_subset ht
    have h1 := hω0 t ht'
    have h2 := hw0 t ht'
    have h3 : 0 ≤ 1 - sin (2 * Θ t) := by linarith [Real.sin_le_one (2 * Θ t)]
    have : af c K t / (1 - t ^ 2) * wf c K t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h1 h2
    have := mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg this (by norm_num : (0 : ℝ) ≤ 2)) h3
    simpa [mul_div_assoc] using this
  have hHm : MonotoneOn H (Icc α β) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc α β)
      (fun t ht => (hHd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hHd t (interior_subset ht)).hasDerivWithinAt) (fun t ht => ?_)
    have ht' := interior_subset ht
    have h1 := hω0 t ht'
    have h2 := hw0 t ht'
    have h3 : 0 ≤ 1 + sin (2 * Θ t) := by linarith [Real.neg_one_le_sin (2 * Θ t)]
    have : af c K t / (1 - t ^ 2) * wf c K t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h1 h2
    have := mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg this (by norm_num : (0 : ℝ) ≤ 2)) h3
    linarith
  have m1 := hGa ⟨h1, h12.trans h2⟩ ⟨h1.trans h12, h2⟩ h12
  have m2 := hHm ⟨h1, h12.trans h2⟩ ⟨h1.trans h12, h2⟩ h12
  simp only [hG, hH] at m1 m2
  constructor <;> linarith

/-! ### The zero counts -/

theorem omega_pos {t : ℝ} (hq : 0 < qf c K t) (ht : t ^ 2 < 1) : 0 < af c K t / (1 - t ^ 2) :=
  div_pos (af_pos ht hq) (by linarith)

/-- `Ω` is nondecreasing and `log a` nonincreasing on `[α, β]`. -/
theorem Omg_mono_log_anti (hα0 : 0 ≤ α) (hβ1 : β < 1) (hq : ∀ t ∈ Icc α β, 0 < qf c K t) {t₁ t₂ : ℝ}
    (h1 : α ≤ t₁) (h12 : t₁ ≤ t₂) (h2 : t₂ ≤ β) :
    Omg c K α t₁ ≤ Omg c K α t₂ ∧ log (af c K t₂) ≤ log (af c K t₁) := by
  have hreg : ∀ t ∈ Icc α β, t ^ 2 < 1 := fun t ht => by nlinarith [ht.1, ht.2]
  constructor
  · refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc α β)
      (fun t ht => (hasDerivAt_Omg hα0 hβ1 ht).continuousAt.continuousWithinAt)
      (fun t ht => (hasDerivAt_Omg hα0 hβ1 (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => (omega_pos (hq t (interior_subset ht)) (hreg t (interior_subset ht))).le)
      ⟨h1, h12.trans h2⟩ ⟨h1.trans h12, h2⟩ h12
  · refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc α β)
      (fun t ht => (Cvs.Prolate.TopRungZeroSplitHalf.hasDerivAt_log_af (hreg t ht) (hq t ht)).continuousAt.continuousWithinAt)
      (fun t ht => (Cvs.Prolate.TopRungZeroSplitHalf.hasDerivAt_log_af (hreg t (interior_subset ht)) (hq t (interior_subset ht))).hasDerivWithinAt)
      (fun t ht => mul_nonpos_of_nonneg_of_nonpos (omega_pos (hq t (interior_subset ht))
        (hreg t (interior_subset ht))).le (wf_nonpos (hα0.trans (interior_subset ht).1) (hreg t (interior_subset ht))
        (hq t (interior_subset ht)))) ⟨h1, h12.trans h2⟩ ⟨h1.trans h12, h2⟩ h12

/-- **The upper count**: `k + 1` zeros in `[α, β]` give `kπ ≤ Ω(β) + ½(log a(α) − log a(β))`. -/
theorem count_le (hα0 : 0 ≤ α) (hαβ : α ≤ β) (hβ1 : β < 1) (hq : ∀ t ∈ Icc α β, 0 < qf c K t) {k : ℕ}
    (hz : ZerosOn (regSol (sqC c) (c ^ 2 - K * c)) (Icc α β) (k + 1)) :
    k * π ≤ Omg c K α β + (log (af c K α) - log (af c K β)) / 2 := by
  obtain ⟨Θ, hΘ, hzero⟩ := prufer_from hα0 hαβ hβ1 hq
  obtain ⟨w, hw, hwI, hw0⟩ := hz
  have hreg : ∀ t ∈ Icc α β, t ^ 2 < 1 := fun t ht => by nlinarith [ht.1, ht.2]
  have hcos : ∀ i, cos (Θ (w i)) = 0 := fun i => (hzero (w i) (hwI i)).mp (hw0 i)
  have hcont : ContinuousOn Θ (Icc α β) := fun t ht => (hΘ t ht).continuousAt.continuousWithinAt
  have hd : ∀ t ∈ Icc α β, cos (Θ t) = 0 → ∃ d, 0 < d ∧ HasDerivAt Θ d t := fun t ht h => by
    refine ⟨_, ?_, hΘ t ht⟩
    rw [Real.sin_two_mul, h]
    simpa using omega_pos (hq t ht) (hreg t ht)
  have hcount := Cvs.Prolate.TopRungDepthBound.phase_count hw hcont hwI hcos hd k (Nat.lt_succ_self k)
  set w0 := w ⟨0, by omega⟩
  set wk := w ⟨k, Nat.lt_succ_self k⟩
  have h0k : w0 ≤ wk := hw.monotone (Fin.mk_le_mk.mpr (Nat.zero_le k))
  have hb := (phase_bounds hα0 hβ1 hq hΘ (hwI _).1 h0k (hwI _).2).1
  obtain ⟨m1, -⟩ := Omg_mono_log_anti hα0 hβ1 hq le_rfl (hwI ⟨0, by omega⟩).1 (h0k.trans (hwI _).2)
  obtain ⟨m2, l2⟩ := Omg_mono_log_anti hα0 hβ1 hq ((hwI _).1.trans h0k) (hwI ⟨k, Nat.lt_succ_self k⟩).2 le_rfl
  obtain ⟨-, l1⟩ := Omg_mono_log_anti hα0 hβ1 hq le_rfl (hwI ⟨0, by omega⟩).1 (h0k.trans (hwI _).2)
  have hO0 : Omg c K α α = 0 := by simp [Omg]
  rw [hO0] at m1
  linarith

/-- **The lower count**: `(m + 1)π ≤ Ω(β) − ½(log a(α) − log a(β))` gives `m` zeros in `(α, β)`. -/
theorem count_ge (hα0 : 0 ≤ α) (hαβ : α ≤ β) (hβ1 : β < 1) (hq : ∀ t ∈ Icc α β, 0 < qf c K t) {m : ℕ}
    (hm : (m + 1) * π ≤ Omg c K α β - (log (af c K α) - log (af c K β)) / 2) :
    ZerosOn (regSol (sqC c) (c ^ 2 - K * c)) (Ioo α β) m := by
  obtain ⟨Θ, hΘ, hzero⟩ := prufer_from hα0 hαβ hβ1 hq
  have hcont : ContinuousOn Θ (Icc α β) := fun t ht => (hΘ t ht).continuousAt.continuousWithinAt
  have hb := (phase_bounds hα0 hβ1 hq hΘ le_rfl hαβ le_rfl).2
  have hO0 : Omg c K α α = 0 := by simp [Omg]
  rw [hO0, sub_zero] at hb
  have hinc : Θ α + (m + 1) * π ≤ Θ β := by linarith
  -- a node of `sin Θ` in `[α, β]` within `π` of `α`
  set n₀ : ℤ := ⌈Θ α / π⌉ with hn₀
  have hn1 : Θ α ≤ n₀ * π := by rw [← div_le_iff₀ Real.pi_pos]; exact Int.le_ceil _
  have hn2 : (n₀ : ℝ) * π < Θ α + π := by
    have h' : (n₀ : ℝ) < Θ α / π + 1 := Int.ceil_lt_add_one (Θ α / π)
    have e : (Θ α / π + 1) * π = Θ α + π := by field_simp
    calc (n₀ : ℝ) * π < (Θ α / π + 1) * π := mul_lt_mul_of_pos_right h' Real.pi_pos
      _ = Θ α + π := e
  obtain ⟨α', hα', hα'v⟩ := intermediate_value_Icc hαβ hcont
    (show (n₀ : ℝ) * π ∈ Icc (Θ α) (Θ β) from ⟨hn1, by nlinarith [Real.pi_pos]⟩)
  have hsin : sin (Θ α') = 0 := by rw [hα'v]; exact Real.sin_int_mul_pi n₀
  obtain ⟨w, hw, hwI, hw0⟩ := Cvs.Prolate.TopRungZeroSplitHalf.crossings (k := m) hα'.2 (hcont.mono (Icc_subset_Icc hα'.1 le_rfl)) hsin
    (by rw [hα'v]; nlinarith [Real.pi_pos])
  refine ⟨w, hw, fun i => ⟨hα'.1.trans_lt (hwI i).1, (hwI i).2⟩, fun i => ?_⟩
  exact (hzero (w i) ⟨(hα'.1.trans_lt (hwI i).1).le, (hwI i).2.le⟩).mpr (hw0 i)

end Cvs.Prolate.LiouvilleGreen.AllowedIntervalZeroCount

end
