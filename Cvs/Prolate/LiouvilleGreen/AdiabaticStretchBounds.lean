import Mathlib
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.PruferAngleRobinRate
import Cvs.Prolate.LiouvilleGreen.RateStrictlyDecreasing
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.TopRungDepthBound

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The adiabatic bound and the stretch bounds for the regular prolate solution

For `y = regSol (sqC c) σ` and `K = (c² − σ)/c` (so `q = σ − c²t²`), the energy `G = ay² + U²/a` changes by at
most the factor `κ(M)` on `[t₀, t₁] ⊆ [0, 1)` while `|w| ≤ M < 2`. Consequently `∫_{t₀}^{t₁} y² ≤ κ(M) G(t₀)
∫_{t₀}^{t₁} 1/a`, and `N = ∫_{½}^1 y² ≤ κ(M)(2m + L) G₀` once `∫_{t₁}^1 y² ≤ L G(t₁)`. On a phase interval of
length `π` on which `h` stays in `[m, e^Λ m]`, `∫ h cos² ≥ (e^{−Λ}/2) ∫ h`.
-/

noncomputable section

open Real Set Filter Topology intervalIntegral MeasureTheory Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.RegularSolutionEdge Cvs.Prolate.TopRungDepthBound Cvs.Prolate.LiouvilleGreen.PruferAngleRobinRate Cvs.Prolate.LiouvilleGreen.RateStrictlyDecreasing

namespace Cvs.Prolate.LiouvilleGreen.AdiabaticStretchBounds

variable {c σ : ℝ}

/-- `σ − c²t² = q` at `K = (c² − σ)/c`. -/
theorem qf_eq (hc : c ≠ 0) (t : ℝ) : qf c ((c ^ 2 - σ) / c) t = σ - c ^ 2 * t ^ 2 := by
  unfold qf; field_simp; ring

/-- The energy of `y = regSol (sqC c) σ` with the scale `a = af` at `K = (c² − σ)/c`. -/
def energyAt (c σ t : ℝ) : ℝ := Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact.energy (af c ((c ^ 2 - σ) / c)) (regSol (sqC c) σ) (regU (sqC c) σ) t

theorem energyAt_half (c σ : ℝ) : energyAt c σ (1 / 2) = energyHalf c σ := rfl

/-- The allowed region: on `[t₀, t₁]` with `0 ≤ t₀`, `t₁² < 1` and `q(t₁) > 0`, every point has `t² < 1`, `q > 0`. -/
theorem mem_allowed {t₀ t₁ t : ℝ} (h0 : 0 ≤ t₀) (hs : t₁ ^ 2 < 1) (hq : 0 < qf c ((c ^ 2 - σ) / c) t₁)
    (ht : t ∈ Icc t₀ t₁) : t ^ 2 < 1 ∧ 0 < qf c ((c ^ 2 - σ) / c) t :=
  ⟨by nlinarith [ht.1, ht.2], hq.trans_le (qf_le_qf (h0.trans ht.1) ht.2)⟩

/-- **Lemma 1.3 for the regular solution**: on `[t₀, t₁]` with `0 ≤ t₀`, `t₁² < 1`, `q(t₁) > 0` and `|w(t₁)| ≤ M < 2`,
`G(t₁) ≤ κ(M) G(t₀)` and `G(t₀) ≤ κ(M) G(t₁)`. -/
theorem energyAt_le_kappa (hc : c ≠ 0) {t₀ t₁ M : ℝ} (h0 : 0 ≤ t₀) (hle : t₀ ≤ t₁) (hs : t₁ ^ 2 < 1)
    (hq : 0 < qf c ((c ^ 2 - σ) / c) t₁) (hM : M < 2) (hwM : |wf c ((c ^ 2 - σ) / c) t₁| ≤ M) :
    energyAt c σ t₁ ≤ kappa M * energyAt c σ t₀ ∧ energyAt c σ t₀ ≤ kappa M * energyAt c σ t₁ := by
  set K := (c ^ 2 - σ) / c
  have hmem := fun t (ht : t ∈ Icc t₀ t₁) => mem_allowed h0 hs hq ht
  have hneg : ∀ t, Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact.energy (af c K) (regSol (sqC c) σ) (fun s => -regU (sqC c) σ s) t =
      energyAt c σ t := fun t => by simp only [energyAt, Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact.energy, neg_sq]; rfl
  have h := energy_le_kappa (ψ := regSol (sqC c) σ) (u := fun s => -regU (sqC c) σ s) (p := fun s => 1 - s ^ 2)
    (q := qf c K) (a := af c K) (w := wf c K) (w' := wd c K) hle hM
    (fun t ht => af_pos (hmem t ht).1 (hmem t ht).2)
    (fun t ht => by have := (hmem t ht).1; show (1 : ℝ) - t ^ 2 ≠ 0; exact ne_of_gt (by linarith))
    (fun t ht => af_sq (hmem t ht).1 (hmem t ht).2)
    (fun t ht => by
      have hgt : -1 < t := by nlinarith [(hmem t ht).1, h0.trans ht.1]
      have hd := hasDerivAt_regSol (sqC c) σ hgt
      have hpv := pP_mul_regV (sqC c) σ hgt
      unfold pP at hpv
      have hp : (1 : ℝ) - t ^ 2 ≠ 0 := by have := (hmem t ht).1; nlinarith
      refine hd.congr_deriv ?_
      field_simp; linarith)
    (fun t ht => by
      have hgt : -1 < t := by nlinarith [(hmem t ht).1, h0.trans ht.1]
      refine (hasDerivAt_regU (sqC c) σ hgt).neg.congr_deriv ?_
      rw [qf_eq hc, sqC_apply]; ring)
    (fun t ht => hasDerivAt_af (hmem t ht).1 (hmem t ht).2)
    (fun t ht => hasDerivAt_wf (hmem t ht).1 (hmem t ht).2)
    (fun t ht => (wd_neg hc (hmem t ht).1 (hmem t ht).2).le)
    (fun t ht => by
      have hw0 := wf_nonpos (h0.trans ht.1) (hmem t ht).1 (hmem t ht).2
      refine ⟨?_, hw0⟩
      have hanti := (wf_strictAntiOn (K := K) hc (h0.trans ht.1) hs hq).antitoneOn
        ⟨le_rfl, ht.2⟩ ⟨ht.2, le_rfl⟩ ht.2
      have := neg_abs_le (wf c K t₁)
      linarith)
  rwa [hneg, hneg] at h

/-- `af` is continuous. -/
theorem continuous_af (c K : ℝ) : Continuous (af c K) := by
  unfold af qf; fun_prop

/-- The stretch `m(t) = ½∫_{½}^{t} 1/a` at `K = (c² − σ)/c`. -/
def stretch (c σ t : ℝ) : ℝ := 1 / 2 * ∫ s in (1 / 2 : ℝ)..t, 1 / af c ((c ^ 2 - σ) / c) s

/-- `y² ≤ G/a` where `a > 0`. -/
theorem sq_le_energyAt_div {t : ℝ} (ha : 0 < af c ((c ^ 2 - σ) / c) t) :
    regSol (sqC c) σ t ^ 2 ≤ energyAt c σ t / af c ((c ^ 2 - σ) / c) t := by
  rw [le_div_iff₀ ha]
  unfold energyAt Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact.energy
  have : 0 ≤ regU (sqC c) σ t ^ 2 / af c ((c ^ 2 - σ) / c) t := by positivity
  nlinarith

/-- **Lemma 3.4 (the stretch, upper)**: for `½ ≤ t₁`, `t₁² < 1`, `q(t₁) > 0` and `|w(t₁)| ≤ M < 2`,
`∫_{½}^{t₁} y² ≤ κ(M) G₀ · 2m(t₁)`. -/
theorem integral_sq_le_stretch (hc : c ≠ 0) {t₁ M : ℝ} (hh : 1 / 2 ≤ t₁) (hs : t₁ ^ 2 < 1)
    (hq : 0 < qf c ((c ^ 2 - σ) / c) t₁) (hM : M < 2) (hwM : |wf c ((c ^ 2 - σ) / c) t₁| ≤ M) :
    ∫ s in (1 / 2 : ℝ)..t₁, regSol (sqC c) σ s ^ 2 ≤ kappa M * energyHalf c σ * (2 * stretch c σ t₁) := by
  set K := (c ^ 2 - σ) / c
  have h0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hmem := fun t (ht : t ∈ Icc (1 / 2 : ℝ) t₁) => mem_allowed h0 hs hq ht
  have ha : ∀ t ∈ Icc (1 / 2 : ℝ) t₁, 0 < af c K t := fun t ht => af_pos (hmem t ht).1 (hmem t ht).2
  have hsub : Icc (1 / 2 : ℝ) t₁ ⊆ Ioi (-1) := fun t ht => by simp only [mem_Ioi]; linarith [ht.1]
  have hyc : ContinuousOn (fun s => regSol (sqC c) σ s ^ 2) (uIcc (1 / 2 : ℝ) t₁) := by
    rw [uIcc_of_le hh]; exact ((continuousOn_regSol (sqC c) σ).mono hsub).pow 2
  have hac : ContinuousOn (fun s => 1 / af c K s) (uIcc (1 / 2 : ℝ) t₁) := by
    rw [uIcc_of_le hh]
    exact continuousOn_const.div (continuous_af c K).continuousOn fun t ht => (ha t ht).ne'
  have hrhs : kappa M * energyHalf c σ * (2 * stretch c σ t₁) =
      ∫ s in (1 / 2 : ℝ)..t₁, kappa M * energyHalf c σ * (1 / af c K s) := by
    rw [intervalIntegral.integral_const_mul]; unfold stretch; ring
  rw [hrhs]
  refine intervalIntegral.integral_mono_on hh hyc.intervalIntegrable
    (hac.const_smul (kappa M * energyHalf c σ)).intervalIntegrable fun t ht => ?_
  have hwt : |wf c K t| ≤ M :=
    ((abs_wf_strictMonoOn hc h0 hs hq).monotoneOn ht ⟨hh, le_rfl⟩ ht.2).trans hwM
  have hst : t ^ 2 < 1 := (hmem t ht).1
  have hk := (energyAt_le_kappa hc h0 ht.1 hst (hmem t ht).2 hM hwt).1
  have h1 := sq_le_energyAt_div (ha t ht)
  calc regSol (sqC c) σ t ^ 2 ≤ energyAt c σ t / af c K t := h1
    _ ≤ kappa M * energyAt c σ (1 / 2) / af c K t := div_le_div_of_nonneg_right hk (ha t ht).le
    _ = kappa M * energyHalf c σ * (1 / af c K t) := by rw [energyAt_half]; ring

/-- The layer bound `∫_{t₁}^1 y² ≤ L G(t₁)`, the interface of Lemmas 3.6–3.8. -/
def LayerBound (c σ t₁ L : ℝ) : Prop := ∫ s in t₁..1, regSol (sqC c) σ s ^ 2 ≤ L * energyAt c σ t₁

/-- `N = ∫_{½}^{t₁} y² + ∫_{t₁}^1 y²`. -/
theorem nodeMass_split (c σ t₁ : ℝ) (hh : 1 / 2 ≤ t₁) :
    nodeMass c σ = (∫ s in (1 / 2 : ℝ)..t₁, regSol (sqC c) σ s ^ 2) + ∫ s in t₁..1, regSol (sqC c) σ s ^ 2 := by
  have hc : ContinuousOn (fun s => regSol (sqC c) σ s ^ 2) (Ioi (-1)) := (continuousOn_regSol (sqC c) σ).pow 2
  have hi : ∀ a b : ℝ, 1 / 2 ≤ a → 1 / 2 ≤ b →
      IntervalIntegrable (fun s => regSol (sqC c) σ s ^ 2) volume a b := fun a b ha hb =>
    (hc.mono fun t ht => by
      simp only [mem_Ioi]; rcases le_total a b with h | h
      · rw [uIcc_of_le h] at ht; linarith [ht.1]
      · rw [uIcc_of_ge h] at ht; linarith [ht.1]).intervalIntegrable
  unfold nodeMass
  rw [intervalIntegral.integral_add_adjacent_intervals (hi _ _ le_rfl hh) (hi _ _ hh (by linarith))]

/-- **The upper bound for `N`**: under `integral_sq_le_stretch`'s hypotheses and a layer bound with `L ≥ 0`,
`N ≤ κ(M)(2m(t₁) + L) G₀`. -/
theorem nodeMass_le (hc : c ≠ 0) {t₁ M L : ℝ} (hh : 1 / 2 ≤ t₁) (hs : t₁ ^ 2 < 1)
    (hq : 0 < qf c ((c ^ 2 - σ) / c) t₁) (hM : M < 2) (hwM : |wf c ((c ^ 2 - σ) / c) t₁| ≤ M)
    (hL0 : 0 ≤ L) (hL : LayerBound c σ t₁ L) :
    nodeMass c σ ≤ kappa M * (2 * stretch c σ t₁ + L) * energyHalf c σ := by
  rw [nodeMass_split c σ t₁ hh]
  have h1 := integral_sq_le_stretch hc hh hs hq hM hwM
  have h2 := (energyAt_le_kappa hc (by norm_num) hh hs hq hM hwM).1
  rw [energyAt_half] at h2
  have h3 : L * energyAt c σ t₁ ≤ L * (kappa M * energyHalf c σ) := mul_le_mul_of_nonneg_left h2 hL0
  unfold LayerBound at hL
  nlinarith

/-! ### Lemma 3.5: period averaging -/

/-- **Period averaging**: if `m ≤ h ≤ e^Λ m` on `[α, α + π]` and `h` is continuous there, then
`(e^{−Λ}/2) ∫_α^{α+π} h ≤ ∫_α^{α+π} h cos²`. -/
theorem integral_mul_cos_sq_ge {h : ℝ → ℝ} {α m Λ : ℝ} (hc : ContinuousOn h (Icc α (α + π)))
    (hm : ∀ φ ∈ Icc α (α + π), m ≤ h φ ∧ h φ ≤ exp Λ * m) :
    exp (-Λ) / 2 * ∫ φ in α..α + π, h φ ≤ ∫ φ in α..α + π, h φ * cos φ ^ 2 := by
  have hle : α ≤ α + π := by linarith [pi_pos]
  have hc' : ContinuousOn h (uIcc α (α + π)) := by rwa [uIcc_of_le hle]
  have hup : ∫ φ in α..α + π, h φ ≤ ∫ φ in α..α + π, exp Λ * m :=
    intervalIntegral.integral_mono_on hle hc'.intervalIntegrable intervalIntegrable_const
      fun φ hφ => (hm φ hφ).2
  have hlo : ∫ φ in α..α + π, m * cos φ ^ 2 ≤ ∫ φ in α..α + π, h φ * cos φ ^ 2 :=
    intervalIntegral.integral_mono_on hle ((by fun_prop : Continuous fun φ => m * cos φ ^ 2).intervalIntegrable _ _)
      (hc'.mul (by fun_prop : Continuous fun φ => cos φ ^ 2).continuousOn).intervalIntegrable
      fun φ hφ => mul_le_mul_of_nonneg_right (hm φ hφ).1 (sq_nonneg _)
  have hcos : ∫ φ in α..α + π, m * cos φ ^ 2 = m * (π / 2) := by
    rw [intervalIntegral.integral_const_mul, integral_cos_sq, cos_add_pi, sin_add_pi]; ring
  rw [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left] at hup
  rw [hcos] at hlo
  have he : exp (-Λ) * exp Λ = 1 := by rw [← exp_add]; simp
  have hpos : 0 ≤ exp (-Λ) / 2 := by positivity
  calc exp (-Λ) / 2 * ∫ φ in α..α + π, h φ ≤ exp (-Λ) / 2 * (π * (exp Λ * m)) := mul_le_mul_of_nonneg_left hup hpos
    _ = m * (π / 2) := by rw [show exp (-Λ) / 2 * (π * (exp Λ * m)) = exp (-Λ) * exp Λ * (m * (π / 2)) by ring, he,
          one_mul]
    _ ≤ _ := hlo

/-! ### The layer lemmas and Lemma 3.5, as hypotheses -/

/-- **Lemma 3.6 (Airy layer)**: for `σ < c²`, `t₂ ∈ [½, 1)` with `|w(t₂)| = ½`, `q(t₂) > 0`, `a(t₂) ≥ 4t₂` and
`√σ/c − t₂ ≤ (1 − t₂²)/4`, `∫_{t₂}^1 y² ≤ 170 G(t₂)/q(t₂)`. -/
def AiryLayer (c σ t₂ : ℝ) : Prop :=
  σ < c ^ 2 → 1 / 2 ≤ t₂ → t₂ < 1 → |wf c ((c ^ 2 - σ) / c) t₂| = 1 / 2 → 0 < qf c ((c ^ 2 - σ) / c) t₂ →
    4 * t₂ ≤ af c ((c ^ 2 - σ) / c) t₂ → √σ / c - t₂ ≤ (1 - t₂ ^ 2) / 4 →
    LayerBound c σ t₂ (170 / qf c ((c ^ 2 - σ) / c) t₂)

/-- **Lemma 3.7(a) (Bessel layer)**: for `β = (σ − c²)/(2c) ≥ 8` and `t₃ = 1 − 1/(4cβ)`,
`∫_{t₃}^1 y² ≤ 4.35 (1 − t₃) G(t₃)/a(t₃)`. -/
def BesselLayer (c σ : ℝ) : Prop :=
  8 ≤ (σ - c ^ 2) / (2 * c) →
    LayerBound c σ (1 - 1 / (2 * (σ - c ^ 2)))
      (435 / 100 * (1 / (2 * (σ - c ^ 2))) / af c ((c ^ 2 - σ) / c) (1 - 1 / (2 * (σ - c ^ 2))))

/-- **Lemma 3.8 (Coulomb layer)**: there is `K_C` with `|w(1 − U₀/c)| ≤ ½` and `∫_{1−U₀/c}^1 y² ≤ K_C G(1 − U₀/c)/c`
for all `c ≥ c₀` and `|β| ≤ B`, `U₀ = 4B + 4`. -/
def CoulombLayer (B c₀ : ℝ) : Prop :=
  ∃ KC : ℝ, 0 ≤ KC ∧ ∀ c σ : ℝ, c₀ ≤ c → |(σ - c ^ 2) / (2 * c)| ≤ B →
    |wf c ((c ^ 2 - σ) / c) (1 - (4 * B + 4) / c)| ≤ 1 / 2 ∧ LayerBound c σ (1 - (4 * B + 4) / c) (KC / c)

/-- The phase-oscillation constant `Λ(M) = 3πM/(1 − M/2) + ln((1 + M/2)/(1 − M/2))` of Lemma 3.5. -/
def oscConst (M : ℝ) : ℝ := 3 * π * M / (1 - M / 2) + Real.log ((1 + M / 2) / (1 - M / 2))

/-- **Lemma 3.5 (the stretch, lower)**: for `0 < M ≤ ½`, `t ∈ [½, 1)` with `q(t) > 0` and `|w(t)| = M`,
`∫_{½}^{t} y² ≥ (e^{−Λ(M)}/2) G₀ (2m(t)/κ(M) − 2πκ(M)/((1 − M/2) q(t)))`. -/
def PeriodAveraging (c σ t M : ℝ) : Prop :=
  0 < M → M ≤ 1 / 2 → 1 / 2 ≤ t → t < 1 → 0 < qf c ((c ^ 2 - σ) / c) t → |wf c ((c ^ 2 - σ) / c) t| = M →
  exp (-oscConst M) / 2 * energyHalf c σ *
      (2 * stretch c σ t / kappa M - 2 * π * kappa M / ((1 - M / 2) * qf c ((c ^ 2 - σ) / c) t)) ≤
    ∫ s in (1 / 2 : ℝ)..t, regSol (sqC c) σ s ^ 2

/-- **The lower bound for `N`**: from Lemma 3.5 at `(t, M)`, `|w(t)| = M`, with the incomplete-period correction
at most `ε m(t)`, `N ≥ (e^{−Λ(M)}/2)(2/κ(M) − ε) m(t) G₀`. -/
theorem nodeMass_ge {t M ε : ℝ} (hM0 : 0 < M) (hM : M ≤ 1 / 2) (ht : 1 / 2 ≤ t) (ht1 : t < 1)
    (hq : 0 < qf c ((c ^ 2 - σ) / c) t) (hw : |wf c ((c ^ 2 - σ) / c) t| = M) (hP : PeriodAveraging c σ t M)
    (hG : 0 ≤ energyHalf c σ)
    (hε : 2 * π * kappa M / ((1 - M / 2) * qf c ((c ^ 2 - σ) / c) t) ≤ ε * stretch c σ t) :
    exp (-oscConst M) / 2 * (2 / kappa M - ε) * stretch c σ t * energyHalf c σ ≤ nodeMass c σ := by
  have hsplit := nodeMass_split c σ t ht
  have hrest : 0 ≤ ∫ s in t..1, regSol (sqC c) σ s ^ 2 :=
    intervalIntegral.integral_nonneg ht1.le fun s _ => sq_nonneg _
  have hE : 0 ≤ exp (-oscConst M) / 2 * energyHalf c σ := by positivity
  have h1 : exp (-oscConst M) / 2 * energyHalf c σ * (2 * stretch c σ t / kappa M - ε * stretch c σ t) ≤
      exp (-oscConst M) / 2 * energyHalf c σ *
        (2 * stretch c σ t / kappa M - 2 * π * kappa M / ((1 - M / 2) * qf c ((c ^ 2 - σ) / c) t)) :=
    mul_le_mul_of_nonneg_left (by linarith) hE
  replace hP := hP hM0 hM ht ht1 hq hw
  have e : exp (-oscConst M) / 2 * (2 / kappa M - ε) * stretch c σ t * energyHalf c σ =
      exp (-oscConst M) / 2 * energyHalf c σ * (2 * stretch c σ t / kappa M - ε * stretch c σ t) := by ring
  rw [e]
  linarith

/-- **Lemma 3.8 in use**: under `CoulombLayer B c₀`, for `c ≥ max c₀ 1`, `|β| ≤ B` and the allowed point
`t₁ = 1 − U₀/c ≥ ½`, `N ≤ κ(½)(2m(t₁) + K_C/c) G₀`. -/
theorem nodeMass_le_coulomb {B c₀ : ℝ} (hC : CoulombLayer B c₀) :
    ∃ KC : ℝ, 0 ≤ KC ∧ ∀ c σ : ℝ, c₀ ≤ c → 0 < c → |(σ - c ^ 2) / (2 * c)| ≤ B →
      1 / 2 ≤ 1 - (4 * B + 4) / c → (1 - (4 * B + 4) / c) ^ 2 < 1 →
      0 < qf c ((c ^ 2 - σ) / c) (1 - (4 * B + 4) / c) →
      nodeMass c σ ≤ kappa (1 / 2) * (2 * stretch c σ (1 - (4 * B + 4) / c) + KC / c) * energyHalf c σ := by
  obtain ⟨KC, hKC, h⟩ := hC
  refine ⟨KC, hKC, fun c σ hc0 hc hβ hh hs hq => ?_⟩
  obtain ⟨hw, hL⟩ := h c σ hc0 hβ
  exact nodeMass_le hc.ne' hh hs hq (by norm_num) hw (by positivity) hL

/-- **Lemma 3.6 in use**: under `AiryLayer c σ t₂` and its conditions, `N ≤ κ(½)(2m(t₂) + 170/q(t₂)) G₀`. -/
theorem nodeMass_le_airy (hc : 0 < c) {t₂ : ℝ} (hA : AiryLayer c σ t₂) (hσ : σ < c ^ 2) (hh : 1 / 2 ≤ t₂)
    (h1 : t₂ < 1) (hw : |wf c ((c ^ 2 - σ) / c) t₂| = 1 / 2) (hq : 0 < qf c ((c ^ 2 - σ) / c) t₂)
    (ha : 4 * t₂ ≤ af c ((c ^ 2 - σ) / c) t₂) (hd : √σ / c - t₂ ≤ (1 - t₂ ^ 2) / 4) :
    nodeMass c σ ≤ kappa (1 / 2) * (2 * stretch c σ t₂ + 170 / qf c ((c ^ 2 - σ) / c) t₂) * energyHalf c σ :=
  nodeMass_le hc.ne' hh (by nlinarith) hq (by norm_num) hw.le (by positivity) (hA hσ hh h1 hw hq ha hd)

/-- **Lemma 3.7 in use**: under `BesselLayer c σ`, `β ≥ 8`, `t₃ = 1 − 1/(2(σ − c²)) ≥ ½`, `q(t₃) > 0` and
`|w(t₃)| ≤ M < 2`, `N ≤ κ(M)(2m(t₃) + 4.35(1 − t₃)/a(t₃)) G₀`. -/
theorem nodeMass_le_bessel (hc : 0 < c) {M : ℝ} (hB : BesselLayer c σ) (hβ : 8 ≤ (σ - c ^ 2) / (2 * c))
    (hh : 1 / 2 ≤ 1 - 1 / (2 * (σ - c ^ 2))) (hq : 0 < qf c ((c ^ 2 - σ) / c) (1 - 1 / (2 * (σ - c ^ 2))))
    (hM : M < 2) (hw : |wf c ((c ^ 2 - σ) / c) (1 - 1 / (2 * (σ - c ^ 2)))| ≤ M) :
    nodeMass c σ ≤ kappa M * (2 * stretch c σ (1 - 1 / (2 * (σ - c ^ 2))) +
      435 / 100 * (1 / (2 * (σ - c ^ 2))) / af c ((c ^ 2 - σ) / c) (1 - 1 / (2 * (σ - c ^ 2)))) *
        energyHalf c σ := by
  have hσ : 0 < σ - c ^ 2 := by
    have : 0 < (σ - c ^ 2) / (2 * c) := by linarith
    have h2 : 0 < 2 * c := by positivity
    exact (div_pos_iff_of_pos_right h2).mp this
  have hs0 : 0 < 1 / (2 * (σ - c ^ 2)) := by positivity
  have hs : (1 - 1 / (2 * (σ - c ^ 2))) ^ 2 < 1 := by nlinarith
  exact nodeMass_le hc.ne' hh hs hq hM hw (div_nonneg (by positivity) (Real.sqrt_nonneg _)) (hB hβ)

end Cvs.Prolate.LiouvilleGreen.AdiabaticStretchBounds
