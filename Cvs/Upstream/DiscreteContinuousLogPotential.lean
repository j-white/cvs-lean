import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Discrete versus continuous log potentials (eq-cpb Lemma 11)

If a finite point set `Y ⊆ [0, B]` counts like `cν` up to `E` on every half-line, then by the layer-cake formula
`Σ_Y log max(|y − p|, r)` and `c∫ log max(|y − v|, r) dν` differ by at most `3E log(B/r) + E|log r|`; with a local bound
`∫_{|v − y| < r} log(r/|y − v|) dν ≤ A√r` and `ν(|v − y| < r) ≤ A√r` this bounds `Σ_{p ≠ y} log|y − p|` above, and
below when the points avoid `(y − γ, y + γ)`.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory

namespace Cvs.Upstream.DiscreteContinuousLogPotential

/-! ### Two measures with close distribution functions -/

section Compare

variable (μ₁ μ₂ : Measure ℝ) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]

/-- The discrepancy on the complement of an open interval. -/
theorem abs_meas_union_sub_le {E : ℝ} (hIic : ∀ u, |μ₁.real (Iic u) - μ₂.real (Iic u)| ≤ E)
    (hIio : ∀ u, |μ₁.real (Iio u) - μ₂.real (Iio u)| ≤ E) (huniv : |μ₁.real univ - μ₂.real univ| ≤ E)
    {α β : ℝ} (hαβ : α < β) :
    |μ₁.real (Iic α ∪ Ici β) - μ₂.real (Iic α ∪ Ici β)| ≤ 3 * E := by
  have hd : Disjoint (Iic α) (Ici β) := Set.disjoint_left.mpr fun v h1 h2 => by
    simp only [mem_Iic, mem_Ici] at h1 h2; linarith
  have hu : ∀ μ : Measure ℝ, [IsFiniteMeasure μ] → μ.real (Iic α ∪ Ici β) =
      μ.real (Iic α) + (μ.real univ - μ.real (Iio β)) := fun μ _ => by
    rw [measureReal_union hd measurableSet_Ici, ← compl_Iio, measureReal_compl measurableSet_Iio]
  rw [hu μ₁, hu μ₂]
  have h1 := hIic α
  have h2 := hIio β
  rw [abs_le] at h1 h2 huniv ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, huniv.1, huniv.2]

/-- **Koksma for unimodal integrands**: for `0 ≤ g ≤ M` measurable whose superlevel sets `{g ≥ s}`, `s > 0`, are
complements of open intervals, `|∫ g dμ₁ − ∫ g dμ₂| ≤ 3EM`. -/
theorem abs_integral_sub_le {E M : ℝ} (hIic : ∀ u, |μ₁.real (Iic u) - μ₂.real (Iic u)| ≤ E)
    (hIio : ∀ u, |μ₁.real (Iio u) - μ₂.real (Iio u)| ≤ E) (huniv : |μ₁.real univ - μ₂.real univ| ≤ E)
    {g : ℝ → ℝ} (hg : Measurable g) (hg0 : ∀ v, 0 ≤ g v) (hM : 0 ≤ M) (hgM₁ : ∀ᵐ v ∂μ₁, g v ≤ M)
    (hgM₂ : ∀ᵐ v ∂μ₂, g v ≤ M) (hshape : ∀ s > 0, ∃ α β, α < β ∧ {v | s ≤ g v} = Iic α ∪ Ici β) :
    |∫ v, g v ∂μ₁ - ∫ v, g v ∂μ₂| ≤ 3 * E * M := by
  have hint : ∀ μ : Measure ℝ, [IsFiniteMeasure μ] → (∀ᵐ v ∂μ, g v ≤ M) → Integrable g μ := fun μ _ h =>
    Integrable.of_bound hg.aestronglyMeasurable M (h.mono fun v hv => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 v)]; exact hv)
  rw [(hint μ₁ hgM₁).integral_eq_integral_Ioc_meas_le (Eventually.of_forall hg0) hgM₁,
    (hint μ₂ hgM₂).integral_eq_integral_Ioc_meas_le (Eventually.of_forall hg0) hgM₂]
  have hfin : volume (Ioc (0 : ℝ) M) < ⊤ := measure_Ioc_lt_top
  have hi : ∀ μ : Measure ℝ, [IsFiniteMeasure μ] →
      IntegrableOn (fun s => μ.real {a | s ≤ g a}) (Ioc 0 M) := fun μ _ => by
    refine Measure.integrableOn_of_bounded (M := μ.real univ) hfin.ne ?_ ?_
    · refine (Antitone.measurable fun s t hst => ?_).aestronglyMeasurable
      exact measureReal_mono fun a ha => le_trans hst ha
    · exact Eventually.of_forall fun s => by
        rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]; exact measureReal_mono (subset_univ _)
  rw [← integral_sub (hi μ₁) (hi μ₂)]
  have hb : ∀ s ∈ Ioc (0 : ℝ) M, ‖μ₁.real {a | s ≤ g a} - μ₂.real {a | s ≤ g a}‖ ≤ 3 * E := by
    intro s hs
    obtain ⟨α, β, hαβ, hset⟩ := hshape s hs.1
    rw [Real.norm_eq_abs, hset]
    exact abs_meas_union_sub_le μ₁ μ₂ hIic hIio huniv hαβ
  have := norm_setIntegral_le_of_norm_le_const hfin hb
  rw [Real.norm_eq_abs, Real.volume_real_Ioc_of_le hM] at this
  linarith

end Compare

/-! ### The point measure -/

/-- The counting measure `Σ_{p ∈ Y} δ_p` of a finite point set. -/
def ptMeas (Y : Finset ℝ) : Measure ℝ := ∑ p ∈ Y, Measure.dirac p

instance (Y : Finset ℝ) : IsFiniteMeasure (ptMeas Y) := by
  unfold ptMeas; infer_instance

theorem ptMeas_real (Y : Finset ℝ) {S : Set ℝ} [DecidablePred (· ∈ S)] (hS : MeasurableSet S) :
    (ptMeas Y).real S = ((Y.filter (· ∈ S)).card : ℝ) := by
  classical
  unfold ptMeas
  rw [measureReal_def, Measure.coe_finsetSum, Finset.sum_apply]
  simp_rw [Measure.dirac_apply' _ hS]
  rw [ENNReal.toReal_sum (fun p _ => by simp [Set.indicator]; split_ifs <;> simp)]
  simp only [Set.indicator, Pi.one_apply]
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs <;> simp

theorem integral_ptMeas (Y : Finset ℝ) (g : ℝ → ℝ) : ∫ v, g v ∂(ptMeas Y) = ∑ p ∈ Y, g p := by
  unfold ptMeas
  rw [integral_finsetSum_measure (fun p _ => integrable_dirac (by simp))]
  simp

/-! ### The truncated logarithm -/

/-- `log max(|y − v|, r)`. -/
def logTr (y r v : ℝ) : ℝ := log (max |y - v| r)

theorem measurable_logTr (y r : ℝ) : Measurable (logTr y r) := by
  unfold logTr; fun_prop

theorem log_abs_le_logTr {y r v : ℝ} (hv : v ≠ y) : log |y - v| ≤ logTr y r v :=
  Real.log_le_log (abs_pos.mpr (sub_ne_zero.mpr hv.symm)) (le_max_left _ _)

theorem logTr_eq_log_abs {y r v : ℝ} (hv : r ≤ |y - v|) : logTr y r v = log |y - v| := by
  unfold logTr; rw [max_eq_left hv]

theorem log_le_logTr {y r v : ℝ} (hr : 0 < r) : log r ≤ logTr y r v :=
  Real.log_le_log hr (le_max_right _ _)

/-! ### The truncated potentials -/

section Potential

variable (ν : Measure ℝ) [IsFiniteMeasure ν] (Y : Finset ℝ)

/-- **Truncated comparison**: under the half-line count bounds, `|Σ_Y log max(|y − p|, r) − c∫ log max(|y − v|, r) dν|`
is at most `3E(log B − log r) + E|log r|` for `y` and both supports in `[0, B]`, `0 < r ≤ 1 ≤ B`. -/
theorem abs_sum_logTr_sub_le {c E B y r : ℝ} (hc : 0 ≤ c) (hB : 1 ≤ B) (hr : 0 < r) (hr1 : r ≤ 1)
    (hy : y ∈ Icc 0 B) (hsupp : ν (Icc 0 B)ᶜ = 0) (hY : ∀ p ∈ Y, p ∈ Icc 0 B)
    (hIic : ∀ u, |(ptMeas Y).real (Iic u) - c * ν.real (Iic u)| ≤ E)
    (hIio : ∀ u, |(ptMeas Y).real (Iio u) - c * ν.real (Iio u)| ≤ E) :
    |∑ p ∈ Y, logTr y r p - c * ∫ v, logTr y r v ∂ν| ≤ 3 * E * (log B - log r) + E * |log r| := by
  set μ₂ := ENNReal.ofReal c • ν with hμ₂
  have : IsFiniteMeasure μ₂ := ⟨by
    rw [hμ₂, Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top ν univ)⟩
  have hreal : ∀ S, μ₂.real S = c * ν.real S := fun S => by
    rw [hμ₂, measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal hc]
  have hIic' : ∀ u, |(ptMeas Y).real (Iic u) - μ₂.real (Iic u)| ≤ E := fun u => by rw [hreal]; exact hIic u
  have hIio' : ∀ u, |(ptMeas Y).real (Iio u) - μ₂.real (Iio u)| ≤ E := fun u => by rw [hreal]; exact hIio u
  have hνae : ∀ᵐ v ∂ν, v ∈ Icc 0 B := by
    rw [ae_iff]; simpa [compl_def] using hsupp
  have hunivν : ν.real univ = ν.real (Iic B) := by
    have h0 : ν (Iic B)ᶜ = 0 := measure_mono_null (fun v hv => fun h => hv h.2) hsupp
    have h1 : ν.real (Iic B)ᶜ = 0 := by rw [measureReal_def, h0, ENNReal.toReal_zero]
    have := measureReal_compl (μ := ν) (s := Iic B) measurableSet_Iic
    linarith
  have hunivY : (ptMeas Y).real univ = (ptMeas Y).real (Iic B) := by
    classical
    rw [ptMeas_real Y MeasurableSet.univ, ptMeas_real Y measurableSet_Iic]
    congr 2
    refine Finset.filter_congr fun p hp => ?_
    simp [(hY p hp).2]
  have huniv : |(ptMeas Y).real univ - μ₂.real univ| ≤ E := by
    rw [hreal, hunivν, hunivY]; exact hIic B
  set g : ℝ → ℝ := fun v => logTr y r v - log r with hg
  have hgm : Measurable g := (measurable_logTr y r).sub_const _
  have hg0 : ∀ v, 0 ≤ g v := fun v => by simp only [hg]; linarith [log_le_logTr (y := y) (v := v) hr]
  have hM : 0 ≤ log B - log r := by
    have := Real.log_le_log hr (hr1.trans hB); linarith
  have hgM : ∀ v ∈ Icc 0 B, g v ≤ log B - log r := fun v hv => by
    simp only [hg, logTr]
    have : max |y - v| r ≤ B := max_le (abs_le.mpr ⟨by linarith [hv.2, hy.1], by linarith [hv.1, hy.2]⟩)
      (hr1.trans hB)
    have := Real.log_le_log (lt_max_of_lt_right hr) this
    linarith
  have hgM₁ : ∀ᵐ v ∂(ptMeas Y), g v ≤ log B - log r := by
    rw [ae_iff]
    have hmeas : MeasurableSet {v | ¬g v ≤ log B - log r} := by
      simp only [not_le]; exact measurableSet_lt measurable_const hgm
    unfold ptMeas
    rw [Measure.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Measure.dirac_apply' _ hmeas, Set.indicator_of_notMem]
    simp only [mem_ofPred_eq, not_not]
    exact hgM p (hY p hp)
  have hgM₂ : ∀ᵐ v ∂μ₂, g v ≤ log B - log r :=
    Measure.ae_smul_measure (hνae.mono fun v hv => hgM v hv) _
  have hshape : ∀ s > 0, ∃ α β, α < β ∧ {v | s ≤ g v} = Iic α ∪ Ici β := by
    intro s hs
    have hre : r < r * Real.exp s := by
      have := Real.one_lt_exp_iff.mpr hs; nlinarith
    refine ⟨y - r * Real.exp s, y + r * Real.exp s, by linarith, ?_⟩
    ext v
    simp only [mem_ofPred_eq, mem_union, mem_Iic, mem_Ici, hg, logTr]
    have hmax : 0 < max |y - v| r := lt_max_of_lt_right hr
    have key : s ≤ log (max |y - v| r) - log r ↔ r * Real.exp s ≤ max |y - v| r := by
      rw [← Real.log_le_log_iff (by positivity) hmax, Real.log_mul hr.ne' (Real.exp_pos s).ne', Real.log_exp]
      constructor <;> intro h <;> linarith
    rw [key]
    constructor
    · intro h
      have h' : r * Real.exp s ≤ |y - v| := by
        rcases le_total |y - v| r with h2 | h2
        · rw [max_eq_right h2] at h; linarith
        · rwa [max_eq_left h2] at h
      rcases le_abs'.mp h' with h3 | h3
      · right; linarith
      · left; linarith
    · intro h
      refine le_max_of_le_left ?_
      rcases h with h | h
      · rw [abs_of_nonneg (by linarith)]; linarith
      · rw [abs_of_nonpos (by linarith)]; linarith
  have hcmp := abs_integral_sub_le (ptMeas Y) μ₂ hIic' hIio' huniv hgm hg0 hM hgM₁ hgM₂ hshape
  -- unfold the two integrals
  have hbdd : ∀ᵐ v ∂ν, ‖logTr y r v‖ ≤ |log r| + |log B| := hνae.mono fun v hv => by
    have h1 := log_le_logTr (y := y) (v := v) hr
    have h2 := hgM v hv
    simp only [hg] at h2
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [neg_abs_le (log r), le_abs_self (log B), le_abs_self (log r), neg_abs_le (log B)]
  have hintν : Integrable (logTr y r) ν := Integrable.of_bound (measurable_logTr y r).aestronglyMeasurable _ hbdd
  have e1 : ∫ v, g v ∂(ptMeas Y) = ∑ p ∈ Y, logTr y r p - (ptMeas Y).real univ * log r := by
    classical
    rw [integral_ptMeas, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ptMeas_real Y MeasurableSet.univ]
    simp
  have e2 : ∫ v, g v ∂μ₂ = c * ∫ v, logTr y r v ∂ν - μ₂.real univ * log r := by
    rw [hμ₂, integral_smul_measure, ENNReal.toReal_ofReal hc, smul_eq_mul, integral_sub hintν (integrable_const _),
      integral_const, smul_eq_mul, ← hμ₂, hreal]
    ring
  rw [e1, e2] at hcmp
  have hE0 : 0 ≤ E := (abs_nonneg _).trans (hIic 0)
  have hlog : |((ptMeas Y).real univ - μ₂.real univ) * log r| ≤ E * |log r| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right huniv (abs_nonneg _)
  calc |∑ p ∈ Y, logTr y r p - c * ∫ v, logTr y r v ∂ν|
      = |(∑ p ∈ Y, logTr y r p - (ptMeas Y).real univ * log r - (c * ∫ v, logTr y r v ∂ν -
          μ₂.real univ * log r)) + ((ptMeas Y).real univ - μ₂.real univ) * log r| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hcmp hlog)

/-- **Lemma 11 (U)**: `Σ_{p ∈ Y, p ≠ y} log|y − p| ≤ c∫ log|y − v| dν + cA√r + 3E(log B − log r) + (E + 1)|log r|`
when `∫ (log max(|y − v|, r) − log|y − v|) dν ≤ A√r`. -/
theorem sum_log_le {c E B y r A : ℝ} (hc : 0 ≤ c) (hB : 1 ≤ B) (hr : 0 < r) (hr1 : r ≤ 1)
    (hy : y ∈ Icc 0 B) (hsupp : ν (Icc 0 B)ᶜ = 0) (hY : ∀ p ∈ Y, p ∈ Icc 0 B)
    (hIic : ∀ u, |(ptMeas Y).real (Iic u) - c * ν.real (Iic u)| ≤ E)
    (hIio : ∀ u, |(ptMeas Y).real (Iio u) - c * ν.real (Iio u)| ≤ E)
    (hint : Integrable (fun v => log |y - v|) ν)
    (hloc : ∫ v, (logTr y r v - log |y - v|) ∂ν ≤ A * √r) :
    ∑ p ∈ Y.erase y, log |y - p| ≤
      c * ∫ v, log |y - v| ∂ν + c * (A * √r) + 3 * E * (log B - log r) + (E + 1) * |log r| := by
  have hcmp := abs_sum_logTr_sub_le ν Y hc hB hr hr1 hy hsupp hY hIic hIio
  have h1 : ∑ p ∈ Y.erase y, log |y - p| ≤ ∑ p ∈ Y.erase y, logTr y r p :=
    Finset.sum_le_sum fun p hp => log_abs_le_logTr (Finset.ne_of_mem_erase hp)
  have h2 : ∑ p ∈ Y.erase y, logTr y r p ≤ ∑ p ∈ Y, logTr y r p + |log r| := by
    by_cases hyY : y ∈ Y
    · rw [← Finset.add_sum_erase Y _ hyY]
      have : logTr y r y = log r := by simp [logTr, max_eq_right hr.le]
      rw [this]; linarith [neg_abs_le (log r)]
    · rw [Finset.erase_eq_of_notMem hyY]; linarith [abs_nonneg (log r)]
  have hνae : ∀ᵐ v ∂ν, v ∈ Icc 0 B := by
    rw [ae_iff]; simpa [compl_def] using hsupp
  have hintTr : Integrable (logTr y r) ν := by
    refine Integrable.of_bound (measurable_logTr y r).aestronglyMeasurable (|log r| + |log B|)
      (hνae.mono fun v hv => ?_)
    have h1 := log_le_logTr (y := y) (v := v) hr
    have hm : max |y - v| r ≤ B := max_le (abs_le.mpr ⟨by linarith [hv.2, hy.1], by linarith [hv.1, hy.2]⟩)
      (hr1.trans hB)
    have h2 := Real.log_le_log (lt_max_of_lt_right hr) hm
    rw [Real.norm_eq_abs, abs_le]
    unfold logTr at *
    constructor <;> linarith [neg_abs_le (log r), le_abs_self (log B), le_abs_self (log r), neg_abs_le (log B)]
  have h3 : ∫ v, logTr y r v ∂ν = ∫ v, log |y - v| ∂ν + ∫ v, (logTr y r v - log |y - v|) ∂ν := by
    rw [integral_sub hintTr hint]; ring
  have hcl := (abs_le.mp hcmp).2
  have hE0 : 0 ≤ E := (abs_nonneg _).trans (hIic 0)
  rw [h3] at hcl
  nlinarith [mul_le_mul_of_nonneg_left hloc hc]

/-- **Lemma 11 (L)**: if `ν{y} = 0`, the points of `Y ∖ {y}` avoid `(y − γ, y + γ)`, `0 < γ ≤ r`, and
`ν(y − r, y + r) ≤ A√r`, then
`Σ_{p ≠ y} log|y − p| ≥ c∫ log|y − v| dν − 3E(log B − log r) − E|log r| − (cA√r + 2E)(log r − log γ)`. -/
theorem le_sum_log {c E B y r A γ : ℝ} (hc : 0 ≤ c) (hB : 1 ≤ B) (hr : 0 < r) (hr1 : r ≤ 1)
    (hy : y ∈ Icc 0 B) (hsupp : ν (Icc 0 B)ᶜ = 0) (hY : ∀ p ∈ Y, p ∈ Icc 0 B)
    (hIic : ∀ u, |(ptMeas Y).real (Iic u) - c * ν.real (Iic u)| ≤ E)
    (hIio : ∀ u, |(ptMeas Y).real (Iio u) - c * ν.real (Iio u)| ≤ E)
    (hint : Integrable (fun v => log |y - v|) ν) (hball : ν.real (Ioo (y - r) (y + r)) ≤ A * √r)
    (hatom : ν {y} = 0) (hγ : 0 < γ) (hγr : γ ≤ r) (hsep : ∀ p ∈ Y, p ≠ y → γ ≤ |y - p|) :
    c * ∫ v, log |y - v| ∂ν - 3 * E * (log B - log r) - E * |log r| -
        (c * (A * √r) + 2 * E) * (log r - log γ) ≤ ∑ p ∈ Y.erase y, log |y - p| := by
  classical
  have hcmp := abs_sum_logTr_sub_le ν Y hc hB hr hr1 hy hsupp hY hIic hIio
  have hE0 : 0 ≤ E := (abs_nonneg _).trans (hIic 0)
  have hlγ : 0 ≤ log r - log γ := by have := Real.log_le_log hγ hγr; linarith
  -- the near points
  set N := (Y.filter (· ∈ Ioo (y - r) (y + r))).card with hN
  have hNle : (N : ℝ) ≤ c * (A * √r) + 2 * E := by
    have hset : Ioo (y - r) (y + r) = Iio (y + r) \ Iic (y - r) := by
      ext v; simp only [mem_Ioo, Set.mem_sdiff, mem_Iio, mem_Iic, not_le]; tauto
    have hIoo : (ptMeas Y).real (Ioo (y - r) (y + r)) =
        (ptMeas Y).real (Iio (y + r)) - (ptMeas Y).real (Iic (y - r)) := by
      rw [hset, measureReal_sdiff (Iic_subset_Iio.mpr (by linarith)) measurableSet_Iic]
    have hνIoo : ν.real (Ioo (y - r) (y + r)) = ν.real (Iio (y + r)) - ν.real (Iic (y - r)) := by
      rw [hset, measureReal_sdiff (Iic_subset_Iio.mpr (by linarith)) measurableSet_Iic]
    have h1 := hIio (y + r)
    have h2 := hIic (y - r)
    rw [hN, ← ptMeas_real Y measurableSet_Ioo, hIoo]
    rw [abs_le] at h1 h2
    have := mul_le_mul_of_nonneg_left hball hc
    rw [hνIoo] at this
    linarith [h1.2, h2.1]
  -- termwise
  have hterm : ∀ p ∈ Y.erase y, logTr y r p - (if p ∈ Ioo (y - r) (y + r) then log r - log γ else 0) ≤
      log |y - p| := by
    intro p hp
    have hpy := Finset.ne_of_mem_erase hp
    have hγp := hsep p (Finset.mem_of_mem_erase hp) hpy
    split_ifs with hin
    · have : logTr y r p ≤ log r := by
        unfold logTr
        have : |y - p| < r := abs_lt.mpr ⟨by linarith [hin.2], by linarith [hin.1]⟩
        rw [max_eq_right this.le]
      have := Real.log_le_log hγ hγp
      linarith
    · have : r ≤ |y - p| := by
        simp only [mem_Ioo, not_and_or, not_lt] at hin
        rcases hin with h | h
        · rw [abs_of_nonneg (by linarith)]; linarith
        · rw [abs_of_nonpos (by linarith)]; linarith
      rw [logTr_eq_log_abs this, sub_zero]
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib] at hsum
  have hnear : ∑ p ∈ Y.erase y, (if p ∈ Ioo (y - r) (y + r) then log r - log γ else 0) ≤
      N * (log r - log γ) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ hlγ
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset y Y))
  have hfull : ∑ p ∈ Y, logTr y r p ≤ ∑ p ∈ Y.erase y, logTr y r p := by
    by_cases hyY : y ∈ Y
    · rw [← Finset.add_sum_erase Y _ hyY]
      have : logTr y r y = log r := by simp [logTr, max_eq_right hr.le]
      rw [this]
      have : log r ≤ 0 := Real.log_nonpos hr.le hr1
      linarith
    · rw [Finset.erase_eq_of_notMem hyY]
  have hνae : ∀ᵐ v ∂ν, v ∈ Icc 0 B := by
    rw [ae_iff]; simpa [compl_def] using hsupp
  have hintTr : Integrable (logTr y r) ν := by
    refine Integrable.of_bound (measurable_logTr y r).aestronglyMeasurable (|log r| + |log B|)
      (hνae.mono fun v hv => ?_)
    have h1 := log_le_logTr (y := y) (v := v) hr
    have hm : max |y - v| r ≤ B := max_le (abs_le.mpr ⟨by linarith [hv.2, hy.1], by linarith [hv.1, hy.2]⟩)
      (hr1.trans hB)
    have h2 := Real.log_le_log (lt_max_of_lt_right hr) hm
    rw [Real.norm_eq_abs, abs_le]
    unfold logTr at *
    constructor <;> linarith [neg_abs_le (log r), le_abs_self (log B), le_abs_self (log r), neg_abs_le (log B)]
  have hmono : ∫ v, log |y - v| ∂ν ≤ ∫ v, logTr y r v ∂ν := by
    refine integral_mono_ae hint hintTr ((measure_eq_zero_iff_ae_notMem.mp hatom).mono fun v hv => ?_)
    exact log_abs_le_logTr hv
  have hcl := (abs_le.mp hcmp).1
  have hNγ := mul_le_mul_of_nonneg_right hNle hlγ
  nlinarith [mul_le_mul_of_nonneg_left hmono hc]

end Potential

end Cvs.Upstream.DiscreteContinuousLogPotential

end
