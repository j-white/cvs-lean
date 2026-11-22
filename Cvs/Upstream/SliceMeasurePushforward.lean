import Mathlib
import Cvs.Upstream.DiscreteContinuousLogPotential

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Slice measures: the pushforward of `φ(t) dt du` on `{α ≤ t ≤ β, 0 ≤ u ≤ L(t)}` under `t² + u²`

Its integrals are `∫_α^β φ(t)∫_0^{L(t)} g(t² + u²) du dt`, its distribution function is `∫_α^β φ min(L, √(y − t²)) dt`,
it has no atoms, its mass near `y` is at most `√(2r)∫φ`, and `∫(log max(|y − v|, r) − log|y − v|) ≤ 4√r∫φ`.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory

namespace Cvs.Upstream.SliceMeasurePushforward

/-! ### The definition and the slice formula -/

/-- The region `{(t, u) : α ≤ t ≤ β, 0 ≤ u ≤ L(t)}`. -/
def region (L : ℝ → ℝ) (α β : ℝ) : Set (ℝ × ℝ) := {p | p.1 ∈ Icc α β ∧ p.2 ∈ Icc 0 (L p.1)}

/-- The slice measure: the pushforward of `φ(t) dt du` on the region under `(t, u) ↦ t² + u²`. -/
def sliceMeas (φ L : ℝ → ℝ) (α β : ℝ) : Measure ℝ :=
  Measure.map (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2)
    (volume.withDensity fun p : ℝ × ℝ => ENNReal.ofReal ((region L α β).indicator (fun q => φ q.1) p))

variable {φ L : ℝ → ℝ} {α β : ℝ}

theorem measurableSet_region (hL : Measurable L) (α β : ℝ) : MeasurableSet (region L α β) := by
  unfold region
  simp only [mem_Icc, ofPred_and]
  refine ((measurableSet_le measurable_const measurable_fst).inter
    (measurableSet_le measurable_fst measurable_const)).inter
    ((measurableSet_le measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd (hL.comp measurable_fst)))

theorem measurable_sq_add_sq : Measurable fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2 := by fun_prop

/-- **The slice formula**: `∫⁻ g dν = ∫⁻_{[α, β]} φ(t)∫⁻_{[0, L(t)]} g(t² + u²) du dt`. -/
theorem lintegral_sliceMeas (hφ : Measurable φ) (hL : Measurable L) {g : ℝ → ENNReal} (hg : Measurable g) :
    ∫⁻ v, g v ∂(sliceMeas φ L α β) =
      ∫⁻ t in Icc α β, ENNReal.ofReal (φ t) * ∫⁻ u in Icc 0 (L t), g (t ^ 2 + u ^ 2) := by
  have hR := measurableSet_region hL α β
  have hd : Measurable fun p : ℝ × ℝ => ENNReal.ofReal ((region L α β).indicator (fun q => φ q.1) p) :=
    ENNReal.measurable_ofReal.comp ((hφ.comp measurable_fst).indicator hR)
  unfold sliceMeas
  have hw := lintegral_withDensity_eq_lintegral_mul volume hd (hg.comp measurable_sq_add_sq)
  simp only [Function.comp_def] at hw
  rw [lintegral_map hg measurable_sq_add_sq, hw, Measure.volume_eq_prod,
    lintegral_prod _ ?_, ← lintegral_indicator measurableSet_Icc]
  swap
  · exact (hd.mul (hg.comp measurable_sq_add_sq)).aemeasurable
  refine lintegral_congr fun t => ?_
  by_cases ht : t ∈ Icc α β
  · have hm : Measurable fun u : ℝ => g (t ^ 2 + u ^ 2) := hg.comp (by fun_prop)
    rw [indicator_of_mem ht, ← lintegral_const_mul _ hm, ← lintegral_indicator measurableSet_Icc]
    refine lintegral_congr fun u => ?_
    simp only [Pi.mul_apply]
    by_cases hu : u ∈ Icc 0 (L t)
    · rw [indicator_of_mem hu, indicator_of_mem (show (t, u) ∈ region L α β from ⟨ht, hu⟩)]
    · rw [indicator_of_notMem hu, indicator_of_notMem (show (t, u) ∉ region L α β from fun h => hu h.2)]
      simp
  · rw [indicator_of_notMem ht]
    refine lintegral_eq_zero_of_ae_eq_zero (Eventually.of_forall fun u => ?_)
    simp only [Pi.mul_apply, Pi.zero_apply]
    rw [indicator_of_notMem (show (t, u) ∉ region L α β from fun h => ht h.1)]
    simp

/-- **The measure of a set**: `ν(A) = ∫⁻_{[α, β]} φ(t)·|{u ∈ [0, L(t)] : t² + u² ∈ A}| dt`. -/
theorem sliceMeas_apply (hφ : Measurable φ) (hL : Measurable L) {A : Set ℝ} (hA : MeasurableSet A) :
    sliceMeas φ L α β A =
      ∫⁻ t in Icc α β, ENNReal.ofReal (φ t) * volume (Icc 0 (L t) ∩ {u | t ^ 2 + u ^ 2 ∈ A}) := by
  rw [← lintegral_indicator_one hA, lintegral_sliceMeas hφ hL (measurable_one.indicator hA)]
  refine setLIntegral_congr_fun measurableSet_Icc fun t _ => ?_
  congr 1
  have hm : MeasurableSet {u : ℝ | t ^ 2 + u ^ 2 ∈ A} := (by fun_prop : Measurable fun u : ℝ => t ^ 2 + u ^ 2) hA
  have e : (fun u : ℝ => A.indicator (1 : ℝ → ENNReal) (t ^ 2 + u ^ 2)) =
      {u : ℝ | t ^ 2 + u ^ 2 ∈ A}.indicator 1 := by
    ext u; by_cases h : t ^ 2 + u ^ 2 ∈ A <;> simp [indicator, h]
  rw [e, lintegral_indicator_one hm, Measure.restrict_apply hm, inter_comm]

/-! ### The distribution function, the mass, atoms and support -/

/-- The slice of `Iic y`: `|{u ∈ [0, L] : t² + u² ≤ y}| = min(L, √(y − t²))` for `L ≥ 0`. -/
theorem volume_slice_Iic {Lt t y : ℝ} (hL : 0 ≤ Lt) :
    volume (Icc 0 Lt ∩ {u | t ^ 2 + u ^ 2 ∈ Iic y}) = ENNReal.ofReal (min Lt √(y - t ^ 2)) := by
  rcases lt_or_ge (y - t ^ 2) 0 with h | h
  · have he : Icc 0 Lt ∩ {u | t ^ 2 + u ^ 2 ∈ Iic y} = ∅ := by
      ext u; simp only [mem_inter_iff, mem_Icc, mem_ofPred_eq, mem_Iic, mem_empty_iff_false, iff_false]
      intro ⟨_, hu⟩; nlinarith [sq_nonneg u]
    rw [he, Real.sqrt_eq_zero_of_nonpos h.le, min_eq_right hL]; simp
  · have he : Icc 0 Lt ∩ {u | t ^ 2 + u ^ 2 ∈ Iic y} = Icc 0 (min Lt √(y - t ^ 2)) := by
      ext u
      simp only [mem_inter_iff, mem_Icc, mem_ofPred_eq, mem_Iic, le_min_iff]
      constructor
      · rintro ⟨⟨h0, h1⟩, h2⟩
        exact ⟨h0, h1, (Real.le_sqrt h0 h).mpr (by linarith)⟩
      · rintro ⟨h0, h1, h2⟩
        exact ⟨⟨h0, h1⟩, by nlinarith [(Real.le_sqrt h0 h).mp h2]⟩
    rw [he, Real.volume_Icc, sub_zero]

/-- **The mass**: `ν(ℝ) = ∫⁻_{[α, β]} φL`. -/
theorem sliceMeas_univ (hφ : Measurable φ) (hL : Measurable L) :
    sliceMeas φ L α β univ = ∫⁻ t in Icc α β, ENNReal.ofReal (φ t) * ENNReal.ofReal (L t) := by
  rw [sliceMeas_apply hφ hL MeasurableSet.univ]
  refine setLIntegral_congr_fun measurableSet_Icc fun t ht => ?_
  simp only [mem_univ, ofPred_true, inter_univ, Real.volume_Icc, sub_zero]

/-- The slice measure is finite when `φL ≤ M` on `[α, β]`, `φ, L ≥ 0`. -/
theorem isFiniteMeasure_sliceMeas (hφ : Measurable φ) (hL : Measurable L) (hφ0 : ∀ t ∈ Icc α β, 0 ≤ φ t) {M : ℝ}
    (hM : ∀ t ∈ Icc α β, φ t * L t ≤ M) :
    IsFiniteMeasure (sliceMeas φ L α β) := by
  refine ⟨?_⟩
  rw [sliceMeas_univ hφ hL]
  calc ∫⁻ t in Icc α β, ENNReal.ofReal (φ t) * ENNReal.ofReal (L t)
      ≤ ∫⁻ _ in Icc α β, ENNReal.ofReal M := by
        refine setLIntegral_mono measurable_const fun t ht => ?_
        rw [← ENNReal.ofReal_mul (hφ0 t ht)]; exact ENNReal.ofReal_le_ofReal (hM t ht)
    _ < ⊤ := by rw [setLIntegral_const, Real.volume_Icc]; exact ENNReal.mul_lt_top (by simp) (by simp)

/-- **No atoms**: `ν{y} = 0`. -/
theorem sliceMeas_singleton (hφ : Measurable φ) (hL : Measurable L) (y : ℝ) : sliceMeas φ L α β {y} = 0 := by
  rw [sliceMeas_apply hφ hL (measurableSet_singleton y)]
  refine (setLIntegral_congr_fun (g := fun _ => 0) measurableSet_Icc fun t _ => ?_).trans (by simp)
  have hsub : Icc 0 (L t) ∩ {u | t ^ 2 + u ^ 2 ∈ ({y} : Set ℝ)} ⊆ {√(y - t ^ 2)} := by
    rintro u ⟨⟨h0, -⟩, hu⟩
    simp only [mem_ofPred_eq, mem_singleton_iff] at hu ⊢
    rw [← hu, add_sub_cancel_left, Real.sqrt_sq h0]
  simp only
  rw [measure_mono_null hsub (Real.volume_singleton), mul_zero]

/-- **The support**: `ν` lives on `[0, B]` when `t² + L(t)² ≤ B` on `[α, β]`. -/
theorem sliceMeas_compl (hφ : Measurable φ) (hL : Measurable L) {B : ℝ} (hB : ∀ t ∈ Icc α β, t ^ 2 + L t ^ 2 ≤ B) :
    sliceMeas φ L α β (Icc 0 B)ᶜ = 0 := by
  rw [sliceMeas_apply hφ hL measurableSet_Icc.compl]
  refine (setLIntegral_congr_fun (g := fun _ => 0) measurableSet_Icc fun t ht => ?_).trans (by simp)
  have he : Icc 0 (L t) ∩ {u | t ^ 2 + u ^ 2 ∈ (Icc 0 B)ᶜ} = ∅ := by
    refine eq_empty_iff_forall_notMem.mpr fun u ⟨⟨h0, h1⟩, hu⟩ => hu ⟨by positivity, ?_⟩
    have := hB t ht; nlinarith [mul_le_mul h1 h1 h0 (h0.trans h1)]
  simp only
  rw [he, measure_empty, mul_zero]

/-- **The distribution function**: `ν(Iic y) = ∫⁻_{[α, β]} φ min(L, √(y − t²))`. -/
theorem sliceMeas_Iic (hφ : Measurable φ) (hL : Measurable L) (hL0 : ∀ t ∈ Icc α β, 0 ≤ L t) (y : ℝ) :
    sliceMeas φ L α β (Iic y) = ∫⁻ t in Icc α β, ENNReal.ofReal (φ t) * ENNReal.ofReal (min (L t) √(y - t ^ 2)) := by
  rw [sliceMeas_apply hφ hL measurableSet_Iic]
  exact setLIntegral_congr_fun measurableSet_Icc fun t ht => by rw [volume_slice_Iic (hL0 t ht)]

/-- **The real distribution function**: `ν(Iic y) = ∫_α^β φ min(L, √(y − t²)) dt` when `φL ≤ M` on `[α, β]`. -/
theorem sliceMeas_real_Iic (hφ : Measurable φ) (hL : Measurable L) (hφ0 : ∀ t ∈ Icc α β, 0 ≤ φ t)
    (hL0 : ∀ t ∈ Icc α β, 0 ≤ L t) {M : ℝ} (hM : ∀ t ∈ Icc α β, φ t * L t ≤ M) (hαβ : α ≤ β) (y : ℝ) :
    (sliceMeas φ L α β).real (Iic y) = ∫ t in α..β, φ t * min (L t) √(y - t ^ 2) := by
  have hint : IntegrableOn (fun t => φ t * min (L t) √(y - t ^ 2)) (Icc α β) := by
    refine Measure.integrableOn_of_bounded (M := M) (by simp) ((hφ.mul (hL.min (by fun_prop))).aestronglyMeasurable)
      ((ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall fun t ht => ?_))
    have h1 := hφ0 t ht
    have h2 : 0 ≤ min (L t) √(y - t ^ 2) := le_min (hL0 t ht) (Real.sqrt_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1 h2)]
    exact (mul_le_mul_of_nonneg_left (min_le_left _ _) h1).trans (hM t ht)
  rw [measureReal_def, sliceMeas_Iic hφ hL hL0, intervalIntegral.integral_of_le hαβ, ← integral_Icc_eq_integral_Ioc,
    integral_eq_lintegral_of_nonneg_ae ((ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall fun t ht =>
      mul_nonneg (hφ0 t ht) (le_min (hL0 t ht) (Real.sqrt_nonneg _)))) hint.aestronglyMeasurable]
  congr 1
  refine setLIntegral_congr_fun measurableSet_Icc fun t ht => ?_
  rw [ENNReal.ofReal_mul (hφ0 t ht)]

/-! ### The local log kernel -/

/-- The kernel `κ_r(d) = log max(|d|, r) − log|d|`. -/
def kap (r d : ℝ) : ℝ := log (max |d| r) - log |d|

theorem kap_eq_indicator (r d : ℝ) :
    kap r d = (Icc (-r) r).indicator (fun d => log r - log d) d := by
  unfold kap
  by_cases hd : d ∈ Icc (-r) r
  · rw [indicator_of_mem hd, max_eq_right (abs_le.mpr hd), Real.log_abs]
  · rw [indicator_of_notMem hd]
    have : r < |d| := by
      by_contra h; push Not at h; exact hd (abs_le.mp h)
    rw [max_eq_left this.le, sub_self]

theorem measurable_kap (r : ℝ) : Measurable (kap r) := by unfold kap; fun_prop

/-- `κ_r ≥ 0` off `0`. -/
theorem kap_nonneg {r d : ℝ} (hd : d ≠ 0) : 0 ≤ kap r d := by
  unfold kap
  have := Real.log_le_log (abs_pos.mpr hd) (le_max_left |d| r)
  linarith

/-- `κ_r` is antitone in `|d|`: `0 < |d| ≤ |e|` gives `κ_r(e) ≤ κ_r(d)`. -/
theorem kap_le_of_abs_le {r d e : ℝ} (hd : d ≠ 0) (hde : |d| ≤ |e|) : kap r e ≤ kap r d := by
  unfold kap
  have hd0 : 0 < |d| := abs_pos.mpr hd
  have he0 : 0 < |e| := hd0.trans_le hde
  rcases le_total r |e| with h | h
  · rw [max_eq_left h, sub_self]
    have := Real.log_le_log hd0 (le_max_left |d| r); linarith
  · rw [max_eq_right h, max_eq_right (hde.trans h)]
    have := Real.log_le_log hd0 hde; linarith

/-- `κ_r(d²) = 2κ_{√r}(d)`. -/
theorem kap_sq {r : ℝ} (hr : 0 ≤ r) (d : ℝ) : kap r (d ^ 2) = 2 * kap √r d := by
  unfold kap
  have hm : max |d ^ 2| r = max |d| √r ^ 2 := by
    rw [abs_pow]
    rcases le_total |d| √r with h | h
    · have h2 : |d| ^ 2 ≤ r := by
        have := pow_le_pow_left₀ (abs_nonneg d) h 2; rwa [Real.sq_sqrt hr] at this
      rw [max_eq_right h2, max_eq_right h, Real.sq_sqrt hr]
    · have h2 : r ≤ |d| ^ 2 := by
        have := pow_le_pow_left₀ (Real.sqrt_nonneg r) h 2; rwa [Real.sq_sqrt hr] at this
      rw [max_eq_left h2, max_eq_left h]
  rw [hm, abs_pow, Real.log_pow, Real.log_pow]
  push_cast; ring

/-- `∫_{−r}^{r}(log r − log d) dd = 2r`. -/
theorem integral_log_sub_log (r : ℝ) : ∫ d in (-r)..r, (log r - log d) = 2 * r := by
  rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_log',
    intervalIntegral.integral_const, integral_log, Real.log_neg_eq_log, smul_eq_mul]
  ring

/-- **The kernel mass**: `∫⁻ κ_r(u − d₀) du = 2r`. -/
theorem lintegral_kap {r : ℝ} (hr : 0 < r) (d₀ : ℝ) :
    ∫⁻ u, ENNReal.ofReal (kap r (u - d₀)) = ENNReal.ofReal (2 * r) := by
  rw [lintegral_sub_right_eq_self (fun u => ENNReal.ofReal (kap r u)) d₀]
  have e : (fun u => ENNReal.ofReal (kap r u)) = (Icc (-r) r).indicator fun d => ENNReal.ofReal (log r - log d) := by
    ext d; rw [kap_eq_indicator]; by_cases h : d ∈ Icc (-r) r <;> simp [h]
  rw [e, lintegral_indicator measurableSet_Icc, ← integral_log_sub_log r,
    intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
    ofReal_integral_eq_lintegral_ofReal]
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mp
      (intervalIntegrable_const.sub intervalIntegral.intervalIntegrable_log')
  · have h0 : ∀ᵐ d ∂(volume.restrict (Icc (-r) r)), d ≠ 0 := by
      refine ae_restrict_of_ae ?_
      rw [ae_iff]; simp
    filter_upwards [h0, ae_restrict_mem measurableSet_Icc] with d h hd
    simp only [Pi.zero_apply, sub_nonneg]
    rw [← Real.log_abs]; exact Real.log_le_log (abs_pos.mpr h) (abs_le.mpr hd)

/-- `|A − u²| ≥ (u − √A)²` for `u ≥ 0`. -/
theorem sq_le_abs_sub_sq {A u : ℝ} (hu : 0 ≤ u) : (u - √A) ^ 2 ≤ |A - u ^ 2| := by
  rcases le_total 0 A with hA | hA
  · have hs := Real.sq_sqrt hA
    have hs0 := Real.sqrt_nonneg A
    have e : A - u ^ 2 = (√A - u) * (√A + u) := by nlinarith
    rw [e, abs_mul, abs_of_nonneg (by linarith : 0 ≤ √A + u), abs_sub_comm, ← sq_abs (u - √A), sq]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [abs_le]; constructor <;> linarith
  · rw [Real.sqrt_eq_zero_of_nonpos hA, sub_zero, abs_of_nonpos (by nlinarith [sq_nonneg u])]
    linarith

/-- **The kernel through the square**: `κ_r(A − u²) ≤ 2κ_{√r}(u − √A)` for `u ≥ 0`, `u ≠ √A`. -/
theorem kap_sub_sq_le {r A u : ℝ} (hr : 0 ≤ r) (hu : 0 ≤ u) (hne : u ≠ √A) :
    kap r (A - u ^ 2) ≤ 2 * kap √r (u - √A) := by
  rw [← kap_sq hr]
  have hd : (u - √A) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hne)
  exact kap_le_of_abs_le hd (by rw [abs_of_nonneg (sq_nonneg _)]; exact sq_le_abs_sub_sq hu)

/-- **The slice kernel mass**: `∫⁻_{[0, L]} κ_r(A − u²) du ≤ 4√r`. -/
theorem lintegral_kap_sub_sq_le {r : ℝ} (hr : 0 < r) (A Lt : ℝ) :
    ∫⁻ u in Icc 0 Lt, ENNReal.ofReal (kap r (A - u ^ 2)) ≤ ENNReal.ofReal (4 * √r) := by
  have hne : ∀ᵐ u ∂(volume.restrict (Icc 0 Lt)), u ≠ √A := by
    refine ae_restrict_of_ae ?_
    rw [ae_iff]; simp
  calc ∫⁻ u in Icc 0 Lt, ENNReal.ofReal (kap r (A - u ^ 2))
      ≤ ∫⁻ u in Icc 0 Lt, ENNReal.ofReal 2 * ENNReal.ofReal (kap √r (u - √A)) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hne, ae_restrict_mem measurableSet_Icc] with u h hu
        rw [← ENNReal.ofReal_mul (by norm_num)]
        exact ENNReal.ofReal_le_ofReal (kap_sub_sq_le hr.le hu.1 h)
    _ ≤ ∫⁻ u, ENNReal.ofReal 2 * ENNReal.ofReal (kap √r (u - √A)) := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (4 * √r) := by
        have hm : Measurable fun u => ENNReal.ofReal (kap √r (u - √A)) := by unfold kap; fun_prop
        rw [lintegral_const_mul _ hm, lintegral_kap (Real.sqrt_pos.mpr hr), ← ENNReal.ofReal_mul (by norm_num)]
        ring_nf

/-- **The slice ball**: `|{u ∈ [0, L] : |t² + u² − y| < r}| ≤ √(2r)`. -/
theorem volume_slice_Ioo_le {Lt t y r : ℝ} (hr : 0 ≤ r) :
    volume (Icc 0 Lt ∩ {u | t ^ 2 + u ^ 2 ∈ Ioo (y - r) (y + r)}) ≤ ENNReal.ofReal √(2 * r) := by
  set A := y - t ^ 2 with hA
  have hsub : Icc 0 Lt ∩ {u | t ^ 2 + u ^ 2 ∈ Ioo (y - r) (y + r)} ⊆ Icc √(A - r) √(A + r) := by
    rintro u ⟨⟨h0, -⟩, h1, h2⟩
    refine ⟨?_, (Real.le_sqrt h0 (by nlinarith [sq_nonneg u])).mpr (by linarith)⟩
    calc √(A - r) ≤ √(u ^ 2) := Real.sqrt_le_sqrt (by linarith)
      _ = u := Real.sqrt_sq h0
  refine (measure_mono hsub).trans ?_
  rw [Real.volume_Icc]
  refine ENNReal.ofReal_le_ofReal ?_
  rcases le_total (A - r) 0 with h | h
  · rw [Real.sqrt_eq_zero_of_nonpos h, sub_zero]; exact Real.sqrt_le_sqrt (by linarith)
  · have : √(A + r) ≤ √(A - r) + √(2 * r) := by
      rw [Real.sqrt_le_left (by positivity), add_sq, Real.sq_sqrt h, Real.sq_sqrt (by linarith)]
      nlinarith [Real.sqrt_nonneg (A - r), Real.sqrt_nonneg (2 * r)]
    linarith

/-- `|log|e|| ≤ log(1 + K) + κ_1(e)` for `|e| ≤ K`. -/
theorem abs_log_le {e K : ℝ} (he : |e| ≤ K) : abs (log |e|) ≤ log (1 + K) + kap 1 e := by
  have hK : 0 ≤ K := (abs_nonneg e).trans he
  have hlK : 0 ≤ log (1 + K) := Real.log_nonneg (by linarith)
  unfold kap
  rcases le_total 1 |e| with h | h
  · rw [max_eq_left h, sub_self, add_zero, abs_of_nonneg (Real.log_nonneg h)]
    exact Real.log_le_log (by linarith) (by linarith)
  · rw [max_eq_right h, Real.log_one, zero_sub]
    rcases eq_or_ne e 0 with h0 | h0
    · simp [h0, hlK]
    · rw [abs_of_nonpos (Real.log_nonpos (abs_nonneg e) h)]; linarith

/-! ### The local bounds on the slice measure -/

/-- **The local log mass**: `∫⁻ κ_r(y − v) dν ≤ 4√r∫⁻φ`. -/
theorem lintegral_kap_sliceMeas_le (hφ : Measurable φ) (hL : Measurable L) {r : ℝ} (hr : 0 < r) (y : ℝ) :
    ∫⁻ v, ENNReal.ofReal (kap r (y - v)) ∂(sliceMeas φ L α β) ≤
      ENNReal.ofReal (4 * √r) * ∫⁻ t in Icc α β, ENNReal.ofReal (φ t) := by
  have hm : Measurable fun v => ENNReal.ofReal (kap r (y - v)) := by unfold kap; fun_prop
  rw [lintegral_sliceMeas hφ hL hm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono (by fun_prop) fun t _ => ?_
  rw [mul_comm (ENNReal.ofReal (4 * √r))]
  gcongr
  have e : ∀ u : ℝ, y - (t ^ 2 + u ^ 2) = (y - t ^ 2) - u ^ 2 := fun u => by ring
  simp_rw [e]
  exact lintegral_kap_sub_sq_le hr _ _

/-- **The local mass**: `ν(y − r, y + r) ≤ √(2r)∫⁻φ`. -/
theorem sliceMeas_Ioo_le (hφ : Measurable φ) (hL : Measurable L) {r : ℝ} (hr : 0 ≤ r) (y : ℝ) :
    sliceMeas φ L α β (Ioo (y - r) (y + r)) ≤ ENNReal.ofReal √(2 * r) * ∫⁻ t in Icc α β, ENNReal.ofReal (φ t) := by
  rw [sliceMeas_apply hφ hL measurableSet_Ioo, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono (by fun_prop) fun t _ => ?_
  rw [mul_comm (ENNReal.ofReal √(2 * r))]
  gcongr
  exact volume_slice_Ioo_le hr

/-! ### Real forms -/

/-- `∫⁻_{[α, β]} φ = ∫_α^β φ` for `φ ≥ 0` integrable on `[α, β]`, `α ≤ β`. -/
theorem lintegral_ofReal_eq (hφ0 : ∀ t ∈ Icc α β, 0 ≤ φ t) (hφi : IntegrableOn φ (Icc α β)) (hαβ : α ≤ β) :
    ∫⁻ t in Icc α β, ENNReal.ofReal (φ t) = ENNReal.ofReal (∫ t in α..β, φ t) := by
  rw [intervalIntegral.integral_of_le hαβ, ← integral_Icc_eq_integral_Ioc,
    ofReal_integral_eq_lintegral_ofReal hφi ((ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall hφ0))]

/-- `∫⁻_{[α, β]} φ < ∞` form: `∫⁻_{[α, β]} φ = ofReal ∫_{[α, β]} φ` for `φ ≥ 0` integrable on `[α, β]`. -/
theorem lintegral_ofReal_eq' (hφ0 : ∀ t ∈ Icc α β, 0 ≤ φ t) (hφi : IntegrableOn φ (Icc α β)) :
    ∫⁻ t in Icc α β, ENNReal.ofReal (φ t) = ENNReal.ofReal (∫ t in Icc α β, φ t) :=
  (ofReal_integral_eq_lintegral_ofReal hφi ((ae_restrict_iff' measurableSet_Icc).mpr
    (Eventually.of_forall hφ0))).symm

/-- **The local mass, real form**: `ν(y − r, y + r) ≤ (√2∫_α^β φ)√r`. -/
theorem sliceMeas_real_Ioo_le (hφ : Measurable φ) (hL : Measurable L) (hφ0 : ∀ t ∈ Icc α β, 0 ≤ φ t)
    (hφi : IntegrableOn φ (Icc α β)) (hαβ : α ≤ β) {r : ℝ} (hr : 0 ≤ r) (y : ℝ) :
    (sliceMeas φ L α β).real (Ioo (y - r) (y + r)) ≤ (√2 * ∫ t in α..β, φ t) * √r := by
  have hI : 0 ≤ ∫ t in α..β, φ t := intervalIntegral.integral_nonneg hαβ hφ0
  have h := sliceMeas_Ioo_le (α := α) (β := β) hφ hL hr y
  rw [lintegral_ofReal_eq hφ0 hφi hαβ, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at h
  rw [measureReal_def]
  refine (ENNReal.toReal_le_of_le_ofReal (by positivity) h).trans_eq ?_
  rw [Real.sqrt_mul (by norm_num)]; ring

/-- The density of the slice measure is finite. -/
theorem ae_density_lt_top (φ L : ℝ → ℝ) (α β : ℝ) :
    ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), ENNReal.ofReal ((region L α β).indicator (fun q => φ q.1) p) < ⊤ :=
  Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

theorem measurable_density (hφ : Measurable φ) (hL : Measurable L) (α β : ℝ) :
    Measurable fun p : ℝ × ℝ => ENNReal.ofReal ((region L α β).indicator (fun q => φ q.1) p) :=
  ENNReal.measurable_ofReal.comp ((hφ.comp measurable_fst).indicator (measurableSet_region hL α β))

/-- **The slice formula, real form**: `∫ g dν = ∫_α^β φ(t)∫_0^{L(t)} g(t² + u²) du dt` for `ν`-integrable `g`. -/
theorem integral_sliceMeas (hφ : Measurable φ) (hL : Measurable L) (hφ0 : ∀ t ∈ Icc α β, 0 ≤ φ t)
    (hL0 : ∀ t ∈ Icc α β, 0 ≤ L t) (hαβ : α ≤ β) {g : ℝ → ℝ} (hg : Measurable g)
    (hgi : Integrable g (sliceMeas φ L α β)) :
    ∫ v, g v ∂(sliceMeas φ L α β) = ∫ t in α..β, φ t * ∫ u in (0 : ℝ)..L t, g (t ^ 2 + u ^ 2) := by
  have hd := measurable_density hφ hL α β
  have hR := measurableSet_region hL α β
  set w : ℝ × ℝ → ℝ := fun p => (region L α β).indicator (fun q => φ q.1) p * g (p.1 ^ 2 + p.2 ^ 2) with hw
  have hpt : ∀ p : ℝ × ℝ, (ENNReal.ofReal ((region L α β).indicator (fun q => φ q.1) p)).toReal •
      g (p.1 ^ 2 + p.2 ^ 2) = w p := fun p => by
    rw [ENNReal.toReal_ofReal, smul_eq_mul]
    by_cases h : p ∈ region L α β
    · rw [indicator_of_mem h]; exact hφ0 _ h.1
    · rw [indicator_of_notMem h]
  have hwi : Integrable w (volume.prod volume) := by
    have h1 := (integrable_map_measure hg.aestronglyMeasurable measurable_sq_add_sq.aemeasurable).mp hgi
    have h2 := (integrable_withDensity_iff_integrable_smul' hd (ae_density_lt_top φ L α β)).mp h1
    rw [← Measure.volume_eq_prod]
    exact h2.congr (Eventually.of_forall hpt)
  unfold sliceMeas
  rw [integral_map measurable_sq_add_sq.aemeasurable hg.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hd (ae_density_lt_top φ L α β)]
  simp only [hpt]
  rw [Measure.volume_eq_prod, integral_prod _ hwi, intervalIntegral.integral_of_le hαβ,
    ← integral_Icc_eq_integral_Ioc, ← integral_indicator measurableSet_Icc]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [hw]
  by_cases ht : t ∈ Icc α β
  · rw [indicator_of_mem ht, intervalIntegral.integral_of_le (hL0 t ht), ← integral_Icc_eq_integral_Ioc,
      ← integral_const_mul, ← integral_indicator measurableSet_Icc]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    by_cases hu : u ∈ Icc 0 (L t)
    · simp only
      rw [indicator_of_mem hu, indicator_of_mem (show (t, u) ∈ region L α β from ⟨ht, hu⟩)]
    · simp only
      rw [indicator_of_notMem hu, indicator_of_notMem (show (t, u) ∉ region L α β from fun h => hu h.2), zero_mul]
  · rw [indicator_of_notMem ht]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun u => ?_)
    simp only [Pi.zero_apply]
    rw [indicator_of_notMem (show (t, u) ∉ region L α β from fun h => ht h.1), zero_mul]

/-- **The local log mass, real form**: `∫(log max(|y − v|, r) − log|y − v|) dν ≤ (4∫_α^β φ)√r`. -/
theorem integral_logTr_sub_le (hφ : Measurable φ) (hL : Measurable L) (hφ0 : ∀ t ∈ Icc α β, 0 ≤ φ t)
    (hφi : IntegrableOn φ (Icc α β)) (hαβ : α ≤ β) {r : ℝ} (hr : 0 < r) (y : ℝ) :
    ∫ v, (Cvs.Upstream.DiscreteContinuousLogPotential.logTr y r v - log |y - v|) ∂(sliceMeas φ L α β) ≤ (4 * ∫ t in α..β, φ t) * √r := by
  have hI : 0 ≤ ∫ t in α..β, φ t := intervalIntegral.integral_nonneg hαβ hφ0
  have e : (fun v => Cvs.Upstream.DiscreteContinuousLogPotential.logTr y r v - log |y - v|) = fun v => kap r (y - v) := rfl
  have hne : ∀ᵐ v ∂(sliceMeas φ L α β), v ≠ y := by
    rw [ae_iff]; simpa using sliceMeas_singleton hφ hL (α := α) (β := β) y
  rw [e, integral_eq_lintegral_of_nonneg_ae (hne.mono fun v hv => kap_nonneg (sub_ne_zero.mpr hv.symm))
    ((measurable_kap r).comp (measurable_const.sub measurable_id)).aestronglyMeasurable]
  have h := lintegral_kap_sliceMeas_le (α := α) (β := β) hφ hL hr y
  rw [lintegral_ofReal_eq hφ0 hφi hαβ, ← ENNReal.ofReal_mul (by positivity)] at h
  refine (ENNReal.toReal_le_of_le_ofReal (by positivity) h).trans_eq ?_
  ring

/-- **The log potential is integrable** against a finite slice measure supported in `[0, B]`. -/
theorem integrable_log_sliceMeas (hφ : Measurable φ) (hL : Measurable L) (hφ0 : ∀ t ∈ Icc α β, 0 ≤ φ t)
    (hφi : IntegrableOn φ (Icc α β)) [IsFiniteMeasure (sliceMeas φ L α β)] {B : ℝ}
    (hsupp : sliceMeas φ L α β (Icc 0 B)ᶜ = 0) (y : ℝ) : Integrable (fun v => log |y - v|) (sliceMeas φ L α β) := by
  set ν := sliceMeas φ L α β
  have hk : Integrable (fun v => kap 1 (y - v)) ν := by
    have hm : Measurable fun v => kap 1 (y - v) := (measurable_kap 1).comp (measurable_const.sub measurable_id)
    have h0 : ∀ v, 0 ≤ kap 1 (y - v) := fun v => by
      rcases eq_or_ne (y - v) 0 with h | h
      · rw [h]; simp [kap]
      · exact kap_nonneg h
    refine ⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall h0)).mpr ?_⟩
    refine (lintegral_kap_sliceMeas_le hφ hL one_pos y).trans_lt ?_
    rw [lintegral_ofReal_eq' hφ0 hφi]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hνae : ∀ᵐ v ∂ν, v ∈ Icc 0 B := by rw [ae_iff]; simpa [compl_def] using hsupp
  refine ((integrable_const (log (1 + (|y| + |B|)))).add hk).mono'
    ((Real.measurable_log.comp (measurable_const.sub measurable_id).abs).aestronglyMeasurable)
    (hνae.mono fun v hv => ?_)
  rw [Real.norm_eq_abs]
  refine abs_log_le ?_
  have : |v| ≤ |B| := by rw [abs_of_nonneg hv.1, abs_of_nonneg (hv.1.trans hv.2)]; exact hv.2
  exact (abs_sub _ _).trans (by linarith)

/-- **The inner integral is integrable**: `t ↦ φ(t)∫_0^{L(t)} g(t² + u²) du` is integrable on `[α, β]` for
`ν`-integrable `g`. -/
theorem integrableOn_inner (hφ : Measurable φ) (hL : Measurable L) (hφ0 : ∀ t ∈ Icc α β, 0 ≤ φ t)
    (hL0 : ∀ t ∈ Icc α β, 0 ≤ L t) {g : ℝ → ℝ} (hg : Measurable g) (hgi : Integrable g (sliceMeas φ L α β)) :
    IntegrableOn (fun t => φ t * ∫ u in (0 : ℝ)..L t, g (t ^ 2 + u ^ 2)) (Icc α β) := by
  have hd := measurable_density hφ hL α β
  set w : ℝ × ℝ → ℝ := fun p => (region L α β).indicator (fun q => φ q.1) p * g (p.1 ^ 2 + p.2 ^ 2) with hw
  have hpt : ∀ p : ℝ × ℝ, (ENNReal.ofReal ((region L α β).indicator (fun q => φ q.1) p)).toReal •
      g (p.1 ^ 2 + p.2 ^ 2) = w p := fun p => by
    rw [ENNReal.toReal_ofReal, smul_eq_mul]
    by_cases h : p ∈ region L α β
    · rw [indicator_of_mem h]; exact hφ0 _ h.1
    · rw [indicator_of_notMem h]
  have hwi : Integrable w (volume.prod volume) := by
    have h1 := (integrable_map_measure hg.aestronglyMeasurable measurable_sq_add_sq.aemeasurable).mp hgi
    have h2 := (integrable_withDensity_iff_integrable_smul' hd (ae_density_lt_top φ L α β)).mp h1
    rw [← Measure.volume_eq_prod]
    exact h2.congr (Eventually.of_forall hpt)
  refine (hwi.integral_prod_left.integrableOn).congr_fun (fun t ht => ?_) measurableSet_Icc
  simp only [hw]
  rw [intervalIntegral.integral_of_le (hL0 t ht), ← integral_Icc_eq_integral_Ioc, ← integral_const_mul,
    ← integral_indicator measurableSet_Icc]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  by_cases hu : u ∈ Icc 0 (L t)
  · simp only
    rw [indicator_of_mem hu, indicator_of_mem (show (t, u) ∈ region L α β from ⟨ht, hu⟩)]
  · simp only
    rw [indicator_of_notMem hu, indicator_of_notMem (show (t, u) ∉ region L α β from fun h => hu h.2), zero_mul]

end Cvs.Upstream.SliceMeasurePushforward

end
