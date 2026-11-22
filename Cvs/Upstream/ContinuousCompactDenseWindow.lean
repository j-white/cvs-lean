import Mathlib
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowRepresentative

/-!
# Continuous functions supported in the open interval are dense in the window

Any class of `window L` is approximated in `L²` by a continuous, compactly supported function
that vanishes off `(0, L)`, obtained by cutting a compactly supported continuous approximant
down to the interval with a trapezoidal bump.
-/

noncomputable section

open MeasureTheory Set

namespace Cvs.Upstream.ContinuousCompactDenseWindow

/-- **A trapezoidal cutoff**: continuous, valued in `[0, 1]`, `1` on `[δ, L−δ]`, `0` off `(0, L)`. -/
def cutoff (L δ : ℝ) : ℝ → ℝ := fun s => max 0 (min 1 (min (s / δ) ((L - s) / δ)))

theorem continuous_cutoff (L δ : ℝ) : Continuous (cutoff L δ) := by
  unfold cutoff
  fun_prop

theorem cutoff_nonneg (L δ : ℝ) (s : ℝ) : 0 ≤ cutoff L δ s := le_max_left _ _

theorem cutoff_le_one (L δ : ℝ) (s : ℝ) : cutoff L δ s ≤ 1 := by
  unfold cutoff
  exact max_le zero_le_one (le_trans (min_le_left _ _) le_rfl)

/-- Off the open interval the cutoff is zero. -/
theorem cutoff_eq_zero {L δ : ℝ} (hδ : 0 < δ) {s : ℝ} (hs : s ∉ Ioo (0:ℝ) L) :
    cutoff L δ s = 0 := by
  unfold cutoff
  rw [Set.mem_Ioo, not_and_or] at hs
  rcases hs with h | h
  · -- s ≤ 0
    push Not at h
    have : s / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
    have h2 : min (s / δ) ((L - s) / δ) ≤ 0 := le_trans (min_le_left _ _) this
    have h3 : min 1 (min (s / δ) ((L - s) / δ)) ≤ 0 := le_trans (min_le_right _ _) h2
    exact max_eq_left h3
  · -- L ≤ s
    push Not at h
    have : (L - s) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
    have h2 : min (s / δ) ((L - s) / δ) ≤ 0 := le_trans (min_le_right _ _) this
    have h3 : min 1 (min (s / δ) ((L - s) / δ)) ≤ 0 := le_trans (min_le_right _ _) h2
    exact max_eq_left h3

/-- On `[δ, L − δ]` the cutoff is one. -/
theorem cutoff_eq_one {L δ : ℝ} (hδ : 0 < δ) {s : ℝ} (h1 : δ ≤ s) (h2 : s ≤ L - δ) :
    cutoff L δ s = 1 := by
  unfold cutoff
  have ha : 1 ≤ s / δ := (one_le_div hδ).mpr h1
  have hb : 1 ≤ (L - s) / δ := (one_le_div hδ).mpr (by linarith)
  have : (1 : ℝ) ≤ min (s / δ) ((L - s) / δ) := le_min ha hb
  rw [min_eq_left this, max_eq_right zero_le_one]

end Cvs.Upstream.ContinuousCompactDenseWindow

namespace Cvs.Upstream.ContinuousCompactDenseWindow

/-- **Density in the window.**  For any class `y` of `window L` and any `ε > 0` there is a
continuous, compactly supported `g` vanishing off `(0, L)` with `‖rep y − g‖₂ ≤ ε`. -/
theorem approx_by_continuous_supported {L : ℝ} (hL : 0 < L)
    (y : Cvs.WeilForm.WeilFormOnWindowL2.window L) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, Continuous g ∧ HasCompactSupport g ∧
      (∀ s, s ∉ Set.Ioo (0:ℝ) L → g s = 0) ∧
      eLpNorm (fun s => Cvs.WeilForm.WindowRepresentative.rep y s - g s) 2 (volume : Measure ℝ)
        ≤ ENNReal.ofReal ε := by
  classical
  set f := Cvs.WeilForm.WindowRepresentative.rep y with hf_def
  have hf : MemLp f 2 (volume : Measure ℝ) := Cvs.WeilForm.WindowRepresentative.memLp_rep y
  have hε3 : (0 : ℝ) < ε / 3 := by linarith
  -- A compactly supported continuous approximant, ε/3-close in L².
  obtain ⟨g₀, hg₀cs, hg₀close, hg₀cont, hg₀mem⟩ :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le (p := 2) (by simp)
      (ENNReal.ofReal_pos.mpr hε3).ne'
  -- A uniform bound on the approximant.
  obtain ⟨C, hC⟩ := hg₀cont.bounded_above_of_compact_support hg₀cs
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  -- Choose the cutoff scale.
  set δ : ℝ := (ε / (3 * (C + 1))) ^ 2 / 2 with hδ_def
  have hCpos : 0 < C + 1 := by linarith
  have hbase : 0 < ε / (3 * (C + 1)) := by positivity
  have hδpos : 0 < δ := by positivity
  have h2δ : 2 * δ = (ε / (3 * (C + 1))) ^ 2 := by rw [hδ_def]; ring
  set g : ℝ → ℝ := fun s => g₀ s * cutoff L δ s with hg_def
  refine ⟨g, hg₀cont.mul (continuous_cutoff L δ), hg₀cs.mul_right, ?_, ?_⟩
  · -- vanishes off the open interval
    intro s hs
    rw [hg_def]
    simp only
    rw [cutoff_eq_zero hδpos hs, mul_zero]
  -- The L² estimate, via bad set / interior split.
  have haesm_fg0 : AEStronglyMeasurable (fun s => f s - g₀ s) (volume : Measure ℝ) :=
    hf.aestronglyMeasurable.sub hg₀cont.aestronglyMeasurable
  have haesm_g0g : AEStronglyMeasurable (fun s => g₀ s - g s) (volume : Measure ℝ) :=
    hg₀cont.aestronglyMeasurable.sub
      (hg₀cont.mul (continuous_cutoff L δ)).aestronglyMeasurable
  set bad : Set ℝ := (Set.Ioo (0:ℝ) L)ᶜ with hbad_def
  set hh : ℝ → ℝ := fun s => g₀ s * (1 - cutoff L δ s) with hh_def
  have hg0g_eq : (fun s => g₀ s - g s) = hh := by
    funext s; rw [hg_def, hh_def]; ring
  -- hh = bad.indicator hh + badᶜ.indicator hh.
  have hind : hh = fun s => bad.indicator hh s + badᶜ.indicator hh s := by
    funext s
    by_cases hs : s ∈ bad
    · rw [Set.indicator_of_mem hs, Set.indicator_of_notMem (by simp [hs]), add_zero]
    · rw [Set.indicator_of_notMem hs, Set.indicator_of_mem (by simpa using hs), zero_add]
  have haesm_bad : AEStronglyMeasurable (bad.indicator hh) (volume : Measure ℝ) := by
    apply AEStronglyMeasurable.indicator _ (measurableSet_Ioo.compl)
    exact hg₀cont.mul (continuous_const.sub (continuous_cutoff L δ)) |>.aestronglyMeasurable
  have haesm_int : AEStronglyMeasurable (badᶜ.indicator hh) (volume : Measure ℝ) := by
    apply AEStronglyMeasurable.indicator _ (measurableSet_Ioo.compl.compl)
    exact hg₀cont.mul (continuous_const.sub (continuous_cutoff L δ)) |>.aestronglyMeasurable
  -- Piece 1: eLpNorm (f - g₀) ≤ ε/3.
  have hpiece1 : eLpNorm (fun s => f s - g₀ s) 2 (volume : Measure ℝ) ≤ ENNReal.ofReal (ε / 3) :=
    hg₀close
  -- The "outside" piece equals (a.e.) an indicator of f - g₀, hence ≤ ε/3.
  have hbad_le : eLpNorm (bad.indicator hh) 2 (volume : Measure ℝ) ≤ ENNReal.ofReal (ε / 3) := by
    have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ L := by
      rw [MeasureTheory.ae_iff]
      simp
    have hcongr : bad.indicator hh =ᵐ[volume] bad.indicator (fun s => g₀ s - f s) := by
      filter_upwards [hae] with s hs
      by_cases hmem : s ∈ bad
      · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
        show g₀ s * (1 - cutoff L δ s) = g₀ s - f s
        have hnotIoo : s ∉ Set.Ioo (0:ℝ) L := hmem
        rw [cutoff_eq_zero hδpos hnotIoo]
        have hfs : f s = 0 := by
          rw [hf_def]
          apply Cvs.WeilForm.WindowRepresentative.rep_supp y
          rw [Set.mem_Ioo, not_and_or] at hnotIoo
          rw [Set.mem_Ioc, not_and_or]
          rcases hnotIoo with h0 | hL'
          · exact Or.inl h0
          · refine Or.inr ?_
            push Not at hL' ⊢
            rcases lt_or_eq_of_le hL' with hlt | heq
            · linarith
            · exact absurd heq.symm hs
        rw [hfs]; ring
      · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
    rw [eLpNorm_congr_ae hcongr]
    calc eLpNorm (bad.indicator (fun s => g₀ s - f s)) 2 (volume : Measure ℝ)
        ≤ eLpNorm (fun s => g₀ s - f s) 2 (volume : Measure ℝ) := eLpNorm_indicator_le _ measurableSet_Ioo.compl.nullMeasurableSet
      _ = eLpNorm (fun s => f s - g₀ s) 2 (volume : Measure ℝ) := by
            rw [show (fun s => g₀ s - f s) = (fun s => -(f s - g₀ s)) by funext s; ring]
            exact eLpNorm_neg _ _ _
      _ ≤ ENNReal.ofReal (ε / 3) := hg₀close
  -- The "interior" piece is supported on two slivers of total measure ≤ 2δ.
  set slivers : Set ℝ := Set.Ioo (0:ℝ) δ ∪ Set.Ioo (L - δ) L with hsl_def
  have hint_le : eLpNorm (badᶜ.indicator hh) 2 (volume : Measure ℝ) ≤ ENNReal.ofReal (ε / 3) := by
    have hpt : ∀ s, ‖badᶜ.indicator hh s‖ ≤ ‖slivers.indicator (fun _ => C) s‖ := by
      intro s
      by_cases hmem : s ∈ badᶜ
      · have hsIoo : s ∈ Set.Ioo (0:ℝ) L := by
          have h := hmem; rw [hbad_def, compl_compl] at h; exact h
        rw [Set.indicator_of_mem hmem]
        by_cases hsl : s ∈ slivers
        · rw [Set.indicator_of_mem hsl]
          show ‖g₀ s * (1 - cutoff L δ s)‖ ≤ ‖C‖
          rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hC0, abs_mul]
          have h1c : |1 - cutoff L δ s| ≤ 1 := by
            rw [abs_of_nonneg (by linarith [cutoff_le_one L δ s])]
            linarith [cutoff_nonneg L δ s]
          calc |g₀ s| * |1 - cutoff L δ s| ≤ |g₀ s| * 1 :=
                mul_le_mul_of_nonneg_left h1c (abs_nonneg _)
            _ = |g₀ s| := mul_one _
            _ ≤ C := by have := hC s; rwa [Real.norm_eq_abs] at this
        · -- s ∈ Ioo but not in slivers ⟹ δ ≤ s ≤ L - δ ⟹ cutoff = 1 ⟹ hh s = 0
          have hbounds : δ ≤ s ∧ s ≤ L - δ := by
            rw [hsl_def, Set.mem_union, Set.mem_Ioo, Set.mem_Ioo, not_or] at hsl
            obtain ⟨hna, hnb⟩ := hsl
            rw [Set.mem_Ioo] at hsIoo
            refine ⟨?_, ?_⟩
            · by_contra hlt; push Not at hlt; exact hna ⟨hsIoo.1, hlt⟩
            · by_contra hgt; push Not at hgt; exact hnb ⟨hgt, hsIoo.2⟩
          have hzero : hh s = 0 := by
            show g₀ s * (1 - cutoff L δ s) = 0
            rw [cutoff_eq_one hδpos hbounds.1 hbounds.2, sub_self, mul_zero]
          rw [hzero, norm_zero]
          positivity
      · rw [Set.indicator_of_notMem hmem, norm_zero]
        positivity
    have hslmeas : MeasurableSet slivers := measurableSet_Ioo.union measurableSet_Ioo
    have hmeas_le : volume slivers ≤ ENNReal.ofReal (2 * δ) := by
      refine le_trans (measure_union_le _ _) ?_
      rw [Real.volume_Ioo, Real.volume_Ioo]
      rw [show L - (L - δ) = δ by ring, show δ - 0 = δ by ring]
      rw [← ENNReal.ofReal_add hδpos.le hδpos.le]
      apply ENNReal.ofReal_le_ofReal; linarith
    calc eLpNorm (badᶜ.indicator hh) 2 (volume : Measure ℝ)
        ≤ eLpNorm (slivers.indicator (fun _ => C)) 2 (volume : Measure ℝ) := eLpNorm_mono haesm_int hpt
      _ ≤ ENNReal.ofReal (ε / 3) := by
            rw [eLpNorm_indicator_const hslmeas.nullMeasurableSet (by norm_num) (by norm_num)]
            have htoReal : ((2 : ENNReal).toReal) = 2 := by simp
            rw [htoReal, Real.eNorm_of_nonneg hC0]
            calc ENNReal.ofReal C * (volume slivers) ^ (1 / (2:ℝ))
                ≤ ENNReal.ofReal C * (ENNReal.ofReal (2 * δ)) ^ (1 / (2:ℝ)) := by
                  gcongr
              _ = ENNReal.ofReal C * ENNReal.ofReal ((2 * δ) ^ (1 / (2:ℝ))) := by
                  rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
              _ = ENNReal.ofReal (C * (2 * δ) ^ (1 / (2:ℝ))) := by
                  rw [← ENNReal.ofReal_mul hC0]
              _ ≤ ENNReal.ofReal (ε / 3) := by
                  apply ENNReal.ofReal_le_ofReal
                  have hne : (C : ℝ) + 1 ≠ 0 := hCpos.ne'
                  have hsqrt : (2 * δ) ^ (1 / (2:ℝ)) = ε / (3 * (C + 1)) := by
                    rw [← Real.sqrt_eq_rpow, h2δ, Real.sqrt_sq hbase.le]
                  rw [hsqrt]
                  have hid : C * (ε / (3 * (C + 1))) = (C / (C + 1)) * (ε / 3) := by
                    field_simp
                  rw [hid]
                  have h2 : C / (C + 1) ≤ 1 := by rw [div_le_one hCpos]; linarith
                  exact mul_le_of_le_one_left (by positivity) h2
  -- Piece 2 total: eLpNorm (g₀ - g) ≤ ε/3 + ε/3.
  have hpiece2 : eLpNorm (fun s => g₀ s - g s) 2 (volume : Measure ℝ)
      ≤ ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3) := by
    rw [hg0g_eq]
    calc eLpNorm hh 2 (volume : Measure ℝ)
        = eLpNorm (fun s => bad.indicator hh s + badᶜ.indicator hh s) 2 (volume : Measure ℝ) := by
          rw [← hind]
      _ ≤ eLpNorm (bad.indicator hh) 2 volume + eLpNorm (badᶜ.indicator hh) 2 volume :=
          eLpNorm_add_le (by norm_num)
      _ ≤ ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3) := add_le_add hbad_le hint_le
  -- Combine: (f - g₀) + (g₀ - g), then ε/3 + (ε/3 + ε/3) = ε.
  calc eLpNorm (fun s => f s - g s) 2 (volume : Measure ℝ)
      = eLpNorm (fun s => (f s - g₀ s) + (g₀ s - g s)) 2 (volume : Measure ℝ) := by
        congr 1; funext s; ring
    _ ≤ eLpNorm (fun s => f s - g₀ s) 2 volume + eLpNorm (fun s => g₀ s - g s) 2 volume :=
        eLpNorm_add_le (by norm_num)
    _ ≤ ENNReal.ofReal (ε / 3) + (ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3)) :=
        add_le_add hpiece1 hpiece2
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add hε3.le hε3.le, ← ENNReal.ofReal_add hε3.le (by linarith)]
        congr 1; ring

end Cvs.Upstream.ContinuousCompactDenseWindow
