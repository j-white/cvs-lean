import Mathlib
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.PastTurningCanonicalLog
import Cvs.Prolate.Mellin.PastTurningLineStart
import Cvs.Prolate.Mellin.PastTurningPhaseSum
import Cvs.Prolate.Mellin.WkbPhaseAntiderivative
import Cvs.Prolate.Mellin.WkbPhaseImaginaryAxis
import Cvs.Upstream.ComplexArsinhStrip

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Taylor at the start of the line past the turning point

For `z > 2c`, `Ĝ(iz + η) → Ĝ(iz)` and `ĝ(iz + η) → ĝ(iz)` as `η → 0⁺`. `|ĝ′| ≤ 13k²/(2|S|)` when `|S| ≥ 1` and
`c ≤ k|S|`, `k ≥ 1`. For `z ≥ (2 + ε)c` with `εc² ≥ 2`, `|S| ≥ √ε c` on `[iz, iz + 2]`, and with `M = 13/(2ε^{3/2}c)`:
`|Ĝ(iz + 2) − Ĝ(iz) − 2ĝ(iz)| ≤ 4M` and `|ĝ(iz + 2) − ĝ(iz)| ≤ 2M`.
-/

noncomputable section

open Complex Filter Topology

namespace Cvs.Prolate.Mellin.PastTurningStartTaylor

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity (csqrt re_csqrt_nonneg)
open Cvs.Upstream.ComplexArsinhStrip (ash)
open Cvs.Prolate.Mellin.WkbPhaseAntiderivative (Sq Sq_sq Gh gh gh1)

variable {c z : ℝ}

theorem Sq_I_ne (hc : 0 < c) (hz : 2 * c < z) : Sq c (I * z) ≠ 0 := by
  rw [Cvs.Prolate.Mellin.WkbPhaseImaginaryAxis.Sq_I_mul hc hz.le]
  have hw : 1 < z / (2 * c) := by rw [lt_div_iff₀ (by positivity)]; linarith
  have hs : 0 < Real.sqrt ((z / (2 * c)) ^ 2 - 1) := Real.sqrt_pos.mpr (by nlinarith)
  intro h0
  have him := congrArg Complex.im h0
  have e : (I * ((2 * c * Real.sqrt ((z / (2 * c)) ^ 2 - 1) : ℝ) : ℂ)).im = 2 * c * Real.sqrt ((z / (2 * c)) ^ 2 - 1) := by
    simp
  rw [e, Complex.zero_im] at him
  have : 0 < 2 * c * Real.sqrt ((z / (2 * c)) ^ 2 - 1) := by positivity
  linarith

theorem two_c_add_Sq_mem (hc : 0 < c) (u : ℂ) : 2 * (c : ℂ) + Sq c u ∈ slitPlane := by
  rw [mem_slitPlane_iff]; left
  have := re_csqrt_nonneg (u ^ 2 + 4 * c ^ 2)
  unfold Sq; simp; linarith

theorem tendsto_u (z : ℝ) : Tendsto (fun η : ℝ => I * (z : ℂ) + η) (𝓝[>] (0 : ℝ)) (𝓝 (I * z)) := by
  have : Tendsto (fun η : ℝ => I * (z : ℂ) + η) (𝓝 (0 : ℝ)) (𝓝 (I * (z : ℂ) + ((0 : ℝ) : ℂ))) := by
    apply Continuous.tendsto; fun_prop
  simp only [Complex.ofReal_zero, add_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- **`Ĝ(iz + η) → Ĝ(iz)`.** -/
theorem tendsto_Gh (hc : 0 < c) (hz : 2 * c < z) :
    Tendsto (fun η : ℝ => Gh c (I * z + η)) (𝓝[>] (0 : ℝ)) (𝓝 (Gh c (I * z))) := by
  have hu := tendsto_u z
  have hA := Cvs.Prolate.Mellin.PastTurningLineStart.tendsto_ash hc hz
  have hS := Cvs.Prolate.Mellin.PastTurningLineStart.tendsto_Sq hc hz
  have hL := (continuousAt_clog (two_c_add_Sq_mem hc (I * z))).tendsto.comp (hS.const_add (2 * (c : ℂ)))
  have := ((hu.neg.mul hA).add hS).sub (hL.const_mul (1 / 2 : ℂ))
  unfold Gh
  exact this

/-- **`ĝ(iz + η) → ĝ(iz)`.** -/
theorem tendsto_gh (hc : 0 < c) (hz : 2 * c < z) :
    Tendsto (fun η : ℝ => gh c (I * z + η)) (𝓝[>] (0 : ℝ)) (𝓝 (gh c (I * z))) := by
  have hu := tendsto_u z
  have hA := Cvs.Prolate.Mellin.PastTurningLineStart.tendsto_ash hc hz
  have hS := Cvs.Prolate.Mellin.PastTurningLineStart.tendsto_Sq hc hz
  have hne : 2 * Sq c (I * z) * (Sq c (I * z) + 2 * c) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero (Sq_I_ne hc hz)) ?_
    rw [add_comm]; exact slitPlane_ne_zero (two_c_add_Sq_mem hc (I * z))
  have hD := ((hS.const_mul (2 : ℂ)).mul (hS.add_const (2 * (c : ℂ))))
  have := hA.neg.sub (hu.div hD hne)
  unfold gh
  exact this

/-- **`|ĝ′| ≤ 13k²/(2|S|)`** once `|S| ≥ 1`, `c ≤ k|S|`, `k ≥ 1`. -/
theorem norm_gh1_le_k (hc : 0 < c) {w : ℂ} {k : ℝ} (hk : 1 ≤ k) (h1 : 1 ≤ ‖Sq c w‖) (hcs : c ≤ k * ‖Sq c w‖) :
    ‖gh1 c w‖ ≤ 13 * k ^ 2 / (2 * ‖Sq c w‖) := by
  set σ := ‖Sq c w‖
  have hσ : 0 < σ := by linarith
  have hcn : ‖(c : ℂ)‖ = c := by rw [Complex.norm_real, Real.norm_of_nonneg hc.le]
  have hS2 : σ ≤ ‖Sq c w + 2 * c‖ := by
    have := Cvs.Prolate.Mellin.PastTurningPhaseSum.norm_add_sq_ge (u := w) hc
    nlinarith [norm_nonneg (Sq c w + 2 * c)]
  have hnum : ‖2 * Sq c w ^ 3 + 4 * c * Sq c w ^ 2 - Sq c w ^ 2 + 2 * c * Sq c w + 4 * c ^ 2‖ ≤ 13 * k ^ 2 * σ ^ 3 := by
    have t1 := norm_add_le (2 * Sq c w ^ 3 + 4 * c * Sq c w ^ 2 - Sq c w ^ 2 + 2 * c * Sq c w) (4 * (c : ℂ) ^ 2)
    have t2 := norm_add_le (2 * Sq c w ^ 3 + 4 * c * Sq c w ^ 2 - Sq c w ^ 2) (2 * (c : ℂ) * Sq c w)
    have t3 := norm_sub_le (2 * Sq c w ^ 3 + 4 * c * Sq c w ^ 2) (Sq c w ^ 2)
    have t4 := norm_add_le (2 * Sq c w ^ 3) (4 * (c : ℂ) * Sq c w ^ 2)
    simp only [norm_mul, norm_pow, hcn, Complex.norm_ofNat] at t1 t2 t3 t4
    have hk2 : 1 ≤ k ^ 2 := by nlinarith
    have a1 : c * σ ^ 2 ≤ k * σ ^ 3 := by nlinarith
    have a2 : σ ^ 2 ≤ σ ^ 3 := by nlinarith
    have a3 : c * σ ≤ k * σ ^ 3 := by nlinarith [mul_le_mul_of_nonneg_left h1 (show 0 ≤ k * σ by positivity)]
    have a4 : c ^ 2 ≤ k ^ 2 * σ ^ 3 := by
      have : c ^ 2 ≤ (k * σ) ^ 2 := pow_le_pow_left₀ hc.le hcs 2
      nlinarith [mul_le_mul_of_nonneg_left h1 (show 0 ≤ k ^ 2 * σ ^ 2 by positivity)]
    have b1 : k * σ ^ 3 ≤ k ^ 2 * σ ^ 3 := by nlinarith [pow_pos hσ 3]
    have b2 : σ ^ 3 ≤ k ^ 2 * σ ^ 3 := by nlinarith [pow_pos hσ 3]
    nlinarith
  unfold gh1
  rw [norm_div, norm_neg, norm_mul, norm_mul, norm_pow, Complex.norm_ofNat,
    div_le_div_iff₀ (by have := lt_of_lt_of_le hσ hS2; positivity) (by positivity)]
  calc ‖2 * Sq c w ^ 3 + 4 * c * Sq c w ^ 2 - Sq c w ^ 2 + 2 * c * Sq c w + 4 * c ^ 2‖ * (2 * σ)
      ≤ 13 * k ^ 2 * σ ^ 3 * (2 * σ) := by gcongr
    _ = 13 * k ^ 2 * (2 * σ ^ 3 * σ) := by ring
    _ ≤ 13 * k ^ 2 * (2 * σ ^ 3 * ‖Sq c w + 2 * c‖) := by gcongr

variable {ε : ℝ}

/-- The facts on the horizontal segment `[iz + η, iz + 2]`. -/
theorem seg_facts (hε : 0 < ε) (hε1 : ε ≤ 1) (hc : 0 < c) (hεc : 2 ≤ ε * c ^ 2) (hz : (2 + ε) * c ≤ z)
    {η : ℝ} (hη : 0 < η) (hη2 : η ≤ 2) {w : ℂ} (hw : w ∈ segment ℝ (I * (z : ℂ) + η) (I * (z : ℂ) + 2)) :
    HasDerivAt (Gh c) (gh c w) w ∧ HasDerivAt (gh c) (gh1 c w) w
      ∧ ‖gh1 c w‖ ≤ 13 / (2 * ε * Real.sqrt ε * c) := by
  rw [segment_eq_image'] at hw
  obtain ⟨l, ⟨hl0, hl1⟩, rfl⟩ := hw
  set t := η + l * (2 - η)
  have ht0 : η ≤ t := by simp only [t]; nlinarith
  have ht2 : t ≤ 2 := by simp only [t]; nlinarith
  have he : I * (z : ℂ) + η + l • (I * (z : ℂ) + 2 - (I * (z : ℂ) + η)) = (t : ℂ) + I * z := by
    simp only [t]; rw [Complex.real_smul]; push_cast; ring
  simp only []
  rw [he]
  have hz0 : 0 < z := by nlinarith
  have hre : 0 < ((t : ℂ) + I * z).re := by simp; linarith
  have him : 0 < ((t : ℂ) + I * z).im := by simp; linarith
  refine ⟨Cvs.Prolate.Mellin.PastTurningPhaseSum.hasDerivAt_Gh hc hre him, Cvs.Prolate.Mellin.PastTurningPhaseSum.hasDerivAt_gh hc hre him, ?_⟩
  -- `|S|² ≥ εc²`
  set σ := ‖Sq c ((t : ℂ) + I * z)‖
  have hσ2 : ε * c ^ 2 ≤ σ ^ 2 := by
    have hw2 : σ ^ 2 = ‖((t : ℂ) + I * z) ^ 2 + 4 * c ^ 2‖ := by
      simp only [σ]; unfold Sq; rw [← norm_pow, Cvs.Prolate.Mellin.FrozenRootErrorIdentity.csqrt_sq]
    rw [hw2]
    have h1 : -(((t : ℂ) + I * z) ^ 2 + 4 * (c : ℂ) ^ 2).re ≤ ‖((t : ℂ) + I * z) ^ 2 + 4 * (c : ℂ) ^ 2‖ := by
      have := Complex.abs_re_le_norm (((t : ℂ) + I * z) ^ 2 + 4 * (c : ℂ) ^ 2)
      linarith [neg_abs_le (((t : ℂ) + I * z) ^ 2 + 4 * (c : ℂ) ^ 2).re]
    have h2 : (((t : ℂ) + I * z) ^ 2 + 4 * (c : ℂ) ^ 2).re = t ^ 2 - z ^ 2 + 4 * c ^ 2 := by simp [sq]
    rw [h2] at h1
    have hz2 : (2 + ε) ^ 2 * c ^ 2 ≤ z ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hz 2
    nlinarith
  set r := Real.sqrt ε
  have hr0 : 0 < r := Real.sqrt_pos.mpr hε
  have hr1 : r ≤ 1 := Real.sqrt_le_one.mpr hε1
  have hrr : r * r = ε := Real.mul_self_sqrt hε.le
  have hσ : r * c ≤ σ := by
    have : (r * c) ^ 2 ≤ σ ^ 2 := by rw [mul_pow, show r ^ 2 = ε by rw [← hrr]; ring]; exact hσ2
    exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp this
  have hσ1 : 1 ≤ σ := by
    have h1 : (1 : ℝ) ^ 2 ≤ (r * c) ^ 2 := by rw [mul_pow, show r ^ 2 = ε by rw [← hrr]; ring]; linarith
    have : 1 ≤ r * c := (pow_le_pow_iff_left₀ zero_le_one (by positivity) two_ne_zero).mp h1
    linarith
  have hk : 1 ≤ 1 / r := by rw [le_div_iff₀ hr0]; linarith
  have hcs : c ≤ 1 / r * σ := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hr0]; linarith
  refine (norm_gh1_le_k hc hk hσ1 hcs).trans ?_
  rw [div_pow, one_pow, show r ^ 2 = ε by rw [← hrr]; ring]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : 0 < ε := hε
  calc 13 * (1 / ε) * (2 * ε * r * c) = 13 * (2 * (r * c)) := by field_simp
    _ ≤ 13 * (2 * σ) := by gcongr
    _ = 13 * (2 * σ) := rfl

/-- **Taylor at the start of the line.** -/
theorem start (hε : 0 < ε) (hε1 : ε ≤ 1) (hc : 0 < c) (hεc : 2 ≤ ε * c ^ 2) (hz : (2 + ε) * c ≤ z) :
    ‖Gh c (I * z + 2) - Gh c (I * z) - 2 * gh c (I * z)‖ ≤ 4 * (13 / (2 * ε * Real.sqrt ε * c))
      ∧ ‖gh c (I * z + 2) - gh c (I * z)‖ ≤ 2 * (13 / (2 * ε * Real.sqrt ε * c)) := by
  set M := 13 / (2 * ε * Real.sqrt ε * c)
  have hM : 0 ≤ M := by have := Real.sqrt_pos.mpr hε; positivity
  have hz2 : 2 * c < z := by nlinarith
  have hGh := tendsto_Gh hc hz2
  have hgh := tendsto_gh hc hz2
  have hη : Tendsto (fun η : ℝ => (η : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using this
  have hev : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < η ∧ η ≤ 1 := by
    have h1 : ∀ᶠ η : ℝ in 𝓝[>] 0, η ∈ Set.Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT (by norm_num)
    filter_upwards [h1] with η hη; exact ⟨hη.1, hη.2.le⟩
  -- the bounds at each `η`
  have hb : ∀ η : ℝ, 0 < η → η ≤ 1 →
      ‖Gh c (I * z + 2) - Gh c (I * z + η) - (2 - η) * gh c (I * z + η)‖ ≤ 4 * M
      ∧ ‖gh c (I * z + 2) - gh c (I * z + η)‖ ≤ 2 * M := by
    intro η hη hη1
    have hconv := convex_segment (𝕜 := ℝ) (I * (z : ℂ) + η) (I * (z : ℂ) + 2)
    have ha := left_mem_segment ℝ (I * (z : ℂ) + η) (I * (z : ℂ) + 2)
    have hbm := right_mem_segment ℝ (I * (z : ℂ) + η) (I * (z : ℂ) + 2)
    have hd : ‖I * (z : ℂ) + 2 - (I * (z : ℂ) + η)‖ = 2 - η := by
      rw [show I * (z : ℂ) + 2 - (I * (z : ℂ) + η) = ((2 - η : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by linarith)]
    have hf := fun w hw => seg_facts hε hε1 hc hεc hz hη (by linarith) (w := w) hw
    constructor
    · have := Cvs.Prolate.Mellin.PastTurningCanonicalLog.taylor2 hconv (f := Gh c) (f₁ := gh c) (f₂ := gh1 c)
        (fun w hw => (hf w hw).1) (fun w hw => (hf w hw).2.1) (fun w hw => (hf w hw).2.2) ha hbm
      rw [hd] at this
      rw [show (I * (z : ℂ) + 2 - (I * (z : ℂ) + η)) = ((2 - η : ℝ) : ℂ) by push_cast; ring] at this
      refine (le_of_eq_of_le (by push_cast; ring_nf) this).trans ?_
      have : (2 - η) ^ 2 ≤ 4 := by nlinarith
      nlinarith
    · have := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le (f := gh c) (f' := gh1 c)
        (fun w hw => (hf w hw).2.1.hasDerivWithinAt) (fun w hw => (hf w hw).2.2) ha hbm
      rw [hd] at this
      refine this.trans ?_
      nlinarith
  constructor
  · have hlim : Tendsto (fun η : ℝ => Gh c (I * z + 2) - Gh c (I * z + η) - (2 - η) * gh c (I * z + η))
        (𝓝[>] 0) (𝓝 (Gh c (I * z + 2) - Gh c (I * z) - (2 - 0) * gh c (I * z))) :=
      (tendsto_const_nhds.sub hGh).sub ((tendsto_const_nhds.sub hη).mul hgh)
    rw [sub_zero] at hlim
    refine le_of_tendsto hlim.norm ?_
    filter_upwards [hev] with η hη
    exact (hb η hη.1 hη.2).1
  · have hlim : Tendsto (fun η : ℝ => gh c (I * z + 2) - gh c (I * z + η)) (𝓝[>] 0)
        (𝓝 (gh c (I * z + 2) - gh c (I * z))) := tendsto_const_nhds.sub hgh
    refine le_of_tendsto hlim.norm ?_
    filter_upwards [hev] with η hη
    exact (hb η hη.1 hη.2).2

end Cvs.Prolate.Mellin.PastTurningStartTaylor
