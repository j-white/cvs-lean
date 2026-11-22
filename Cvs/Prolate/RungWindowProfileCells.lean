import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.FullSpanIndexFloor
import Cvs.L2a.TailLogScaleTest
import Cvs.Prolate.EvenLevelIndexLemma
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.Visibility.WindowLaplaceUPairing
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowReflectionSymmetry
import Cvs.Xi.EImageWindowPoisson

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The window profile of a rung as a sum of entire pieces on the cells

On the window `t ∈ (−L/2, L/2)`, `L = log x`, the profile of `r_j` is `(f(t) + f(−t))/2` with
`f(t) = Σ_{n ≤ x} 1_{[t_n, L/2]}(t) a e^{−(t − L/2)/2} G_j((n/x) e^{−(t − L/2)})`, `t_n = log n − L/2`, `a = 1/x`; so
`F_{r_j}(w) = (F_f(w) + F_f(−w))/2` with `F_f(w) = Σ_n ∫_{t_n}^{L/2} piece_n(t) e^{wt} dt`.
-/

noncomputable section

open Real Set MeasureTheory Filter Complex
open Cvs.Route.L1FloorFromBulkD0 (Dom rung)
open Cvs.Route.Visibility.WindowLaplaceUPairing (prof winLaplace)

namespace Cvs.Prolate.RungWindowProfileCells
open Cvs.ZeroCounting

/-- The real rung profile `G_j = h_{4j} − α_j h₀` at `c = 2πx`. -/
def Gr (x j : ℕ) (s : ℝ) : ℝ :=
  Cvs.Prolate.EvenRungsByIndex.rung (2 * π * x) (2 * j) s - Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j * Cvs.Prolate.EvenRungsByIndex.rung (2 * π * x) 0 s

/-- The cell start `t_n = log n − L/2`. -/
def tn (x n : ℕ) : ℝ := Real.log n - Real.log x / 2

/-- The `n`-th piece `a e^{−(t − L/2)/2} G_j((n/x) e^{−(t − L/2)})` on the real line. -/
def piece (x j n : ℕ) (t : ℝ) : ℝ :=
  1 / x * Real.exp (-((t - Real.log x / 2) / 2)) * Gr x j (n / x * Real.exp (-(t - Real.log x / 2)))

/-- The one-sided window profile `f(t) = Σ_{n ≤ x} 1_{[t_n, L/2]}(t) piece_n(t)`. -/
def fR (x j : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 x, (Icc (tn x n) (Real.log x / 2)).indicator (piece x j n) t

/-! ### The profile of the rung -/

/-- The spine test of rung `j` is `k_{G_j}`. -/
theorem spineG_single {x : ℕ} (j : Cvs.Approximant.SpineSubspace.SF x) (s : ℝ) :
    Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j (1 : ℝ)) s = Gr x j s := by
  unfold Cvs.Approximant.DeepIndexSpineSpan.spineG Gr
  rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
  simp

/-- **The profile of a rung is the even part of `k_{G_j}`**: `r_j(s) = (k(s) + k(L − s))/2` a.e. -/
theorem prof_rung_ae {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Cvs.Approximant.SpineSubspace.SF x) :
    prof (rung x j) =ᵐ[volume] fun s =>
      (Cvs.Approximant.SpineSubspace.kG x (Pi.single j (1 : ℝ)) s + Cvs.Approximant.SpineSubspace.kG x (Pi.single j (1 : ℝ)) (Real.log x - s)) / 2 := by
  let A : Lp ℝ 2 (volume : Measure ℝ) := (Cvs.Approximant.SpineSubspace.spineMap x (Pi.single j (1 : ℝ))).1.1
  have hφae : (A : ℝ → ℝ) =ᵐ[volume] Cvs.Approximant.SpineSubspace.kG x (Pi.single j (1 : ℝ)) :=
    Cvs.Approximant.SpineSubspace.coe_spineMap_ae x hx (Pi.single j (1 : ℝ))
  have hrefl : (fun s => (A : ℝ → ℝ) (Real.log x - s))
      =ᵐ[volume] fun s => Cvs.Approximant.SpineSubspace.kG x (Pi.single j (1 : ℝ)) (Real.log x - s) :=
    (Measure.measurePreserving_sub_left volume (Real.log x)).quasiMeasurePreserving.ae_eq_comp
      (g₁ := (A : ℝ → ℝ)) (g₂ := Cvs.Approximant.SpineSubspace.kG x (Pi.single j (1 : ℝ))) hφae
  have hR := Cvs.WeilForm.WindowReflectionSymmetry.refl_ae (Real.log x) A
  have e : prof (rung x j) = ⇑(((1 / 2 : ℝ) • (A + Cvs.WeilForm.WindowReflectionSymmetry.refl (Real.log x) A) : Lp ℝ 2 (volume : Measure ℝ))) :=
    rfl
  rw [e]
  filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ) (A + Cvs.WeilForm.WindowReflectionSymmetry.refl (Real.log x) A),
    Lp.coeFn_add A (Cvs.WeilForm.WindowReflectionSymmetry.refl (Real.log x) A), hφae, hR, hrefl] with s h1 h2 h3 h4 h5
  rw [h1, Pi.smul_apply, h2, Pi.add_apply, h3, h4, h5, smul_eq_mul]
  ring

/-- **The one-sided profile on the window**: for `−L/2 < t ≤ L/2`, `k_{G_j}(t + L/2) = f(t)`. -/
theorem kG_eq_fR {x : ℕ} (hx : 0 < x) (j : Cvs.Approximant.SpineSubspace.SF x) {t : ℝ} (ht1 : -(Real.log x / 2) < t)
    (ht2 : t ≤ Real.log x / 2) :
    Cvs.Approximant.SpineSubspace.kG x (Pi.single j (1 : ℝ)) (t + Real.log x / 2) = fR x j t := by
  have hxr : (0 : ℝ) < x := by exact_mod_cast hx
  set L := Real.log x with hL
  set θ := Real.exp (t - L / 2) with hθ
  have hθ0 : 0 < θ := Real.exp_pos _
  have hxL : Real.exp L = x := Real.exp_log hxr
  have ha : 2 * π / (2 * π * (x : ℝ)) = 1 / x := by field_simp
  have hθx : θ * x = Real.exp (t + L / 2) := by
    rw [hθ, ← hxL, ← Real.exp_add]; congr 1; ring
  have hθa : 1 / (x : ℝ) ≤ θ := by
    rw [div_le_iff₀ hxr, hθx, ← Real.exp_zero]; exact Real.exp_le_exp.2 (by linarith)
  have hθ1 : θ ≤ 1 := by rw [hθ, ← Real.exp_zero]; exact Real.exp_le_exp.2 (by linarith)
  have hθd : θ / (1 / (x : ℝ)) = θ * x := by field_simp
  have hfl : ⌊θ / (1 / x)⌋₊ ≤ x := by
    rw [hθd]
    exact Nat.floor_le_of_le (by nlinarith)
  unfold Cvs.Approximant.SpineSubspace.kG Cvs.L2a.TailLogScaleTest.logScale Cvs.Xi.EImageWindowPoisson.window
  rw [ha, show t + L / 2 - Real.log x = t - L / 2 by rw [hL]; ring, ← hθ,
    indicator_of_mem (mem_Icc.2 ⟨hθa, hθ1⟩)]
  unfold Cvs.Xi.EImageWindowPoisson.eimage fR
  rw [Finset.mul_sum, Finset.sum_mul]
  have hsub : Finset.Icc 1 ⌊θ / (1 / x)⌋₊ = (Finset.Icc 1 x).filter (fun n => n ≤ ⌊θ / (1 / x)⌋₊) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_filter]; omega
  rw [hsub, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn1
  have hiff : n ≤ ⌊θ / (1 / x)⌋₊ ↔ t ∈ Icc (tn x n) (L / 2) := by
    rw [hθd, Nat.le_floor_iff (by positivity), hθx, mem_Icc, tn, ← hL]
    constructor
    · intro h
      refine ⟨?_, ht2⟩
      have := Real.log_le_log hnr h
      rw [Real.log_exp] at this; linarith
    · intro h
      have h' : Real.log n ≤ t + L / 2 := by linarith [h.1]
      calc (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hnr).symm
        _ ≤ Real.exp (t + L / 2) := Real.exp_le_exp.2 h'
  by_cases h : n ≤ ⌊θ / (1 / x)⌋₊
  · rw [ite_eq_left h, indicator_of_mem (hiff.1 h), piece, Gr, Cvs.Prolate.RungWindowProfileCells.spineG_single j]
    unfold Gr
    have e1 : (n : ℝ) * (1 / x) / θ = n / x * Real.exp (-(t - L / 2)) := by
      rw [hθ, Real.exp_neg]; field_simp
    have e2 : 1 / (x : ℝ) / θ * Real.exp ((t - L / 2) / 2) = 1 / x * Real.exp (-((t - L / 2) / 2)) := by
      rw [hθ, div_eq_mul_inv (1 / (x : ℝ)), ← Real.exp_neg, mul_assoc, ← Real.exp_add]
      congr 2; ring
    rw [e1, ← e2]; ring
  · rw [ite_eq_right h, indicator_of_notMem (fun hm => h (hiff.2 hm))]

/-! ### The transform as a sum over the cells -/

/-- `G_j` is continuous on `[−1, 1]`. -/
theorem continuousOn_Gr {x j : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) : ContinuousOn (Gr x j) (Icc (-1) 1) := by
  have h1 := (Cvs.L2a.FullSpanIndexFloor.full_index x hx hj).1
  have h0 := Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero (2 * π * x)
  exact (Cvs.Prolate.EvenRungsByIndex.continuousOn_rung h1).sub (continuousOn_const.mul (Cvs.Prolate.EvenRungsByIndex.continuousOn_rung h0))

/-- On its cell `[t_n, L/2]` the argument `(n/x) e^{−(t − L/2)}` lies in `[0, 1]`. -/
theorem arg_mem {x n : ℕ} (hx : 0 < x) (hn : 1 ≤ n) {t : ℝ} (ht : t ∈ Icc (tn x n) (Real.log x / 2)) :
    (n : ℝ) / x * Real.exp (-(t - Real.log x / 2)) ∈ Icc (0 : ℝ) 1 := by
  have hxr : (0 : ℝ) < x := by exact_mod_cast hx
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨by positivity, ?_⟩
  have h1 : -(t - Real.log x / 2) ≤ Real.log x - Real.log n := by unfold tn at ht; linarith [ht.1]
  calc (n : ℝ) / x * Real.exp (-(t - Real.log x / 2)) ≤ n / x * Real.exp (Real.log x - Real.log n) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h1) (by positivity)
    _ = 1 := by rw [Real.exp_sub, Real.exp_log hxr, Real.exp_log hnr]; field_simp

/-- The `n`-th piece is continuous on its cell. -/
theorem continuousOn_piece {x j n : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) (hn : 1 ≤ n) :
    ContinuousOn (piece x j n) (Icc (tn x n) (Real.log x / 2)) := by
  have hx0 : 0 < x := by exact_mod_cast Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have hm : MapsTo (fun t : ℝ => (n : ℝ) / x * Real.exp (-(t - Real.log x / 2))) (Icc (tn x n) (Real.log x / 2))
      (Icc (-1) 1) := fun t ht => by
    have := arg_mem hx0 hn ht
    exact ⟨by linarith [this.1], this.2⟩
  have hG := (continuousOn_Gr hx hj).comp (by fun_prop : Continuous fun t : ℝ =>
    (n : ℝ) / x * Real.exp (-(t - Real.log x / 2))).continuousOn hm
  have hc : Continuous fun t : ℝ => 1 / (x : ℝ) * Real.exp (-((t - Real.log x / 2) / 2)) := by fun_prop
  unfold piece
  exact hc.continuousOn.mul hG

/-- `t_n ≤ L/2` for `n ≤ x`, and `−L/2 ≤ t_n` for `1 ≤ n`. -/
theorem tn_mem {x n : ℕ} (hn : n ∈ Finset.Icc 1 x) : tn x n ∈ Icc (-(Real.log x / 2)) (Real.log x / 2) := by
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hn
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast h1
  have hxn : (n : ℝ) ≤ x := by exact_mod_cast h2
  have hl0 := Real.log_nonneg hnr
  have hl1 := Real.log_le_log (by linarith) hxn
  unfold tn; constructor <;> linarith

/-- **The cell integral**: `∫_{−L/2}^{L/2} 1_{[t_n, L/2]}(t) piece_n(t) e^{wt} dt = ∫_{t_n}^{L/2} piece_n(t) e^{wt}
dt`. -/
theorem integral_indicator_piece {x j n : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) (hn : n ∈ Finset.Icc 1 x)
    (w : ℂ) :
    IntervalIntegrable (fun t : ℝ => (((Icc (tn x n) (Real.log x / 2)).indicator (piece x j n) t : ℝ) : ℂ)
        * Complex.exp (w * t)) volume (-(Real.log x / 2)) (Real.log x / 2)
      ∧ ∫ t in -(Real.log x / 2)..Real.log x / 2,
          (((Icc (tn x n) (Real.log x / 2)).indicator (piece x j n) t : ℝ) : ℂ) * Complex.exp (w * t)
        = ∫ t in tn x n..Real.log x / 2, ((piece x j n t : ℝ) : ℂ) * Complex.exp (w * t) := by
  have hm := tn_mem hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
  set F : ℝ → ℂ := fun t => ((piece x j n t : ℝ) : ℂ) * Complex.exp (w * t) with hF
  have hFc : ContinuousOn F (Icc (tn x n) (Real.log x / 2)) :=
    (Complex.continuous_ofReal.comp_continuousOn (continuousOn_piece hx hj hn1)).mul (by fun_prop)
  have hFi : IntegrableOn F (Icc (tn x n) (Real.log x / 2)) := hFc.integrableOn_compact isCompact_Icc
  have e : (fun t : ℝ => (((Icc (tn x n) (Real.log x / 2)).indicator (piece x j n) t : ℝ) : ℂ)
      * Complex.exp (w * t)) = (Icc (tn x n) (Real.log x / 2)).indicator F := by
    funext t
    by_cases ht : t ∈ Icc (tn x n) (Real.log x / 2)
    · simp [indicator_of_mem ht, hF]
    · simp [indicator_of_notMem ht]
  rw [e]
  have hI : Integrable ((Icc (tn x n) (Real.log x / 2)).indicator F) :=
    (integrable_indicator_iff measurableSet_Icc).2 hFi
  refine ⟨hI.intervalIntegrable, ?_⟩
  rw [intervalIntegral.integral_of_le (by linarith [hm.1, hm.2]), intervalIntegral.integral_of_le hm.2,
    integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
  have hs : (Icc (tn x n) (Real.log x / 2) ∩ Ioc (-(Real.log x / 2)) (Real.log x / 2) : Set ℝ)
      =ᵐ[volume] (Ioc (tn x n) (Real.log x / 2) : Set ℝ) := by
    have h1 : Ioc (tn x n) (Real.log x / 2)
        ⊆ Icc (tn x n) (Real.log x / 2) ∩ Ioc (-(Real.log x / 2)) (Real.log x / 2) :=
      fun t ht => ⟨⟨le_of_lt ht.1, ht.2⟩, ⟨by linarith [hm.1, ht.1], ht.2⟩⟩
    have h2 : Icc (tn x n) (Real.log x / 2) ∩ Ioc (-(Real.log x / 2)) (Real.log x / 2)
        ⊆ Icc (tn x n) (Real.log x / 2) :=
      inter_subset_left
    exact (ae_eq_of_subset_of_measure_ge h1 (by
      rw [Real.volume_Ioc, ← Real.volume_Icc]; exact measure_mono h2) (by measurability)
      (ne_top_of_le_ne_top (by simp [Real.volume_Icc]) (measure_mono h2))).symm
  rw [Measure.restrict_congr_set hs]

/-- The one-sided transform `F_f(w) = Σ_n ∫_{t_n}^{L/2} piece_n(t) e^{wt} dt`. -/
def Ff (x j : ℕ) (w : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 x, ∫ t in tn x n..Real.log x / 2, ((piece x j n t : ℝ) : ℂ) * Complex.exp (w * t)

/-- `f(t)e^{wt}` is integrable on the window, and its integral is `F_f(w)`. -/
theorem integral_fR {x : ℕ} (hx : 80 ≤ 2 * π * x) {j : ℕ} (hj : j < x) (w : ℂ) :
    IntervalIntegrable (fun t : ℝ => ((fR x j t : ℝ) : ℂ) * Complex.exp (w * t)) volume
        (-(Real.log x / 2)) (Real.log x / 2)
      ∧ ∫ t in -(Real.log x / 2)..Real.log x / 2, ((fR x j t : ℝ) : ℂ) * Complex.exp (w * t) = Ff x j w := by
  have e : (fun t : ℝ => ((fR x j t : ℝ) : ℂ) * Complex.exp (w * t)) = fun t => ∑ n ∈ Finset.Icc 1 x,
      (((Icc (tn x n) (Real.log x / 2)).indicator (piece x j n) t : ℝ) : ℂ) * Complex.exp (w * t) := by
    funext t; unfold fR; push_cast; rw [Finset.sum_mul]
  rw [e]
  have hI : ∀ n ∈ Finset.Icc 1 x, IntervalIntegrable (fun t : ℝ =>
      (((Icc (tn x n) (Real.log x / 2)).indicator (piece x j n) t : ℝ) : ℂ) * Complex.exp (w * t)) volume
      (-(Real.log x / 2)) (Real.log x / 2) := fun n hn => (integral_indicator_piece hx hj hn w).1
  have hS := IntervalIntegrable.sum _ hI
  have e2 : (∑ n ∈ Finset.Icc 1 x, fun t : ℝ =>
      (((Icc (tn x n) (Real.log x / 2)).indicator (piece x j n) t : ℝ) : ℂ) * Complex.exp (w * t))
      = fun t => ∑ n ∈ Finset.Icc 1 x,
      (((Icc (tn x n) (Real.log x / 2)).indicator (piece x j n) t : ℝ) : ℂ) * Complex.exp (w * t) := by
    funext t; simp [Finset.sum_apply]
  rw [e2] at hS
  refine ⟨hS, ?_⟩
  rw [intervalIntegral.integral_finsetSum hI]
  exact Finset.sum_congr rfl fun n hn => (integral_indicator_piece hx hj hn w).2

/-- **The rung transform from the one-sided profile**: `F_{r_j}(w) = (F_f(w) + F_f(−w))/2`. -/
theorem winLaplace_rung_eq {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Cvs.Approximant.SpineSubspace.SF x) (w : ℂ) :
    winLaplace (rung x j) w = (Ff x j w + Ff x j (-w)) / 2 := by
  have hx0 : 0 < x := by exact_mod_cast Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have hj : (j : ℕ) < x := Cvs.Approximant.SpineSubspace.SF_lt x j j.2
  set h := Real.log x / 2 with hh
  have hh0 : 0 ≤ h := by have := Real.log_natCast_nonneg x; rw [hh]; linarith
  have hpa := (measurePreserving_add_right volume h).quasiMeasurePreserving.ae_eq_comp
    (g₁ := prof (rung x j)) (g₂ := fun s =>
      (Cvs.Approximant.SpineSubspace.kG x (Pi.single j (1 : ℝ)) s + Cvs.Approximant.SpineSubspace.kG x (Pi.single j (1 : ℝ)) (Real.log x - s)) / 2)
    (prof_rung_ae hx j)
  have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ h := by rw [ae_iff]; simp
  have hcongr : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ uIoc (-h) h →
      ((prof (rung x j) (t + h) : ℝ) : ℂ) * Complex.exp (w * t)
        = (((fR x j t : ℝ) : ℂ) * Complex.exp (w * t) + ((fR x j (-t) : ℝ) : ℂ) * Complex.exp (w * t)) / 2 := by
    filter_upwards [hpa, hne] with t ht htn hmem
    rw [uIoc_of_le (by linarith)] at hmem
    have h1 := kG_eq_fR hx0 j hmem.1 hmem.2
    have h2 := kG_eq_fR hx0 j (t := -t) (by linarith [lt_of_le_of_ne hmem.2 htn]) (by linarith [hmem.1])
    simp only [Function.comp] at ht
    rw [← hh] at h1 h2
    rw [ht, show Real.log x - (t + h) = -t + h by rw [hh]; ring, h1, h2]
    push_cast; ring
  rw [winLaplace, intervalIntegral.integral_congr_ae hcongr]
  obtain ⟨hI1, hE1⟩ := integral_fR hx hj w
  obtain ⟨hI2, hE2⟩ := integral_fR hx hj (-w)
  have hI2' : IntervalIntegrable (fun t : ℝ => ((fR x j (-t) : ℝ) : ℂ) * Complex.exp (w * t)) volume (-h) h := by
    have := (IntervalIntegrable.iff_comp_neg (f := fun t : ℝ => ((fR x j t : ℝ) : ℂ) * Complex.exp (-w * t))).1 hI2
    simp only [neg_neg] at this
    refine this.symm.congr fun t _ => ?_
    simp only [Complex.ofReal_neg]; ring_nf
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add hI1 hI2', hE1]
  refine congrArg (fun z => (Ff x j w + z) / 2) ?_
  rw [← hE2]
  have hc := intervalIntegral.integral_comp_neg (a := -h) (b := h)
    (fun t : ℝ => ((fR x j t : ℝ) : ℂ) * Complex.exp (-w * t))
  simp only [neg_neg] at hc
  rw [← hh, ← hc]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [Complex.ofReal_neg]; ring_nf

end Cvs.Prolate.RungWindowProfileCells

end
