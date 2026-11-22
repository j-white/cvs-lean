import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.RungProfileEntireExtension
import Cvs.Prolate.RungWindowProfileCells
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.Visibility.WindowLaplaceUPairing
import Cvs.Upstream.SegmentLaplaceVerticalLines
import Cvs.WeilForm.WeilFormOnWindowL2

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The rung transform through the unit circle and the right-edge rays

Each cell integral of Cvs.Prolate.RungWindowProfileCells is the difference of two vertical lines (Cvs.Upstream.SegmentLaplaceVerticalLines): the line at `t_n` is the jump
coefficient `a e^{−(t_n − L/2)/2} e^{w t_n}` times the unit-circle transform `A(w)`, and the lines at `L/2` sum to
`e^{wL/2}` times the right-edge transform `B(w)`, so `F_f(w) = i A(w) J(w) − i e^{wL/2} B(w)` for `Im w > 0`.
-/

noncomputable section

open Real Set MeasureTheory Filter Complex
open Cvs.Route.L1FloorFromBulkD0 (rung)
open Cvs.Route.Visibility.WindowLaplaceUPairing (winLaplace)
open Cvs.Prolate.RungProfileEntireExtension (GC)
open Cvs.Prolate.RungWindowProfileCells (tn piece Ff Gr)

namespace Cvs.Prolate.Mellin.RungTransformUnitCircle
open Cvs.ZeroCounting

/-- The entire `n`-th piece `Φ_n(z) = a e^{−(z − L/2)/2} G_j((n/x) e^{−(z − L/2)})`. -/
def Phi (x j n : ℕ) (z : ℂ) : ℂ :=
  1 / x * Complex.exp (-((z - Real.log x / 2) / 2)) * GC x j (n / x * Complex.exp (-(z - Real.log x / 2)))

/-- **The unit-circle transform** `A(w) = ∫_0^∞ G_j(e^{−is}) e^{−is/2} e^{iws} ds`. -/
def Aw (x j : ℕ) (w : ℂ) : ℂ :=
  ∫ s in Ioi (0 : ℝ), GC x j (Complex.exp (-(s * I))) * Complex.exp (-(s * I / 2)) * Complex.exp (w * (s * I))

/-- **The jump sum** `J(w) = Σ_{n ≤ x} a e^{−(t_n − L/2)/2} e^{w t_n}`. -/
def Jw (x : ℕ) (w : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 x, ((1 / x * Real.exp (-((tn x n - Real.log x / 2) / 2)) : ℝ) : ℂ) * Complex.exp (w * tn x n)

/-- **The right-edge transform** `B(w) = ∫_0^∞ a e^{−is/2} Σ_{n ≤ x} G_j((n/x)e^{−is}) e^{iws} ds`. -/
def Bw (x j : ℕ) (w : ℂ) : ℂ :=
  ∫ s in Ioi (0 : ℝ), 1 / x * Complex.exp (-(s * I / 2))
    * (∑ n ∈ Finset.Icc 1 x, GC x j (n / x * Complex.exp (-(s * I)))) * Complex.exp (w * (s * I))

/-! ### The pieces are entire and bounded on their half strips -/

theorem differentiable_Phi {x j : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) (n : ℕ) : Differentiable ℂ (Phi x j n) := by
  unfold Phi
  have hG := Cvs.Prolate.RungProfileEntireExtension.differentiable_GC hx hj
  fun_prop

/-- On its cell the entire piece is the real piece. -/
theorem Phi_ofReal {x j n : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) (hn : 1 ≤ n) {t : ℝ}
    (ht : t ∈ Icc (tn x n) (Real.log x / 2)) : Phi x j n t = ((piece x j n t : ℝ) : ℂ) := by
  have hx0 : 0 < x := by exact_mod_cast Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have hm := Cvs.Prolate.RungWindowProfileCells.arg_mem hx0 hn ht
  have e1 : (n : ℂ) / x * Complex.exp (-((t : ℂ) - Real.log x / 2))
      = (((n : ℝ) / x * Real.exp (-(t - Real.log x / 2)) : ℝ) : ℂ) := by push_cast; rfl
  have e2 : Complex.exp (-(((t : ℂ) - Real.log x / 2) / 2)) = ((Real.exp (-((t - Real.log x / 2) / 2)) : ℝ) : ℂ) := by
    push_cast; rfl
  unfold Phi piece
  rw [e1, e2, Cvs.Prolate.RungProfileEntireExtension.GC_ofReal hx hj ⟨by linarith [hm.1], hm.2⟩]
  unfold Gr
  push_cast
  ring

/-- **The piece is bounded on its half strip**. -/
theorem exists_bound_Phi {x j : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) {n : ℕ} (hn : 1 ≤ n) :
    ∃ M : ℝ, ∀ t ∈ Icc (tn x n) (Real.log x / 2), ∀ s : ℝ, 0 ≤ s → ‖Phi x j n (t + s * I)‖ ≤ M := by
  have hx0 : 0 < x := by exact_mod_cast Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  obtain ⟨M, hM⟩ := Cvs.Prolate.RungProfileEntireExtension.exists_bound_GC hx hj
  refine ⟨1 / x * Real.exp (Real.log x / 2) * M, fun t ht s _ => ?_⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simp))
  have hm := Cvs.Prolate.RungWindowProfileCells.arg_mem hx0 hn ht
  have htn : -(Real.log x / 2) ≤ t := by
    have := Cvs.Prolate.RungWindowProfileCells.tn_mem (x := x) (n := n) (Finset.mem_Icc.2 ⟨hn, ?_⟩)
    · linarith [this.1, ht.1]
    · have : Real.log n ≤ Real.log x := by unfold tn at ht; linarith [ht.1, ht.2]
      have hnr : (0 : ℝ) < n := by exact_mod_cast hn
      have hxr : (0 : ℝ) < x := by exact_mod_cast hx0
      exact_mod_cast (Real.log_le_log_iff hnr hxr).1 this
  unfold Phi
  rw [norm_mul, norm_mul]
  have h1 : ‖(1 : ℂ) / x‖ = 1 / x := by simp
  have h2 : ‖Complex.exp (-(((t : ℂ) + s * I - Real.log x / 2) / 2))‖ = Real.exp (-((t - Real.log x / 2) / 2)) := by
    rw [Complex.norm_exp]; congr 1; simp [-Complex.natCast_log]
  have h3 : ‖(n : ℂ) / x * Complex.exp (-((t : ℂ) + s * I - Real.log x / 2))‖
      = (n : ℝ) / x * Real.exp (-(t - Real.log x / 2)) := by
    rw [norm_mul, Complex.norm_exp]
    have : ‖(n : ℂ) / x‖ = (n : ℝ) / x := by
      rw [norm_div]; simp
    rw [this]; congr 2; simp [-Complex.natCast_log]
  rw [h1, h2]
  have hG := hM _ (by rw [h3]; exact hm.2)
  have he : Real.exp (-((t - Real.log x / 2) / 2)) ≤ Real.exp (Real.log x / 2) := Real.exp_le_exp.2 (by linarith)
  calc 1 / (x : ℝ) * Real.exp (-((t - Real.log x / 2) / 2)) * ‖GC x j (n / x * Complex.exp (-((t : ℂ) + s * I
        - Real.log x / 2)))‖
      ≤ 1 / x * Real.exp (Real.log x / 2) * M := by gcongr

/-! ### The two vertical lines of a cell -/

/-- The line at `t_n`: `Φ_n(t_n + is) = a e^{−(t_n − L/2)/2} e^{−is/2} G_j(e^{−is})`. -/
theorem Phi_tn {x j n : ℕ} (hx0 : 0 < x) (hn : 1 ≤ n) (s : ℝ) :
    Phi x j n (tn x n + s * I)
      = 1 / x * Real.exp (-((tn x n - Real.log x / 2) / 2)) * Complex.exp (-(s * I / 2))
        * GC x j (Complex.exp (-(s * I))) := by
  have hxr : (0 : ℝ) < x := by exact_mod_cast hx0
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  unfold Phi
  have e1 : (n : ℂ) / x * Complex.exp (-(((tn x n : ℝ) : ℂ) + s * I - Real.log x / 2)) = Complex.exp (-(s * I)) := by
    have : -(((tn x n : ℝ) : ℂ) + s * I - Real.log x / 2) = ((Real.log x - Real.log n : ℝ) : ℂ) + -(s * I) := by
      unfold tn; push_cast; ring
    rw [this, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_sub, Real.exp_log hxr, Real.exp_log hnr]
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hnr.ne'
    have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hxr.ne'
    push_cast
    field_simp
  have e2 : Complex.exp (-((((tn x n : ℝ) : ℂ) + s * I - Real.log x / 2) / 2))
      = ((Real.exp (-((tn x n - Real.log x / 2) / 2)) : ℝ) : ℂ) * Complex.exp (-(s * I / 2)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1; push_cast; ring
  rw [e1, e2]; ring

/-- The lines at `L/2` sum to `a e^{−is/2} Σ_n G_j((n/x) e^{−is})`. -/
theorem sum_Phi_edge {x j : ℕ} (s : ℝ) :
    ∑ n ∈ Finset.Icc 1 x, Phi x j n (((Real.log x / 2 : ℝ) : ℂ) + s * I)
      = 1 / x * Complex.exp (-(s * I / 2)) * ∑ n ∈ Finset.Icc 1 x, GC x j (n / x * Complex.exp (-(s * I))) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold Phi
  have e : (((Real.log x / 2 : ℝ) : ℂ) + s * I - ((Real.log x : ℝ) : ℂ) / 2) = s * I := by push_cast; ring
  push_cast at e ⊢
  rw [e]

/-! ### The factorisation of the one-sided transform -/

/-- **The one-sided transform factorises through its vertical lines**: for `Im w > 0`,
`F_f(w) = i A(w) J(w) − i e^{wL/2} B(w)`. -/
theorem Ff_eq {x : ℕ} (hx : 80 ≤ 2 * π * x) {j : ℕ} (hj : j < x) {w : ℂ} (hwi : 0 < w.im) :
    Ff x j w = I * Aw x j w * Jw x w - I * Complex.exp (w * (Real.log x / 2 : ℝ)) * Bw x j w := by
  have hx0 : 0 < x := by exact_mod_cast Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  set h := Real.log x / 2 with hh
  have hcell : ∀ n ∈ Finset.Icc 1 x, ∫ t in tn x n..h, ((piece x j n t : ℝ) : ℂ) * Complex.exp (w * t)
      = I * (∫ s in Ioi (0 : ℝ), Phi x j n (tn x n + s * I) * Complex.exp (w * (tn x n + s * I)))
        - I * (∫ s in Ioi (0 : ℝ), Phi x j n (h + s * I) * Complex.exp (w * (h + s * I))) := fun n hn => by
    have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
    have hm := Cvs.Prolate.RungWindowProfileCells.tn_mem hn
    obtain ⟨M, hM⟩ := exists_bound_Phi hx hj hn1
    rw [← Cvs.Upstream.SegmentLaplaceVerticalLines.laplace_eq_vertical (differentiable_Phi hx hj n) hwi hm.2 hM]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hm.2] at ht
    rw [Phi_ofReal hx hj hn1 ht]
  -- the line at `t_n` is the jump coefficient times `A(w)`
  have hA : ∀ n ∈ Finset.Icc 1 x,
      ∫ s in Ioi (0 : ℝ), Phi x j n (tn x n + s * I) * Complex.exp (w * (tn x n + s * I))
        = ((1 / x * Real.exp (-((tn x n - h) / 2)) : ℝ) : ℂ) * Complex.exp (w * tn x n) * Aw x j w := fun n hn => by
    have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
    rw [Aw, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    rw [Phi_tn hx0 hn1, ← hh, show w * ((tn x n : ℂ) + s * I) = w * tn x n + w * (s * I) by ring, Complex.exp_add]
    push_cast; ring
  -- the lines at `L/2` sum to `e^{wL/2} B(w)`
  have hint : ∀ n ∈ Finset.Icc 1 x, IntegrableOn (fun s : ℝ => Phi x j n (h + s * I) * Complex.exp (w * (h + s * I)))
      (Ioi 0) := fun n hn => by
    have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
    obtain ⟨M, hM⟩ := exists_bound_Phi hx hj hn1
    exact Cvs.Upstream.SegmentLaplaceVerticalLines.integrableOn_vertical (differentiable_Phi hx hj n).continuous hwi h
      (hM h ⟨(Cvs.Prolate.RungWindowProfileCells.tn_mem hn).2, le_rfl⟩)
  have hB : ∑ n ∈ Finset.Icc 1 x, (∫ s in Ioi (0 : ℝ), Phi x j n (h + s * I) * Complex.exp (w * (h + s * I)))
      = Complex.exp (w * (h : ℂ)) * Bw x j w := by
    rw [← integral_finsetSum _ hint, Bw, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    rw [← Finset.sum_mul, hh, sum_Phi_edge, ← hh,
      show w * ((h : ℂ) + s * I) = w * h + w * (s * I) by ring, Complex.exp_add]
    ring
  unfold Ff
  rw [Finset.sum_congr rfl hcell, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hB,
    Finset.sum_congr rfl hA, ← Finset.sum_mul, Jw, ← hh]
  ring

/-- The one-sided transform is real on the real axis: `F_f(w̄) = conj F_f(w)`. -/
theorem Ff_conj (x j : ℕ) (w : ℂ) : Ff x j ((starRingEnd ℂ) w) = (starRingEnd ℂ) (Ff x j w) := by
  unfold Ff
  rw [map_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hm := Cvs.Prolate.RungWindowProfileCells.tn_mem hn
  rw [intervalIntegral.integral_of_le hm.2, intervalIntegral.integral_of_le hm.2, ← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]

/-- The window transform is real on the real axis: `F_u(w̄) = conj F_u(w)`. -/
theorem winLaplace_conj {x : ℕ} (u : Cvs.Route.L1FloorFromBulkD0.Dom x) (w : ℂ) :
    winLaplace u ((starRingEnd ℂ) w) = (starRingEnd ℂ) (winLaplace u w) := by
  have hh : -(Real.log x / 2) ≤ Real.log x / 2 := by have := Real.log_natCast_nonneg x; linarith
  unfold winLaplace
  rw [intervalIntegral.integral_of_le hh, intervalIntegral.integral_of_le hh, ← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]

end Cvs.Prolate.Mellin.RungTransformUnitCircle

end
