import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Mellin.RungTransformUnitCircle
import Cvs.Prolate.RungProfileEntireExtension
import Cvs.Prolate.RungWindowProfileCells

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The ray transform, its integration-by-parts identity and its limit at infinite height

For a continuous `F` put `T_F(w) = ∫_0^∞ F(e^{−is}) e^{−is/2} e^{iws} ds`; the unit-circle transform is
`A = T_{G_j}` and the right-edge transform is `B = T_H` with `H(ζ) = (1/x) Σ_{n ≤ x} G_j((n/x)ζ)`. For entire `F`
and `Im w > 0`, `(w − ½) T_F(w) = i F(1) + T_{ζF′}(w)`, so `‖g T_F(σ + ig) − F(1)‖ ≤ (|½ − σ|‖F(1)‖ + M′)/g` with
`M′` a bound for `ζF′` on the unit circle, and `g T_F(σ + ig) → F(1)` as `g → ∞`.
-/

noncomputable section

open Real Set MeasureTheory Filter Complex Topology
open Cvs.Prolate.RungProfileEntireExtension (GC)
open Cvs.Prolate.RungWindowProfileCells (Gr)
open Cvs.Prolate.Mellin.RungTransformUnitCircle (Aw Bw)

namespace Cvs.Prolate.Mellin.RayTransformEdgeSum
open Cvs.ZeroCounting

/-- The ray transform `T_F(w) = ∫_0^∞ F(e^{−is}) e^{−is/2} e^{iws} ds`. -/
def rayT (F : ℂ → ℂ) (w : ℂ) : ℂ :=
  ∫ s in Ioi (0 : ℝ), F (Complex.exp (-(s * I))) * Complex.exp (-(s * I / 2)) * Complex.exp (w * (s * I))

/-- The right-edge sum `H(ζ) = (1/x) Σ_{n ≤ x} G_j((n/x)ζ)`. -/
def edgeSum (x j : ℕ) (ζ : ℂ) : ℂ := 1 / x * ∑ n ∈ Finset.Icc 1 x, GC x j (n / x * ζ)

/-- The unit-circle transform is the ray transform of `G_j`. -/
theorem Aw_eq_rayT (x j : ℕ) : Aw x j = rayT (GC x j) := rfl

/-- The right-edge transform is the ray transform of the right-edge sum. -/
theorem Bw_eq_rayT (x j : ℕ) : Bw x j = rayT (edgeSum x j) := by
  funext w
  unfold Bw rayT edgeSum
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  ring

/-- The edge sum at `ζ = 1` is the Riemann sum `(1/x) Σ_{n ≤ x} G_j(n/x)`. -/
theorem edgeSum_one {x j : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) :
    edgeSum x j 1 = ((1 / x * ∑ n ∈ Finset.Icc 1 x, Gr x j (n / x) : ℝ) : ℂ) := by
  have hx0 : 0 < x := by exact_mod_cast Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  unfold edgeSum
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hn
  have hxr : (0 : ℝ) < x := by exact_mod_cast hx0
  have hmem : (n : ℝ) / x ∈ Icc (-1 : ℝ) 1 := by
    have h0 : (0 : ℝ) ≤ n / x := by positivity
    exact ⟨by linarith, (div_le_one hxr).2 (by exact_mod_cast h2)⟩
  have := Cvs.Prolate.RungProfileEntireExtension.GC_ofReal hx hj hmem
  rw [mul_one, show ((n : ℂ) / x) = (((n : ℝ) / x : ℝ) : ℂ) by push_cast; rfl, this]
  unfold Gr
  push_cast
  rfl

/-! ### Integrability and the size bound -/

/-- A continuous function is bounded on the unit circle. -/
theorem exists_bound_circle {F : ℂ → ℂ} (hF : Continuous F) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℝ, ‖F (Complex.exp (-(s * I)))‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : ℂ) 1).exists_bound_of_continuousOn hF.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun s => (hM _ ?_).trans (le_max_left _ _)⟩
  rw [mem_sphere_zero_iff_norm, show -((s : ℂ) * I) = ((-s : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The norm of the ray integrand is `‖F(e^{−is})‖ e^{−s Im w}`. -/
theorem norm_integrand (F : ℂ → ℂ) (w : ℂ) (s : ℝ) :
    ‖F (Complex.exp (-(s * I))) * Complex.exp (-(s * I / 2)) * Complex.exp (w * (s * I))‖
      = ‖F (Complex.exp (-(s * I)))‖ * Real.exp (-(w.im * s)) := by
  rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp]
  simp [Complex.mul_re]

/-- The ray integrand of a continuous function is integrable for `Im w > 0`. -/
theorem integrableOn_integrand {F : ℂ → ℂ} (hF : Continuous F) {w : ℂ} (hw : 0 < w.im) :
    IntegrableOn (fun s : ℝ => F (Complex.exp (-(s * I))) * Complex.exp (-(s * I / 2)) * Complex.exp (w * (s * I)))
      (Ioi 0) := by
  obtain ⟨M, -, hM⟩ := exists_bound_circle hF
  have hdom : IntegrableOn (fun s : ℝ => M * Real.exp (-w.im * s)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hw).const_mul M
  refine hdom.mono' (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s _ => ?_)
  rw [norm_integrand, neg_mul]
  exact mul_le_mul_of_nonneg_right (hM s) (Real.exp_pos _).le

/-- **The size bound** `‖T_F(w)‖ ≤ M / Im w` when `‖F‖ ≤ M` on the unit circle. -/
theorem norm_rayT_le {F : ℂ → ℂ} {w : ℂ} (hw : 0 < w.im) {M : ℝ}
    (hM : ∀ s : ℝ, ‖F (Complex.exp (-(s * I)))‖ ≤ M) : ‖rayT F w‖ ≤ M / w.im := by
  have hdom : IntegrableOn (fun s : ℝ => M * Real.exp (-w.im * s)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hw).const_mul M
  calc ‖rayT F w‖ ≤ ∫ s in Ioi (0 : ℝ), M * Real.exp (-w.im * s) := by
        refine norm_integral_le_of_norm_le hdom ((ae_restrict_iff' measurableSet_Ioi).2
          (Eventually.of_forall fun s _ => ?_))
        rw [norm_integrand, neg_mul]
        exact mul_le_mul_of_nonneg_right (hM s) (Real.exp_pos _).le
    _ = M / w.im := by
        rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) 0]
        simp [div_eq_mul_inv]

/-! ### Integration by parts -/

/-- **Integration by parts in the ray transform**: for entire `F` and `Im w > 0`,
`(w − ½) T_F(w) = i F(1) + T_{ζF′}(w)`. -/
theorem rayT_ibp {F : ℂ → ℂ} (hF : Differentiable ℂ F) {w : ℂ} (hw : 0 < w.im) :
    (w - 1 / 2) * rayT F w = I * F 1 + rayT (fun ζ => ζ * deriv F ζ) w := by
  have hFc := hF.continuous
  have hdc := hF.deriv.continuous
  set e : ℝ → ℂ := fun s => Complex.exp (-(s * I)) with he_def
  set u : ℝ → ℂ := fun s => F (e s) * Complex.exp (-(s * I / 2)) with hu_def
  set u' : ℝ → ℂ := fun s => deriv F (e s) * (e s * -I) * Complex.exp (-(s * I / 2))
      + F (e s) * (Complex.exp (-(s * I / 2)) * -(I / 2)) with hu'_def
  set v : ℝ → ℂ := fun s => Complex.exp (w * (s * I)) with hv_def
  set v' : ℝ → ℂ := fun s => Complex.exp (w * (s * I)) * (w * I) with hv'_def
  have he : ∀ s : ℝ, HasDerivAt e (e s * -I) s := fun s => by
    have := (((hasDerivAt_id s).ofReal_comp).mul_const I).neg.cexp
    convert this using 1 <;> simp [he_def, Pi.neg_apply]
  have hh : ∀ s : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (-(s * I / 2)))
      (Complex.exp (-(s * I / 2)) * -(I / 2)) s := fun s => by
    have := ((((hasDerivAt_id s).ofReal_comp).mul_const I).div_const 2).neg.cexp
    convert this using 1 <;> simp [Pi.neg_apply]
  have hu : ∀ s ∈ Ioi (0 : ℝ), HasDerivAt u (u' s) s := fun s _ =>
    (((hF (e s)).hasDerivAt.comp s (he s))).mul (hh s)
  have hv : ∀ s ∈ Ioi (0 : ℝ), HasDerivAt v (v' s) s := fun s _ => by
    have := ((((hasDerivAt_id s).ofReal_comp).mul_const I).const_mul w).cexp
    convert this using 1 <;> simp [hv'_def, hv_def]
  have hI1 := integrableOn_integrand hFc hw
  have hI2 := integrableOn_integrand (F := fun ζ => ζ * deriv F ζ) (by fun_prop) hw
  have huv' : IntegrableOn (u * v') (Ioi 0) :=
    IntegrableOn.congr_fun (hI1.mul_const (w * I))
      (fun s _ => by simp only [Pi.mul_apply, hu_def, hv'_def, he_def]; ring) measurableSet_Ioi
  have hu'v : IntegrableOn (u' * v) (Ioi 0) :=
    IntegrableOn.congr_fun ((hI2.const_mul (-I)).add (hI1.const_mul (-(I / 2))))
      (fun s _ => by simp only [Pi.mul_apply, Pi.add_apply, hu'_def, hv_def, he_def]; ring) measurableSet_Ioi
  have huvc : Continuous (u * v) := by
    simp only [hu_def, hv_def, he_def]; fun_prop
  have h0 : Tendsto (u * v) (𝓝[>] 0) (𝓝 (F 1)) := by
    have := (huvc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    convert this using 2
    simp [hu_def, hv_def, he_def]
  have hinf : Tendsto (u * v) atTop (𝓝 0) := by
    obtain ⟨M, -, hM⟩ := exists_bound_circle hFc
    have hlim : Tendsto (fun s : ℝ => M * Real.exp (-(w.im * s))) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
        (tendsto_id.const_mul_atTop hw))).const_mul M
      simpa using this
    refine squeeze_zero_norm (fun s => ?_) hlim
    have := norm_integrand F w s
    simp only [Pi.mul_apply, hu_def, hv_def, he_def] at this ⊢
    rw [this]
    exact mul_le_mul_of_nonneg_right (hM s) (Real.exp_pos _).le
  have key := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h0 hinf
  have e1 : ∫ s in Ioi (0 : ℝ), u s * v' s = w * I * rayT F w := by
    rw [rayT, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    simp only [hu_def, hv'_def, he_def]; ring
  have e2 : ∫ s in Ioi (0 : ℝ), u' s * v s
      = -I * rayT (fun ζ => ζ * deriv F ζ) w + -(I / 2) * rayT F w := by
    rw [rayT, rayT, ← integral_const_mul, ← integral_const_mul, ← integral_add (hI2.const_mul _) (hI1.const_mul _)]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    simp only [hu'_def, hv_def, he_def]; ring
  rw [e1, e2] at key
  linear_combination (-I) * key + (w * rayT F w - rayT (fun ζ => ζ * deriv F ζ) w - rayT F w / 2) * Complex.I_sq

/-! ### The approach to the edge value at infinite height -/

/-! ### The Riemann-sum condition the right-edge law forces -/

/-- The edge sum of a rung is entire. -/
theorem differentiable_edgeSum {x j : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) :
    Differentiable ℂ (edgeSum x j) := by
  have hG := Cvs.Prolate.RungProfileEntireExtension.differentiable_GC hx hj
  unfold edgeSum
  fun_prop

end Cvs.Prolate.Mellin.RayTransformEdgeSum

end
