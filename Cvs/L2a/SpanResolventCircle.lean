import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.RungExactOrthogonality

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The span resolvent `Ψ_w = Σ a_iψ_i/(w − σ_i²)` on the circle `|w − c²/2| = c²`

For `f` holomorphic on the disc, `Σ a_iψ_i(t) f(σ_i²) = (2πi)⁻¹ ∮ f(w) Ψ_w(t) dw` with `σ_i² = c² − χ_i ∈ [0, c²]`.
On the circle `|w − σ_i²| ≥ c²/2`, so orthogonality of the rungs (Cvs.Prolate.RungExactOrthogonality) gives `∫_{Ioi 1} |Ψ_w|² ≤ 4P/c⁴`
with `P = ∫_{Ioi 1} (Σ a_iψ_i)²`.
-/

namespace Cvs.L2a.SpanResolventCircle

open Real Set Filter Topology MeasureTheory Complex Metric Cvs.L2a.AngularProlateTailPositive

/-- **Cauchy formula for a finite combination**: `Σ b_i f(z_i) = (2πi)⁻¹ ∮ (Σ b_i/(w − z_i)) f(w) dw`
for `f` holomorphic on the open disc and continuous on its closure, and all `z_i` in the disc. -/
theorem sum_smul_eq_circleIntegral {ι : Type*} (S : Finset ι) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E} {z₀ : ℂ} {R : ℝ} (hf : DiffContOnCl ℂ f (ball z₀ R))
    (b z : ι → ℂ) (hz : ∀ i ∈ S, z i ∈ ball z₀ R) :
    ∑ i ∈ S, b i • f (z i) = (2 * π * I : ℂ)⁻¹ • ∮ w in C(z₀, R), (∑ i ∈ S, b i / (w - z i)) • f w := by
  have hint : ∀ i ∈ S, CircleIntegrable (fun w => (b i / (w - z i)) • f w) z₀ R := by
    intro i hi
    have hR : 0 < R := pos_of_mem_ball (hz i hi)
    refine ContinuousOn.circleIntegrable hR.le ?_
    refine ContinuousOn.smul ?_ (hf.continuousOn.mono ?_)
    · refine continuousOn_const.div₀ (continuousOn_id.sub continuousOn_const) fun w hw => ?_
      refine sub_ne_zero.mpr fun h => ?_
      have h1 := hz i hi
      rw [mem_ball, ← h] at h1
      rw [mem_sphere] at hw
      linarith
    · rw [closure_ball z₀ hR.ne']
      exact sphere_subset_closedBall
  simp_rw [Finset.sum_smul]
  rw [circleIntegral.integral_fun_sum hint, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← hf.two_pi_i_inv_smul_circleIntegral_sub_inv_smul (hz i hi), smul_comm]
  congr 1
  rw [← circleIntegral.integral_smul]
  congr 1
  ext w
  rw [smul_smul, div_eq_mul_inv]

/-- The span resolvent `Ψ_w(t) = Σ a_iψ_i(t)/(w − σ_i²)` with `σ_i² = c² − χ_i`. -/
noncomputable def psiW {ι : Type*} [Fintype ι] (c : ℝ) (a χ : ι → ℝ) (g : ι → ℝ → ℝ) (w : ℂ) (t : ℝ) : ℂ :=
  ∑ i, ((a i * psi c (g i) t : ℝ) : ℂ) / (w - ((c ^ 2 - χ i : ℝ) : ℂ))

/-- `σ² = c² − χ ∈ [0, c²]` lies at distance at most `c²/2` from the centre `c²/2`. -/
theorem norm_sigma_sub_center_le {c χ : ℝ} (hχ0 : 0 ≤ χ) (hχc : χ ≤ c ^ 2) :
    ‖((c ^ 2 - χ : ℝ) : ℂ) - ((c ^ 2 / 2 : ℝ) : ℂ)‖ ≤ c ^ 2 / 2 := by
  rw [← ofReal_sub, norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-- For `c ≠ 0` every `σ² = c² − χ ∈ [0, c²]` lies in the open disc `|w − c²/2| < c²`. -/
theorem sigma_mem_ball {c χ : ℝ} (hc : c ≠ 0) (hχ0 : 0 ≤ χ) (hχc : χ ≤ c ^ 2) :
    ((c ^ 2 - χ : ℝ) : ℂ) ∈ ball ((c ^ 2 / 2 : ℝ) : ℂ) (c ^ 2) := by
  have hc2 : 0 < c ^ 2 := by positivity
  rw [mem_ball, dist_eq_norm]
  linarith [norm_sigma_sub_center_le hχ0 hχc]

/-- On the circle `|w − c²/2| = c²`, every `σ² = c² − χ ∈ [0, c²]` has `|w − σ²| ≥ c²/2`. -/
theorem half_le_norm_sub_sigma {c χ : ℝ} {w : ℂ} (hw : w ∈ sphere ((c ^ 2 / 2 : ℝ) : ℂ) (c ^ 2))
    (hχ0 : 0 ≤ χ) (hχc : χ ≤ c ^ 2) : c ^ 2 / 2 ≤ ‖w - ((c ^ 2 - χ : ℝ) : ℂ)‖ := by
  rw [mem_sphere, dist_eq_norm] at hw
  have h := norm_sigma_sub_center_le hχ0 hχc
  have htri := norm_sub_le_norm_sub_add_norm_sub w ((c ^ 2 - χ : ℝ) : ℂ) ((c ^ 2 / 2 : ℝ) : ℂ)
  linarith

/-- **The resolvent representation**: for `f` holomorphic on `|w − c²/2| < c²` and continuous on its closure,
`Σ a_iψ_i(t) f(σ_i²) = (2πi)⁻¹ ∮_{|w − c²/2| = c²} Ψ_w(t) f(w) dw`, where `σ_i² = c² − χ_i ∈ [0, c²]`. -/
theorem sum_mul_eq_circleIntegral_psiW {ι : Type*} [Fintype ι] {c : ℝ} (a χ : ι → ℝ) (g : ι → ℝ → ℝ)
    (hc : c ≠ 0) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i ≤ c ^ 2) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (ball ((c ^ 2 / 2 : ℝ) : ℂ) (c ^ 2))) (t : ℝ) :
    ∑ i, ((a i * psi c (g i) t : ℝ) : ℂ) * f ((c ^ 2 - χ i : ℝ) : ℂ)
      = (2 * π * I : ℂ)⁻¹ * ∮ w in C(((c ^ 2 / 2 : ℝ) : ℂ), c ^ 2), psiW c a χ g w t * f w := by
  have h := sum_smul_eq_circleIntegral Finset.univ hf (fun i => ((a i * psi c (g i) t : ℝ) : ℂ))
    (fun i => ((c ^ 2 - χ i : ℝ) : ℂ)) fun i _ => sigma_mem_ball hc (hχ0 i) (hχc i)
  simpa only [smul_eq_mul, psiW] using h

/-- The real combination `Σ r_iψ_i` has square integrable on `Ioi 1`. -/
theorem integrableOn_span_sq {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ}
    (r : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) :
    IntegrableOn (fun t => (∑ i, r i * psi c (g i) t) ^ 2) (Ioi 1) := by
  refine MemLp.integrable_sq ?_
  exact memLp_finsetSum _ fun i _ =>
    (Cvs.Prolate.RungExactOrthogonality.memLp_psi (hg i) (hg₁ i) (hg₂c i) (hang i) hc).const_mul (r i)

/-- `|Ψ_w|²` splits into the squares of two real combinations of rungs, with coefficients
`Re` and `Im` of `a_i/(w − σ_i²)`. -/
theorem norm_psiW_sq {ι : Type*} [Fintype ι] (c : ℝ) (a χ : ι → ℝ) (g : ι → ℝ → ℝ) (w : ℂ) (t : ℝ) :
    ‖psiW c a χ g w t‖ ^ 2
      = (∑ i, ((a i : ℂ) / (w - ((c ^ 2 - χ i : ℝ) : ℂ))).re * psi c (g i) t) ^ 2
        + (∑ i, ((a i : ℂ) / (w - ((c ^ 2 - χ i : ℝ) : ℂ))).im * psi c (g i) t) ^ 2 := by
  have e : psiW c a χ g w t
      = ∑ i, ((a i : ℂ) / (w - ((c ^ 2 - χ i : ℝ) : ℂ))) * (psi c (g i) t : ℂ) := by
    unfold psiW
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  rw [Complex.sq_norm, normSq_apply, e, re_sum, im_sum]
  simp only [re_mul_ofReal, im_mul_ofReal]
  ring

/-- `|Ψ_w|²` is integrable on `Ioi 1`. -/
theorem integrableOn_norm_psiW_sq {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ}
    (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (w : ℂ) :
    IntegrableOn (fun t => ‖psiW c a χ g w t‖ ^ 2) (Ioi 1) := by
  simp_rw [norm_psiW_sq]
  exact (integrableOn_span_sq _ hg hg₁ hg₂c hang hc).add (integrableOn_span_sq _ hg hg₁ hg₂c hang hc)

/-- **The resolvent is bounded on the circle**: for rungs with pairwise distinct `χ_i ∈ [0, c²]` and
`|w − c²/2| = c²`, `∫_{Ioi 1} |Ψ_w|² ≤ (4/c⁴) ∫_{Ioi 1} (Σ a_iψ_i)²`. -/
theorem integral_norm_psiW_sq_le {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ}
    (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i ≤ c ^ 2) (hχi : Function.Injective χ)
    {w : ℂ} (hw : w ∈ sphere ((c ^ 2 / 2 : ℝ) : ℂ) (c ^ 2)) :
    ∫ t in Ioi 1, ‖psiW c a χ g w t‖ ^ 2
      ≤ 4 / c ^ 4 * ∫ t in Ioi 1, (∑ i, a i * psi c (g i) t) ^ 2 := by
  set b : ι → ℂ := fun i => (a i : ℂ) / (w - ((c ^ 2 - χ i : ℝ) : ℂ)) with hb
  simp_rw [norm_psiW_sq]
  rw [integral_add (integrableOn_span_sq _ hg hg₁ hg₂c hang hc) (integrableOn_span_sq _ hg hg₁ hg₂c hang hc)]
  rw [Cvs.Prolate.RungExactOrthogonality.integral_span_sq _ hg hg₁ hg₂c hang hc hχi,
    Cvs.Prolate.RungExactOrthogonality.integral_span_sq _ hg hg₁ hg₂c hang hc hχi,
    Cvs.Prolate.RungExactOrthogonality.integral_span_sq _ hg hg₁ hg₂c hang hc hχi, ← Finset.sum_add_distrib,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hM : 0 ≤ ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2 := setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have hc2 : 0 < c ^ 2 := by positivity
  have hd := half_le_norm_sub_sigma hw (hχ0 i) (hχc i)
  have hd0 : 0 < ‖w - ((c ^ 2 - χ i : ℝ) : ℂ)‖ := by linarith
  have hnb : (b i).re ^ 2 + (b i).im ^ 2 = a i ^ 2 / ‖w - ((c ^ 2 - χ i : ℝ) : ℂ)‖ ^ 2 := by
    have h1 : (b i).re ^ 2 + (b i).im ^ 2 = ‖b i‖ ^ 2 := by rw [Complex.sq_norm, normSq_apply]; ring
    rw [h1, hb]
    simp only [norm_div, norm_real, Real.norm_eq_abs, div_pow, sq_abs]
  have hle : a i ^ 2 / ‖w - ((c ^ 2 - χ i : ℝ) : ℂ)‖ ^ 2 ≤ 4 / c ^ 4 * a i ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have hsq : (c ^ 2 / 2) ^ 2 ≤ ‖w - ((c ^ 2 - χ i : ℝ) : ℂ)‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) hd 2
    have ha := sq_nonneg (a i)
    have : a i ^ 2 = 4 / c ^ 4 * a i ^ 2 * (c ^ 2 / 2) ^ 2 := by field_simp; ring
    calc a i ^ 2 = 4 / c ^ 4 * a i ^ 2 * (c ^ 2 / 2) ^ 2 := this
      _ ≤ 4 / c ^ 4 * a i ^ 2 * ‖w - ((c ^ 2 - χ i : ℝ) : ℂ)‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
  calc (b i).re ^ 2 * (∫ ξ in Ioi 1, psi c (g i) ξ ^ 2) + (b i).im ^ 2 * ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2
      = ((b i).re ^ 2 + (b i).im ^ 2) * ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2 := by ring
    _ ≤ 4 / c ^ 4 * a i ^ 2 * ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2 :=
        mul_le_mul_of_nonneg_right (hnb ▸ hle) hM
    _ = 4 / c ^ 4 * (a i ^ 2 * ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2) := by ring

/-- The same bound on any measurable `S ⊆ Ioi 1`: `∫_S |Ψ_w|² ≤ (4/c⁴) ∫_{Ioi 1} (Σ a_iψ_i)²`. -/
theorem setIntegral_norm_psiW_sq_le {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ}
    (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i ≤ c ^ 2) (hχi : Function.Injective χ)
    {w : ℂ} (hw : w ∈ sphere ((c ^ 2 / 2 : ℝ) : ℂ) (c ^ 2)) {S : Set ℝ} (hS : S ⊆ Ioi 1) :
    ∫ t in S, ‖psiW c a χ g w t‖ ^ 2
      ≤ 4 / c ^ 4 * ∫ t in Ioi 1, (∑ i, a i * psi c (g i) t) ^ 2 := by
  refine le_trans ?_ (integral_norm_psiW_sq_le a hg hg₁ hg₂c hang hc hχ0 hχc hχi hw)
  exact setIntegral_mono_set (integrableOn_norm_psiW_sq a hg hg₁ hg₂c hang hc w)
    (ae_of_all _ fun _ => sq_nonneg _) (ae_of_all _ hS)

/-- `(w, t) ↦ Ψ_w(t)` is continuous on the circle `|w − c²/2| = c²` times `ℝ`, for continuous rungs. -/
theorem continuousOn_psiW {ι : Type*} [Fintype ι] {c : ℝ} (a χ : ι → ℝ) (g : ι → ℝ → ℝ)
    (hψ : ∀ i, Continuous (psi c (g i))) (hc : c ≠ 0) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i ≤ c ^ 2) :
    ContinuousOn (fun p : ℂ × ℝ => psiW c a χ g p.1 p.2) (sphere ((c ^ 2 / 2 : ℝ) : ℂ) (c ^ 2) ×ˢ univ) := by
  have hc2 : 0 < c ^ 2 := by positivity
  unfold psiW
  refine continuousOn_finsetSum _ fun i _ => ?_
  refine ContinuousOn.div₀ ?_ ?_ fun p hp => ?_
  · exact (continuous_ofReal.comp (continuous_const.mul ((hψ i).comp continuous_snd))).continuousOn
  · exact (continuous_fst.sub continuous_const).continuousOn
  · have h := half_le_norm_sub_sigma (mem_prod.1 hp).1 (hχ0 i) (hχc i)
    intro h0
    rw [h0, norm_zero] at h
    linarith

end Cvs.L2a.SpanResolventCircle
