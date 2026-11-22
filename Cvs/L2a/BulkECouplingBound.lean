import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BandRungOutgoingWave
import Cvs.L2a.BulkECouplingRemainder
import Cvs.L2a.FarFarBound
import Cvs.L2a.FarIntegrationByParts
import Cvs.L2a.QIdentityComplexWeight
import Cvs.L2a.SpanResolventCircle
import Cvs.L2a.UnitWeightRemainderSymbol
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The bulk of the E-coupling is `O(F/c)` against the span norm

On a cut `[m, M]` the unit-weight remainder sees the rung only through `σᵢ² = c² − χᵢ`, so
`Σᵢ aᵢψᵢRᵢ = (2πi)⁻¹∮ Ψ_w fR(w)` (Cvs.L2a.SpanResolventCircle, Cvs.L2a.UnitWeightRemainderSymbol). Fubini, Bernstein–Riesz in `s`, Cauchy–Schwarz in `t` with
`∫|Ψ_w|² ≤ 4P/c⁴`, and `Σ_{m ≥ 2} m^{-5/2} ≤ 1/2` give `|bulkE| ≤ (700F/c)√P`, `P = ∫_{(1,∞)} (Σ aᵢψᵢ)²`.
-/

noncomputable section

namespace Cvs.L2a.BulkECouplingBound

open Real Set Filter MeasureTheory intervalIntegral Complex Metric
open Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.L2a.FarIntegrationByParts Cvs.L2a.QIdentityComplexWeight
open Cvs.L2a.SpanResolventCircle Cvs.L2a.UnitWeightRemainderSymbol

/-! ### Clamping and the circle -/

/-- `clampI a b x = max a (min b x)`, the nearest point of `[a, b]` when `a ≤ b`. -/
def clampI (a b x : ℝ) : ℝ := max a (min b x)

theorem continuous_clampI (a b : ℝ) : Continuous (clampI a b) :=
  continuous_const.max (continuous_const.min continuous_id)

theorem clampI_of_mem {a b x : ℝ} (hx : x ∈ Icc a b) : clampI a b x = x := by
  unfold clampI; rw [min_eq_right hx.2, max_eq_right hx.1]

theorem clampI_mem {a b : ℝ} (hab : a ≤ b) (x : ℝ) : clampI a b x ∈ Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

/-- Points of the circle `|w − c²/2| = c²` satisfy `|w − c²/2| ≤ c²`. -/
theorem norm_circleMap_sub_le (c θ : ℝ) :
    ‖circleMap ((c ^ 2 / 2 : ℝ) : ℂ) (c ^ 2) θ - ((c ^ 2 / 2 : ℝ) : ℂ)‖ ≤ c ^ 2 := by
  rw [circleMap_sub_center, norm_circleMap_zero, abs_of_nonneg (sq_nonneg c)]

theorem circleMap_mem (c θ : ℝ) :
    circleMap ((c ^ 2 / 2 : ℝ) : ℂ) (c ^ 2) θ ∈ sphere ((c ^ 2 / 2 : ℝ) : ℂ) (c ^ 2) :=
  circleMap_mem_sphere _ (sq_nonneg c) θ

/-- `σ² = c² − χ` with `χ ∈ [0, c²]` satisfies `|σ² − c²/2| ≤ c²`. -/
theorem norm_sigma_sub_le {c χ : ℝ} (hχ0 : 0 ≤ χ) (hχc : χ ≤ c ^ 2) :
    ‖((c ^ 2 - χ : ℝ) : ℂ) - ((c ^ 2 / 2 : ℝ) : ℂ)‖ ≤ c ^ 2 := by
  have := norm_sigma_sub_center_le hχ0 hχc
  nlinarith [sq_nonneg c]

/-! ### The clamped kernels -/

/-- The symbol at clamped arguments, `fR(w, clamp_{[−1,1]}(s)/m, clamp_{[m,M]}(t))`. -/
def fRb (c m M : ℝ) (w : ℂ) (s t : ℝ) : ℂ := fR c w ((clampI (-1) 1 s / m : ℝ) : ℂ) (clampI m M t)

theorem continuous_fRb {X : Type*} [TopologicalSpace X] {c m M : ℝ} (hc : 80 ≤ c) (hm : 2 ≤ m)
    (hmM : m ≤ M) {W : X → ℂ} {S T : X → ℝ} (hW : Continuous W)
    (hWb : ∀ x, ‖W x - ((c ^ 2 / 2 : ℝ) : ℂ)‖ ≤ c ^ 2) (hS : Continuous S) (hT : Continuous T) :
    Continuous fun x => fRb c m M (W x) (S x) (T x) := by
  have hm0 : 0 < m := by linarith
  have hf : Continuous fun x => (W x, ((clampI (-1) 1 (S x) / m : ℝ) : ℂ), clampI m M (T x)) :=
    hW.prodMk ((continuous_ofReal.comp (((continuous_clampI _ _).comp hS).div_const m)).prodMk
      ((continuous_clampI _ _).comp hT))
  have hmem : ∀ x, (W x, ((clampI (-1) 1 (S x) / m : ℝ) : ℂ), clampI m M (T x))
      ∈ {p : ℂ × ℂ × ℝ | ‖p.1 - ((c ^ 2 / 2 : ℝ) : ℂ)‖ ≤ c ^ 2 ∧ ‖p.2.1‖ ≤ 3 / 4 ∧ 2 ≤ p.2.2} := by
    intro x
    refine ⟨hWb x, ?_, hm.trans (clampI_mem hmM (T x)).1⟩
    have h := clampI_mem (by norm_num : (-1 : ℝ) ≤ 1) (S x)
    have h1 : |clampI (-1) 1 (S x)| ≤ 1 := abs_le.2 h
    show ‖((clampI (-1) 1 (S x) / m : ℝ) : ℂ)‖ ≤ 3 / 4
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hm0, div_le_iff₀ hm0]
    linarith
  have key := (continuousOn_fR hc).comp_continuous hf hmem
  unfold fRb
  exact key

/-- The `s`-kernel `g_j(s) e^{ic(s/m)t} fR(w, s/m, t)`, with `g_j` and the symbol read at clamped arguments. -/
def kerS (c m M : ℝ) (gj : ℝ → ℝ) (w : ℂ) (s t : ℝ) : ℂ :=
  (gj (clampI (-1) 1 s) : ℂ) * eF c (s / m) t * fRb c m M w s t

theorem continuous_gj_clamp {gj : ℝ → ℝ} (hgj : ContinuousOn gj (Icc (-1) 1)) :
    Continuous fun s => gj (clampI (-1) 1 s) :=
  hgj.comp_continuous (continuous_clampI _ _) (clampI_mem (by norm_num))

theorem continuous_kerS {X : Type*} [TopologicalSpace X] {c m M : ℝ} {gj : ℝ → ℝ} (hc : 80 ≤ c)
    (hm : 2 ≤ m) (hmM : m ≤ M) (hgj : ContinuousOn gj (Icc (-1) 1)) {W : X → ℂ} {S T : X → ℝ}
    (hW : Continuous W) (hWb : ∀ x, ‖W x - ((c ^ 2 / 2 : ℝ) : ℂ)‖ ≤ c ^ 2) (hS : Continuous S)
    (hT : Continuous T) :
    Continuous fun x => kerS c m M gj (W x) (S x) (T x) := by
  have h1 : Continuous fun x => (gj (clampI (-1) 1 (S x)) : ℂ) :=
    continuous_ofReal.comp ((continuous_gj_clamp hgj).comp hS)
  have h2 : Continuous fun x => eF c (S x / m) (T x) := by unfold eF; fun_prop
  have key := (h1.mul h2).mul (continuous_fRb hc hm hmM hW hWb hS hT)
  unfold kerS
  exact key

section kernel
variable {ι : Type} [Fintype ι]

/-- The cut kernel `w′(θ) Ψ_{w(θ)}(t) kerS(w(θ), s, t)` on the circle `w(θ)` of radius `c²` about `c²/2`. -/
def kerB (c m M : ℝ) (gj : ℝ → ℝ) (a χ : ι → ℝ) (g : ι → ℝ → ℝ) (s t θ : ℝ) : ℂ :=
  circleMap 0 (c ^ 2) θ * I * psiW c a χ g (circleMap ((c ^ 2 / 2 : ℝ) : ℂ) (c ^ 2) θ) t
    * kerS c m M gj (circleMap ((c ^ 2 / 2 : ℝ) : ℂ) (c ^ 2) θ) s t

/-- One rung's clamped integrand `g_j(s) e^{ic(s/m)t} ψᵢ(t) fR(σᵢ², s/m, t)`. -/
def kerY (c m M : ℝ) (gj : ℝ → ℝ) (χ : ι → ℝ) (g : ι → ℝ → ℝ) (i : ι) (s t : ℝ) : ℂ :=
  (gj (clampI (-1) 1 s) : ℂ) * (eF c (s / m) t * (psi c (g i) t : ℂ) * fRb c m M ((c ^ 2 - χ i : ℝ) : ℂ) s t)

theorem continuous_psiW_circle {c : ℝ} {a χ : ι → ℝ} {g : ι → ℝ → ℝ} (hψ : ∀ i, Continuous (psi c (g i)))
    (hc : c ≠ 0) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i ≤ c ^ 2) :
    Continuous fun p : ℝ × ℝ => psiW c a χ g (circleMap ((c ^ 2 / 2 : ℝ) : ℂ) (c ^ 2) p.1) p.2 := by
  have key := (continuousOn_psiW a χ g hψ hc hχ0 hχc).comp_continuous
    (((continuous_circleMap _ _).comp continuous_fst).prodMk continuous_snd)
    fun p => ⟨circleMap_mem c p.1, mem_univ _⟩
  simpa only [Function.comp_def] using key

theorem continuous_kerB {c m M : ℝ} {gj : ℝ → ℝ} {a χ : ι → ℝ} {g : ι → ℝ → ℝ} (hc : 80 ≤ c) (hm : 2 ≤ m)
    (hmM : m ≤ M) (hgj : ContinuousOn gj (Icc (-1) 1)) (hψ : ∀ i, Continuous (psi c (g i)))
    (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i ≤ c ^ 2) :
    Continuous fun p : ℝ × ℝ × ℝ => kerB c m M gj a χ g p.1 p.2.1 p.2.2 := by
  have hc0 : c ≠ 0 := by linarith
  have hθ : Continuous fun p : ℝ × ℝ × ℝ => p.2.2 := continuous_snd.comp continuous_snd
  have ht : Continuous fun p : ℝ × ℝ × ℝ => p.2.1 := continuous_fst.comp continuous_snd
  have hcm : ∀ z : ℂ, Continuous fun p : ℝ × ℝ × ℝ => circleMap z (c ^ 2) p.2.2 := fun z => by
    have key := (continuous_circleMap z (c ^ 2)).comp hθ
    simpa only [Function.comp_def] using key
  have h1 : Continuous fun p : ℝ × ℝ × ℝ => circleMap 0 (c ^ 2) p.2.2 * I := (hcm 0).mul continuous_const
  have h2 : Continuous fun p : ℝ × ℝ × ℝ =>
      psiW c a χ g (circleMap ((c ^ 2 / 2 : ℝ) : ℂ) (c ^ 2) p.2.2) p.2.1 := by
    have key := (continuous_psiW_circle (a := a) hψ hc0 hχ0 hχc).comp
      (hθ.prodMk ht : Continuous fun p : ℝ × ℝ × ℝ => (p.2.2, p.2.1))
    simpa only [Function.comp_def] using key
  have h3 : Continuous fun p : ℝ × ℝ × ℝ =>
      kerS c m M gj (circleMap ((c ^ 2 / 2 : ℝ) : ℂ) (c ^ 2) p.2.2) p.1 p.2.1 :=
    continuous_kerS hc hm hmM hgj (hcm _) (fun p => norm_circleMap_sub_le c _) continuous_fst ht
  have key := (h1.mul h2).mul h3
  unfold kerB
  exact key

omit [Fintype ι] in
theorem continuous_kerY {c m M : ℝ} {gj : ℝ → ℝ} {χ : ι → ℝ} {g : ι → ℝ → ℝ} (hc : 80 ≤ c) (hm : 2 ≤ m)
    (hmM : m ≤ M) (hgj : ContinuousOn gj (Icc (-1) 1)) (hψ : ∀ i, Continuous (psi c (g i)))
    (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i ≤ c ^ 2) (i : ι) :
    Continuous fun p : ℝ × ℝ => kerY c m M gj χ g i p.1 p.2 := by
  have h1 : Continuous fun p : ℝ × ℝ => (gj (clampI (-1) 1 p.1) : ℂ) :=
    continuous_ofReal.comp ((continuous_gj_clamp hgj).comp continuous_fst)
  have h2 : Continuous fun p : ℝ × ℝ => eF c (p.1 / m) p.2 := by unfold eF; fun_prop
  have h3 : Continuous fun p : ℝ × ℝ => (psi c (g i) p.2 : ℂ) := continuous_ofReal.comp ((hψ i).comp continuous_snd)
  have h4 : Continuous fun p : ℝ × ℝ => fRb c m M ((c ^ 2 - χ i : ℝ) : ℂ) p.1 p.2 :=
    continuous_fRb hc hm hmM continuous_const (fun _ => norm_sigma_sub_le (hχ0 i) (hχc i)) continuous_fst
      continuous_snd
  have key := h1.mul ((h2.mul h3).mul h4)
  unfold kerY
  exact key

end kernel

/-! ### Fubini on a box -/

/-- **Fubini on a box** for a continuous integrand: `∫_s ∫_t ∫_θ Φ = ∫_θ ∫_t ∫_s Φ`. -/
theorem integral_swap3 {Φ : ℝ → ℝ → ℝ → ℂ} (hΦ : Continuous fun p : ℝ × ℝ × ℝ => Φ p.1 p.2.1 p.2.2)
    {a b α β u v : ℝ} (hab : a ≤ b) (hαβ : α ≤ β) (huv : u ≤ v) :
    ∫ s in a..b, ∫ t in α..β, ∫ θ in u..v, Φ s t θ = ∫ θ in u..v, ∫ t in α..β, ∫ s in a..b, Φ s t θ := by
  have h1 : Continuous fun q : ℝ × ℝ => ∫ θ in u..v, Φ q.1 q.2 θ := by
    have hu : Continuous (Function.uncurry fun (q : ℝ × ℝ) (θ : ℝ) => Φ q.1 q.2 θ) :=
      hΦ.comp (by fun_prop : Continuous fun r : (ℝ × ℝ) × ℝ => (r.1.1, r.1.2, r.2))
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hu u v
  rw [Cvs.L2a.BulkECouplingRemainder.integral_swap_rect (f := fun s t => ∫ θ in u..v, Φ s t θ) hab hαβ h1.continuousOn]
  have h2 : ∀ t, ∫ s in a..b, ∫ θ in u..v, Φ s t θ = ∫ θ in u..v, ∫ s in a..b, Φ s t θ := fun t =>
    Cvs.L2a.BulkECouplingRemainder.integral_swap_rect (f := fun s θ => Φ s t θ) hab huv
      (hΦ.comp (by fun_prop : Continuous fun r : ℝ × ℝ => (r.1, t, r.2))).continuousOn
  simp_rw [h2]
  have h3 : Continuous fun q : ℝ × ℝ => ∫ s in a..b, Φ s q.1 q.2 := by
    have hu : Continuous (Function.uncurry fun (q : ℝ × ℝ) (s : ℝ) => Φ s q.1 q.2) :=
      hΦ.comp (by fun_prop : Continuous fun r : (ℝ × ℝ) × ℝ => (r.2, r.1.1, r.1.2))
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hu a b
  exact Cvs.L2a.BulkECouplingRemainder.integral_swap_rect (f := fun t θ => ∫ s in a..b, Φ s t θ) hαβ huv h3.continuousOn

/-! ### The bounds in `s` and in `t` -/

/-- **Bernstein–Riesz in `s`** on the box: `|∫ kerS(w, s, t) ds| ≤ 3F(200/c + 2600/c²)/(m|t|)`. -/
theorem norm_integral_kerS_le {c m M F t : ℝ} {gj : ℝ → ℝ} {w : ℂ} (hgj : ContinuousOn gj (Icc (-1) 1))
    (hevenj : ∀ s ∈ Icc (-1 : ℝ) 1, gj (-s) = gj s) (hpsi : ∀ x, |psi c gj x| ≤ F) (hc : 80 ≤ c)
    (hm : 2 ≤ m) (ht : t ∈ Icc m M) (hw : ‖w - ((c ^ 2 / 2 : ℝ) : ℂ)‖ ≤ c ^ 2) :
    ‖∫ s in (-1 : ℝ)..1, kerS c m M gj w s t‖ ≤ 3 * F * (200 / c + 2600 / c ^ 2) / m * |t|⁻¹ := by
  have hF : 0 ≤ F := (abs_nonneg _).trans (hpsi 0)
  have hc0 : 0 < c := by linarith
  have hm0 : 0 < m := by linarith
  have ht0 : 0 < t := by linarith [ht.1]
  have e : ∫ s in (-1 : ℝ)..1, kerS c m M gj w s t
      = ∫ s in (-1 : ℝ)..1, (gj s : ℂ) * eF c (s / m) t * fR c w ((s / m : ℝ) : ℂ) t := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le (by norm_num)] at hs
    simp only [kerS, fRb, clampI_of_mem hs, clampI_of_mem ht]
  rw [e]
  refine (norm_integral_fR_le hgj hevenj hpsi hc hm ht.1 hw).trans ?_
  rw [abs_of_pos ht0]
  have hmt : m * t ≤ t ^ 2 := by nlinarith [ht.1]
  have h1 : 2600 / (c ^ 2 * t ^ 2) ≤ 2600 / (c ^ 2 * (m * t)) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (mul_le_mul_of_nonneg_left hmt (sq_nonneg c))
  have h2 : 3 * F * (200 / c + 2600 / c ^ 2) / m * t⁻¹
      = 3 * F * (200 / (c * m * t) + 2600 / (c ^ 2 * (m * t))) := by
    field_simp
  rw [h2]
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- `∫_{(m, M]} t⁻² ≤ 1/m`. -/
theorem setIntegral_inv_sq_le {m M : ℝ} (hm : 0 < m) (hmM : m ≤ M) :
    ∫ t in Ioc m M, (|t|⁻¹) ^ 2 ≤ 1 / m := by
  rw [← intervalIntegral.integral_of_le hmM]
  have e : ∫ t in m..M, (|t|⁻¹) ^ 2 = ∫ t in m..M, (t ^ 2)⁻¹ := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hmM] at ht
    simp only [abs_of_pos (by linarith [ht.1] : 0 < t), inv_pow]
  have hderiv : ∀ t ∈ uIcc m M, HasDerivAt (fun y : ℝ => -y⁻¹) ((t ^ 2)⁻¹) t := by
    intro t ht
    rw [uIcc_of_le hmM] at ht
    have h := (hasDerivAt_inv (by linarith [ht.1] : t ≠ 0)).neg
    rw [neg_neg] at h
    exact h
  have hint : IntervalIntegrable (fun t : ℝ => (t ^ 2)⁻¹) volume m M := by
    refine ContinuousOn.intervalIntegrable ?_
    refine (continuousOn_pow 2).inv₀ fun t ht => ?_
    rw [uIcc_of_le hmM] at ht
    exact pow_ne_zero 2 (by linarith [ht.1])
  rw [e, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hM : 0 < M := by linarith
  have := inv_nonneg.2 hM.le
  rw [one_div]
  linarith

section bound
variable {ι : Type} [Fintype ι]

/-- **Cauchy–Schwarz in `t` on the circle**: for every `θ`,
`|∫_m^M ∫_{−1}^1 kerB(s, t, θ) ds dt| ≤ 6F(200/c + 2600/c²)√P m^{-3/2}`. -/
theorem norm_integral_kerB_le {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) {gj : ℝ → ℝ}
    {F m M : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i ≤ c ^ 2) (hχi : Function.Injective χ)
    (hgj : ContinuousOn gj (Icc (-1) 1)) (hevenj : ∀ s ∈ Icc (-1 : ℝ) 1, gj (-s) = gj s)
    (hpsi : ∀ x, |psi c gj x| ≤ F) (hm : 2 ≤ m) (hmM : m ≤ M) (θ : ℝ) :
    ‖∫ t in m..M, ∫ s in (-1 : ℝ)..1, kerB c m M gj a χ g s t θ‖
      ≤ 6 * F * (200 / c + 2600 / c ^ 2) * √(∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2) / m * √(1 / m) := by
  set K := 200 / c + 2600 / c ^ 2 with hK
  set P := ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 with hP
  set w := circleMap ((c ^ 2 / 2 : ℝ) : ℂ) (c ^ 2) θ with hw
  have hF : 0 ≤ F := (abs_nonneg _).trans (hpsi 0)
  have hc0 : 0 < c := by linarith
  have hm0 : 0 < m := by linarith
  have hK0 : 0 ≤ K := by positivity
  have hψ : ∀ i, Continuous (psi c (g i)) := fun i => (rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)).2.2.1
  have hpsiWc : Continuous fun t => psiW c a χ g w t := by
    have key := (continuous_psiW_circle (a := a) hψ hc0.ne' hχ0 hχc).comp (continuous_const.prodMk continuous_id
      : Continuous fun t : ℝ => (θ, t))
    simpa only [Function.comp_def] using key
  have hA : ∀ t, ∫ s in (-1 : ℝ)..1, kerB c m M gj a χ g s t θ
      = (circleMap 0 (c ^ 2) θ * I * psiW c a χ g w t) * ∫ s in (-1 : ℝ)..1, kerS c m M gj w s t := fun t => by
    unfold kerB
    exact intervalIntegral.integral_const_mul _ _
  simp_rw [hA]
  have hkS : Continuous fun t => ∫ s in (-1 : ℝ)..1, kerS c m M gj w s t := by
    have hu : Continuous (Function.uncurry fun (t s : ℝ) => kerS c m M gj w s t) := by
      have key := continuous_kerS (gj := gj) hc hm hmM hgj (continuous_const (y := w))
        (fun _ => norm_circleMap_sub_le c θ) continuous_snd continuous_fst
      simpa only [Function.uncurry_def] using key
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hu (-1) 1
  have hle : ∀ t ∈ Icc m M, ‖(circleMap 0 (c ^ 2) θ * I * psiW c a χ g w t)
      * ∫ s in (-1 : ℝ)..1, kerS c m M gj w s t‖
        ≤ c ^ 2 * (3 * F * K / m) * (|t|⁻¹ * ‖psiW c a χ g w t‖) := by
    intro t ht
    rw [norm_mul, norm_mul, norm_mul, norm_circleMap_zero, Complex.norm_I, abs_of_nonneg (sq_nonneg c), mul_one]
    have h := norm_integral_kerS_le hgj hevenj hpsi hc hm ht (norm_circleMap_sub_le c θ)
    calc c ^ 2 * ‖psiW c a χ g w t‖ * ‖∫ s in (-1 : ℝ)..1, kerS c m M gj w s t‖
        ≤ c ^ 2 * ‖psiW c a χ g w t‖ * (3 * F * K / m * |t|⁻¹) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = c ^ 2 * (3 * F * K / m) * (|t|⁻¹ * ‖psiW c a χ g w t‖) := by ring
  have hint1 : IntervalIntegrable (fun t => ‖(circleMap 0 (c ^ 2) θ * I * psiW c a χ g w t)
      * ∫ s in (-1 : ℝ)..1, kerS c m M gj w s t‖) volume m M :=
    ((continuous_const.mul hpsiWc).mul hkS).norm.intervalIntegrable _ _
  have hinvc : ContinuousOn (fun t : ℝ => |t|⁻¹) (Icc m M) :=
    continuous_abs.continuousOn.inv₀ fun t ht => (abs_pos.2 (by linarith [ht.1] : t ≠ 0)).ne'
  have hint2 : IntervalIntegrable (fun t => c ^ 2 * (3 * F * K / m) * (|t|⁻¹ * ‖psiW c a χ g w t‖)) volume m M :=
    ContinuousOn.intervalIntegrable_of_Icc hmM (continuousOn_const.mul (hinvc.mul hpsiWc.norm.continuousOn))
  have hS : Ioc m M ⊆ Ioi 1 := fun x hx => lt_trans (by linarith : (1:ℝ) < m) hx.1
  have hfL : MemLp (fun t : ℝ => |t|⁻¹) 2 (volume.restrict (Ioc m M)) := by
    refine MemLp.of_bound ((hinvc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc) m⁻¹ ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun x hx => ?_)
    rw [Real.norm_eq_abs, abs_inv, abs_abs, abs_of_pos (by linarith [hx.1] : 0 < x)]
    exact inv_anti₀ hm0 hx.1.le
  have huL : MemLp (fun t => ‖psiW c a χ g w t‖) 2 (volume.restrict (Ioc m M)) :=
    (memLp_two_iff_integrable_sq hpsiWc.norm.aestronglyMeasurable).2
      ((integrableOn_norm_psiW_sq a hg hg₁ hg₂c hang hc0 w).mono_set hS)
  have hcs := Cvs.L2a.FarFarBound.integral_mul_abs_le (fun x => inv_nonneg.2 (abs_nonneg x)) hfL huL
  have hsq1 := setIntegral_inv_sq_le hm0 hmM
  have hsq2 := setIntegral_norm_psiW_sq_le a hg hg₁ hg₂c hang hc0 hχ0 hχc hχi (circleMap_mem c θ) hS
  have hP0 : 0 ≤ P := setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have hsqrt : √(4 / c ^ 4 * P) = 2 / c ^ 2 * √P := by
    rw [Real.sqrt_mul (by positivity), show (4 : ℝ) / c ^ 4 = (2 / c ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  calc ‖∫ t in m..M, (circleMap 0 (c ^ 2) θ * I * psiW c a χ g w t) * ∫ s in (-1 : ℝ)..1, kerS c m M gj w s t‖
      ≤ ∫ t in m..M, ‖(circleMap 0 (c ^ 2) θ * I * psiW c a χ g w t)
          * ∫ s in (-1 : ℝ)..1, kerS c m M gj w s t‖ := intervalIntegral.norm_integral_le_integral_norm hmM
    _ ≤ ∫ t in m..M, c ^ 2 * (3 * F * K / m) * (|t|⁻¹ * ‖psiW c a χ g w t‖) :=
        intervalIntegral.integral_mono_on hmM hint1 hint2 hle
    _ = c ^ 2 * (3 * F * K / m) * ∫ t in Ioc m M, |t|⁻¹ * |‖psiW c a χ g w t‖| := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hmM]
        simp only [abs_norm]
    _ ≤ c ^ 2 * (3 * F * K / m) * (√(∫ t in Ioc m M, (|t|⁻¹) ^ 2) * √(∫ t in Ioc m M, ‖psiW c a χ g w t‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
    _ ≤ c ^ 2 * (3 * F * K / m) * (√(1 / m) * √(4 / c ^ 4 * P)) := by
        gcongr
    _ = 6 * F * K * √P / m * √(1 / m) := by
        rw [hsqrt]
        field_simp
        ring

end bound

/-! ### The cut as a circle integral -/

section cut
variable {ι : Type} [Fintype ι]

/-- The cut term `Σᵢ aᵢ (1/m) ∫ g_j(s) ∫_m^M e^{ic(s/m)t} ψᵢ(t) R(c, χᵢ, s/m, t) dt ds` of `BulkECouplingRemainder`'s `bulkR`. -/
def vCut (c : ℝ) (gj : ℝ → ℝ) (a χ : ι → ℝ) (g : ι → ℝ → ℝ) (m M : ℝ) : ℂ :=
  ∑ i, (a i : ℂ) * ((1 / m : ℝ) : ℂ) * ∫ s in (-1 : ℝ)..1, (gj s : ℂ)
    * ∫ t in m..M, eF c (s / m) t * (psi c (g i) t : ℂ)
      * rRc (fun _ => 1) (fun _ => 0) (fun _ => 0) c (χ i) (s / m) t

theorem bulkR_eq (c : ℝ) (gj : ℝ → ℝ) (a χ : ι → ℝ) (g : ι → ℝ → ℝ) (M : ℕ) :
    Cvs.L2a.BulkECouplingRemainder.bulkR c gj a χ g M = (∑ m ∈ Finset.Ico 2 M, vCut c gj a χ g m M).re := rfl

/-- **The cut as a circle integral**:
`vCut = (1/m)(2πi)⁻¹ ∫_0^{2π} ∫_m^M ∫_{−1}^1 kerB(s, t, θ) ds dt dθ`. -/
theorem vCut_eq {c m M : ℝ} {gj : ℝ → ℝ} {a χ : ι → ℝ} {g : ι → ℝ → ℝ}
    (hψ : ∀ i, Continuous (psi c (g i))) (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i ≤ c ^ 2)
    (hgj : ContinuousOn gj (Icc (-1) 1)) (hm : 2 ≤ m) (hmM : m ≤ M) :
    vCut c gj a χ g m M = ((1 / m : ℝ) : ℂ) * ((2 * π * I)⁻¹
      * ∫ θ in (0 : ℝ)..2 * π, ∫ t in m..M, ∫ s in (-1 : ℝ)..1, kerB c m M gj a χ g s t θ) := by
  have hc0 : 0 < c := by linarith
  have hm0 : 0 < m := by linarith
  have h11 : (-1 : ℝ) ≤ 1 := by norm_num
  have hY := fun i => continuous_kerY (gj := gj) (χ := χ) (g := g) hc hm hmM hgj hψ hχ0 hχc i
  -- (a) the clamped form, rung by rung
  have ha : ∀ i, ∫ s in (-1 : ℝ)..1, (gj s : ℂ) * ∫ t in m..M, eF c (s / m) t * (psi c (g i) t : ℂ)
      * rRc (fun _ => 1) (fun _ => 0) (fun _ => 0) c (χ i) (s / m) t
        = ∫ s in (-1 : ℝ)..1, ∫ t in m..M, kerY c m M gj χ g i s t := by
    intro i
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le h11] at hs
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hmM] at ht
    rw [rRc_one_eq]
    simp only [kerY, fRb, clampI_of_mem hs, clampI_of_mem ht]
  -- (b) the rung sum inside
  have hb : ∑ i, (a i : ℂ) * ∫ s in (-1 : ℝ)..1, ∫ t in m..M, kerY c m M gj χ g i s t
      = ∫ s in (-1 : ℝ)..1, ∫ t in m..M, ∑ i, (a i : ℂ) * kerY c m M gj χ g i s t := by
    have hYt : ∀ i s, Continuous fun t => (a i : ℂ) * kerY c m M gj χ g i s t := fun i s => by
      have hk : Continuous fun t => kerY c m M gj χ g i s t := by
        have key := (hY i).comp (continuous_const.prodMk continuous_id : Continuous fun t : ℝ => (s, t))
        simpa only [Function.comp_def] using key
      exact Continuous.mul (f := fun _ => (a i : ℂ)) (g := fun t => kerY c m M gj χ g i s t)
        continuous_const hk
    have hYs : ∀ i, Continuous fun s => ∫ t in m..M, (a i : ℂ) * kerY c m M gj χ g i s t := fun i => by
      have key : Continuous fun p : ℝ × ℝ => (a i : ℂ) * kerY c m M gj χ g i p.1 p.2 :=
        Continuous.mul (f := fun _ => (a i : ℂ))
          (g := fun p : ℝ × ℝ => kerY c m M gj χ g i p.1 p.2) continuous_const (hY i)
      have hu : Continuous (Function.uncurry fun (s t : ℝ) => (a i : ℂ) * kerY c m M gj χ g i s t) := by
        rw [Function.uncurry_def]; exact key
      exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hu m M
    have h1 : ∀ s, ∫ t in m..M, ∑ i, (a i : ℂ) * kerY c m M gj χ g i s t
        = ∑ i, ∫ t in m..M, (a i : ℂ) * kerY c m M gj χ g i s t := fun s =>
      intervalIntegral.integral_finsetSum fun i _ => (hYt i s).intervalIntegrable _ _
    simp_rw [h1]
    rw [intervalIntegral.integral_finsetSum fun i _ => (hYs i).intervalIntegrable _ _]
    simp_rw [intervalIntegral.integral_const_mul]
  -- (c) the resolvent, pointwise on the box
  have hc' : ∀ s ∈ Icc (-1 : ℝ) 1, ∀ t ∈ Icc m M, ∑ i, (a i : ℂ) * kerY c m M gj χ g i s t
      = (2 * π * I)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, kerB c m M gj a χ g s t θ := by
    intro s hs t ht
    have hy : ‖((s / m : ℝ) : ℂ)‖ ≤ 3 / 4 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hm0, div_le_iff₀ hm0]
      have : |s| ≤ 1 := abs_le.2 hs
      linarith
    have hcirc := sum_mul_eq_circleIntegral_psiW a χ g hc0.ne' hχ0 hχc
      (f := fun w => fR c w ((s / m : ℝ) : ℂ) t) (diffContOnCl_fR_w hc (by linarith [ht.1]) hy) t
    have hL : ∑ i, (a i : ℂ) * kerY c m M gj χ g i s t
        = ((gj s : ℂ) * eF c (s / m) t)
          * ∑ i, ((a i * psi c (g i) t : ℝ) : ℂ) * fR c ((c ^ 2 - χ i : ℝ) : ℂ) ((s / m : ℝ) : ℂ) t := by
      simp only [kerY, fRb, clampI_of_mem hs, clampI_of_mem ht]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast
      ring
    have hR : ∫ θ in (0 : ℝ)..2 * π, kerB c m M gj a χ g s t θ
        = ((gj s : ℂ) * eF c (s / m) t)
          * ∮ w in C(((c ^ 2 / 2 : ℝ) : ℂ), c ^ 2), psiW c a χ g w t * fR c w ((s / m : ℝ) : ℂ) t := by
      unfold circleIntegral
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun θ _ => ?_
      simp only [kerB, kerS, fRb, clampI_of_mem hs, clampI_of_mem ht, deriv_circleMap, smul_eq_mul]
      ring
    rw [hL, hcirc, hR]
    ring
  -- (d) pull the constant out and (e) swap
  have hd : ∫ s in (-1 : ℝ)..1, ∫ t in m..M, ∑ i, (a i : ℂ) * kerY c m M gj χ g i s t
      = (2 * π * I)⁻¹ * ∫ s in (-1 : ℝ)..1, ∫ t in m..M, ∫ θ in (0 : ℝ)..2 * π, kerB c m M gj a χ g s t θ := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le h11] at hs
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hmM] at ht
    exact hc' s hs t ht
  have he := integral_swap3 (continuous_kerB (a := a) hc hm hmM hgj hψ hχ0 hχc) h11 hmM
    (by positivity : (0 : ℝ) ≤ 2 * π)
  unfold vCut
  simp_rw [ha]
  have hsum : ∑ i, (a i : ℂ) * ((1 / m : ℝ) : ℂ) * ∫ s in (-1 : ℝ)..1, ∫ t in m..M, kerY c m M gj χ g i s t
      = ((1 / m : ℝ) : ℂ) * ∑ i, (a i : ℂ) * ∫ s in (-1 : ℝ)..1, ∫ t in m..M, kerY c m M gj χ g i s t := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum, hb, hd, he]

end cut

/-! ### The bulk bound -/

/-- `m^{-2}√(1/m) ≤ (1/2)(1/(m − 1) − 1/m)` for `m ≥ 2`. -/
theorem term_le {m : ℝ} (hm : 2 ≤ m) : 1 / m ^ 2 * √(1 / m) ≤ 1 / 2 * (1 / (m - 1) - 1 / m) := by
  have hm0 : 0 < m := by linarith
  have hm1 : 0 < m - 1 := by linarith
  have hs : √(1 / m) ≤ m / (2 * (m - 1)) := by
    rw [show m / (2 * (m - 1)) = √((m / (2 * (m - 1))) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    refine Real.sqrt_le_sqrt ?_
    rw [div_pow, div_le_div_iff₀ hm0 (by positivity)]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ m - 2) (by nlinarith : (0 : ℝ) ≤ m ^ 2 - 2 * m + 4)]
  calc 1 / m ^ 2 * √(1 / m) ≤ 1 / m ^ 2 * (m / (2 * (m - 1))) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = 1 / 2 * (1 / (m - 1) - 1 / m) := by field_simp; ring

/-- Telescoping: `Σ_{2 ≤ m < M} (1/(m − 1) − 1/m) = 1 − 1/(M − 1)` for `M ≥ 2`. -/
theorem sum_telescope {M : ℕ} (hM : 2 ≤ M) :
    ∑ m ∈ Finset.Ico 2 M, (1 / ((m : ℝ) - 1) - 1 / (m : ℝ)) = 1 - 1 / ((M : ℝ) - 1) := by
  induction M, hM using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn, ih]
    push_cast
    rw [add_sub_cancel_right]
    ring

/-- `Σ_{2 ≤ m < M} m^{-2}√(1/m) ≤ 1/2`. -/
theorem sum_le_half (M : ℕ) : ∑ m ∈ Finset.Ico 2 M, 1 / (m : ℝ) ^ 2 * √(1 / (m : ℝ)) ≤ 1 / 2 := by
  rcases le_or_gt M 2 with hM | hM
  · rw [Finset.Ico_eq_empty_of_le hM, Finset.sum_empty]; norm_num
  · calc ∑ m ∈ Finset.Ico 2 M, 1 / (m : ℝ) ^ 2 * √(1 / (m : ℝ))
        ≤ ∑ m ∈ Finset.Ico 2 M, 1 / 2 * (1 / ((m : ℝ) - 1) - 1 / (m : ℝ)) :=
          Finset.sum_le_sum fun m hm => term_le (by exact_mod_cast (Finset.mem_Ico.1 hm).1)
      _ = 1 / 2 * (1 - 1 / ((M : ℝ) - 1)) := by rw [← Finset.mul_sum, sum_telescope hM.le]
      _ ≤ 1 / 2 := by
          have : (1 : ℝ) < M - 1 := by
            have : (2 : ℝ) < M := by exact_mod_cast hM
            linarith
          have : 0 ≤ 1 / ((M : ℝ) - 1) := by positivity
          linarith

section main
variable {ι : Type} [Fintype ι]

/-- **The bulk of the E-coupling**: for the angular span with distinct `χᵢ ∈ [0, c²)`, `c ≥ 80`, `M ≥ 3`, and
`g_j` continuous and even with `|ψ_j| ≤ F`, `|bulkE| ≤ (700F/c)√(∫_{(1,∞)} (Σ aᵢψᵢ)²)`. -/
theorem bulkE_le {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) {gj : ℝ → ℝ} {F : ℝ} {M : ℕ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχi : Function.Injective χ)
    (hgj : ContinuousOn gj (Icc (-1) 1)) (hevenj : ∀ s ∈ Icc (-1 : ℝ) 1, gj (-s) = gj s)
    (hpsi : ∀ t, |psi c gj t| ≤ F) (hM : 3 ≤ M) :
    |Cvs.L2a.BandRungOutgoingWave.bulkE c gj a χ g M| ≤ 700 * F / c * √(∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2) := by
  set P := ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 with hP
  have hc0 : 0 < c := by linarith
  have hF : 0 ≤ F := (abs_nonneg _).trans (hpsi 0)
  have hχc' : ∀ i, χ i ≤ c ^ 2 := fun i => (hχc i).le
  have hψ : ∀ i, Continuous (psi c (g i)) := fun i => (rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)).2.2.1
  set B := 6 * F * (200 / c + 2600 / c ^ 2) * √P with hB
  have hB0 : 0 ≤ B := by positivity
  have hcut : ∀ m ∈ Finset.Ico 2 M, ‖vCut c gj a χ g (m : ℝ) (M : ℝ)‖ ≤ B * (1 / (m : ℝ) ^ 2 * √(1 / (m : ℝ))) := by
    intro m hm
    have hm' := Finset.mem_Ico.1 hm
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm'.1
    have hmM : (m : ℝ) ≤ M := by exact_mod_cast hm'.2.le
    have hm0 : (0 : ℝ) < m := by linarith
    rw [vCut_eq hψ hc hχ0 hχc' hgj hm2 hmM]
    have hJ := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * π)
      fun θ _ => norm_integral_kerB_le a hg hg₁ hg₂c hang hc hχ0 hχc' hχi hgj hevenj hpsi hm2 hmM θ
    have h2pi : ‖(2 * π * I : ℂ)‖ = 2 * π := by
      simp [abs_of_pos Real.pi_pos]
    rw [norm_mul, norm_mul, norm_inv, h2pi, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / m)]
    rw [sub_zero, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at hJ
    have hpi : 0 < 2 * π := by positivity
    calc 1 / (m : ℝ) * ((2 * π)⁻¹ * ‖∫ θ in (0 : ℝ)..2 * π, ∫ t in (m : ℝ)..M, ∫ s in (-1 : ℝ)..1,
          kerB c m M gj a χ g s t θ‖)
        ≤ 1 / (m : ℝ) * ((2 * π)⁻¹ * (B / m * √(1 / m) * (2 * π))) := by gcongr
      _ = B * (1 / (m : ℝ) ^ 2 * √(1 / (m : ℝ))) := by field_simp
  rw [Cvs.L2a.BulkECouplingRemainder.bulkE_eq_bulkR hg hg₁ hg₂c hang hc0 hχc hgj (by omega), bulkR_eq]
  refine (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans ?_)
  calc ∑ m ∈ Finset.Ico 2 M, ‖vCut c gj a χ g (m : ℝ) (M : ℝ)‖
      ≤ ∑ m ∈ Finset.Ico 2 M, B * (1 / (m : ℝ) ^ 2 * √(1 / (m : ℝ))) := Finset.sum_le_sum hcut
    _ = B * ∑ m ∈ Finset.Ico 2 M, 1 / (m : ℝ) ^ 2 * √(1 / (m : ℝ)) := (Finset.mul_sum _ _ _).symm
    _ ≤ B * (1 / 2) := mul_le_mul_of_nonneg_left (sum_le_half M) hB0
    _ ≤ 700 * F / c * √P := by
        rw [hB]
        have hk : 6 * (200 / c + 2600 / c ^ 2) * (1 / 2) ≤ 700 / c := by
          have h1 : 7800 / c ^ 2 ≤ 100 / c := by
            rw [div_le_div_iff₀ (by positivity) hc0]
            nlinarith
          have e1 : 6 * (200 / c + 2600 / c ^ 2) * (1 / 2) = 600 / c + 7800 / c ^ 2 := by ring
          have e2 : 700 / c = 600 / c + 100 / c := by ring
          rw [e1, e2]
          linarith
        have hsP := Real.sqrt_nonneg P
        calc 6 * F * (200 / c + 2600 / c ^ 2) * √P * (1 / 2)
            = F * √P * (6 * (200 / c + 2600 / c ^ 2) * (1 / 2)) := by ring
          _ ≤ F * √P * (700 / c) := mul_le_mul_of_nonneg_left hk (by positivity)
          _ = 700 * F / c * √P := by ring

end main

end Cvs.L2a.BulkECouplingBound
