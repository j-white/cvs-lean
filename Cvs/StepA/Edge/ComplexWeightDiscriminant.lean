import Mathlib
import Cvs.StepA.Edge.EdgeDiscriminant
import Cvs.StepA.Edge.OneOrdinateDiscriminant
import Cvs.StepA.Edge.TwoEdgeSplit

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The edge discriminant at complex weights

The edge form `∑ᵢ Re(zᵢ · edgePairᵢ²)` at complex weights `z` and its discriminant `sSup + sInf`:
on the orbit `zᵢ = mᵢ e^{i gᵢ L}` it is the real-scale edge discriminant; it is odd and Lipschitz in
`z`, a single block `c` has discriminant `Re(c/(2(δ + i g)))`, and the lowest ordinate dominates
under the heat flow `zᵢ ↦ zᵢ e^{−gᵢ² y}`.
-/

noncomputable section

open Real MeasureTheory
open scoped Pointwise

namespace Cvs.StepA.Edge.PlanarBoxLemma
open Cvs.ZeroCounting
open Cvs.StepA.Edge.TwoEdgeSplit (edgePair edgeForm norm_sq_edgePair_le)
open Cvs.StepA.Edge.EdgeDiscriminant (edgeRay edgeDisc pos_of_integral_sq_pos)

section Flow

variable {ι : Type*}

/-- The orbit-and-heat flow of the weights: `zᵢ ↦ zᵢ e^{i gᵢ x − gᵢ² y}`. -/
def flow (g : ι → ℝ) (x y : ℝ) (z : ι → ℂ) : ι → ℂ :=
  fun i => z i * Complex.exp (((g i * x : ℝ) : ℂ) * Complex.I - ((g i ^ 2 * y : ℝ) : ℂ))

/-! ### The flow -/

/-- The flow at time `(0, 0)` is the identity. -/
@[simp] theorem flow_zero (g : ι → ℝ) (z : ι → ℂ) : flow g 0 0 z = z := by
  funext i
  simp [flow]

/-- The flow is jointly continuous in the times and the weights. -/
theorem continuous_flow (g : ι → ℝ) :
    Continuous fun p : (ℝ × ℝ) × (ι → ℂ) => flow g p.1.1 p.1.2 p.2 := by
  refine continuous_pi fun i => ?_
  simp only [flow]
  fun_prop

end Flow

variable {ι : Type*} [Fintype ι]

/-- The edge form at complex weights `z`: `∑ᵢ Re(zᵢ · edgePair(δ, gᵢ, F, a)²)`. -/
def edgeFormZ (δ : ℝ) (g : ι → ℝ) (z : ι → ℂ) (F : ℝ → ℝ) (a : ℝ) : ℝ :=
  ∑ i, (z i * edgePair δ (g i) F a ^ 2).re

/-- The edge Rayleigh quotients at complex weights `z`, over continuous profiles on `[0, a]`. -/
def edgeRayZ (δ : ℝ) (g : ι → ℝ) (z : ι → ℂ) : Set ℝ :=
  {r | ∃ F : ℝ → ℝ, ∃ a : ℝ, Continuous F ∧ 0 < ∫ u in (0 : ℝ)..a, F u ^ 2 ∧
    r = edgeFormZ δ g z F a / ∫ u in (0 : ℝ)..a, F u ^ 2}

/-- The edge discriminant `sSup + sInf` of the edge Rayleigh quotients at complex weights `z`. -/
def edgeDiscZ (δ : ℝ) (g : ι → ℝ) (z : ι → ℂ) : ℝ :=
  sSup (edgeRayZ δ g z) + sInf (edgeRayZ δ g z)

/-! ### The orbit -/

/-- On the orbit `zᵢ = mᵢ e^{i gᵢ L}` the complex-weight edge form is the edge form at scale `L`. -/
theorem edgeFormZ_orbit (δ : ℝ) (m g : ι → ℝ) (L : ℝ) (F : ℝ → ℝ) (a : ℝ) :
    edgeFormZ δ g (fun i => (m i : ℂ) * Complex.exp ((g i * L : ℝ) * Complex.I)) F a
      = edgeForm Finset.univ m g δ L F a := by
  unfold edgeFormZ edgeForm
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc, Complex.re_ofReal_mul]
  push_cast
  ring_nf

/-- On the orbit `zᵢ = mᵢ e^{i gᵢ L}` the complex-weight edge Rayleigh quotients are those at
scale `L`. -/
theorem edgeRayZ_orbit (δ : ℝ) (m g : ι → ℝ) (L : ℝ) :
    edgeRayZ δ g (fun i => (m i : ℂ) * Complex.exp ((g i * L : ℝ) * Complex.I))
      = edgeRay Finset.univ m g δ L := by
  unfold edgeRayZ edgeRay
  simp only [edgeFormZ_orbit]

/-- On the orbit `zᵢ = mᵢ e^{i gᵢ L}` the complex-weight edge discriminant is the edge discriminant
at scale `L`. -/
theorem edgeDiscZ_orbit (δ : ℝ) (m g : ι → ℝ) (L : ℝ) :
    edgeDiscZ δ g (fun i => (m i : ℂ) * Complex.exp ((g i * L : ℝ) * Complex.I))
      = edgeDisc Finset.univ m g δ L := by
  unfold edgeDiscZ edgeDisc
  rw [edgeRayZ_orbit]

/-! ### Oddness and the Lipschitz bound -/

/-- The complex-weight edge form is odd in the weights. -/
private theorem edgeFormZ_neg (δ : ℝ) (g : ι → ℝ) (z : ι → ℂ) (F : ℝ → ℝ) (a : ℝ) :
    edgeFormZ δ g (-z) F a = -edgeFormZ δ g z F a := by
  unfold edgeFormZ
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [neg_mul]

-- merged §0 (F4)
/-- The edge Rayleigh quotients are odd in the weights. -/
theorem edgeRayZ_neg (δ : ℝ) (g : ι → ℝ) (z : ι → ℂ) :
    edgeRayZ δ g (-z) = -edgeRayZ δ g z := by
  ext r
  simp only [edgeRayZ, Set.mem_neg, Set.mem_ofPred_eq, edgeFormZ_neg]
  constructor
  · rintro ⟨F, a, hF, hpos, rfl⟩
    exact ⟨F, a, hF, hpos, by rw [neg_div, neg_neg]⟩
  · rintro ⟨F, a, hF, hpos, hr⟩
    exact ⟨F, a, hF, hpos, by rw [neg_div, ← hr, neg_neg]⟩

/-- Moving the weights from `z'` to `z` moves the edge form by at most
`∑ ‖zᵢ − z'ᵢ‖ · ∫₀^a F² / (2δ)`. -/
private theorem abs_edgeFormZ_sub_le {δ : ℝ} (hδ : 0 < δ) (g : ι → ℝ) (z z' : ι → ℂ)
    {F : ℝ → ℝ} (hF : Continuous F) {a : ℝ} (ha : 0 ≤ a) :
    |edgeFormZ δ g z F a - edgeFormZ δ g z' F a|
      ≤ (∑ i, ‖z i - z' i‖) * (∫ u in (0 : ℝ)..a, F u ^ 2) / (2 * δ) := by
  unfold edgeFormZ
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul, Finset.sum_div]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Complex.sub_re, ← sub_mul]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, norm_pow, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (norm_sq_edgePair_le hδ _ hF ha) (norm_nonneg _)

/-- The complex-weight edge form vanishes at zero weights. -/
private theorem edgeFormZ_zero (δ : ℝ) (g : ι → ℝ) (F : ℝ → ℝ) (a : ℝ) :
    edgeFormZ δ g 0 F a = 0 := by
  simp [edgeFormZ]

/-- The complex-weight edge Rayleigh quotients form a nonempty set. -/
private theorem edgeRayZ_nonempty (δ : ℝ) (g : ι → ℝ) (z : ι → ℂ) : (edgeRayZ δ g z).Nonempty :=
  ⟨_, fun _ => 1, 1, continuous_const, by simp, rfl⟩

/-- Every complex-weight edge Rayleigh quotient is bounded in absolute value by
`∑ ‖zᵢ‖ / (2δ)`. -/
private theorem abs_le_of_mem_edgeRayZ {δ : ℝ} (hδ : 0 < δ) (g : ι → ℝ) (z : ι → ℂ) {r : ℝ}
    (hr : r ∈ edgeRayZ δ g z) : |r| ≤ (∑ i, ‖z i‖) / (2 * δ) := by
  obtain ⟨F, a, hF, hpos, rfl⟩ := hr
  have ha := (pos_of_integral_sq_pos hpos).le
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  have h := abs_edgeFormZ_sub_le hδ g z 0 hF ha
  simp only [edgeFormZ_zero, sub_zero, Pi.zero_apply] at h
  calc |edgeFormZ δ g z F a| ≤ (∑ i, ‖z i‖) * (∫ u in (0 : ℝ)..a, F u ^ 2) / (2 * δ) := h
    _ = (∑ i, ‖z i‖) / (2 * δ) * ∫ u in (0 : ℝ)..a, F u ^ 2 := by ring

/-- The complex-weight edge Rayleigh quotients are bounded above. -/
private theorem edgeRayZ_bddAbove {δ : ℝ} (hδ : 0 < δ) (g : ι → ℝ) (z : ι → ℂ) :
    BddAbove (edgeRayZ δ g z) :=
  ⟨_, fun _ hr => (abs_le.mp (abs_le_of_mem_edgeRayZ hδ g z hr)).2⟩

/-- The complex-weight edge Rayleigh quotients are bounded below. -/
private theorem edgeRayZ_bddBelow {δ : ℝ} (hδ : 0 < δ) (g : ι → ℝ) (z : ι → ℂ) :
    BddBelow (edgeRayZ δ g z) :=
  ⟨_, fun _ hr => (abs_le.mp (abs_le_of_mem_edgeRayZ hδ g z hr)).1⟩

/-- Moving the weights moves each Rayleigh quotient by at most `∑ ‖zᵢ − z'ᵢ‖/(2δ)`. -/
private theorem exists_mem_edgeRayZ_near {δ : ℝ} (hδ : 0 < δ) (g : ι → ℝ) (z z' : ι → ℂ) {r : ℝ}
    (hr : r ∈ edgeRayZ δ g z) :
    ∃ r' ∈ edgeRayZ δ g z', |r - r'| ≤ (∑ i, ‖z i - z' i‖) / (2 * δ) := by
  obtain ⟨F, a, hF, hpos, rfl⟩ := hr
  have ha := (pos_of_integral_sq_pos hpos).le
  refine ⟨_, ⟨F, a, hF, hpos, rfl⟩, ?_⟩
  rw [← sub_div, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  have h := abs_edgeFormZ_sub_le hδ g z z' hF ha
  calc |edgeFormZ δ g z F a - edgeFormZ δ g z' F a|
      ≤ (∑ i, ‖z i - z' i‖) * (∫ u in (0 : ℝ)..a, F u ^ 2) / (2 * δ) := h
    _ = _ := by ring

-- merged §0 (F2); copy of an earlier result abs_edgeFormP_sub_le / abs_edgeDiscP_sub_le
/-- **The edge discriminant is Lipschitz in the weights**:
`|edgeDiscZ z − edgeDiscZ z'| ≤ ∑ᵢ ‖zᵢ − z'ᵢ‖ / δ`. -/
theorem abs_edgeDiscZ_sub_le {δ : ℝ} (hδ : 0 < δ) (g : ι → ℝ) (z z' : ι → ℂ) :
    |edgeDiscZ δ g z - edgeDiscZ δ g z'| ≤ (∑ i, ‖z i - z' i‖) / δ := by
  set η := (∑ i, ‖z i - z' i‖) / (2 * δ) with hη
  have hη' : (∑ i, ‖z' i - z i‖) / (2 * δ) = η := by
    simp only [hη, norm_sub_rev]
  have sup1 : sSup (edgeRayZ δ g z) ≤ sSup (edgeRayZ δ g z') + η := by
    refine csSup_le (edgeRayZ_nonempty δ g z) fun r hr => ?_
    obtain ⟨r', hr', hle⟩ := exists_mem_edgeRayZ_near hδ g z z' hr
    linarith [le_csSup (edgeRayZ_bddAbove hδ g z') hr', le_abs_self (r - r')]
  have sup2 : sSup (edgeRayZ δ g z') ≤ sSup (edgeRayZ δ g z) + η := by
    refine csSup_le (edgeRayZ_nonempty δ g z') fun r hr => ?_
    obtain ⟨r', hr', hle⟩ := exists_mem_edgeRayZ_near hδ g z' z hr
    rw [hη'] at hle
    linarith [le_csSup (edgeRayZ_bddAbove hδ g z) hr', le_abs_self (r - r')]
  have inf1 : sInf (edgeRayZ δ g z) - η ≤ sInf (edgeRayZ δ g z') := by
    refine le_csInf (edgeRayZ_nonempty δ g z') fun r hr => ?_
    obtain ⟨r', hr', hle⟩ := exists_mem_edgeRayZ_near hδ g z' z hr
    rw [hη'] at hle
    linarith [csInf_le (edgeRayZ_bddBelow hδ g z) hr', neg_abs_le (r - r')]
  have inf2 : sInf (edgeRayZ δ g z') - η ≤ sInf (edgeRayZ δ g z) := by
    refine le_csInf (edgeRayZ_nonempty δ g z) fun r hr => ?_
    obtain ⟨r', hr', hle⟩ := exists_mem_edgeRayZ_near hδ g z z' hr
    linarith [csInf_le (edgeRayZ_bddBelow hδ g z') hr', neg_abs_le (r - r')]
  have hgen : ∀ X : ℝ, X / δ = 2 * (X / (2 * δ)) := fun X => by field_simp
  rw [hgen, ← hη]
  unfold edgeDiscZ
  rw [abs_le]
  constructor <;> linarith

/-- The complex-weight edge discriminant is continuous in the weights. -/
theorem continuous_edgeDiscZ {δ : ℝ} (hδ : 0 < δ) (g : ι → ℝ) :
    Continuous (edgeDiscZ δ g) := by
  refine (LipschitzWith.of_dist_le_mul fun z z' => ?_ :
    LipschitzWith (Real.toNNReal ((Fintype.card ι : ℝ) / δ)) (edgeDiscZ δ g)).continuous
  rw [Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
  refine (abs_edgeDiscZ_sub_le hδ g z z').trans ?_
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hδ]
  calc ∑ i, ‖z i - z' i‖ ≤ ∑ _i : ι, dist z z' := Finset.sum_le_sum fun i _ => by
        rw [← dist_eq_norm]; exact dist_le_pi_dist z z' i
    _ = (Fintype.card ι : ℝ) * dist z z' := by rw [Finset.sum_const, nsmul_eq_mul]; rfl

/-! ### One block -/

/-- At the weights `Pi.single i₀ c` the edge form is `Re(c · edgePair(δ, g_{i₀})²)`. -/
private theorem edgeFormZ_single [DecidableEq ι] (δ : ℝ) (g : ι → ℝ) (i₀ : ι) (c : ℂ)
    (F : ℝ → ℝ) (a : ℝ) :
    edgeFormZ δ g (Pi.single i₀ c) F a = (c * edgePair δ (g i₀) F a ^ 2).re := by
  unfold edgeFormZ
  rw [Finset.sum_eq_single i₀ (fun i _ hi => by simp [Pi.single_eq_of_ne hi])
    (fun h => absurd (Finset.mem_univ i₀) h)]
  simp

/-- The half-turned edge pairing in real coordinates: `e^{iθ/2} edgePair(δ, γ) = x + i y` with
`x = ∫₀^a F Re w`, `y = ∫₀^a F Im w` and `w = rotW θ δ γ`. -/
private theorem exp_half_mul_edgePair (θ δ γ : ℝ) {F : ℝ → ℝ} (hF : Continuous F) (a : ℝ) :
    Complex.exp (θ * Complex.I / 2) * edgePair δ γ F a
      = ((∫ u in (0 : ℝ)..a, F u * (Cvs.StepA.Edge.OneOrdinateDiscriminant.rotW θ δ γ u).re : ℝ) : ℂ)
        + Complex.I
          * ((∫ u in (0 : ℝ)..a, F u * (Cvs.StepA.Edge.OneOrdinateDiscriminant.rotW θ δ γ u).im : ℝ) : ℂ) := by
  have hint : IntervalIntegrable
      (fun u => ((F u : ℝ) : ℂ) * Cvs.StepA.Edge.OneOrdinateDiscriminant.rotW θ δ γ u) volume 0 a :=
    (by fun_prop : Continuous fun u =>
      ((F u : ℝ) : ℂ) * Cvs.StepA.Edge.OneOrdinateDiscriminant.rotW θ δ γ u).intervalIntegrable _ _
  have h1 : Complex.exp (θ * Complex.I / 2) * edgePair δ γ F a
      = ∫ u in (0 : ℝ)..a, ((F u : ℝ) : ℂ) * Cvs.StepA.Edge.OneOrdinateDiscriminant.rotW θ δ γ u := by
    unfold edgePair Cvs.StepA.Edge.OneOrdinateDiscriminant.rotW
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [sub_eq_add_neg, Complex.exp_add]
    ring_nf
  rw [h1]
  apply Complex.ext
  · have := intervalIntegral.intervalIntegral_re hint
    simp only [RCLike.re_to_complex] at this
    rw [← this]
    simp [Complex.mul_re]
  · have := intervalIntegral.intervalIntegral_im hint
    simp only [RCLike.im_to_complex] at this
    rw [← this]
    simp [Complex.mul_im]

/-- The energy of `s f + t h` on `[0, b]`: `s² ∫ f² + 2st ∫ f h + t² ∫ h²`. -/
private theorem integral_lin_sq {f h : ℝ → ℝ} (hf : Continuous f) (hh : Continuous h)
    (s t b : ℝ) :
    ∫ τ in (0 : ℝ)..b, (s * f τ + t * h τ) ^ 2
      = s ^ 2 * (∫ τ in (0 : ℝ)..b, f τ ^ 2) + 2 * s * t * (∫ τ in (0 : ℝ)..b, f τ * h τ)
        + t ^ 2 * ∫ τ in (0 : ℝ)..b, h τ ^ 2 := by
  have e : ∀ τ, (s * f τ + t * h τ) ^ 2
      = (s ^ 2 * f τ ^ 2 + 2 * s * t * (f τ * h τ)) + t ^ 2 * h τ ^ 2 := fun τ => by ring
  simp_rw [e]
  rw [intervalIntegral.integral_add ((by fun_prop : Continuous fun τ =>
      s ^ 2 * f τ ^ 2 + 2 * s * t * (f τ * h τ)).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun τ => t ^ 2 * h τ ^ 2).intervalIntegrable _ _),
    intervalIntegral.integral_add ((by fun_prop : Continuous fun τ =>
      s ^ 2 * f τ ^ 2).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun τ => 2 * s * t * (f τ * h τ)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]

/-- The pairing of `F` with `s f + t h` on `[0, b]`: `s ∫ F f + t ∫ F h`. -/
private theorem integral_mul_lin {F f h : ℝ → ℝ} (hF : Continuous F) (hf : Continuous f)
    (hh : Continuous h) (s t b : ℝ) :
    ∫ τ in (0 : ℝ)..b, F τ * (s * f τ + t * h τ)
      = s * (∫ τ in (0 : ℝ)..b, F τ * f τ) + t * ∫ τ in (0 : ℝ)..b, F τ * h τ := by
  have e : ∀ τ, F τ * (s * f τ + t * h τ) = s * (F τ * f τ) + t * (F τ * h τ) := fun τ => by ring
  simp_rw [e]
  rw [intervalIntegral.integral_add ((by fun_prop : Continuous fun τ =>
      s * (F τ * f τ)).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun τ => t * (F τ * h τ)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

/-- Bessel's inequality against one function on `[0, a]`, `a ≥ 0`:
`2 ∫ F h − ∫ h² ≤ ∫ F²`. -/
private theorem two_integral_mul_sub_le {F h : ℝ → ℝ} (hF : Continuous F) (hh : Continuous h)
    {a : ℝ} (ha : 0 ≤ a) :
    2 * (∫ τ in (0 : ℝ)..a, F τ * h τ) - ∫ τ in (0 : ℝ)..a, h τ ^ 2
      ≤ ∫ τ in (0 : ℝ)..a, F τ ^ 2 := by
  have h0 : 0 ≤ ∫ τ in (0 : ℝ)..a, (F τ - h τ) ^ 2 :=
    intervalIntegral.integral_nonneg ha fun τ _ => sq_nonneg _
  have e1 : ∀ τ, (F τ - h τ) ^ 2 = (F τ ^ 2 - 2 * (F τ * h τ)) + h τ ^ 2 := fun τ => by ring
  simp_rw [e1] at h0
  rw [intervalIntegral.integral_add ((by fun_prop : Continuous fun τ =>
      F τ ^ 2 - 2 * (F τ * h τ)).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun τ => h τ ^ 2).intervalIntegrable _ _),
    intervalIntegral.integral_sub ((by fun_prop : Continuous fun τ => F τ ^ 2).intervalIntegrable
      _ _) ((by fun_prop : Continuous fun τ => 2 * (F τ * h τ)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul] at h0
  linarith

/-- The quadratic form `α(x² − y²) − 2βxy` under the Bessel bound
`2(sx + ty) − (s²a² + t²b²) ≤ N` for all `s, t` lies between `(α(a² − b²) − ρ)/2 · N` and
`(α(a² − b²) + ρ)/2 · N`, where `ρ ≥ 0` and `ρ² = (α(a² + b²))² + 4(βab)²`. -/
private theorem quad_bounds {α β a b x y N ρ : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hKI : ∀ s t : ℝ, 2 * (s * x + t * y) - (s ^ 2 * a ^ 2 + t ^ 2 * b ^ 2) ≤ N)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ^ 2 = (α * (a ^ 2 + b ^ 2)) ^ 2 + 4 * (β * a * b) ^ 2) :
    (α * (a ^ 2 - b ^ 2) - ρ) / 2 * N ≤ α * (x ^ 2 - y ^ 2) - 2 * β * x * y ∧
      α * (x ^ 2 - y ^ 2) - 2 * β * x * y ≤ (α * (a ^ 2 - b ^ 2) + ρ) / 2 * N := by
  have hρα : |α * (a ^ 2 + b ^ 2)| ≤ ρ := by
    have h : (α * (a ^ 2 + b ^ 2)) ^ 2 ≤ ρ ^ 2 := by rw [hρ]; nlinarith [sq_nonneg (β * a * b)]
    have := sq_le_sq.mp h
    rwa [abs_of_nonneg hρ0] at this
  have hρα' := abs_le.mp hρα
  have hpm : 0 ≤ α * (a ^ 2 - b ^ 2) + ρ ∧ α * (a ^ 2 - b ^ 2) - ρ ≤ 0 := by
    rcases le_total 0 α with hα | hα
    · constructor <;> nlinarith [mul_nonneg hα (sq_nonneg a), mul_nonneg hα (sq_nonneg b)]
    · constructor <;> nlinarith [mul_nonneg (neg_nonneg.mpr hα) (sq_nonneg a),
        mul_nonneg (neg_nonneg.mpr hα) (sq_nonneg b)]
  rcases hb.lt_or_eq with hb0 | hb0
  · -- `b > 0`: the coordinates `X = x/a`, `Y = y/b`
    set X := x / a with hX
    set Y := y / b with hY
    have hx : x = a * X := by rw [hX]; field_simp
    have hy : y = b * Y := by rw [hY]; field_simp
    have hS : X ^ 2 + Y ^ 2 ≤ N := by
      have h := hKI (X / a) (Y / b)
      have e : 2 * (X / a * x + Y / b * y) - ((X / a) ^ 2 * a ^ 2 + (Y / b) ^ 2 * b ^ 2)
          = X ^ 2 + Y ^ 2 := by
        rw [hx, hy]; field_simp; ring
      linarith
    set T := α * (a ^ 2 + b ^ 2) / 2 * (X ^ 2 - Y ^ 2) - β * a * b * (2 * X * Y) with hT
    have hQ : α * (x ^ 2 - y ^ 2) - 2 * β * x * y
        = α * (a ^ 2 - b ^ 2) / 2 * (X ^ 2 + Y ^ 2) + T := by
      rw [hx, hy, hT]; ring
    have hT2 : T ^ 2 ≤ (ρ / 2 * (X ^ 2 + Y ^ 2)) ^ 2 := by
      have e : (ρ / 2 * (X ^ 2 + Y ^ 2)) ^ 2 - T ^ 2
          = (α * (a ^ 2 + b ^ 2) / 2 * (2 * X * Y) + β * a * b * (X ^ 2 - Y ^ 2)) ^ 2 := by
        rw [mul_pow, div_pow, hρ, hT]; ring
      nlinarith [sq_nonneg (α * (a ^ 2 + b ^ 2) / 2 * (2 * X * Y)
        + β * a * b * (X ^ 2 - Y ^ 2))]
    have hTabs : |T| ≤ ρ / 2 * (X ^ 2 + Y ^ 2) := by
      have := sq_le_sq.mp hT2
      rwa [abs_of_nonneg (by positivity : 0 ≤ ρ / 2 * (X ^ 2 + Y ^ 2))] at this
    have hT' := abs_le.mp hTabs
    rw [hQ]
    constructor
    · calc (α * (a ^ 2 - b ^ 2) - ρ) / 2 * N
          ≤ (α * (a ^ 2 - b ^ 2) - ρ) / 2 * (X ^ 2 + Y ^ 2) :=
            mul_le_mul_of_nonpos_left hS (by linarith [hpm.2])
        _ = α * (a ^ 2 - b ^ 2) / 2 * (X ^ 2 + Y ^ 2) - ρ / 2 * (X ^ 2 + Y ^ 2) := by ring
        _ ≤ α * (a ^ 2 - b ^ 2) / 2 * (X ^ 2 + Y ^ 2) + T := by linarith [hT'.1]
    · calc α * (a ^ 2 - b ^ 2) / 2 * (X ^ 2 + Y ^ 2) + T
          ≤ α * (a ^ 2 - b ^ 2) / 2 * (X ^ 2 + Y ^ 2) + ρ / 2 * (X ^ 2 + Y ^ 2) := by
            linarith [hT'.2]
        _ = (α * (a ^ 2 - b ^ 2) + ρ) / 2 * (X ^ 2 + Y ^ 2) := by ring
        _ ≤ (α * (a ^ 2 - b ^ 2) + ρ) / 2 * N :=
            mul_le_mul_of_nonneg_left hS (by linarith [hpm.1])
  · -- `b = 0`: then `y = 0` and the form is `α x²`
    subst hb0
    have hy : y = 0 := by
      by_contra hy
      have h := hKI 0 ((|N| + 1) / (2 * y))
      have e : 2 * (0 * x + (|N| + 1) / (2 * y) * y)
          - (0 ^ 2 * a ^ 2 + ((|N| + 1) / (2 * y)) ^ 2 * 0 ^ 2) = |N| + 1 := by
        field_simp; ring
      linarith [le_abs_self N]
    have hx : x ^ 2 ≤ a ^ 2 * N := by
      have h := hKI (x / a ^ 2) 0
      have e : 2 * (x / a ^ 2 * x + 0 * y) - ((x / a ^ 2) ^ 2 * a ^ 2 + 0 ^ 2 * 0 ^ 2)
          = x ^ 2 / a ^ 2 := by
        field_simp; ring
      rw [e, div_le_iff₀ (by positivity)] at h
      linarith
    subst hy
    have hρ' : ρ = |α * a ^ 2| := by
      rw [← Real.sqrt_sq hρ0, hρ, ← Real.sqrt_sq_eq_abs]
      congr 1
      ring
    rw [hρ']
    rcases le_total 0 α with hα | hα
    · rw [abs_of_nonneg (by positivity)]
      constructor
      · nlinarith [mul_nonneg hα (sq_nonneg x)]
      · nlinarith [mul_le_mul_of_nonneg_left hx hα]
    · rw [abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hα (sq_nonneg a))]
      constructor
      · nlinarith [mul_le_mul_of_nonpos_left hx hα]
      · nlinarith [mul_nonneg (neg_nonneg.mpr hα) (sq_nonneg x)]

/-- For continuous `u, v` with energies on `[0, a]` tending to `Ps > 0`, `Qs ≥ 0` and cross energy to
`0`, the Rayleigh quotients of `α(x² − y²) − 2βxy`, `x = ∫₀^a F u`, `y = ∫₀^a F v`, have
`sSup + sInf = α(Ps − Qs)`, given that the set contains `0` when `Qs = 0`. -/
private theorem sSup_add_sInf_quad {u v : ℝ → ℝ} (hu : Continuous u) (hv : Continuous v)
    {Ps Qs : ℝ} (hPs : 0 < Ps) (hQs : 0 ≤ Qs)
    (hU : Filter.Tendsto (fun a => ∫ τ in (0 : ℝ)..a, u τ ^ 2) Filter.atTop (nhds Ps))
    (hV : Filter.Tendsto (fun a => ∫ τ in (0 : ℝ)..a, v τ ^ 2) Filter.atTop (nhds Qs))
    (hC : Filter.Tendsto (fun a => ∫ τ in (0 : ℝ)..a, u τ * v τ) Filter.atTop (nhds 0))
    (α β : ℝ) {T : Set ℝ}
    (hT : ∀ r, r ∈ T ↔ ∃ F : ℝ → ℝ, ∃ a : ℝ, Continuous F ∧ 0 < ∫ τ in (0 : ℝ)..a, F τ ^ 2 ∧
      r = (α * ((∫ τ in (0 : ℝ)..a, F τ * u τ) ^ 2 - (∫ τ in (0 : ℝ)..a, F τ * v τ) ^ 2)
        - 2 * β * (∫ τ in (0 : ℝ)..a, F τ * u τ) * (∫ τ in (0 : ℝ)..a, F τ * v τ))
        / ∫ τ in (0 : ℝ)..a, F τ ^ 2)
    (h0 : Qs = 0 → (0 : ℝ) ∈ T) :
    sSup T + sInf T = α * (Ps - Qs) := by
  -- the finite energies lie below their limits
  have hLw : ∀ a, 0 ≤ a → ∀ s t : ℝ,
      ∫ τ in (0 : ℝ)..a, (s * u τ + t * v τ) ^ 2 ≤ s ^ 2 * Ps + t ^ 2 * Qs := by
    intro a ha s t
    have hlim : Filter.Tendsto (fun b => ∫ τ in (0 : ℝ)..b, (s * u τ + t * v τ) ^ 2)
        Filter.atTop (nhds (s ^ 2 * Ps + t ^ 2 * Qs)) := by
      have := ((hU.const_mul (s ^ 2)).add (hC.const_mul (2 * s * t))).add (hV.const_mul (t ^ 2))
      simp only [mul_zero, add_zero] at this
      exact this.congr fun b => (integral_lin_sq hu hv s t b).symm
    refine ge_of_tendsto hlim ?_
    filter_upwards [Filter.eventually_ge_atTop a] with b hb
    exact intervalIntegral.integral_mono_interval le_rfl ha hb
      (Filter.Eventually.of_forall fun τ => sq_nonneg _)
      ((by fun_prop : Continuous fun τ => (s * u τ + t * v τ) ^ 2).intervalIntegrable _ _)
  -- Bessel against `s u + t v`
  have hKI : ∀ F : ℝ → ℝ, Continuous F → ∀ a, 0 ≤ a → ∀ s t : ℝ,
      2 * (s * (∫ τ in (0 : ℝ)..a, F τ * u τ) + t * (∫ τ in (0 : ℝ)..a, F τ * v τ))
        - (s ^ 2 * Ps + t ^ 2 * Qs) ≤ ∫ τ in (0 : ℝ)..a, F τ ^ 2 := by
    intro F hF a ha s t
    have h1 := two_integral_mul_sub_le hF
      (by fun_prop : Continuous fun τ => s * u τ + t * v τ) ha
    rw [integral_mul_lin hF hu hv] at h1
    linarith [hLw a ha s t]
  set a' := Real.sqrt Ps with ha'def
  set b' := Real.sqrt Qs with hb'def
  have ha' : 0 < a' := Real.sqrt_pos.mpr hPs
  have hb' : 0 ≤ b' := Real.sqrt_nonneg _
  have ha'2 : a' ^ 2 = Ps := Real.sq_sqrt hPs.le
  have hb'2 : b' ^ 2 = Qs := Real.sq_sqrt hQs
  set μ : ℂ := ((α * (Ps + Qs) : ℝ) : ℂ) + ((-(2 * β * a' * b') : ℝ) : ℂ) * Complex.I with hμ
  set ρ := ‖μ‖ with hρdef
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  have hρ2 : ρ ^ 2 = (α * (a' ^ 2 + b' ^ 2)) ^ 2 + 4 * (β * a' * b') ^ 2 := by
    rw [hρdef, hμ, Complex.sq_norm, Complex.normSq_add_mul_I, ha'2, hb'2]
    ring
  -- every quotient lies between the two eigenvalues
  have hbd : ∀ r ∈ T, (α * (Ps - Qs) - ρ) / 2 ≤ r ∧ r ≤ (α * (Ps - Qs) + ρ) / 2 := by
    intro r hr
    obtain ⟨F, a, hF, hN, rfl⟩ := (hT r).mp hr
    have ha := (pos_of_integral_sq_pos hN).le
    have hq := quad_bounds (α := α) (β := β) ha' hb' (fun s t => by
      rw [ha'2, hb'2]; exact hKI F hF a ha s t) hρ0 hρ2
    rw [ha'2, hb'2] at hq
    constructor
    · rw [le_div_iff₀ hN]; linarith [hq.1]
    · rw [div_le_iff₀ hN]; linarith [hq.2]
  have hbddA : BddAbove T := ⟨_, fun r hr => (hbd r hr).2⟩
  have hbddB : BddBelow T := ⟨_, fun r hr => (hbd r hr).1⟩
  -- the profiles `s u + t v` on `[0, a]`, `a → ∞`
  have hfam : ∀ s t : ℝ, 0 < s ^ 2 * Ps + t ^ 2 * Qs →
      (∀ᶠ a in Filter.atTop,
        (α * ((∫ τ in (0 : ℝ)..a, (s * u τ + t * v τ) * u τ) ^ 2
          - (∫ τ in (0 : ℝ)..a, (s * u τ + t * v τ) * v τ) ^ 2)
          - 2 * β * (∫ τ in (0 : ℝ)..a, (s * u τ + t * v τ) * u τ)
            * (∫ τ in (0 : ℝ)..a, (s * u τ + t * v τ) * v τ))
          / (∫ τ in (0 : ℝ)..a, (s * u τ + t * v τ) ^ 2) ∈ T) ∧
      Filter.Tendsto (fun a =>
        (α * ((∫ τ in (0 : ℝ)..a, (s * u τ + t * v τ) * u τ) ^ 2
          - (∫ τ in (0 : ℝ)..a, (s * u τ + t * v τ) * v τ) ^ 2)
          - 2 * β * (∫ τ in (0 : ℝ)..a, (s * u τ + t * v τ) * u τ)
            * (∫ τ in (0 : ℝ)..a, (s * u τ + t * v τ) * v τ))
          / (∫ τ in (0 : ℝ)..a, (s * u τ + t * v τ) ^ 2)) Filter.atTop
        (nhds ((α * ((s * Ps) ^ 2 - (t * Qs) ^ 2) - 2 * β * (s * Ps) * (t * Qs))
          / (s ^ 2 * Ps + t ^ 2 * Qs))) := by
    intro s t hpos
    have hx : ∀ a, ∫ τ in (0 : ℝ)..a, (s * u τ + t * v τ) * u τ
        = s * (∫ τ in (0 : ℝ)..a, u τ ^ 2) + t * ∫ τ in (0 : ℝ)..a, u τ * v τ := by
      intro a
      have := integral_mul_lin hu hu hv s t a
      simp only [← sq] at this
      rw [← this]
      congr 1; funext τ; ring
    have hy : ∀ a, ∫ τ in (0 : ℝ)..a, (s * u τ + t * v τ) * v τ
        = s * (∫ τ in (0 : ℝ)..a, u τ * v τ) + t * ∫ τ in (0 : ℝ)..a, v τ ^ 2 := by
      intro a
      have := integral_mul_lin hv hu hv s t a
      simp only [← sq] at this
      have e : ∫ τ in (0 : ℝ)..a, v τ * u τ = ∫ τ in (0 : ℝ)..a, u τ * v τ := by
        congr 1; funext τ; ring
      rw [e] at this
      rw [← this]
      congr 1; funext τ; ring
    have tx : Filter.Tendsto (fun a => ∫ τ in (0 : ℝ)..a, (s * u τ + t * v τ) * u τ)
        Filter.atTop (nhds (s * Ps)) := by
      have := (hU.const_mul s).add (hC.const_mul t)
      simp only [mul_zero, add_zero] at this
      exact this.congr fun a => (hx a).symm
    have ty : Filter.Tendsto (fun a => ∫ τ in (0 : ℝ)..a, (s * u τ + t * v τ) * v τ)
        Filter.atTop (nhds (t * Qs)) := by
      have := (hC.const_mul s).add (hV.const_mul t)
      simp only [mul_zero, zero_add] at this
      exact this.congr fun a => (hy a).symm
    have tN : Filter.Tendsto (fun a => ∫ τ in (0 : ℝ)..a, (s * u τ + t * v τ) ^ 2)
        Filter.atTop (nhds (s ^ 2 * Ps + t ^ 2 * Qs)) := by
      have := ((hU.const_mul (s ^ 2)).add (hC.const_mul (2 * s * t))).add (hV.const_mul (t ^ 2))
      simp only [mul_zero, add_zero] at this
      exact this.congr fun b => (integral_lin_sq hu hv s t b).symm
    refine ⟨?_, ?_⟩
    · filter_upwards [tN.eventually (lt_mem_nhds hpos)] with a ha
      exact (hT _).mpr ⟨fun τ => s * u τ + t * v τ, a, by fun_prop, ha, rfl⟩
    · exact ((((tx.pow 2).sub (ty.pow 2)).const_mul α).sub
        ((tx.const_mul (2 * β)).mul ty)).div tN hpos.ne'
  have hach : ∀ s t : ℝ, 0 < s ^ 2 * Ps + t ^ 2 * Qs →
      (α * ((s * Ps) ^ 2 - (t * Qs) ^ 2) - 2 * β * (s * Ps) * (t * Qs))
          / (s ^ 2 * Ps + t ^ 2 * Qs) ≤ sSup T ∧
        sInf T ≤ (α * ((s * Ps) ^ 2 - (t * Qs) ^ 2) - 2 * β * (s * Ps) * (t * Qs))
          / (s ^ 2 * Ps + t ^ 2 * Qs) := by
    intro s t hpos
    obtain ⟨hev, htd⟩ := hfam s t hpos
    exact ⟨le_of_tendsto htd (hev.mono fun a ha => le_csSup hbddA ha),
      ge_of_tendsto htd (hev.mono fun a ha => csInf_le hbddB ha)⟩
  have hne : T.Nonempty := by
    have hpos : 0 < (1 : ℝ) ^ 2 * Ps + 0 ^ 2 * Qs := by simpa using hPs
    obtain ⟨a, ha⟩ := (hfam 1 0 hpos).1.exists
    exact ⟨_, ha⟩
  have hsup : sSup T ≤ (α * (Ps - Qs) + ρ) / 2 := csSup_le hne fun r hr => (hbd r hr).2
  have hinf : (α * (Ps - Qs) - ρ) / 2 ≤ sInf T := le_csInf hne fun r hr => (hbd r hr).1
  rcases hQs.lt_or_eq with hQ | hQ
  · -- `Qs > 0`: the two eigen-directions
    have hb'0 : 0 < b' := Real.sqrt_pos.mpr hQ
    set φ := Complex.arg μ with hφ
    have hcos : ρ * Real.cos φ = α * (a' ^ 2 + b' ^ 2) := by
      rw [hρdef, hφ, Complex.norm_mul_cos_arg, ha'2, hb'2, hμ]
      simp
    have hsin : ρ * Real.sin φ = -(2 * β * a' * b') := by
      rw [hρdef, hφ, Complex.norm_mul_sin_arg, hμ]
      simp
    set C := Real.cos (φ / 2) with hC'
    set S := Real.sin (φ / 2) with hS'
    have hpy : S ^ 2 + C ^ 2 = 1 := Real.sin_sq_add_cos_sq _
    have hc2 : Real.cos φ = C ^ 2 - S ^ 2 := by
      have : Real.cos φ = Real.cos (2 * (φ / 2)) := by congr 1; ring
      rw [this, Real.cos_two_mul]
      linear_combination hpy
    have hs2 : Real.sin φ = 2 * S * C := by
      have : Real.sin φ = Real.sin (2 * (φ / 2)) := by congr 1; ring
      rw [this, Real.sin_two_mul]
    have H1 : ρ * (C ^ 2 - S ^ 2) = α * (a' ^ 2 + b' ^ 2) := by rw [← hc2]; exact hcos
    have H2 : ρ * (2 * S * C) = -(2 * β * a' * b') := by rw [← hs2]; exact hsin
    -- the top direction `(C/a', S/b')`
    have hdt : (C / a') ^ 2 * Ps + (S / b') ^ 2 * Qs = 1 := by
      rw [← ha'2, ← hb'2]; field_simp; linear_combination hpy
    have hvt : (α * ((C / a' * Ps) ^ 2 - (S / b' * Qs) ^ 2) - 2 * β * (C / a' * Ps) * (S / b' * Qs))
        / ((C / a') ^ 2 * Ps + (S / b') ^ 2 * Qs) = (α * (Ps - Qs) + ρ) / 2 := by
      rw [hdt, div_one, ← ha'2, ← hb'2]
      have e1 : C / a' * a' ^ 2 = C * a' := by field_simp
      have e2 : S / b' * b' ^ 2 = S * b' := by field_simp
      rw [e1, e2]
      linear_combination (-(C ^ 2 - S ^ 2) / 2) * H1 + (-(C * S)) * H2
        + (ρ * (C ^ 2 + S ^ 2 + 1) / 2 + α * (a' ^ 2 - b' ^ 2) / 2) * hpy
    -- the bottom direction `(S/a', −C/b')`
    have hdb : (S / a') ^ 2 * Ps + (-C / b') ^ 2 * Qs = 1 := by
      rw [← ha'2, ← hb'2]; field_simp; linear_combination hpy
    have hvb : (α * ((S / a' * Ps) ^ 2 - (-C / b' * Qs) ^ 2)
          - 2 * β * (S / a' * Ps) * (-C / b' * Qs))
        / ((S / a') ^ 2 * Ps + (-C / b') ^ 2 * Qs) = (α * (Ps - Qs) - ρ) / 2 := by
      rw [hdb, div_one, ← ha'2, ← hb'2]
      have e1 : S / a' * a' ^ 2 = S * a' := by field_simp
      have e2 : -C / b' * b' ^ 2 = -(C * b') := by field_simp
      rw [e1, e2]
      linear_combination ((C ^ 2 - S ^ 2) / 2) * H1 + (S * C) * H2
        + (-ρ * (C ^ 2 + S ^ 2 + 1) / 2 + α * (a' ^ 2 - b' ^ 2) / 2) * hpy
    have ht := (hach _ _ (by rw [hdt]; exact one_pos)).1
    have hb := (hach _ _ (by rw [hdb]; exact one_pos)).2
    rw [hvt] at ht
    rw [hvb] at hb
    linarith
  · -- `Qs = 0`: the eigenvalues are `α Ps` and `0`
    have h0T := h0 hQ.symm
    have hs0 : 0 ≤ sSup T := le_csSup hbddA h0T
    have hi0 : sInf T ≤ 0 := csInf_le hbddB h0T
    have h1 := hach 1 0 (by simpa using hPs)
    have hv1 : (α * ((1 * Ps) ^ 2 - (0 * Qs) ^ 2) - 2 * β * (1 * Ps) * (0 * Qs))
        / (1 ^ 2 * Ps + 0 ^ 2 * Qs) = α * Ps := by
      field_simp; ring
    rw [hv1] at h1
    have hρ' : ρ = |α * Ps| := by
      have hb0 : b' = 0 := by rw [hb'def, ← hQ, Real.sqrt_zero]
      rw [← Real.sqrt_sq hρ0, hρ2, ← Real.sqrt_sq_eq_abs, hb0, ha'2]
      congr 1
      ring
    rw [hρ', ← hQ] at hsup hinf
    rw [← hQ]
    rcases le_total 0 α with hα | hα
    · rw [abs_of_nonneg (mul_nonneg hα hPs.le)] at hsup hinf
      linarith [h1.1]
    · rw [abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hα hPs.le)] at hsup hinf
      linarith [h1.2]

/-- **One block at one ordinate**: the Rayleigh quotients `Re(c · edgePair(δ, γ)²)/∫₀^a F²` over
continuous profiles have `sSup + sInf = Re(c / (2(δ + iγ)))`, for `δ > 0`. -/
private theorem sSup_add_sInf_single {δ : ℝ} (hδ : 0 < δ) (γ : ℝ) (c : ℂ) {S : Set ℝ}
    (hS : ∀ r, r ∈ S ↔ ∃ F : ℝ → ℝ, ∃ a : ℝ, Continuous F ∧ 0 < ∫ u in (0 : ℝ)..a, F u ^ 2 ∧
      r = (c * edgePair δ γ F a ^ 2).re / ∫ u in (0 : ℝ)..a, F u ^ 2) :
    sSup S + sInf S = (c / (2 * ((δ : ℂ) + γ * Complex.I))).re := by
  have hZδ := Cvs.StepA.Edge.OneOrdinateDiscriminant.le_norm_add_mul_I δ γ
  have hen := Cvs.StepA.Edge.OneOrdinateDiscriminant.rotW_arg_energies hδ γ
  have hX := Cvs.StepA.Edge.OneOrdinateDiscriminant.tendsto_exp_neg_two_mul hδ
  have hpolar := Complex.norm_mul_exp_arg_mul_I ((δ : ℂ) + γ * Complex.I)
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = Complex.arg ((δ : ℂ) + γ * Complex.I) := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = ‖(δ : ℂ) + γ * Complex.I‖ := ⟨_, rfl⟩
  rw [← hθ] at hen hpolar
  rw [← hZ] at hen hZδ hpolar
  have hZ0 : 0 < Z := hδ.trans_le hZδ
  have hPs0 : 0 < (1 / (2 * δ) + 1 / (2 * Z)) / 2 := by positivity
  have hQs0 : 0 ≤ (1 / (2 * δ) - 1 / (2 * Z)) / 2 := by
    have : 1 / (2 * Z) ≤ 1 / (2 * δ) := one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  have hu : Continuous fun τ => (Cvs.StepA.Edge.OneOrdinateDiscriminant.rotW θ δ γ τ).re := by fun_prop
  have hv : Continuous fun τ => (Cvs.StepA.Edge.OneOrdinateDiscriminant.rotW θ δ γ τ).im := by fun_prop
  have hU : Filter.Tendsto
      (fun a => ∫ τ in (0 : ℝ)..a, (Cvs.StepA.Edge.OneOrdinateDiscriminant.rotW θ δ γ τ).re ^ 2)
      Filter.atTop (nhds ((1 / (2 * δ) + 1 / (2 * Z)) / 2)) := by
    have hlow := (((hX.const_sub 1).div_const (2 * δ)).add
      ((hX.const_sub 1).div_const (2 * Z))).div_const 2
    simp only [sub_zero] at hlow
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
      (fun a => (hen a).1) (fun a => (hen a).2.1)
  have hV : Filter.Tendsto
      (fun a => ∫ τ in (0 : ℝ)..a, (Cvs.StepA.Edge.OneOrdinateDiscriminant.rotW θ δ γ τ).im ^ 2)
      Filter.atTop (nhds ((1 / (2 * δ) - 1 / (2 * Z)) / 2)) := by
    have hlow := (((hX.const_sub 1).div_const (2 * δ)).sub
      (((tendsto_const_nhds (x := (1 : ℝ))).add hX).div_const (2 * Z))).div_const 2
    simp only [sub_zero, add_zero] at hlow
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
      (fun a => (hen a).2.2.1) (fun a => (hen a).2.2.2.1)
  have hC : Filter.Tendsto
      (fun a => ∫ τ in (0 : ℝ)..a,
        (Cvs.StepA.Edge.OneOrdinateDiscriminant.rotW θ δ γ τ).re * (Cvs.StepA.Edge.OneOrdinateDiscriminant.rotW θ δ γ τ).im)
      Filter.atTop (nhds 0) := by
    have h4 := hX.div_const (4 * Z)
    rw [zero_div] at h4
    exact squeeze_zero_norm (fun a => by rw [Real.norm_eq_abs]; exact (hen a).2.2.2.2) h4
  obtain ⟨d, hd⟩ : ∃ d : ℂ, d = c * Complex.exp (-(θ * Complex.I)) := ⟨_, rfl⟩
  have hrep : ∀ F : ℝ → ℝ, Continuous F → ∀ a : ℝ, (c * edgePair δ γ F a ^ 2).re
      = d.re * ((∫ τ in (0 : ℝ)..a, F τ * (Cvs.StepA.Edge.OneOrdinateDiscriminant.rotW θ δ γ τ).re) ^ 2
          - (∫ τ in (0 : ℝ)..a, F τ * (Cvs.StepA.Edge.OneOrdinateDiscriminant.rotW θ δ γ τ).im) ^ 2)
        - 2 * d.im * (∫ τ in (0 : ℝ)..a, F τ * (Cvs.StepA.Edge.OneOrdinateDiscriminant.rotW θ δ γ τ).re)
          * (∫ τ in (0 : ℝ)..a, F τ * (Cvs.StepA.Edge.OneOrdinateDiscriminant.rotW θ δ γ τ).im) := by
    intro F hF a
    have h2 := exp_half_mul_edgePair θ δ γ hF a
    have hc : c * edgePair δ γ F a ^ 2
        = d * (Complex.exp (θ * Complex.I / 2) * edgePair δ γ F a) ^ 2 := by
      have e : Complex.exp (θ * Complex.I / 2) ^ 2 = Complex.exp (θ * Complex.I) := by
        rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
      have e2 : Complex.exp (-(θ * Complex.I)) * Complex.exp (θ * Complex.I) = 1 := by
        rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
      rw [hd, mul_pow, e]
      linear_combination (-(c * edgePair δ γ F a ^ 2)) * e2
    rw [hc, h2]
    simp only [sq, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have h0 : (1 / (2 * δ) - 1 / (2 * Z)) / 2 = 0 → (0 : ℝ) ∈ S := by
    intro hQ
    have hγ0 : γ = 0 := by
      by_contra hγ
      have hlt := Cvs.StepA.Edge.OneOrdinateDiscriminant.lt_norm_of_ne_zero δ hγ
      rw [← hZ] at hlt
      have : 1 / (2 * Z) < 1 / (2 * δ) := one_div_lt_one_div_of_lt (by positivity) (by linarith)
      linarith
    subst hγ0
    have hFc : Continuous fun τ : ℝ => (Real.exp (δ * τ) * (τ - 1)) ^ 2 := by fun_prop
    refine (hS 0).mpr ⟨fun τ => Real.exp (δ * τ) * (τ - 1), 2, by fun_prop, ?_, ?_⟩
    · have h1 : 0 < ∫ τ in (0 : ℝ)..1, (Real.exp (δ * τ) * (τ - 1)) ^ 2 := by
        refine intervalIntegral.intervalIntegral_pos_of_pos_on (hFc.intervalIntegrable _ _)
          (fun τ hτ => ?_) one_pos
        have h := mul_neg_of_pos_of_neg (Real.exp_pos (δ * τ)) (by linarith [hτ.2] : τ - 1 < 0)
        nlinarith
      have h2 : 0 ≤ ∫ τ in (1 : ℝ)..2, (Real.exp (δ * τ) * (τ - 1)) ^ 2 :=
        intervalIntegral.integral_nonneg (by norm_num) fun τ _ => sq_nonneg _
      rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1)
        (hFc.intervalIntegrable _ _) (hFc.intervalIntegrable _ _)]
      linarith
    · have hP : edgePair δ 0 (fun τ => Real.exp (δ * τ) * (τ - 1)) 2 = 0 := by
        unfold edgePair
        have e : ∀ τ : ℝ, (((Real.exp (δ * τ) * (τ - 1) : ℝ)) : ℂ)
            * Complex.exp (-((δ : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) * τ) = ((τ - 1 : ℝ) : ℂ) := by
          intro τ
          simp only [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_sub,
            Complex.ofReal_one, Complex.ofReal_zero, zero_mul, add_zero]
          rw [mul_right_comm, ← Complex.exp_add,
            show (δ : ℂ) * τ + -δ * τ = 0 by ring, Complex.exp_zero, one_mul]
        simp_rw [e]
        rw [intervalIntegral.integral_ofReal]
        have : ∫ τ in (0 : ℝ)..2, (τ - 1) = 0 := by
          rw [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id
              intervalIntegrable_const,
            integral_id, intervalIntegral.integral_const]
          norm_num
        rw [this, Complex.ofReal_zero]
      rw [hP]
      simp
  have key := sSup_add_sInf_quad hu hv hPs0 hQs0 hU hV hC d.re d.im (T := S) (fun r => by
    rw [hS]
    constructor <;> rintro ⟨F, a, hF, hN, rfl⟩ <;> exact ⟨F, a, hF, hN, by rw [hrep F hF a]⟩) h0
  rw [key, ← hpolar]
  have hZc : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ0.ne'
  have e : c / (2 * ((Z : ℂ) * Complex.exp (θ * Complex.I))) = d / ((2 * Z : ℝ) : ℂ) := by
    rw [hd, Complex.exp_neg]
    push_cast
    field_simp
  rw [e, Complex.div_ofReal_re]
  field_simp
  ring

-- merged §3 (single-block trace); Cvs.StepA.Edge.OneOrdinateDiscriminant edgeDisc_of_sign pattern
/-- **One block**: with a single nonzero weight `c` at `i₀` the edge discriminant is the trace
`Re(c / (2(δ + i g_{i₀})))`. -/
theorem edgeDiscZ_single [DecidableEq ι] {δ : ℝ} (hδ : 0 < δ) (g : ι → ℝ) (i₀ : ι) (c : ℂ) :
    edgeDiscZ δ g (Pi.single i₀ c) = (c / (2 * ((δ : ℂ) + (g i₀ : ℂ) * Complex.I))).re := by
  unfold edgeDiscZ
  exact sSup_add_sInf_single hδ (g i₀) c fun r => by
    simp only [edgeRayZ, Set.mem_ofPred_eq, edgeFormZ_single]

/-! ### The seed bound (merged §3, Lemma Y) -/

section Seed

variable [DecidableEq ι]

/-- **The single-block lower bound**:
`edgeDiscZ v ≥ Re(v_{i₀}/(2(δ + i g_{i₀}))) − ∑_{i ≠ i₀} ‖vᵢ‖/δ`. -/
theorem edgeDiscZ_ge_single {δ : ℝ} (hδ : 0 < δ) (g : ι → ℝ) (i₀ : ι) (v : ι → ℂ) :
    (v i₀ / (2 * ((δ : ℂ) + (g i₀ : ℂ) * Complex.I))).re - (∑ i ∈ Finset.univ.erase i₀, ‖v i‖) / δ
      ≤ edgeDiscZ δ g v := by
  have h := abs_edgeDiscZ_sub_le hδ g v (Pi.single i₀ (v i₀))
  rw [edgeDiscZ_single hδ] at h
  have hs : ∑ i, ‖v i - (Pi.single i₀ (v i₀) : ι → ℂ) i‖ = ∑ i ∈ Finset.univ.erase i₀, ‖v i‖ := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
    simp only [Pi.single_eq_same, sub_self, norm_zero, zero_add]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hi), sub_zero]
  rw [hs] at h
  linarith [(abs_le.mp h).1]

-- merged §3: `gᵢ² − g_{i₀}² > 0` for `i ≠ i₀`, so the tail decays faster than the head
/-- **The large-heat comparison**: with `g_{i₀}` the strictly smallest of positive ordinates and
`m > 0`, for all large `y`,
`∑_{i ≠ i₀} m_i e^{−gᵢ² y}/δ < m_{i₀} e^{−g_{i₀}² y}/(2|δ + i g_{i₀}|)`. -/
theorem exists_seed_level {δ : ℝ} (hδ : 0 < δ) {g : ι → ℝ} (hg0 : ∀ i, 0 < g i) {i₀ : ι}
    (hmin : ∀ i ≠ i₀, g i₀ < g i) {m : ι → ℝ} (hm : ∀ i, 0 < m i) :
    ∃ Y₀ : ℝ, ∀ y ≥ Y₀, (∑ i ∈ Finset.univ.erase i₀, m i * Real.exp (-(g i ^ 2 * y))) / δ
      < m i₀ * Real.exp (-(g i₀ ^ 2 * y)) / (2 * ‖(δ : ℂ) + (g i₀ : ℂ) * Complex.I‖) := by
  set N := ‖(δ : ℂ) + (g i₀ : ℂ) * Complex.I‖ with hN
  have hNpos : 0 < N := by
    refine norm_pos_iff.mpr fun h => ?_
    have := congrArg Complex.re h
    simp at this
    linarith
  set A := m i₀ / (2 * N) with hA
  have hApos : 0 < A := div_pos (hm i₀) (by positivity)
  -- the rescaled tail `∑_{i ≠ i₀} (mᵢ/δ) e^{−(gᵢ² − g_{i₀}²) y}` tends to `0`
  have hT : Filter.Tendsto (fun y : ℝ => ∑ i ∈ Finset.univ.erase i₀,
      m i / δ * Real.exp (-((g i ^ 2 - g i₀ ^ 2) * y))) Filter.atTop (nhds 0) := by
    rw [show (0 : ℝ) = ∑ i ∈ Finset.univ.erase i₀, m i / δ * 0 by simp]
    refine tendsto_finsetSum _ fun i hi => (tendsto_const_nhds).mul ?_
    have hgap : 0 < g i ^ 2 - g i₀ ^ 2 := by
      have := hmin i (Finset.ne_of_mem_erase hi)
      nlinarith [hg0 i₀]
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.tendsto_id.const_mul_atTop hgap)
    refine this.congr fun y => ?_
    simp [Function.comp]
  obtain ⟨Y₀, hY⟩ := Filter.eventually_atTop.mp (hT.eventually (gt_mem_nhds hApos))
  refine ⟨Y₀, fun y hy => ?_⟩
  have h := hY y hy
  have he : 0 < Real.exp (-(g i₀ ^ 2 * y)) := Real.exp_pos _
  have hsplit : (∑ i ∈ Finset.univ.erase i₀, m i * Real.exp (-(g i ^ 2 * y))) / δ
      = (∑ i ∈ Finset.univ.erase i₀, m i / δ * Real.exp (-((g i ^ 2 - g i₀ ^ 2) * y)))
        * Real.exp (-(g i₀ ^ 2 * y)) := by
    rw [Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, ← Real.exp_add]
    ring_nf
  have hrhs : m i₀ * Real.exp (-(g i₀ ^ 2 * y)) / (2 * N) = A * Real.exp (-(g i₀ ^ 2 * y)) := by
    rw [hA]; ring
  rw [hsplit, hrhs]
  exact mul_lt_mul_of_pos_right h he

end Seed

end Cvs.StepA.Edge.PlanarBoxLemma
