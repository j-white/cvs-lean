/-
The Single-Atom Path Law — bounded-weight multiplication operators.

The factorization `A = C^* B` of `Cvs.PathLaw.Symmetry` needs the two weighted
operators `B = M_u M_{s₁} K_α` and `C = M_{1/u} M_{s₁}`, where
`u = √(w(z)/w(z+β))` (`schurWeight`) is the ratio of the chain weight `w` of
`Cvs.PathLaw.ThreeDistance` at the two ends of a hop. This file builds the
multiplication operator `M_g` for an arbitrary bounded measurable weight `g`,
generalising the indicator operator `maskCLM`.

Blocks leaned on:
* `MeasureTheory.eLpNorm_le_mul_eLpNorm_of_ae_le_mul` — the `L^p` bound for a
  pointwise-dominated function;
* `MeasureTheory.MemLp.toLp`, `Lp.ext` — the same construction pattern as
  `maskCLM`;
* `Nat.measurable_floor` / `Nat.measurable_ceil` — measurability of the chain
  coordinates.

Proved here (no `sorry`):
* `mulCLM` — multiplication by a bounded measurable weight, with
  `norm_mulCLM_le : ‖M_g‖ ≤ M`;
* `measurable_chainPos`, `measurable_chainBase`, `measurable_chainLength`,
  `measurable_chainWeight` — the chain weight is measurable, hence a legitimate
  multiplier.
-/
import Cvs.PathLaw.Symmetry
import Cvs.PathLaw.ThreeDistance

open MeasureTheory Real

namespace Cvs.PathLaw

/-! ### Multiplication by a bounded measurable weight -/

variable {X : Type*} [MeasurableSpace X] [Nonempty X]

omit [Nonempty X] in
/-- A bounded measurable multiple of an `L²` function is `L²`. -/
theorem memLp_mul (μ : Measure X) (g : X → ℝ) (hg : Measurable g) {M : ℝ}
    (hM : ∀ x, |g x| ≤ M) (f : Lp ℝ 2 μ) :
    MemLp (fun x => g x * (f : X → ℝ) x) 2 μ := by
  have hmeas : AEStronglyMeasurable (fun x => g x * (f : X → ℝ) x) μ :=
    hg.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)
  have hae : ∀ᵐ x ∂μ, ‖g x * (f : X → ℝ) x‖ ≤ M * ‖(f : X → ℝ) x‖ := by
    filter_upwards with x
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)
  have hle := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hmeas hae 2
  exact lt_of_le_of_lt hle
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.eLpNorm_lt_top f))

/-- The pointwise product `g · f` as an `L²` element. -/
noncomputable def mulFun (μ : Measure X) (g : X → ℝ) (hg : Measurable g) {M : ℝ}
    (hM : ∀ x, |g x| ≤ M) (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  MemLp.toLp _ (memLp_mul μ g hg hM f)

omit [Nonempty X] in
lemma coeFn_mulFun (μ : Measure X) (g : X → ℝ) (hg : Measurable g) {M : ℝ}
    (hM : ∀ x, |g x| ≤ M) (f : Lp ℝ 2 μ) :
    (mulFun μ g hg hM f : X → ℝ) =ᵐ[μ] fun x => g x * (f : X → ℝ) x :=
  MemLp.coeFn_toLp _

set_option maxHeartbeats 800000 in
/-- Multiplication by a bounded measurable weight, as a linear map on `L²`. -/
noncomputable def mulₗ (μ : Measure X) (g : X → ℝ) (hg : Measurable g) {M : ℝ}
    (hM : ∀ x, |g x| ≤ M) : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ where
  toFun := mulFun μ g hg hM
  map_add' f₁ f₂ := by
    apply Lp.ext
    filter_upwards [coeFn_mulFun μ g hg hM (f₁ + f₂),
      Lp.coeFn_add (mulFun μ g hg hM f₁) (mulFun μ g hg hM f₂),
      coeFn_mulFun μ g hg hM f₁, coeFn_mulFun μ g hg hM f₂,
      Lp.coeFn_add f₁ f₂] with x h1 h2 h3 h4 h5
    rw [h1, h2, Pi.add_apply, h3, h4, h5, Pi.add_apply]
    ring
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [coeFn_mulFun μ g hg hM (c • f),
      Lp.coeFn_smul c (mulFun μ g hg hM f),
      coeFn_mulFun μ g hg hM f, Lp.coeFn_smul c f] with x h1 h2 h3 h4
    rw [RingHom.id_apply, h1, h2, Pi.smul_apply, h3, h4, Pi.smul_apply]
    simp [mul_left_comm]

theorem norm_mulₗ_le (μ : Measure X) (g : X → ℝ) (hg : Measurable g) {M : ℝ}
    (hM : ∀ x, |g x| ≤ M) (f : Lp ℝ 2 μ) :
    ‖mulₗ μ g hg hM f‖ ≤ M * ‖f‖ := by
  have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (hM (Classical.arbitrary X))
  have h1 : ‖mulFun μ g hg hM f‖
      = (eLpNorm (fun x => g x * (f : X → ℝ) x) 2 μ).toReal := Lp.norm_toLp _ _
  show ‖mulFun μ g hg hM f‖ ≤ M * ‖f‖
  rw [h1, Lp.norm_def]
  have hae : ∀ᵐ x ∂μ, ‖g x * (f : X → ℝ) x‖ ≤ M * ‖(f : X → ℝ) x‖ := by
    filter_upwards with x
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)
  have hle := eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    (hg.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)) hae 2
  calc (eLpNorm (fun x => g x * (f : X → ℝ) x) 2 μ).toReal
      ≤ (ENNReal.ofReal M * eLpNorm (f : X → ℝ) 2 μ).toReal :=
        ENNReal.toReal_mono
          (by
            refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
            exact Lp.eLpNorm_ne_top f)
          hle
    _ = M * (eLpNorm (f : X → ℝ) 2 μ).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hMnn]

/-- Multiplication by a bounded measurable weight, as a bounded operator. -/
noncomputable def mulCLM (μ : Measure X) (g : X → ℝ) (hg : Measurable g) {M : ℝ}
    (hM : ∀ x, |g x| ≤ M) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  LinearMap.mkContinuous (mulₗ μ g hg hM) M (norm_mulₗ_le μ g hg hM)

theorem norm_mulCLM_le (μ : Measure X) (g : X → ℝ) (hg : Measurable g)
    {M : ℝ} (hM : ∀ x, |g x| ≤ M) : ‖mulCLM μ g hg hM‖ ≤ M :=
  LinearMap.mkContinuous_norm_le _
    (le_trans (abs_nonneg _) (hM (Classical.arbitrary X))) _

lemma coeFn_mulCLM (μ : Measure X) (g : X → ℝ) (hg : Measurable g) {M : ℝ}
    (hM : ∀ x, |g x| ≤ M) (f : Lp ℝ 2 μ) :
    (mulCLM μ g hg hM f : X → ℝ) =ᵐ[μ] fun x => g x * (f : X → ℝ) x :=
  coeFn_mulFun μ g hg hM f

/-! ### The chain weight is a legitimate multiplier -/

theorem measurable_chainPos (β : ℝ) : Measurable (chainPos β) :=
  Nat.measurable_floor.comp (measurable_id.div_const β)

theorem measurable_chainBase (β : ℝ) : Measurable (chainBase β) := by
  unfold chainBase
  exact measurable_id.sub ((measurable_from_top.comp (measurable_chainPos β) : Measurable (fun x => ((chainPos β x : ℕ) : ℝ))).mul_const β)

theorem measurable_chainLength (β : ℝ) :
    Measurable (fun x => chainLength β (chainBase β x)) := by
  unfold chainLength
  exact Nat.measurable_ceil.comp
    (((measurable_const.sub (measurable_chainBase β)).div_const β))

/-- The chain weight is measurable, hence multiplication by it
is a bounded operator on `L²`. -/
theorem measurable_chainWeight (β : ℝ) : Measurable (chainWeight β) := by
  unfold chainWeight
  refine Real.measurable_sin.comp ?_
  have hp : Measurable (fun x => ((chainPos β x : ℕ) : ℝ)) :=
    measurable_from_top.comp (measurable_chainPos β)
  have hl : Measurable (fun x => ((chainLength β (chainBase β x) : ℕ) : ℝ)) :=
    measurable_from_top.comp (measurable_chainLength β)
  exact ((hp.add_const 1).mul_const π).div (hl.add_const 1)

/-! ### The chain weight on the circle

Transporting the chain weight from `[0,1)` to `𝕋 = ℝ/ℤ` via Mathlib's
`AddCircle.equivIco`. All the properties needed to make it a Schur multiplier
— measurable, bounded above, bounded below by a positive constant — descend
directly from the corresponding facts on `[0,1)`. -/

/-- The canonical representative of `z ∈ 𝕋` in `[0,1)`. -/
noncomputable def rep (z : AddCircle (1 : ℝ)) : ℝ :=
  ((AddCircle.equivIco (1 : ℝ) 0 z : Set.Ico (0:ℝ) (0+1)) : ℝ)

theorem rep_nonneg (z : AddCircle (1 : ℝ)) : 0 ≤ rep z :=
  (Set.mem_Ico.mp (AddCircle.equivIco (1 : ℝ) 0 z).2).1

theorem rep_lt_one (z : AddCircle (1 : ℝ)) : rep z < 1 := by
  have h := (Set.mem_Ico.mp (AddCircle.equivIco (1 : ℝ) 0 z).2).2
  unfold rep
  linarith

theorem measurable_rep : Measurable rep :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco (T := (1:ℝ)) 0).measurable

/-- The chain weight, transported to the circle. -/
noncomputable def circleWeight (β : ℝ) (z : AddCircle (1 : ℝ)) : ℝ :=
  chainWeight β (rep z)

theorem circleWeight_pos (β : ℝ) (hβ : 0 < β) (z : AddCircle (1 : ℝ)) :
    0 < circleWeight β z :=
  chainWeight_pos β _ hβ (rep_lt_one z)

theorem circleWeight_le_one (β : ℝ) (z : AddCircle (1 : ℝ)) :
    circleWeight β z ≤ 1 :=
  chainWeight_le_one β _

/-- **The circle weight is bounded away from zero**, so its reciprocal is a
bounded multiplier. -/
theorem circleWeight_ge (β : ℝ) (hβ : 0 < β) (z : AddCircle (1 : ℝ)) :
    Real.sin (π / ((capacity 1 β : ℝ) + 1)) ≤ circleWeight β z :=
  chainWeight_ge_capacity β _ hβ (rep_nonneg z) (rep_lt_one z)

theorem measurable_circleWeight (β : ℝ) : Measurable (circleWeight β) :=
  (measurable_chainWeight β).comp measurable_rep

/-- The circle weight is a bounded multiplier: `|w| ≤ 1`. -/
theorem abs_circleWeight_le_one (β : ℝ) (hβ : 0 < β) (z : AddCircle (1 : ℝ)) :
    |circleWeight β z| ≤ 1 := by
  rw [abs_of_pos (circleWeight_pos β hβ z)]
  exact circleWeight_le_one β z

/-- Multiplication by the chain weight, as a bounded operator on `L²(𝕋)`. -/
noncomputable def weightCLM (β : ℝ) (hβ : 0 < β) :
    Lp ℝ 2 (volume : Measure (AddCircle (1 : ℝ))) →L[ℝ]
      Lp ℝ 2 (volume : Measure (AddCircle (1 : ℝ))) :=
  mulCLM volume (circleWeight β) (measurable_circleWeight β)
    (abs_circleWeight_le_one β hβ)

theorem norm_weightCLM_le (β : ℝ) (hβ : 0 < β) : ‖weightCLM β hβ‖ ≤ 1 :=
  norm_mulCLM_le _ _ _ _

/-! ### The Schur factorization operators

The atom half factors as `A = C^* B` with

    B = M_u ∘ M_{s₁} ∘ K_α,      C = M_{1/u} ∘ M_{s₁}

for *any* strictly positive bounded weight `u` with bounded reciprocal: the
weight cancels in the inner product `⟪B x, C x⟫`, while in `‖B x‖² + ‖C x‖²`
it survives as the AM-GM weight. Choosing `u` from the chain weight is what
will produce the Chebyshev constant. -/

local notation "L2c" => Lp ℝ 2 (volume : Measure (AddCircle (1 : ℝ)))

omit [Nonempty X] in
/-- The mask operator is idempotent. -/
theorem maskCLM_idem (μ : Measure X) (s : Set X) (hs : MeasurableSet s)
    (f : Lp ℝ 2 μ) :
    maskCLM μ s hs (maskCLM μ s hs f) = maskCLM μ s hs f := by
  apply Lp.ext
  filter_upwards [coeFn_maskCLM μ s hs (maskCLM μ s hs f),
    coeFn_maskCLM μ s hs f] with x h1 h2
  rw [h1]
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, h2, Set.indicator_of_notMem hx]

/-- **The weight cancels in the inner product.** Multiplying one argument by a
positive weight and the other by its reciprocal leaves `⟪·,·⟫` unchanged. -/
theorem inner_mulCLM_inv (μ : Measure X) (u : X → ℝ) (hu : Measurable u)
    (hupos : ∀ x, 0 < u x) {M N : ℝ} (hM : ∀ x, |u x| ≤ M)
    (hN : ∀ x, |(u x)⁻¹| ≤ N) (f g : Lp ℝ 2 μ) :
    inner ℝ (mulCLM μ u hu hM f)
        (mulCLM μ (fun x => (u x)⁻¹) hu.inv hN g)
      = inner ℝ f g := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_mulCLM μ u hu hM f,
    coeFn_mulCLM μ (fun x => (u x)⁻¹) hu.inv hN g] with x h1 h2
  rw [RCLike.inner_apply, RCLike.inner_apply, h1, h2]
  have hne : u x ≠ 0 := ne_of_gt (hupos x)
  simp only [starRingEnd_apply, star_trivial]
  field_simp

variable {P : ℝ}

/-- With a mask on both arguments, one mask is redundant. -/
theorem inner_maskCLM_both {Q : ℝ} [Fact (0 < Q)] (s : Set (AddCircle Q))
    (hs : MeasurableSet s)
    (f g : Lp ℝ 2 (volume : Measure (AddCircle Q))) :
    inner ℝ (maskCLM volume s hs f) (maskCLM volume s hs g)
      = inner ℝ (maskCLM volume s hs f) g := by
  rw [← inner_maskCLM_left, maskCLM_idem]

/-- The first Schur factor `B = M_u ∘ M_{s₁} ∘ K_α`. -/
noncomputable def factorB (u : AddCircle (1 : ℝ) → ℝ) (hu : Measurable u) {M : ℝ}
    (hM : ∀ x, |u x| ≤ M) (a : AddCircle (1 : ℝ)) (s₁ : Set (AddCircle (1 : ℝ)))
    (h₁ : MeasurableSet s₁) : L2c →L[ℝ] L2c :=
  (mulCLM volume u hu hM).comp
    ((maskCLM volume s₁ h₁).comp (koopman a).toContinuousLinearMap)

/-- The second Schur factor `C = M_{1/u} ∘ M_{s₁}`. -/
noncomputable def factorC (u : AddCircle (1 : ℝ) → ℝ) (hu : Measurable u) {N : ℝ}
    (hN : ∀ x, |(u x)⁻¹| ≤ N) (s₁ : Set (AddCircle (1 : ℝ)))
    (h₁ : MeasurableSet s₁) : L2c →L[ℝ] L2c :=
  (mulCLM volume (fun x => (u x)⁻¹) hu.inv hN).comp (maskCLM volume s₁ h₁)

/-- **The factorization identity.** `⟪A x, x⟫ = ⟪B x, C x⟫` — exactly the
hypothesis `hfac` of `pathLaw_le_of_factorization`, now discharged for every
strictly positive bounded weight with bounded reciprocal. -/
theorem inner_atomHalf_eq (u : AddCircle (1 : ℝ) → ℝ) (hu : Measurable u)
    (hupos : ∀ x, 0 < u x) {M N : ℝ} (hM : ∀ x, |u x| ≤ M)
    (hN : ∀ x, |(u x)⁻¹| ≤ N) (a : AddCircle (1 : ℝ))
    (s₁ : Set (AddCircle (1 : ℝ))) (h₁ : MeasurableSet s₁) (x : L2c) :
    inner ℝ (atomHalf a s₁ h₁ x) x
      = inner ℝ (factorB u hu hM a s₁ h₁ x) (factorC u hu hN s₁ h₁ x) := by
  show inner ℝ (maskCLM volume s₁ h₁ (koopman a x)) x
      = inner ℝ (mulCLM volume u hu hM (maskCLM volume s₁ h₁ (koopman a x)))
          (mulCLM volume (fun y => (u y)⁻¹) hu.inv hN (maskCLM volume s₁ h₁ x))
  rw [inner_mulCLM_inv volume u hu hupos hM hN, inner_maskCLM_both]

/-! ### The masks in chain coordinates

The chain through a point is cut exactly where the orbit wraps past `1`. So
the forward hop `z ↦ z + β` stays inside the chain precisely when
`rep z + β < 1`, and the backward hop precisely when `β ≤ rep z`. These two
sets are the paper's masks, and they satisfy the `MaskShift` condition that
makes `W` symmetric. -/

theorem coe_rep (z : AddCircle (1 : ℝ)) : ((rep z : ℝ) : AddCircle (1 : ℝ)) = z :=
  AddCircle.coe_equivIco

theorem rep_coe (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    rep ((y : AddCircle (1 : ℝ))) = y := by
  unfold rep
  rw [AddCircle.equivIco_coe_of_mem (by exact Set.mem_Ico.mpr ⟨hy0, by linarith⟩)]

/-- No wraparound: the representative advances by `β`. -/
theorem rep_add_step (β : ℝ) (z : AddCircle (1 : ℝ)) (hβ : 0 ≤ β)
    (h : rep z + β < 1) :
    rep (z + (β : AddCircle (1 : ℝ))) = rep z + β := by
  have hz : z + (β : AddCircle (1 : ℝ)) = ((rep z + β : ℝ) : AddCircle (1 : ℝ)) := by
    rw [AddCircle.coe_add, coe_rep z]
  rw [hz, rep_coe _ (by linarith [rep_nonneg z]) h]

/-- Wraparound: subtracting `β` from a point below `β` lands `1 - β` higher. -/
theorem rep_sub_wrap (β : ℝ) (z : AddCircle (1 : ℝ)) (hβ1 : β ≤ 1)
    (h : rep z < β) :
    rep (z - (β : AddCircle (1 : ℝ))) = rep z - β + 1 := by
  have hz : z - (β : AddCircle (1 : ℝ))
      = ((rep z - β + 1 : ℝ) : AddCircle (1 : ℝ)) := by
    rw [AddCircle.coe_add_period, AddCircle.coe_sub, coe_rep z]
  rw [hz, rep_coe _ (by linarith [rep_nonneg z]) (by linarith [rep_lt_one z])]

/-- No wraparound in the backward direction. -/
theorem rep_sub_step (β : ℝ) (z : AddCircle (1 : ℝ)) (hβ : 0 ≤ β)
    (h : β ≤ rep z) :
    rep (z - (β : AddCircle (1 : ℝ))) = rep z - β := by
  have hz : z - (β : AddCircle (1 : ℝ)) = ((rep z - β : ℝ) : AddCircle (1 : ℝ)) := by
    rw [AddCircle.coe_sub, coe_rep z]
  rw [hz, rep_coe _ (by linarith) (by linarith [rep_lt_one z])]

/-- The forward mask: the hop `z ↦ z + β` stays inside the chain. -/
def maskFwd (β : ℝ) : Set (AddCircle (1 : ℝ)) := {z | rep z + β < 1}

/-- The backward mask: the hop `z ↦ z - β` stays inside the chain. -/
def maskBwd (β : ℝ) : Set (AddCircle (1 : ℝ)) := {z | β ≤ rep z}

theorem measurableSet_maskFwd (β : ℝ) : MeasurableSet (maskFwd β) := by
  have : maskFwd β = rep ⁻¹' (Set.Iio (1 - β)) := by
    ext z
    simp [maskFwd, Set.mem_Iio]
    constructor <;> intro h <;> linarith
  rw [this]
  exact measurable_rep measurableSet_Iio

theorem measurableSet_maskBwd (β : ℝ) : MeasurableSet (maskBwd β) := by
  have : maskBwd β = rep ⁻¹' (Set.Ici β) := rfl
  rw [this]
  exact measurable_rep measurableSet_Ici

/-- **The masks satisfy the shift condition**, so the masked rotation built
from them is symmetric (`isSymmetric_maskedRotation`). -/
theorem maskShift_fwd_bwd (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    MaskShift ((β : ℝ) : AddCircle (1 : ℝ)) (maskFwd β) (maskBwd β) := by
  unfold MaskShift
  ext z
  simp only [Set.mem_preimage, maskFwd, maskBwd, Set.mem_ofPred_eq]
  constructor
  · intro hz
    have hsub : rep (z + -(β : AddCircle (1 : ℝ))) = rep z - β := by
      rw [← sub_eq_add_neg]
      exact rep_sub_step β z hβ0 hz
    rw [hsub]
    linarith [rep_lt_one z]
  · intro hz
    by_contra hcon
    push Not at hcon
    have hsub : rep (z + -(β : AddCircle (1 : ℝ))) = rep z - β + 1 := by
      rw [← sub_eq_add_neg]
      exact rep_sub_wrap β z hβ1 hcon
    rw [hsub] at hz
    linarith [rep_nonneg z]

/-! ### The Schur weight

The weight that makes the factorization's bracket match the pointwise bound
`chainWeight_schur` is `u(z) = √(w(z)/w(z+β))`: then `u(z)⁻² = w(z+β)/w(z)`
carries the forward neighbour and `u(z-β)² = w(z-β)/w(z)` the backward one. -/

/-- The lower bound on the circle weight, as a constant. -/
noncomputable def wLow (β : ℝ) : ℝ := Real.sin (π / ((capacity 1 β : ℝ) + 1))

theorem wLow_le_circleWeight (β : ℝ) (hβ : 0 < β) (z : AddCircle (1 : ℝ)) :
    wLow β ≤ circleWeight β z := circleWeight_ge β hβ z

/-- The circle weight's lower bound is genuinely positive. -/
theorem wLow_pos (β : ℝ) (hβ : 0 < β) : 0 < wLow β := by
  unfold wLow
  have hcap : 0 < capacity 1 β := by
    unfold capacity
    rw [Nat.ceil_pos]
    positivity
  have hc1 : (1 : ℝ) ≤ (capacity 1 β : ℝ) := by exact_mod_cast hcap
  refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [pi_pos]

/-- The Schur weight `u(z) = √(w(z)/w(z+β))`. -/
noncomputable def schurWeight (β : ℝ) (z : AddCircle (1 : ℝ)) : ℝ :=
  Real.sqrt (circleWeight β z / circleWeight β (z + ((β : ℝ) : AddCircle (1 : ℝ))))

theorem schurWeight_pos (β : ℝ) (hβ : 0 < β) (z : AddCircle (1 : ℝ)) :
    0 < schurWeight β z := by
  unfold schurWeight
  exact Real.sqrt_pos.mpr
    (div_pos (circleWeight_pos β hβ z) (circleWeight_pos β hβ _))

theorem measurable_schurWeight (β : ℝ) : Measurable (schurWeight β) := by
  unfold schurWeight
  exact Real.continuous_sqrt.measurable.comp
    ((measurable_circleWeight β).div
      ((measurable_circleWeight β).comp (measurable_add_const _)))

/-- The Schur weight is bounded above by `√(1/w_low)`. -/
theorem schurWeight_le (β : ℝ) (hβ : 0 < β) (hlow : 0 < wLow β)
    (z : AddCircle (1 : ℝ)) :
    schurWeight β z ≤ Real.sqrt (1 / wLow β) := by
  unfold schurWeight
  apply Real.sqrt_le_sqrt
  rw [div_le_div_iff₀ (circleWeight_pos β hβ _) hlow]
  have h1 : circleWeight β z ≤ 1 := circleWeight_le_one β z
  have h2 : wLow β ≤ circleWeight β (z + ((β : ℝ) : AddCircle (1 : ℝ))) :=
    wLow_le_circleWeight β hβ _
  nlinarith [circleWeight_pos β hβ (z + ((β : ℝ) : AddCircle (1 : ℝ)))]

/-- The Schur weight is bounded below by `√(w_low)`, so its reciprocal is
bounded above by `√(1/w_low)` as well. -/
theorem schurWeight_ge (β : ℝ) (hβ : 0 < β) (hlow : 0 < wLow β)
    (z : AddCircle (1 : ℝ)) :
    Real.sqrt (wLow β) ≤ schurWeight β z := by
  unfold schurWeight
  apply Real.sqrt_le_sqrt
  rw [le_div_iff₀ (circleWeight_pos β hβ _)]
  have h1 : circleWeight β (z + ((β : ℝ) : AddCircle (1 : ℝ))) ≤ 1 :=
    circleWeight_le_one β _
  have h2 : wLow β ≤ circleWeight β z := wLow_le_circleWeight β hβ z
  nlinarith [hlow]

theorem abs_schurWeight_le (β : ℝ) (hβ : 0 < β) (hlow : 0 < wLow β)
    (z : AddCircle (1 : ℝ)) : |schurWeight β z| ≤ Real.sqrt (1 / wLow β) := by
  rw [abs_of_pos (schurWeight_pos β hβ z)]
  exact schurWeight_le β hβ hlow z

theorem abs_inv_schurWeight_le (β : ℝ) (hβ : 0 < β) (hlow : 0 < wLow β)
    (z : AddCircle (1 : ℝ)) :
    |(schurWeight β z)⁻¹| ≤ Real.sqrt (1 / wLow β) := by
  rw [abs_of_pos (inv_pos.mpr (schurWeight_pos β hβ z))]
  have hs : Real.sqrt (1 / wLow β) = (Real.sqrt (wLow β))⁻¹ := by
    rw [one_div, Real.sqrt_inv]
  rw [hs, inv_le_inv₀ (schurWeight_pos β hβ z) (Real.sqrt_pos.mpr hlow)]
  exact schurWeight_ge β hβ hlow z

/-! ### Commuting a multiplier past the rotation

`M_h ∘ K_a = K_a ∘ M_{h(·-a)}`. Because `K_a` is an isometry this converts
`‖M_h (K_a x)‖` into `‖M_{h(·-a)} x‖` with no change of variables in sight —
the translation is absorbed by the Koopman operator. -/

theorem mulCLM_comp_maskCLM (μ : Measure X) (g : X → ℝ) (hg : Measurable g)
    {M : ℝ} (hM : ∀ x, |g x| ≤ M) (s : Set X) (hs : MeasurableSet s)
    (hMs : ∀ x, |s.indicator g x| ≤ M) (f : Lp ℝ 2 μ) :
    mulCLM μ g hg hM (maskCLM μ s hs f)
      = mulCLM μ (s.indicator g) (hg.indicator hs) hMs f := by
  apply Lp.ext
  filter_upwards [coeFn_mulCLM μ g hg hM (maskCLM μ s hs f),
    coeFn_maskCLM μ s hs f,
    coeFn_mulCLM μ (s.indicator g) (hg.indicator hs) hMs f] with x h1 h2 h3
  rw [h1, h2, h3]
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    ring

/-- Shifting a multiplier past the Koopman operator. -/
theorem mulCLM_koopman (h : AddCircle (1 : ℝ) → ℝ) (hh : Measurable h) {M : ℝ}
    (hM : ∀ z, |h z| ≤ M) (a : AddCircle (1 : ℝ))
    (hMs : ∀ z, |h (z - a)| ≤ M) (f : L2c) :
    mulCLM volume h hh hM (koopman a f)
      = koopman a (mulCLM volume (fun z => h (z - a))
          (hh.comp (measurable_sub_const a)) hMs f) := by
  apply Lp.ext
  filter_upwards [coeFn_mulCLM volume h hh hM (koopman a f),
    koopman_ae a f,
    koopman_ae a (mulCLM volume (fun z => h (z - a))
      (hh.comp (measurable_sub_const a)) hMs f),
    ae_translate a (coeFn_mulCLM volume (fun z => h (z - a))
      (hh.comp (measurable_sub_const a)) hMs f)] with z h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  simp

/-- **Norm transfer.** `‖M_h (K_a x)‖ = ‖M_{h(·-a)} x‖`: the rotation is an
isometry, so the shift costs nothing. -/
theorem norm_mulCLM_koopman (h : AddCircle (1 : ℝ) → ℝ) (hh : Measurable h)
    {M : ℝ} (hM : ∀ z, |h z| ≤ M) (a : AddCircle (1 : ℝ))
    (hMs : ∀ z, |h (z - a)| ≤ M) (f : L2c) :
    ‖mulCLM volume h hh hM (koopman a f)‖
      = ‖mulCLM volume (fun z => h (z - a))
          (hh.comp (measurable_sub_const a)) hMs f‖ := by
  rw [mulCLM_koopman h hh hM a hMs f]
  exact (koopman a).norm_map _

/-! ### The norm bound

`‖M_g f‖² = ∫ g² f²`, and the integrability comes for free from the fact that
`M_g f` is itself an `L²` element — no domination argument needed. -/

theorem norm_sq_mulCLM (g : AddCircle (1 : ℝ) → ℝ) (hg : Measurable g) {M : ℝ}
    (hM : ∀ z, |g z| ≤ M) (f : L2c) :
    ‖mulCLM volume g hg hM f‖ ^ 2
      = ∫ z, (g z) ^ 2 * (f : AddCircle (1 : ℝ) → ℝ) z ^ 2 := by
  rw [norm_sq_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_mulCLM volume g hg hM f] with z hz
  rw [hz]
  ring

theorem integrable_sq_mulCLM (g : AddCircle (1 : ℝ) → ℝ) (hg : Measurable g)
    {M : ℝ} (hM : ∀ z, |g z| ≤ M) (f : L2c) :
    Integrable (fun z => (g z) ^ 2 * (f : AddCircle (1 : ℝ) → ℝ) z ^ 2) volume := by
  have h := MemLp.integrable_sq (Lp.memLp (mulCLM volume g hg hM f))
  refine h.congr ?_
  filter_upwards [coeFn_mulCLM volume g hg hM f] with z hz
  rw [hz]
  ring

/-- **The factorization norm bound from a pointwise inequality.** -/
theorem norm_sq_factor_add_le (u : AddCircle (1 : ℝ) → ℝ) (hu : Measurable u)
    {M N : ℝ} (hM : ∀ z, |u z| ≤ M) (hN : ∀ z, |(u z)⁻¹| ≤ N)
    (a : AddCircle (1 : ℝ)) (s₁ : Set (AddCircle (1 : ℝ)))
    (h₁ : MeasurableSet s₁)
    (hMi : ∀ z, |s₁.indicator u z| ≤ M)
    (hMs : ∀ z, |s₁.indicator u (z - a)| ≤ M)
    (hNi : ∀ z, |s₁.indicator (fun y => (u y)⁻¹) z| ≤ N)
    (K : ℝ)
    (hpt : ∀ z, (s₁.indicator u (z - a)) ^ 2
        + (s₁.indicator (fun y => (u y)⁻¹) z) ^ 2 ≤ K)
    (x : L2c) :
    ‖factorB u hu hM a s₁ h₁ x‖ ^ 2 + ‖factorC u hu hN s₁ h₁ x‖ ^ 2
      ≤ K * ‖x‖ ^ 2 := by
  classical
  set gB : AddCircle (1 : ℝ) → ℝ := fun z => s₁.indicator u (z - a) with hgB
  set gC : AddCircle (1 : ℝ) → ℝ := s₁.indicator (fun y => (u y)⁻¹) with hgC
  have hgBm : Measurable gB := (hu.indicator h₁).comp (measurable_sub_const a)
  have hgCm : Measurable gC := (hu.inv).indicator h₁
  -- rewrite both norms
  have hB : ‖factorB u hu hM a s₁ h₁ x‖ ^ 2
      = ∫ z, (gB z) ^ 2 * (x : AddCircle (1 : ℝ) → ℝ) z ^ 2 := by
    show ‖mulCLM volume u hu hM (maskCLM volume s₁ h₁ (koopman a x))‖ ^ 2 = _
    rw [mulCLM_comp_maskCLM volume u hu hM s₁ h₁ hMi,
      norm_mulCLM_koopman (s₁.indicator u) (hu.indicator h₁) hMi a hMs,
      norm_sq_mulCLM]
  have hC : ‖factorC u hu hN s₁ h₁ x‖ ^ 2
      = ∫ z, (gC z) ^ 2 * (x : AddCircle (1 : ℝ) → ℝ) z ^ 2 := by
    show ‖mulCLM volume (fun y => (u y)⁻¹) hu.inv hN (maskCLM volume s₁ h₁ x)‖ ^ 2 = _
    rw [mulCLM_comp_maskCLM volume (fun y => (u y)⁻¹) hu.inv hN s₁ h₁ hNi,
      norm_sq_mulCLM]
  rw [hB, hC, norm_sq_eq_integral, ← integral_add
    (integrable_sq_mulCLM gB hgBm hMs x) (integrable_sq_mulCLM gC hgCm hNi x),
    ← integral_const_mul]
  refine integral_mono ?_ ?_ ?_
  · exact (integrable_sq_mulCLM gB hgBm hMs x).add
      (integrable_sq_mulCLM gC hgCm hNi x)
  · exact (MemLp.integrable_sq (Lp.memLp x)).const_mul K
  · intro z
    have hx2 : (0 : ℝ) ≤ (x : AddCircle (1 : ℝ) → ℝ) z ^ 2 := sq_nonneg _
    have := hpt z
    nlinarith [this, hx2]

/-! ### The pointwise hypothesis, verified for the Schur weight

Unwinding `(√(w/w'))²` back to the weight ratio turns the abstract pointwise
hypothesis of `norm_sq_factor_add_le` into exactly `chainWeight_schur`. -/

private lemma indicator_sq {α : Type*} (s : Set α) (g : α → ℝ) (y : α) :
    (s.indicator g y) ^ 2 = s.indicator (fun t => (g t) ^ 2) y := by
  by_cases h : y ∈ s
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
    ring

theorem schurWeight_sq (β : ℝ) (hβ : 0 < β) (z : AddCircle (1 : ℝ)) :
    (schurWeight β z) ^ 2
      = circleWeight β z / circleWeight β (z + ((β : ℝ) : AddCircle (1 : ℝ))) := by
  unfold schurWeight
  exact Real.sq_sqrt
    (le_of_lt (div_pos (circleWeight_pos β hβ z) (circleWeight_pos β hβ _)))

theorem inv_schurWeight_sq (β : ℝ) (hβ : 0 < β) (z : AddCircle (1 : ℝ)) :
    ((schurWeight β z)⁻¹) ^ 2
      = circleWeight β (z + ((β : ℝ) : AddCircle (1 : ℝ))) / circleWeight β z := by
  rw [inv_pow, schurWeight_sq β hβ z, inv_div]

/-- Membership in the shifted forward mask is the backward condition. -/
theorem sub_mem_maskFwd_iff (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (z : AddCircle (1 : ℝ)) :
    z - ((β : ℝ) : AddCircle (1 : ℝ)) ∈ maskFwd β ↔ β ≤ rep z := by
  have h := maskShift_fwd_bwd β hβ0 hβ1
  unfold MaskShift at h
  constructor
  · intro hz
    have : z ∈ maskBwd β := by
      rw [h]
      simpa [sub_eq_add_neg] using hz
    exact this
  · intro hz
    have hzb : z ∈ maskBwd β := hz
    rw [h] at hzb
    simpa [sub_eq_add_neg] using hzb

/-- **The pointwise hypothesis of `norm_sq_factor_add_le`, verified.** -/
theorem schur_pointwise (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) (m : ℕ)
    (z : AddCircle (1 : ℝ))
    (hm : chainLength β (chainBase β (rep z)) ≤ m) :
    ((maskFwd β).indicator (schurWeight β)
        (z - ((β : ℝ) : AddCircle (1 : ℝ)))) ^ 2
      + ((maskFwd β).indicator (fun y => (schurWeight β y)⁻¹) z) ^ 2
      ≤ chebFactor m := by
  set bc := ((β : ℝ) : AddCircle (1 : ℝ)) with hbc
  set r := rep z with hr
  have hr0 : 0 ≤ r := rep_nonneg z
  have hr1 : r < 1 := rep_lt_one z
  have hwz : circleWeight β z = chainWeight β r := rfl
  have hwpos : 0 < chainWeight β r := chainWeight_pos β r hβ hr1
  -- first term
  have hT1 : ((maskFwd β).indicator (schurWeight β) (z - bc)) ^ 2
      = (if β ≤ r then chainWeight β (r - β) else 0) / chainWeight β r := by
    rw [indicator_sq]
    by_cases hb : β ≤ r
    · have hmem : z - bc ∈ maskFwd β :=
        (sub_mem_maskFwd_iff β hβ.le hβ1 z).mpr hb
      rw [Set.indicator_of_mem hmem, ite_eq_left hb, schurWeight_sq β hβ]
      refine congrArg₂ (· / ·) ?_ ?_
      · show circleWeight β (z - bc) = chainWeight β (r - β)
        unfold circleWeight
        rw [rep_sub_step β z hβ.le hb]
      · show circleWeight β (z - bc + bc) = chainWeight β r
        rw [sub_add_cancel]
        exact hwz
    · have hmem : z - bc ∉ maskFwd β := by
        intro hc
        exact hb ((sub_mem_maskFwd_iff β hβ.le hβ1 z).mp hc)
      rw [Set.indicator_of_notMem hmem, ite_eq_right hb, zero_div]
  -- second term
  have hT2 : ((maskFwd β).indicator (fun y => (schurWeight β y)⁻¹) z) ^ 2
      = (if r + β < 1 then chainWeight β (r + β) else 0) / chainWeight β r := by
    rw [indicator_sq]
    by_cases hf : r + β < 1
    · have hmem : z ∈ maskFwd β := hf
      rw [Set.indicator_of_mem hmem, ite_eq_left hf, inv_schurWeight_sq β hβ]
      refine congrArg (· / chainWeight β r) ?_
      show circleWeight β (z + bc) = chainWeight β (r + β)
      unfold circleWeight
      rw [rep_add_step β z hβ.le hf]
    · have hmem : z ∉ maskFwd β := hf
      rw [Set.indicator_of_notMem hmem, ite_eq_right hf, zero_div]
  rw [hT1, hT2, ← add_div, div_le_iff₀ hwpos]
  have hs := chainWeight_schur β r hβ hr0 hr1 m hm
  linarith [hs]

/-! ### The Path Law upper bound, closed

Every hypothesis of `pathLaw_le_of_factorization` is now available for the
paper's actual operator, so the chain estimate follows. -/

private lemma abs_indicator_le {α : Type*} (s : Set α) (g : α → ℝ) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ y, |g y| ≤ M) (y : α) : |s.indicator g y| ≤ M := by
  by_cases h : y ∈ s
  · rw [Set.indicator_of_mem h]; exact hM y
  · rw [Set.indicator_of_notMem h]; simpa using hM0

/-- The masked rotation built from the paper's geometry: rotation by `β` with
the forward/backward chain masks. -/
noncomputable def pathLawW (β : ℝ) : L2c →L[ℝ] L2c :=
  maskedRotation ((β : ℝ) : AddCircle (1 : ℝ)) (maskFwd β) (maskBwd β)
    (measurableSet_maskFwd β) (measurableSet_maskBwd β)

/-- **The chain bound for the paper's masked rotation.**
`‖W‖ ≤ 2cos(π/(m+1))` with `m = ⌈1/β⌉` the capacity. -/
theorem norm_pathLawW_le (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ‖pathLawW β‖ ≤ chebFactor (capacity 1 β) := by
  have hlow : 0 < wLow β := wLow_pos β hβ
  set Mb := Real.sqrt (1 / wLow β) with hMb
  have hMb0 : 0 ≤ Mb := Real.sqrt_nonneg _
  have hu := measurable_schurWeight β
  have hMabs := abs_schurWeight_le β hβ hlow
  have hNabs := abs_inv_schurWeight_le β hβ hlow
  have hcap : 0 < capacity 1 β := by
    unfold capacity
    rw [Nat.ceil_pos]
    positivity
  refine norm_maskedRotation_le_of_factorization
    ((β : ℝ) : AddCircle (1 : ℝ)) (maskFwd β) (maskBwd β)
    (measurableSet_maskFwd β) (measurableSet_maskBwd β)
    (maskShift_fwd_bwd β hβ.le hβ1) (chebFactor_nonneg _ hcap)
    (factorB (schurWeight β) hu hMabs ((β : ℝ) : AddCircle (1 : ℝ))
      (maskFwd β) (measurableSet_maskFwd β))
    (factorC (schurWeight β) hu hNabs (maskFwd β) (measurableSet_maskFwd β))
    (fun x => inner_atomHalf_eq (schurWeight β) hu (schurWeight_pos β hβ)
      hMabs hNabs _ _ _ x)
    (fun x => ?_)
  refine norm_sq_factor_add_le (schurWeight β) hu hMabs hNabs _ _ _
    (abs_indicator_le _ _ hMb0 hMabs) (fun z => abs_indicator_le _ _ hMb0 hMabs _)
    (abs_indicator_le _ _ hMb0 hNabs) _ (fun z => ?_) x
  exact schur_pointwise β hβ hβ1 _ z
    (chainLength_le_capacity β _ hβ (chainBase_nonneg β (rep z) hβ (rep_nonneg z)))

/-! ### The long chains

For attainment we need a test function supported on a union of *complete*
chains of the full length `m`. The long-chain set is exactly that, and it is
seeded by the base points below `1 - (m-1)β`. -/

/-- The union of the long chains. -/
def longSet (β : ℝ) : Set (AddCircle (1 : ℝ)) :=
  {z | chainLength β (chainBase β (rep z)) = capacity 1 β}

theorem measurableSet_longSet (β : ℝ) : MeasurableSet (longSet β) :=
  ((measurable_chainLength β).comp measurable_rep) (measurableSet_singleton _)

/-- Base points below this threshold start chains of the full capacity. -/
noncomputable def longThreshold (β : ℝ) : ℝ :=
  min β (1 - ((capacity 1 β : ℝ) - 1) * β)

theorem capacity_sub_one_mul_lt (β : ℝ) (hβ : 0 < β) :
    ((capacity 1 β : ℝ) - 1) * β < 1 := by
  have hm : ((capacity 1 β : ℝ)) < 1 / β + 1 := by
    unfold capacity
    exact Nat.ceil_lt_add_one (by positivity)
  have h1 : (capacity 1 β : ℝ) - 1 < 1 / β := by linarith
  calc ((capacity 1 β : ℝ) - 1) * β < (1 / β) * β :=
        mul_lt_mul_of_pos_right h1 hβ
    _ = 1 := by field_simp

theorem longThreshold_pos (β : ℝ) (hβ : 0 < β) : 0 < longThreshold β :=
  lt_min hβ (by linarith [capacity_sub_one_mul_lt β hβ])

theorem one_le_capacity (β : ℝ) (hβ : 0 < β) : 1 ≤ capacity 1 β := by
  unfold capacity
  rw [Nat.one_le_ceil_iff]
  positivity

/-- Every point with a small representative lies on a long chain. -/
theorem mem_longSet_of_rep_lt (β : ℝ) (hβ : 0 < β) (z : AddCircle (1 : ℝ))
    (h : rep z < longThreshold β) : z ∈ longSet β := by
  have hrb : rep z < β := lt_of_lt_of_le h (min_le_left _ _)
  have hpos0 : chainPos β (rep z) = 0 := by
    unfold chainPos
    exact Nat.floor_eq_zero.mpr (by rw [div_lt_one hβ]; exact hrb)
  have hbase : chainBase β (rep z) = rep z := by
    unfold chainBase
    rw [hpos0]
    push_cast
    ring
  show chainLength β (chainBase β (rep z)) = capacity 1 β
  rw [hbase, chainLength_eq_capacity_iff β (rep z) hβ (rep_nonneg z)
    (one_le_capacity β hβ)]
  have h2 := lt_of_lt_of_le h (min_le_right _ _)
  linarith

/-- **The long chains have positive measure**, so a test function supported on
them is a nonzero `L²` element. -/
theorem volume_longSet_pos (β : ℝ) (hβ : 0 < β) :
    0 < volume (longSet β) := by
  set d := min (longThreshold β) (1 / 2) with hd
  have hdpos : 0 < d := lt_min (longThreshold_pos β hβ) (by norm_num)
  have hd2 : d ≤ 1 / 2 := min_le_right _ _
  have hdt : d ≤ longThreshold β := min_le_left _ _
  -- the projection of `(0, d)` lands in the long set
  have hsub : Set.Ioo (0 : ℝ) d
      ⊆ (QuotientAddGroup.mk ⁻¹' (longSet β)) ∩ Set.Ioc (0 : ℝ) (0 + 1) := by
    intro y hy
    constructor
    · show ((y : ℝ) : AddCircle (1 : ℝ)) ∈ longSet β
      refine mem_longSet_of_rep_lt β hβ _ ?_
      rw [rep_coe y (le_of_lt hy.1) (by linarith [hy.2])]
      linarith [hy.2]
    · exact Set.mem_Ioc.mpr ⟨hy.1, by linarith [hy.2]⟩
  have hproj := AddCircle.add_projection_respects_measure (T := (1 : ℝ)) 0
    (measurableSet_longSet β)
  rw [hproj]
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioo]
  simp only [sub_zero]
  exact ENNReal.ofReal_pos.mpr hdpos

/-! ### The test function, and attainment

`x = w · 1_{Long}` is an exact eigenvector of `W`: on a long chain the
recurrence is an equality, and admissible hops never leave the chain, so the
mask boundaries leak nothing. -/

/-- The long set is invariant under an admissible forward hop. -/
theorem longSet_add_step (β : ℝ) (hβ : 0 < β) (z : AddCircle (1 : ℝ))
    (hz : z ∈ maskFwd β) :
    (z + ((β : ℝ) : AddCircle (1 : ℝ))) ∈ longSet β ↔ z ∈ longSet β := by
  have hrep : rep (z + ((β : ℝ) : AddCircle (1 : ℝ))) = rep z + β :=
    rep_add_step β z hβ.le hz
  show chainLength β (chainBase β (rep (z + _))) = _ ↔ _
  rw [hrep, chainBase_add_step β (rep z) hβ (rep_nonneg z)]
  rfl

/-- The long set is invariant under an admissible backward hop. -/
theorem longSet_sub_step (β : ℝ) (hβ : 0 < β) (z : AddCircle (1 : ℝ))
    (hz : z ∈ maskBwd β) :
    (z - ((β : ℝ) : AddCircle (1 : ℝ))) ∈ longSet β ↔ z ∈ longSet β := by
  have hb : β ≤ rep z := hz
  have hrep : rep (z - ((β : ℝ) : AddCircle (1 : ℝ))) = rep z - β :=
    rep_sub_step β z hβ.le hb
  have hpos : 1 ≤ chainPos β (rep z) := chainPos_ge_one β (rep z) hβ hb
  show chainLength β (chainBase β (rep (z - _))) = _ ↔ _
  rw [hrep, chainBase_sub_step β (rep z) hβ hpos]
  rfl

/-- The test function `w · 1_{Long}` is square integrable: the weight is a
sine, so it is bounded by `1` outright. -/
theorem memLp_testFun (β : ℝ) :
    MemLp ((longSet β).indicator (circleWeight β)) 2
      (volume : Measure (AddCircle (1 : ℝ))) := by
  have habs : ∀ z, |circleWeight β z| ≤ 1 := by
    intro z
    show |Real.sin _| ≤ 1
    exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  refine MemLp.of_bound
    (((measurable_circleWeight β).indicator (measurableSet_longSet β)).aestronglyMeasurable)
    1 ?_
  filter_upwards with z
  rw [Real.norm_eq_abs]
  by_cases h : z ∈ longSet β
  · rw [Set.indicator_of_mem h]
    exact habs z
  · rw [Set.indicator_of_notMem h]
    norm_num

/-- The test function as an `L²` element. -/
noncomputable def testFun (β : ℝ) : L2c := MemLp.toLp _ (memLp_testFun β)

theorem coeFn_testFun (β : ℝ) :
    (testFun β : AddCircle (1 : ℝ) → ℝ)
      =ᵐ[volume] (longSet β).indicator (circleWeight β) :=
  MemLp.coeFn_toLp _

/-- **The test function is an exact eigenvector.** On a long chain the Schur
identity is an equality and admissible hops stay inside the chain, so
`W x = 2cos(π/(m+1)) · x`. -/
theorem pathLawW_testFun (β : ℝ) (hβ : 0 < β) :
    pathLawW β (testFun β) = chebFactor (capacity 1 β) • testFun β := by
  apply Lp.ext
  set bc := ((β : ℝ) : AddCircle (1 : ℝ)) with hbc
  set K := chebFactor (capacity 1 β) with hK
  have hmr : ∀ u : L2c, pathLawW β u
      = maskCLM volume (maskFwd β) (measurableSet_maskFwd β) (koopman bc u)
        + maskCLM volume (maskBwd β) (measurableSet_maskBwd β)
            (koopman (-bc) u) := fun u => rfl
  filter_upwards [
    Lp.coeFn_add
      (maskCLM volume (maskFwd β) (measurableSet_maskFwd β) (koopman bc (testFun β)))
      (maskCLM volume (maskBwd β) (measurableSet_maskBwd β)
        (koopman (-bc) (testFun β))),
    coeFn_maskCLM volume (maskFwd β) (measurableSet_maskFwd β)
      (koopman bc (testFun β)),
    coeFn_maskCLM volume (maskBwd β) (measurableSet_maskBwd β)
      (koopman (-bc) (testFun β)),
    koopman_ae bc (testFun β), koopman_ae (-bc) (testFun β),
    ae_translate bc (coeFn_testFun β), ae_translate (-bc) (coeFn_testFun β),
    coeFn_testFun β, Lp.coeFn_smul K (testFun β)] with z h1 h2 h3 h4 h5 h6 h7 h8 h9
  rw [hmr, h1, Pi.add_apply, h2, h3, h9, Pi.smul_apply, smul_eq_mul, h8]
  have hsub : z + -bc = z - bc := by rw [sub_eq_add_neg]
  by_cases hL : z ∈ longSet β
  · -- the interesting case: `z` is on a long chain
    have hk : chainLength β (chainBase β (rep z)) = capacity 1 β := hL
    have hf : (maskFwd β).indicator
        ((koopman bc (testFun β) : AddCircle (1 : ℝ) → ℝ)) z
        = if rep z + β < 1 then chainWeight β (rep z + β) else 0 := by
      by_cases hm : z ∈ maskFwd β
      · rw [Set.indicator_of_mem hm, h4, h6,
          ite_eq_left (show rep z + β < 1 from hm),
          Set.indicator_of_mem ((longSet_add_step β hβ z hm).mpr hL)]
        show circleWeight β (z + bc) = _
        unfold circleWeight
        rw [rep_add_step β z hβ.le hm]
      · rw [Set.indicator_of_notMem hm, ite_eq_right (show ¬(rep z + β < 1) from hm)]
    have hb : (maskBwd β).indicator
        ((koopman (-bc) (testFun β) : AddCircle (1 : ℝ) → ℝ)) z
        = if β ≤ rep z then chainWeight β (rep z - β) else 0 := by
      by_cases hm : z ∈ maskBwd β
      · rw [Set.indicator_of_mem hm, h5, h7,
          ite_eq_left (show β ≤ rep z from hm), hsub,
          Set.indicator_of_mem ((longSet_sub_step β hβ z hm).mpr hL)]
        show circleWeight β (z - bc) = _
        unfold circleWeight
        rw [rep_sub_step β z hβ.le hm]
      · rw [Set.indicator_of_notMem hm, ite_eq_right (show ¬(β ≤ rep z) from hm)]
    rw [hf, hb, Set.indicator_of_mem hL]
    have heq := chainWeight_schur_eq β (rep z) hβ (rep_nonneg z) (rep_lt_one z)
    rw [heq, hk, hK, chebFactor]
    show _ = 2 * Real.cos (π / ((capacity 1 β : ℝ) + 1)) * chainWeight β (rep z)
    ring
  · -- off the long chains everything vanishes
    have hf : (maskFwd β).indicator
        ((koopman bc (testFun β) : AddCircle (1 : ℝ) → ℝ)) z = 0 := by
      by_cases hm : z ∈ maskFwd β
      · rw [Set.indicator_of_mem hm, h4, h6,
          Set.indicator_of_notMem (fun hc => hL ((longSet_add_step β hβ z hm).mp hc))]
      · rw [Set.indicator_of_notMem hm]
    have hb : (maskBwd β).indicator
        ((koopman (-bc) (testFun β) : AddCircle (1 : ℝ) → ℝ)) z = 0 := by
      by_cases hm : z ∈ maskBwd β
      · rw [Set.indicator_of_mem hm, h5, h7, hsub,
          Set.indicator_of_notMem (fun hc => hL ((longSet_sub_step β hβ z hm).mp hc))]
      · rw [Set.indicator_of_notMem hm]
    rw [hf, hb, Set.indicator_of_notMem hL]
    ring

/-- The test function is a nonzero `L²` element, since the long chains have
positive measure. -/
theorem testFun_ne_zero (β : ℝ) (hβ : 0 < β) : testFun β ≠ 0 := by
  intro hzero
  have hco := coeFn_testFun β
  rw [hzero] at hco
  have h0 : (longSet β).indicator (circleWeight β) =ᵐ[volume] 0 :=
    hco.symm.trans (Lp.coeFn_zero ℝ 2 volume)
  have hsub : longSet β ⊆ {z | (longSet β).indicator (circleWeight β) z ≠ 0} := by
    intro z hz
    show (longSet β).indicator (circleWeight β) z ≠ 0
    rw [Set.indicator_of_mem hz]
    exact ne_of_gt (circleWeight_pos β hβ z)
  have hmeas0 : volume {z | (longSet β).indicator (circleWeight β) z ≠ 0} = 0 := by
    rw [← ae_iff]
    exact h0
  have hle := measure_mono (μ := (volume : Measure (AddCircle (1 : ℝ)))) hsub
  rw [hmeas0] at hle
  exact absurd (le_antisymm hle bot_le) (ne_of_gt (volume_longSet_pos β hβ))

/-- **Attainment.** The chain bound is achieved. -/
theorem le_norm_pathLawW (β : ℝ) (hβ : 0 < β) :
    chebFactor (capacity 1 β) ≤ ‖pathLawW β‖ := by
  refine le_opNorm_of_quadratic_form (pathLawW β) (testFun β)
    (testFun_ne_zero β hβ) ?_
  rw [pathLawW_testFun β hβ, real_inner_smul_left, real_inner_self_eq_norm_sq]

/-- **The Path Law norm identity for the masked rotation.**
`‖W‖ = 2cos(π/(m+1))` exactly, with `m = ⌈1/β⌉` the capacity. -/
theorem norm_pathLawW (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ‖pathLawW β‖ = chebFactor (capacity 1 β) :=
  le_antisymm (norm_pathLawW_le β hβ hβ1) (le_norm_pathLawW β hβ)

end Cvs.PathLaw
