/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/
import Cvs.PathLaw.GevreyBump

/-!
# A prime atom is not a finite-rank perturbation

Every Chebyshev value `2cos(pathAngle m j)` of the long-chain family is an eigenvalue of the masked rotation
`pathLawW β` with an infinite-dimensional eigenspace. The chain eigenvector `rungFunL2 β m j c` is an eigenvector
for every bounded measurable envelope `c` on the chain base. Envelopes supported on disjoint subintervals of the
long-base interval give pairwise orthogonal, non-zero eigenvectors, hence an infinite linearly independent family.
When the top eigenvalue is non-zero (`m ≥ 2`, i.e. every genuine atom `q < c`), the range of `pathLawW β`
contains that eigenspace, so `pathLawW β` does not have finite rank.
-/

noncomputable section

open MeasureTheory Real

namespace Cvs.PathLaw

local notation "L2c" => Lp ℝ 2 (volume : Measure (AddCircle (1 : ℝ)))

/-- **The position-zero slice is non-null** for any envelope that is non-zero on a subinterval `(u, v)` of the
long-base interval `[0, ℓ)`, `ℓ = 1 − (m − 1)β`. -/
lemma volume_slice_pos_of_nonvanishing_Ioo (β : ℝ) (hβ : 0 < β) (b : ℝ → ℝ) {u v : ℝ} (hu : 0 ≤ u)
    (huv : u < v) (hv : v ≤ 1 - ((capacity 1 β : ℝ) - 1) * β)
    (hne : ∀ y, y ∈ Set.Ioo u v → b y ≠ 0) (hbm : Measurable b) :
    0 < volume {z : AddCircle (1 : ℝ) |
      z ∈ chainSet β (capacity 1 β) ∧ chainPos β (rep z) = 0
        ∧ b (chainBase β (rep z)) ≠ 0} := by
  have hℓ1 : (1 - ((capacity 1 β : ℝ) - 1) * β) ≤ 1 := by
    have hm1 : 1 ≤ capacity 1 β := one_le_capacity β hβ
    have h1 : (1 : ℝ) ≤ (capacity 1 β : ℝ) := by exact_mod_cast hm1
    nlinarith
  have hsub : Set.Ioo u v
      ⊆ (QuotientAddGroup.mk ⁻¹' {z : AddCircle (1 : ℝ) |
          z ∈ chainSet β (capacity 1 β) ∧ chainPos β (rep z) = 0
            ∧ b (chainBase β (rep z)) ≠ 0})
        ∩ Set.Ioc (0 : ℝ) (0 + 1) := by
    intro y hy
    have hy0 : 0 < y := lt_of_le_of_lt hu hy.1
    have hyℓ : y < 1 - ((capacity 1 β : ℝ) - 1) * β := lt_of_lt_of_le hy.2 hv
    have hy1 : y < 1 := lt_of_lt_of_le hyℓ hℓ1
    have hrep : rep ((y : ℝ) : AddCircle (1 : ℝ)) = y := rep_coe y hy0.le hy1
    have hwin : y ∈ Set.Ico (((0 : ℕ) : ℝ) * β)
        (((0 : ℕ) : ℝ) * β + (1 - ((capacity 1 β : ℝ) - 1) * β)) := by
      constructor
      · simpa using hy0.le
      · simpa using hyℓ
    obtain ⟨hpos, hbase, hlen⟩ := chain_coords_window β hβ hwin
    constructor
    · show ((y : ℝ) : AddCircle (1 : ℝ)) ∈ {z : AddCircle (1 : ℝ) | _}
      refine ⟨?_, ?_, ?_⟩
      · show chainLength β (chainBase β (rep _)) = capacity 1 β
        rw [hrep]
        exact hlen
      · rw [hrep]
        exact hpos
      · rw [hrep, hbase]
        have : y - ((0 : ℕ) : ℝ) * β = y := by simp
        rw [this]
        exact hne y hy
    · exact Set.mem_Ioc.mpr ⟨hy0, by linarith⟩
  have hms : MeasurableSet {z : AddCircle (1 : ℝ) |
      z ∈ chainSet β (capacity 1 β) ∧ chainPos β (rep z) = 0
        ∧ b (chainBase β (rep z)) ≠ 0} := by
    change MeasurableSet (chainSet β (capacity 1 β) ∩ ((chainPos β ∘ rep) ⁻¹' {0}
      ∩ ((b ∘ chainBase β ∘ rep) ⁻¹' {0}ᶜ)))
    refine (measurableSet_chainSet β _).inter
      ((((measurable_chainPos β).comp measurable_rep)
        (measurableSet_singleton 0)).inter ?_)
    exact (hbm.comp ((measurable_chainBase β).comp measurable_rep))
      (measurableSet_singleton 0).compl
  have hproj := AddCircle.add_projection_respects_measure (T := (1 : ℝ)) 0 hms
  rw [hproj]
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioo]
  exact ENNReal.ofReal_pos.mpr (by linarith)

/-- Chain functions whose envelopes have disjoint supports have product zero. -/
lemma rungFun_mul_eq_zero (β : ℝ) (L : ℕ) (j : Fin L) {c₁ c₂ : ℝ → ℝ} (h : ∀ r, c₁ r * c₂ r = 0)
    (z : AddCircle (1 : ℝ)) : rungFun β L j c₁ z * rungFun β L j c₂ z = 0 := by
  unfold rungFun
  by_cases hz : z ∈ chainSet β L
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
    have := h (chainBase β (rep z))
    calc c₁ (chainBase β (rep z)) * chainEnv β L j z * (c₂ (chainBase β (rep z)) * chainEnv β L j z)
        = (c₁ (chainBase β (rep z)) * c₂ (chainBase β (rep z))) * (chainEnv β L j z) ^ 2 := by ring
      _ = 0 := by rw [this, zero_mul]
  · rw [Set.indicator_of_notMem hz, zero_mul]

/-- The `k`-th dyadic piece `(ℓ/2^{k+1}, ℓ/2^k)` of the long-base interval. -/
def dyadicEnv (ℓ : ℝ) (k : ℕ) : ℝ → ℝ :=
  (Set.Ioo (ℓ / 2 ^ (k + 1)) (ℓ / 2 ^ k)).indicator fun _ => (1 : ℝ)

lemma measurable_dyadicEnv (ℓ : ℝ) (k : ℕ) : Measurable (dyadicEnv ℓ k) :=
  measurable_const.indicator measurableSet_Ioo

lemma abs_dyadicEnv_le (ℓ : ℝ) (k : ℕ) (r : ℝ) : |dyadicEnv ℓ k r| ≤ 1 := by
  unfold dyadicEnv
  by_cases hr : r ∈ Set.Ioo (ℓ / 2 ^ (k + 1)) (ℓ / 2 ^ k)
  · rw [Set.indicator_of_mem hr, abs_one]
  · rw [Set.indicator_of_notMem hr, abs_zero]; exact zero_le_one

lemma dyadicEnv_mul_eq_zero {ℓ : ℝ} (hℓ : 0 < ℓ) {k l : ℕ} (hkl : k ≠ l) (r : ℝ) :
    dyadicEnv ℓ k r * dyadicEnv ℓ l r = 0 := by
  wlog h : k < l generalizing k l
  · rw [mul_comm]; exact this (Ne.symm hkl) (lt_of_le_of_ne (not_lt.mp h) (Ne.symm hkl))
  unfold dyadicEnv
  by_cases hk : r ∈ Set.Ioo (ℓ / 2 ^ (k + 1)) (ℓ / 2 ^ k)
  · by_cases hl : r ∈ Set.Ioo (ℓ / 2 ^ (l + 1)) (ℓ / 2 ^ l)
    · exfalso
      have hpow : (2 : ℝ) ^ (k + 1) ≤ 2 ^ l := pow_le_pow_right₀ (by norm_num) h
      have hle : ℓ / 2 ^ l ≤ ℓ / 2 ^ (k + 1) :=
        div_le_div_of_nonneg_left hℓ.le (by positivity) hpow
      linarith [hk.1, hl.2]
    · rw [Set.indicator_of_notMem hl, mul_zero]
  · rw [Set.indicator_of_notMem hk, zero_mul]

/-- The chain eigenvector built on the `k`-th dyadic piece. -/
def dyadicEigen (β : ℝ) (hβ : 0 < β) (j : Fin (capacity 1 β)) (k : ℕ) : L2c :=
  rungFunL2 β hβ (capacity 1 β) j (dyadicEnv (1 - ((capacity 1 β : ℝ) - 1) * β) k)
    (measurable_dyadicEnv _ k) 1 zero_le_one (fun r _ _ => abs_dyadicEnv_le _ k r)

lemma dyadicEigen_ne_zero (β : ℝ) (hβ : 0 < β) (j : Fin (capacity 1 β)) (k : ℕ) :
    dyadicEigen β hβ j k ≠ 0 := by
  have hℓ : 0 < 1 - ((capacity 1 β : ℝ) - 1) * β := by
    have := capacity_sub_one_mul_lt β hβ
    linarith
  set ℓ := 1 - ((capacity 1 β : ℝ) - 1) * β
  refine rungFunL2_ne_zero β hβ _ j _ _ 1 zero_le_one _ ?_
  refine volume_slice_pos_of_nonvanishing_Ioo β hβ (dyadicEnv ℓ k) (u := ℓ / 2 ^ (k + 1)) (v := ℓ / 2 ^ k)
    (by positivity) ?_ ?_ ?_
    (measurable_dyadicEnv ℓ k)
  · exact div_lt_div_of_pos_left hℓ (by positivity) (pow_lt_pow_right₀ (by norm_num) (Nat.lt_succ_self k))
  · exact div_le_self hℓ.le (one_le_pow₀ (by norm_num))
  · intro y hy
    unfold dyadicEnv
    rw [Set.indicator_of_mem hy]
    exact one_ne_zero

lemma inner_dyadicEigen (β : ℝ) (hβ : 0 < β) (j : Fin (capacity 1 β)) {k l : ℕ} (hkl : k ≠ l) :
    inner ℝ (dyadicEigen β hβ j k) (dyadicEigen β hβ j l) = 0 := by
  have hℓ : 0 < 1 - ((capacity 1 β : ℝ) - 1) * β := by
    have := capacity_sub_one_mul_lt β hβ
    linarith
  rw [MeasureTheory.L2.inner_def]
  refine integral_eq_zero_of_ae ?_
  unfold dyadicEigen rungFunL2
  filter_upwards [MemLp.coeFn_toLp (memLp_rungFun β hβ (capacity 1 β) j
      (dyadicEnv (1 - ((capacity 1 β : ℝ) - 1) * β) k) (measurable_dyadicEnv _ k) 1 zero_le_one
      (fun r _ _ => abs_dyadicEnv_le _ k r)),
    MemLp.coeFn_toLp (memLp_rungFun β hβ (capacity 1 β) j
      (dyadicEnv (1 - ((capacity 1 β : ℝ) - 1) * β) l) (measurable_dyadicEnv _ l) 1 zero_le_one
      (fun r _ _ => abs_dyadicEnv_le _ l r))] with z hz₁ hz₂
  rw [hz₁, hz₂]
  simp only [Pi.zero_apply, RCLike.inner_apply, conj_trivial]
  rw [mul_comm]
  exact rungFun_mul_eq_zero β _ j (dyadicEnv_mul_eq_zero hℓ hkl) z

lemma dyadicEigen_mem_eigenspace (β : ℝ) (hβ : 0 < β) (j : Fin (capacity 1 β)) (k : ℕ) :
    dyadicEigen β hβ j k ∈
      Module.End.eigenspace (pathLawW β : L2c →ₗ[ℝ] L2c) (2 * Real.cos (pathAngle (capacity 1 β) j)) := by
  rw [Module.End.mem_eigenspace_iff]
  exact pathLawW_rungFunL2 β hβ _ j _ _ 1 zero_le_one _

/-- **Every long-family Chebyshev value has infinite multiplicity.** The eigenspace of the masked rotation
`pathLawW β` at `2cos(pathAngle m j)`, `m = ⌈1/β⌉`, is not finite-dimensional. -/
theorem not_finiteDimensional_eigenspace (β : ℝ) (hβ : 0 < β) (j : Fin (capacity 1 β)) :
    ¬ FiniteDimensional ℝ
      (Module.End.eigenspace (pathLawW β : L2c →ₗ[ℝ] L2c) (2 * Real.cos (pathAngle (capacity 1 β) j))) := by
  intro hfin
  set E := Module.End.eigenspace (pathLawW β : L2c →ₗ[ℝ] L2c) (2 * Real.cos (pathAngle (capacity 1 β) j))
  let v : ℕ → E := fun k => ⟨dyadicEigen β hβ j k, dyadicEigen_mem_eigenspace β hβ j k⟩
  have hli : LinearIndependent ℝ (fun k => dyadicEigen β hβ j k) :=
    linearIndependent_of_ne_zero_of_inner_eq_zero (dyadicEigen_ne_zero β hβ j)
      (fun k l hkl => inner_dyadicEigen β hβ j hkl)
  have hv : LinearIndependent ℝ v := LinearIndependent.of_comp E.subtype hli
  have := hv.finite
  exact not_finite ℕ

/-- **A prime atom is not a finite-rank perturbation.** For `m = ⌈1/β⌉ ≥ 2` (every atom `q < c`), the range of
the masked rotation `pathLawW β` is infinite-dimensional. -/
theorem not_finiteDimensional_range (β : ℝ) (hβ : 0 < β) (hm : 2 ≤ capacity 1 β) :
    ¬ FiniteDimensional ℝ (LinearMap.range (pathLawW β : L2c →ₗ[ℝ] L2c)) := by
  intro hfin
  have hm0 : 0 < capacity 1 β := by omega
  set j : Fin (capacity 1 β) := ⟨0, hm0⟩
  set ev := 2 * Real.cos (pathAngle (capacity 1 β) j)
  have hev : ev ≠ 0 := by
    have hpos : 0 < Real.cos (pathAngle (capacity 1 β) j) := by
      apply Real.cos_pos_of_mem_Ioo
      have hm2 : (2 : ℝ) ≤ capacity 1 β := by exact_mod_cast hm
      simp only [pathAngle, j, Nat.cast_zero, zero_add, one_mul]
      constructor
      · have : 0 < π / ((capacity 1 β : ℝ) + 1) := by positivity
        linarith [Real.pi_pos]
      · rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [Real.pi_pos]
    positivity
  have hle : Module.End.eigenspace (pathLawW β : L2c →ₗ[ℝ] L2c) ev
      ≤ LinearMap.range (pathLawW β : L2c →ₗ[ℝ] L2c) := by
    intro x hx
    rw [Module.End.mem_eigenspace_iff] at hx
    refine ⟨ev⁻¹ • x, ?_⟩
    rw [map_smul, hx, smul_smul, inv_mul_cancel₀ hev, one_smul]
  exact not_finiteDimensional_eigenspace β hβ j (Submodule.finiteDimensional_of_le hle)

/-! ### The short family -/

/-- **The short position-zero slice is non-null** for any envelope that is non-zero on a subinterval `(u, v)` of
the short-base interval `(ℓ, β)`, `ℓ = 1 − (m − 1)β`. -/
lemma volume_short_slice_pos_of_nonvanishing_Ioo (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hshort : 1 < (capacity 1 β : ℝ) * β) (b : ℝ → ℝ) {u v : ℝ}
    (hu : 1 - ((capacity 1 β : ℝ) - 1) * β ≤ u) (huv : u < v) (hv : v ≤ β)
    (hne : ∀ y, y ∈ Set.Ioo u v → b y ≠ 0) (hbm : Measurable b) :
    0 < volume {z : AddCircle (1 : ℝ) |
      z ∈ chainSet β (capacity 1 β - 1) ∧ chainPos β (rep z) = 0
        ∧ b (chainBase β (rep z)) ≠ 0} := by
  have hm1 : 1 ≤ capacity 1 β := one_le_capacity β hβ
  have hmul : ((capacity 1 β : ℝ) - 1) * β < 1 := capacity_sub_one_mul_lt β hβ
  have hm2 : 2 ≤ capacity 1 β := by
    by_contra hcon
    have hm1' : capacity 1 β ≤ 1 := by omega
    have hle : (capacity 1 β : ℝ) * β ≤ 1 := by
      calc (capacity 1 β : ℝ) * β ≤ 1 * β := by
            apply mul_le_mul_of_nonneg_right _ hβ.le
            exact_mod_cast hm1'
        _ ≤ 1 := by linarith
    linarith
  have hcast1 : ((capacity 1 β - 1 : ℕ) : ℝ) = (capacity 1 β : ℝ) - 1 := by
    push_cast [Nat.cast_sub hm1]
    ring
  set lo : ℝ := 1 - ((capacity 1 β : ℝ) - 1) * β with hlo
  have hlopos : 0 < lo := by rw [hlo]; linarith
  have hsub : Set.Ioo u v
      ⊆ (QuotientAddGroup.mk ⁻¹' {z : AddCircle (1 : ℝ) |
          z ∈ chainSet β (capacity 1 β - 1) ∧ chainPos β (rep z) = 0
            ∧ b (chainBase β (rep z)) ≠ 0})
        ∩ Set.Ioc (0 : ℝ) (0 + 1) := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le hlopos (hu.trans hy.1.le)
    have hyβ : y < β := lt_of_lt_of_le hy.2 hv
    have hy1 : y < 1 := lt_of_lt_of_le hyβ hβ1
    have hrep : rep ((y : ℝ) : AddCircle (1 : ℝ)) = y := rep_coe y hy0.le hy1
    have hposy : chainPos β y = 0 :=
      Nat.floor_eq_zero.mpr ((div_lt_one hβ).mpr hyβ)
    have hbase : chainBase β y = y := by
      unfold chainBase
      rw [hposy]
      push_cast
      ring
    constructor
    · show ((y : ℝ) : AddCircle (1 : ℝ)) ∈ {z : AddCircle (1 : ℝ) | _}
      refine ⟨?_, ?_, ?_⟩
      · show chainLength β (chainBase β (rep _)) = capacity 1 β - 1
        rw [hrep, hbase]
        unfold chainLength
        have hcast2 : ((capacity 1 β - 2 : ℕ) : ℝ)
            = (capacity 1 β : ℝ) - 2 := by
          push_cast [Nat.cast_sub hm2]
          ring
        have hylo : lo < y := lt_of_le_of_lt hu hy.1
        have hup : ⌈(1 - y) / β⌉₊ ≤ capacity 1 β - 1 := by
          rw [Nat.ceil_le, hcast1, div_le_iff₀ hβ]
          rw [hlo] at hylo
          nlinarith
        have hdown : capacity 1 β - 2 < ⌈(1 - y) / β⌉₊ := by
          rw [Nat.lt_ceil, hcast2, lt_div_iff₀ hβ]
          nlinarith
        omega
      · rw [hrep]
        exact hposy
      · rw [hrep, hbase]
        exact hne y hy
    · exact Set.mem_Ioc.mpr ⟨hy0, by linarith [hy.2, hv]⟩
  have hms : MeasurableSet {z : AddCircle (1 : ℝ) |
      z ∈ chainSet β (capacity 1 β - 1) ∧ chainPos β (rep z) = 0
        ∧ b (chainBase β (rep z)) ≠ 0} := by
    change MeasurableSet (chainSet β (capacity 1 β - 1) ∩ ((chainPos β ∘ rep) ⁻¹' {0}
      ∩ ((b ∘ chainBase β ∘ rep) ⁻¹' {0}ᶜ)))
    refine (measurableSet_chainSet β _).inter
      ((((measurable_chainPos β).comp measurable_rep)
        (measurableSet_singleton 0)).inter ?_)
    exact (hbm.comp ((measurable_chainBase β).comp measurable_rep))
      (measurableSet_singleton 0).compl
  have hproj := AddCircle.add_projection_respects_measure (T := (1 : ℝ)) 0 hms
  rw [hproj]
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioo]
  exact ENNReal.ofReal_pos.mpr (by linarith)

/-- The `k`-th dyadic piece `(p + w/2^{k+1}, p + w/2^k)` of an interval `(p, p + w)`. -/
def dyadicEnvAt (p w : ℝ) (k : ℕ) : ℝ → ℝ :=
  (Set.Ioo (p + w / 2 ^ (k + 1)) (p + w / 2 ^ k)).indicator fun _ => (1 : ℝ)

lemma measurable_dyadicEnvAt (p w : ℝ) (k : ℕ) : Measurable (dyadicEnvAt p w k) :=
  measurable_const.indicator measurableSet_Ioo

lemma abs_dyadicEnvAt_le (p w : ℝ) (k : ℕ) (r : ℝ) : |dyadicEnvAt p w k r| ≤ 1 := by
  unfold dyadicEnvAt
  by_cases hr : r ∈ Set.Ioo (p + w / 2 ^ (k + 1)) (p + w / 2 ^ k)
  · rw [Set.indicator_of_mem hr, abs_one]
  · rw [Set.indicator_of_notMem hr, abs_zero]; exact zero_le_one

lemma dyadicEnvAt_mul_eq_zero (p : ℝ) {w : ℝ} (hw : 0 < w) {k l : ℕ} (hkl : k ≠ l) (r : ℝ) :
    dyadicEnvAt p w k r * dyadicEnvAt p w l r = 0 := by
  wlog h : k < l generalizing k l
  · rw [mul_comm]; exact this (Ne.symm hkl) (lt_of_le_of_ne (not_lt.mp h) (Ne.symm hkl))
  unfold dyadicEnvAt
  by_cases hk : r ∈ Set.Ioo (p + w / 2 ^ (k + 1)) (p + w / 2 ^ k)
  · by_cases hl : r ∈ Set.Ioo (p + w / 2 ^ (l + 1)) (p + w / 2 ^ l)
    · exfalso
      have hpow : (2 : ℝ) ^ (k + 1) ≤ 2 ^ l := pow_le_pow_right₀ (by norm_num) h
      have hle : w / 2 ^ l ≤ w / 2 ^ (k + 1) :=
        div_le_div_of_nonneg_left hw.le (by positivity) hpow
      linarith [hk.1, hl.2]
    · rw [Set.indicator_of_notMem hl, mul_zero]
  · rw [Set.indicator_of_notMem hk, zero_mul]

/-- The short-chain eigenvector built on the `k`-th dyadic piece of the short-base interval. -/
def shortEigen (β : ℝ) (hβ : 0 < β) (j : Fin (capacity 1 β - 1)) (k : ℕ) : L2c :=
  rungFunL2 β hβ (capacity 1 β - 1) j
    (dyadicEnvAt (1 - ((capacity 1 β : ℝ) - 1) * β) (β - (1 - ((capacity 1 β : ℝ) - 1) * β)) k)
    (measurable_dyadicEnvAt _ _ k) 1 zero_le_one (fun r _ _ => abs_dyadicEnvAt_le _ _ k r)

/-- **Every short-family Chebyshev value has infinite multiplicity.** When both chain lengths occur, the
eigenspace of `pathLawW β` at `2cos(pathAngle (m − 1) j)` is not finite-dimensional. -/
theorem not_finiteDimensional_eigenspace_short (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hshort : 1 < (capacity 1 β : ℝ) * β) (j : Fin (capacity 1 β - 1)) :
    ¬ FiniteDimensional ℝ
      (Module.End.eigenspace (pathLawW β : L2c →ₗ[ℝ] L2c)
        (2 * Real.cos (pathAngle (capacity 1 β - 1) j))) := by
  intro hfin
  set lo := 1 - ((capacity 1 β : ℝ) - 1) * β with hlo
  have hw : 0 < β - lo := by
    rw [hlo]
    have : (1 : ℝ) < (capacity 1 β : ℝ) * β := hshort
    nlinarith
  set E := Module.End.eigenspace (pathLawW β : L2c →ₗ[ℝ] L2c)
    (2 * Real.cos (pathAngle (capacity 1 β - 1) j))
  have hmem : ∀ k, shortEigen β hβ j k ∈ E := fun k => by
    rw [Module.End.mem_eigenspace_iff]
    exact pathLawW_rungFunL2 β hβ _ j _ _ 1 zero_le_one _
  have hne : ∀ k, shortEigen β hβ j k ≠ 0 := by
    intro k
    refine rungFunL2_ne_zero β hβ _ j _ _ 1 zero_le_one _ ?_
    refine volume_short_slice_pos_of_nonvanishing_Ioo β hβ hβ1 hshort
      (dyadicEnvAt lo (β - lo) k) (u := lo + (β - lo) / 2 ^ (k + 1)) (v := lo + (β - lo) / 2 ^ k)
      ?_ ?_ ?_ ?_ (measurable_dyadicEnvAt _ _ k)
    · have : 0 < (β - lo) / 2 ^ (k + 1) := by positivity
      linarith
    · have := div_lt_div_of_pos_left hw (by positivity : (0 : ℝ) < 2 ^ k)
        (pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : k < k + 1))
      linarith
    · have := div_le_self hw.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := k))
      linarith
    · intro y hy
      unfold dyadicEnvAt
      rw [Set.indicator_of_mem hy]
      exact one_ne_zero
  have horth : Pairwise fun k l => inner ℝ (shortEigen β hβ j k) (shortEigen β hβ j l) = 0 := by
    intro k l hkl
    rw [MeasureTheory.L2.inner_def]
    refine integral_eq_zero_of_ae ?_
    unfold shortEigen rungFunL2
    filter_upwards [MemLp.coeFn_toLp (memLp_rungFun β hβ (capacity 1 β - 1) j
        (dyadicEnvAt lo (β - lo) k) (measurable_dyadicEnvAt _ _ k) 1 zero_le_one
        (fun r _ _ => abs_dyadicEnvAt_le _ _ k r)),
      MemLp.coeFn_toLp (memLp_rungFun β hβ (capacity 1 β - 1) j
        (dyadicEnvAt lo (β - lo) l) (measurable_dyadicEnvAt _ _ l) 1 zero_le_one
        (fun r _ _ => abs_dyadicEnvAt_le _ _ l r))] with z hz₁ hz₂
    rw [hz₁, hz₂]
    simp only [Pi.zero_apply, RCLike.inner_apply, conj_trivial]
    rw [mul_comm]
    exact rungFun_mul_eq_zero β _ j (dyadicEnvAt_mul_eq_zero lo hw hkl) z
  let v : ℕ → E := fun k => ⟨shortEigen β hβ j k, hmem k⟩
  have hli : LinearIndependent ℝ (fun k => shortEigen β hβ j k) :=
    linearIndependent_of_ne_zero_of_inner_eq_zero hne horth
  have hv : LinearIndependent ℝ v := LinearIndependent.of_comp E.subtype hli
  have := hv.finite
  exact not_finite ℕ

end Cvs.PathLaw
