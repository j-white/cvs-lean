/-
The chain measure ratio law.

The circle splits into the long chains (`P_m`) and the short chains
(`P_{m−1}`), and their measures are exact:

* `volume_longSet_eq` — the long chains occupy `m·(1 − (m−1)β)`;
* `volume_chainSet_short_eq` — the short chains occupy `(m−1)·(mβ − 1)`;
* `long_base_fraction` — the long fraction of the base interval is
  `frac(1/β)`, the long-chain fraction.

The long set decomposes, up to a null set, into `m` disjoint translates
`[jβ, jβ + ℓ)` of the long base interval `[0, ℓ)`, `ℓ = 1 − (m−1)β`; the
short set is its complement by the two-length dichotomy.
-/
import Cvs.PathLaw.SpectralSet

open MeasureTheory

namespace Cvs.PathLaw

/-- The short chains are exactly the complement of the long chains: the
two-length dichotomy, as a set identity. -/
theorem chainSet_short_eq_compl (β : ℝ) (hβ : 0 < β) :
    chainSet β (capacity 1 β - 1) = (longSet β)ᶜ := by
  have h1m : 1 ≤ capacity 1 β := one_le_capacity β hβ
  ext z
  have hdi := chainLength_eq_or β (chainBase β (rep z)) hβ
    (chainBase_nonneg β (rep z) hβ (rep_nonneg z))
    (chainBase_lt β (rep z) hβ)
  constructor
  · intro hz hlong
    have h1 : chainLength β (chainBase β (rep z)) = capacity 1 β - 1 := hz
    have h2 : chainLength β (chainBase β (rep z)) = capacity 1 β := hlong
    omega
  · intro hz
    have h2 : ¬(chainLength β (chainBase β (rep z)) = capacity 1 β) := hz
    show chainLength β (chainBase β (rep z)) = capacity 1 β - 1
    omega

/-- `mβ ≥ 1`: the capacity covers the circle. -/
lemma one_le_capacity_mul (β : ℝ) (hβ : 0 < β) :
    1 ≤ (capacity 1 β : ℝ) * β := by
  have h2 : 1 / β ≤ (capacity 1 β : ℝ) := by
    have := Nat.le_ceil (1 / β)
    exact_mod_cast this
  calc (1 : ℝ) = (1 / β) * β := by field_simp
    _ ≤ (capacity 1 β : ℝ) * β := mul_le_mul_of_nonneg_right h2 hβ.le

/-- **The long-chain measure.** The long chains occupy exactly
`m·(1 − (m−1)β)` of the circle. -/
theorem volume_longSet_eq (β : ℝ) (hβ : 0 < β) :
    volume (longSet β)
      = ENNReal.ofReal
          ((capacity 1 β : ℝ) * (1 - ((capacity 1 β : ℝ) - 1) * β)) := by
  set m := capacity 1 β with hm
  set ℓ : ℝ := 1 - ((m : ℝ) - 1) * β with hℓ
  have hℓpos : 0 < ℓ := by
    have := capacity_sub_one_mul_lt β hβ
    rw [hℓ]
    linarith
  have hℓβ : ℓ ≤ β := by
    have := one_le_capacity_mul β hβ
    rw [hℓ]
    nlinarith
  have hproj := AddCircle.add_projection_respects_measure (T := (1 : ℝ)) 0
    (measurableSet_longSet β)
  rw [hproj]
  refine Eq.trans
    (measure_congr
      (t := ⋃ j ∈ Finset.range m,
        Set.Ico ((j : ℝ) * β) ((j : ℝ) * β + ℓ)) ?_) ?_
  · rw [MeasureTheory.ae_eq_set]
    constructor
    · refine measure_mono_null (fun y hy => ?_)
        (measure_singleton (1 : ℝ))
      obtain ⟨⟨hyS, hyIoc⟩, hyU⟩ := hy
      by_contra hy1
      have hylt : y < 1 := lt_of_le_of_ne (by linarith [hyIoc.2]) hy1
      have hrepy : rep ((y : ℝ) : AddCircle (1 : ℝ)) = y :=
        rep_coe y hyIoc.1.le hylt
      have hlen : chainLength β (chainBase β y) = m := by
        have := hyS
        rw [Set.mem_preimage] at this
        have h2 : chainLength β (chainBase β (rep ((y : ℝ) : AddCircle (1 : ℝ)))) = m :=
          this
        rw [hrepy] at h2
        exact h2
      have hjm : chainPos β y < m := by
        have := chainPos_lt_chainLength β y hβ hylt
        omega
      have hbase0 : 0 ≤ chainBase β y := chainBase_nonneg β y hβ hyIoc.1.le
      have hbaseℓ : chainBase β y < ℓ := by
        have hiff := (chainLength_eq_capacity_iff β (chainBase β y) hβ hbase0
          (one_le_capacity β hβ)).mp hlen
        have hcm : ((capacity 1 β : ℕ) : ℝ) = (m : ℝ) := by rw [← hm]
        rw [hcm] at hiff
        rw [hℓ]
        linarith
      apply hyU
      refine Set.mem_biUnion (Finset.mem_range.mpr hjm) ?_
      have hrecon := chainBase_add β y
      constructor
      · linarith
      · linarith
    · refine measure_mono_null (fun y hy => ?_)
        (measure_singleton (0 : ℝ))
      obtain ⟨hyU, hyS⟩ := hy
      obtain ⟨j, hj, hyj⟩ := Set.mem_iUnion₂.mp hyU
      rw [Finset.mem_range] at hj
      by_contra hy0
      have hy0' : 0 < y := by
        rcases lt_or_eq_of_le (le_trans (by positivity) hyj.1) with h | h
        · exact h
        · exact absurd h.symm hy0
      have hjtop : (j : ℝ) * β + ℓ ≤ 1 := by
        have hcast : (j : ℝ) ≤ (m : ℝ) - 1 := by
          have : (j : ℝ) ≤ (m : ℝ) - 1 ↔ (j : ℝ) + 1 ≤ (m : ℝ) := by
            constructor <;> intro <;> linarith
          rw [this]
          exact_mod_cast hj
        have : (j : ℝ) * β ≤ ((m : ℝ) - 1) * β :=
          mul_le_mul_of_nonneg_right hcast hβ.le
        rw [hℓ]
        linarith
      have hylt1 : y < 1 := lt_of_lt_of_le hyj.2 hjtop
      apply hyS
      constructor
      · rw [Set.mem_preimage]
        have hrepy : rep ((y : ℝ) : AddCircle (1 : ℝ)) = y :=
          rep_coe y hy0'.le hylt1
        show chainLength β
          (chainBase β (rep ((y : ℝ) : AddCircle (1 : ℝ)))) = m
        rw [hrepy]
        have hposj : chainPos β y = j := by
          unfold chainPos
          rw [Nat.floor_eq_iff (by positivity)]
          constructor
          · rw [le_div_iff₀ hβ]
            linarith [hyj.1]
          · rw [div_lt_iff₀ hβ]
            have : (j : ℝ) * β + ℓ ≤ (j : ℝ) * β + β := by linarith
            calc y < (j : ℝ) * β + ℓ := hyj.2
              _ ≤ ((j : ℝ) + 1) * β := by linarith
        have hbase : chainBase β y = y - (j : ℝ) * β := by
          unfold chainBase
          rw [hposj]
        rw [chainLength_eq_capacity_iff β _ hβ
          (by rw [hbase]; linarith [hyj.1]) (one_le_capacity β hβ), hbase]
        have hy2 := hyj.2
        have hcm : ((capacity 1 β : ℕ) : ℝ) = (m : ℝ) := by rw [← hm]
        rw [hℓ] at hy2
        rw [hcm]
        linarith
      · exact Set.mem_Ioc.mpr ⟨hy0', by linarith⟩
  · rw [measure_biUnion_finset ?_ (fun j _ => measurableSet_Ico)]
    · have hterm : ∀ j ∈ Finset.range m,
          volume (Set.Ico ((j : ℝ) * β) ((j : ℝ) * β + ℓ))
            = ENNReal.ofReal ℓ := fun j _ => by
        rw [Real.volume_Ico, add_sub_cancel_left]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, ← ENNReal.ofReal_natCast m,
        ← ENNReal.ofReal_mul (by positivity)]
    · intro i hi j hj hij
      simp only [Finset.coe_range, Set.mem_Iio] at hi hj
      have hsep : ∀ a b : ℕ, a < b →
          Disjoint (Set.Ico ((a : ℝ) * β) ((a : ℝ) * β + ℓ))
            (Set.Ico ((b : ℝ) * β) ((b : ℝ) * β + ℓ)) := by
        intro a b hab
        rw [Set.Ico_disjoint_Ico]
        have hcast : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hab
        have h1 : (a : ℝ) * β + ℓ ≤ (b : ℝ) * β := by nlinarith
        calc min ((a : ℝ) * β + ℓ) ((b : ℝ) * β + ℓ)
            ≤ (a : ℝ) * β + ℓ := min_le_left _ _
          _ ≤ (b : ℝ) * β := h1
          _ ≤ max ((a : ℝ) * β) ((b : ℝ) * β) := le_max_right _ _
      rcases lt_or_gt_of_ne hij with h | h
      · exact hsep i j h
      · exact (hsep j i h).symm

/-- **The short-chain measure.** The short chains occupy exactly
`(m−1)·(mβ − 1)` of the circle. -/
theorem volume_chainSet_short_eq (β : ℝ) (hβ : 0 < β) :
    volume (chainSet β (capacity 1 β - 1))
      = ENNReal.ofReal
          (((capacity 1 β : ℝ) - 1) * ((capacity 1 β : ℝ) * β - 1)) := by
  set m := capacity 1 β with hm
  rw [chainSet_short_eq_compl β hβ,
    measure_compl (measurableSet_longSet β) (measure_ne_top _ _),
    volume_longSet_eq β hβ]
  have huniv : volume (Set.univ : Set (AddCircle (1 : ℝ)))
      = ENNReal.ofReal 1 := by
    rw [AddCircle.measure_univ]
  have hℓ0 : (0 : ℝ) ≤ 1 - ((m : ℝ) - 1) * β := by
    have := capacity_sub_one_mul_lt β hβ
    linarith
  rw [huniv, ← ENNReal.ofReal_sub _ (mul_nonneg (by positivity) hℓ0)]
  congr 1
  ring

/-- **The chain-count ratio law.** In the non-degenerate case the long
fraction of the base interval is `frac(1/β)`. -/
theorem long_base_fraction (β : ℝ) (hβ : 0 < β)
    (hshort : 1 < (capacity 1 β : ℝ) * β) :
    (1 - ((capacity 1 β : ℝ) - 1) * β) / β = Int.fract (1 / β) := by
  set m := capacity 1 β with hm
  have hub : 1 / β < (m : ℝ) := by
    rw [div_lt_iff₀ hβ]
    linarith
  have hlb : (m : ℝ) - 1 < 1 / β := by
    have := capacity_sub_one_mul_lt β hβ
    rw [lt_div_iff₀ hβ]
    linarith
  have hfloor : ⌊(1 : ℝ) / β⌋ = (m : ℤ) - 1 := by
    rw [Int.floor_eq_iff]
    constructor
    · push_cast
      linarith
    · push_cast
      linarith
  rw [Int.fract, hfloor]
  push_cast
  field_simp

end Cvs.PathLaw
