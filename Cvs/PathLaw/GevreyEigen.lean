/-
The bump-modulated top eigenfunction (rapid-decay campaign, stage 2).

The top eigenvalue `2cos(π/(m+1))` of the masked rotation is attained on
the capacity-`m` chain family with an arbitrary base amplitude `c`; the
machinery (`rungFun`, `wStep_baseEnv`, `memLp_rungFun`) exists in
`Cvs.PathLaw.ParityFold`. This file extracts the standalone eigen-equation
and non-vanishing, and establishes the pointwise window description of
the rung function needed for its Fourier coefficients: on the `p`-th
long window `[pβ, pβ + ℓ)` (with `ℓ = 1 - (m-1)β` the long base length)
the rung function is the translated amplitude times the envelope
constant `sin((p+1)·pathAngle m j)`, and it vanishes off the windows.

Next stage: the coefficient product formula
`c_n(rungFun) = (∑_p sin θ_p e^{-2πinpβ}) · c_n(amplitude)`, which
together with `rapidFourierDecay_of_smooth_bump` discharges the tail
hypothesis for smooth bump amplitudes.
-/
import Cvs.PathLaw.ParityFold
import Cvs.PathLaw.ChainMeasure
import Cvs.PathLaw.FourierDecay

open MeasureTheory Real

namespace Cvs.PathLaw

local notation "L2c" => Lp ℝ 2 (volume : Measure (AddCircle (1 : ℝ)))

/-- **The rung eigen-equation, standalone**: for any bounded measurable
base amplitude, the rung function is an eigenfunction of the masked
rotation at the rung eigenvalue. -/
theorem pathLawW_rungFunL2 (β : ℝ) (hβ : 0 < β) (L : ℕ) (j : Fin L)
    (c : ℝ → ℝ) (hcm : Measurable c) (B : ℝ) (hB : 0 ≤ B)
    (hbd : ∀ r, 0 ≤ r → r < β → |c r| ≤ B) :
    pathLawW β (rungFunL2 β hβ L j c hcm B hB hbd)
      = (2 * Real.cos (pathAngle L j))
          • rungFunL2 β hβ L j c hcm B hB hbd := by
  set g : L2c := rungFunL2 β hβ L j c hcm B hB hbd with hgdef
  have hco : (g : AddCircle (1 : ℝ) → ℝ) =ᵐ[volume] rungFun β L j c :=
    MemLp.coeFn_toLp _
  apply Lp.ext
  filter_upwards [coeFn_pathLawW_step β g _ hco,
    Lp.coeFn_smul (2 * Real.cos (pathAngle L j)) g, hco] with z hh1 hh2 hh3
  rw [hh1, hh2, Pi.smul_apply, smul_eq_mul, hh3]
  exact wStep_baseEnv β hβ L j c z

/-- The rung function is nonzero whenever the amplitude survives on a
positive-measure part of the position-zero slice. -/
theorem rungFunL2_ne_zero (β : ℝ) (hβ : 0 < β) (L : ℕ) (j : Fin L)
    (c : ℝ → ℝ) (hcm : Measurable c) (B : ℝ) (hB : 0 ≤ B)
    (hbd : ∀ r, 0 ≤ r → r < β → |c r| ≤ B)
    (hvol : 0 < volume {z : AddCircle (1 : ℝ) |
      z ∈ chainSet β L ∧ chainPos β (rep z) = 0
        ∧ c (chainBase β (rep z)) ≠ 0}) :
    rungFunL2 β hβ L j c hcm B hB hbd ≠ 0 := by
  set g : L2c := rungFunL2 β hβ L j c hcm B hB hbd with hgdef
  have hco : (g : AddCircle (1 : ℝ) → ℝ) =ᵐ[volume] rungFun β L j c :=
    MemLp.coeFn_toLp _
  intro hzero
  have hco0 := hco
  rw [hzero] at hco0
  have h0 : rungFun β L j c =ᵐ[volume] 0 :=
    hco0.symm.trans (Lp.coeFn_zero ℝ 2 volume)
  have hsub : {z : AddCircle (1 : ℝ) |
      z ∈ chainSet β L ∧ chainPos β (rep z) = 0
        ∧ c (chainBase β (rep z)) ≠ 0}
      ⊆ {z | rungFun β L j c z ≠ 0} := by
    rintro z ⟨hzS, hzpos, hzc⟩
    show rungFun β L j c z ≠ 0
    unfold rungFun
    rw [Set.indicator_of_mem hzS]
    have hsin : 0 < chainEnv β L j z := by
      unfold chainEnv
      rw [hzpos]
      push_cast
      rw [zero_add, one_mul]
      exact Real.sin_pos_of_pos_of_lt_pi (pathAngle_pos _ _)
        (pathAngle_lt_pi _ _)
    exact mul_ne_zero hzc (ne_of_gt hsin)
  have hmeas0 : volume {z : AddCircle (1 : ℝ) |
      rungFun β L j c z ≠ 0} = 0 := by
    rw [← ae_iff]
    exact h0
  have hle := measure_mono
    (μ := (volume : Measure (AddCircle (1 : ℝ)))) hsub
  rw [hmeas0] at hle
  exact absurd (le_zero_iff.mp hle) (ne_of_gt hvol)

/-! ### The window description of the long-chain family -/

/-- Chain coordinates on the `p`-th long window: for
`y ∈ [pβ, pβ + ℓ)` with `ℓ = 1 - (m-1)β`, the chain through `y` has
position `p`, base `y - pβ`, and length `m = capacity`. -/
theorem chain_coords_window (β : ℝ) (hβ : 0 < β) {p : ℕ} {y : ℝ}
    (hy : y ∈ Set.Ico ((p : ℝ) * β)
      ((p : ℝ) * β + (1 - ((capacity 1 β : ℝ) - 1) * β))) :
    chainPos β y = p
      ∧ chainBase β y = y - (p : ℝ) * β
      ∧ chainLength β (chainBase β y) = capacity 1 β := by
  set m := capacity 1 β with hm
  set ℓ : ℝ := 1 - ((m : ℝ) - 1) * β with hℓ
  have hℓβ : ℓ ≤ β := by
    have := one_le_capacity_mul β hβ
    rw [hℓ]
    nlinarith
  have hposj : chainPos β y = p := by
    unfold chainPos
    have hy0 : 0 ≤ y := le_trans (by positivity) hy.1
    rw [Nat.floor_eq_iff (div_nonneg hy0 hβ.le)]
    constructor
    · rw [le_div_iff₀ hβ]
      linarith [hy.1]
    · rw [div_lt_iff₀ hβ]
      calc y < (p : ℝ) * β + ℓ := hy.2
        _ ≤ ((p : ℝ) + 1) * β := by linarith
  have hbase : chainBase β y = y - (p : ℝ) * β := by
    unfold chainBase
    rw [hposj]
  refine ⟨hposj, hbase, ?_⟩
  rw [chainLength_eq_capacity_iff β _ hβ
    (by rw [hbase]; linarith [hy.1]) (one_le_capacity β hβ), hbase]
  have hy2 := hy.2
  rw [hℓ] at hy2
  linarith

/-- The right endpoint of every long window stays inside the circle. -/
lemma window_subset_unit (β : ℝ) (hβ : 0 < β) {p : ℕ}
    (hp : p < capacity 1 β) :
    (p : ℝ) * β + (1 - ((capacity 1 β : ℝ) - 1) * β) ≤ 1 := by
  have hcast : (p : ℝ) ≤ (capacity 1 β : ℝ) - 1 := by
    have h1 : (p : ℝ) + 1 ≤ (capacity 1 β : ℝ) := by exact_mod_cast hp
    linarith
  nlinarith [mul_le_mul_of_nonneg_right hcast hβ.le]

/-- **The rung function on the `p`-th long window** is the translated
amplitude times the envelope constant `sin((p+1)·pathAngle m j)`. -/
theorem rungFun_eval_window (β : ℝ) (hβ : 0 < β)
    (j : Fin (capacity 1 β)) (c : ℝ → ℝ) {p : ℕ}
    (hp : p < capacity 1 β) {y : ℝ}
    (hy : y ∈ Set.Ico ((p : ℝ) * β)
      ((p : ℝ) * β + (1 - ((capacity 1 β : ℝ) - 1) * β))) :
    rungFun β (capacity 1 β) j c ((y : ℝ) : AddCircle (1 : ℝ))
      = c (y - (p : ℝ) * β)
        * Real.sin (((p : ℝ) + 1) * pathAngle (capacity 1 β) j) := by
  have hy0 : 0 ≤ y := le_trans (by positivity) hy.1
  have hy1 : y < 1 :=
    lt_of_lt_of_le hy.2 (window_subset_unit β hβ hp)
  have hrep : rep ((y : ℝ) : AddCircle (1 : ℝ)) = y := rep_coe y hy0 hy1
  obtain ⟨hpos, hbase, hlen⟩ := chain_coords_window β hβ hy
  have hmem : ((y : ℝ) : AddCircle (1 : ℝ)) ∈ chainSet β (capacity 1 β) := by
    show chainLength β (chainBase β (rep _)) = capacity 1 β
    rw [hrep]
    exact hlen
  unfold rungFun
  rw [Set.indicator_of_mem hmem]
  unfold chainEnv
  rw [hrep, hbase, hpos]

/-- **Off the long windows, the rung function of the capacity family
vanishes**: membership in the length-`m` chain set forces the point into
some long window. -/
theorem rungFun_eval_off_windows (β : ℝ) (hβ : 0 < β)
    (j : Fin (capacity 1 β)) (c : ℝ → ℝ) {y : ℝ} (hy0 : 0 ≤ y)
    (hy1 : y < 1)
    (hoff : ∀ p : ℕ, p < capacity 1 β →
      y ∉ Set.Ico ((p : ℝ) * β)
        ((p : ℝ) * β + (1 - ((capacity 1 β : ℝ) - 1) * β))) :
    rungFun β (capacity 1 β) j c ((y : ℝ) : AddCircle (1 : ℝ)) = 0 := by
  have hrep : rep ((y : ℝ) : AddCircle (1 : ℝ)) = y := rep_coe y hy0 hy1
  unfold rungFun
  rw [Set.indicator_of_notMem]
  intro hmem
  have hlen : chainLength β (chainBase β y) = capacity 1 β := by
    have h := hmem
    show chainLength β (chainBase β y) = capacity 1 β
    have h2 : chainLength β (chainBase β (rep ((y : ℝ) : AddCircle (1 : ℝ))))
        = capacity 1 β := h
    rwa [hrep] at h2
  have hposlt : chainPos β y < capacity 1 β := by
    have := chainPos_lt_chainLength β y hβ hy1
    omega
  have hbase0 : 0 ≤ chainBase β y := chainBase_nonneg β y hβ hy0
  have hbaseℓ : chainBase β y < 1 - ((capacity 1 β : ℝ) - 1) * β := by
    have hiff := (chainLength_eq_capacity_iff β (chainBase β y) hβ hbase0
      (one_le_capacity β hβ)).mp hlen
    linarith
  refine hoff (chainPos β y) hposlt ?_
  have hrecon := chainBase_add β y
  constructor
  · linarith
  · linarith

end Cvs.PathLaw
