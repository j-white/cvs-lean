/-
The Single-Atom Path Law — the chain partition.

The chain lengths in the proof of Theorem 1.1 (paper Section 3). Normalising the
circle to `[0,1)`, the rotation step is `β = y/L` and the forbidden arc is
`[0, β)`. A base point `r ∈ [0, β)` generates the chain
`{r, r+β, …, r+(ℓ-1)β}` with

    ℓ(r) = ⌈(1 - r)/β⌉,

the number of steps before the orbit wraps past `1` and lands back in the
forbidden arc. The content of the proposition is that `ℓ` takes only the two
values `m` and `m-1`, where `m = ⌈1/β⌉ = ⌈L/y⌉` is the capacity — and that
the long chains are exactly those with `r < 1 - (m-1)β`.

Only ceiling arithmetic is needed, as in the paper's proof; the
Three-Distance (Steinhaus) theorem is not used.

Proved here (no `sorry`):
* `chainLength_le_capacity` and `capacity_le_chainLength_succ` — the two
  bounds;
* `chainLength_eq_or` — the two-length dichotomy `ℓ ∈ {m, m-1}`;
* `chainLength_eq_capacity_iff` — the long-chain criterion, giving the
  measure split `frac(L/y)` vs `1 - frac(L/y)`;
* `capacity_one_div` — the normalised capacity `⌈1/β⌉` agrees with the
  paper's `m = ⌈L/y⌉`.
-/
import Cvs.PathLaw.Spectrum

open Real

namespace Cvs.PathLaw

/-- The chain length of a base point `r ∈ [0, β)`: the number of steps of
size `β` the orbit takes before wrapping past `1` (the paper's `ℓ(r)`). -/
noncomputable def chainLength (β r : ℝ) : ℕ := ⌈(1 - r) / β⌉₊

/-- Normalising the circle: `⌈1/(y/L)⌉ = ⌈L/y⌉`, so the chain capacity in the
normalised picture is the paper's `m`. -/
theorem capacity_one_div (L y : ℝ) :
    capacity 1 (y / L) = capacity L y := by
  unfold capacity
  congr 1
  rw [one_div_div]

/-! ### The two bounds -/

/-- A chain is never longer than the capacity. -/
theorem chainLength_le_capacity (β r : ℝ) (hβ : 0 < β) (hr0 : 0 ≤ r) :
    chainLength β r ≤ capacity 1 β := by
  unfold chainLength capacity
  apply Nat.ceil_mono
  gcongr
  linarith

/-- A chain is never shorter than `m - 1`. -/
theorem capacity_le_chainLength_succ (β r : ℝ) (hβ : 0 < β) (hrβ : r < β) :
    capacity 1 β ≤ chainLength β r + 1 := by
  by_contra hcon
  push Not at hcon
  -- `hcon : chainLength β r + 1 < capacity 1 β`
  have hstep : (chainLength β r : ℝ) + 2 ≤ (capacity 1 β : ℝ) := by
    have : chainLength β r + 2 ≤ capacity 1 β := by omega
    exact_mod_cast this
  -- the ceiling of `1/β` is less than `1/β + 1`
  have hm : (capacity 1 β : ℝ) < 1 / β + 1 := by
    unfold capacity
    have hnn : (0 : ℝ) ≤ 1 / β := by positivity
    exact Nat.ceil_lt_add_one hnn
  -- the chain length dominates `(1 - r)/β`
  have hge : (1 - r) / β ≤ (chainLength β r : ℝ) := Nat.le_ceil _
  -- but `(1 - r)/β > 1/β - 1`
  have hgt : 1 / β - 1 < (1 - r) / β := by
    rw [sub_lt_iff_lt_add, div_add' _ _ _ (ne_of_gt hβ), div_lt_div_iff_of_pos_right hβ]
    linarith
  linarith

/-! ### The two-length dichotomy -/

/-- **Two-length chain partition** (paper Section 3). Every base point
`r ∈ [0, β)` generates a chain of length either `m = ⌈1/β⌉` or `m - 1`. -/
theorem chainLength_eq_or (β r : ℝ) (hβ : 0 < β) (hr0 : 0 ≤ r) (hrβ : r < β) :
    chainLength β r = capacity 1 β ∨ chainLength β r + 1 = capacity 1 β := by
  have h1 := chainLength_le_capacity β r hβ hr0
  have h2 := capacity_le_chainLength_succ β r hβ hrβ
  omega

/-! ### The long-chain criterion and the measure split -/

/-- **The long-chain criterion.** A base point generates a chain of the full
capacity `m` exactly when `r < 1 - (m-1)β`. Since
`1 - (m-1)β = frac(1/β)·β`, this is the split of the paper's Section 3: long chains
occupy a proportion `frac(L/y)` of the base interval and short chains
`1 - frac(L/y)`. -/
theorem chainLength_eq_capacity_iff (β r : ℝ) (hβ : 0 < β) (hr0 : 0 ≤ r)
    (hcap : 1 ≤ capacity 1 β) :
    chainLength β r = capacity 1 β
      ↔ ((capacity 1 β : ℝ) - 1) * β < 1 - r := by
  constructor
  · intro h
    have hlt : ((capacity 1 β : ℝ) - 1) < (1 - r) / β := by
      have hnat : capacity 1 β - 1 < chainLength β r := by omega
      have := (Nat.lt_ceil (α := ℝ)).mp (by simpa [chainLength] using hnat)
      have hcast : ((capacity 1 β - 1 : ℕ) : ℝ) = (capacity 1 β : ℝ) - 1 := by
        have : (1 : ℕ) ≤ capacity 1 β := hcap
        push_cast [Nat.cast_sub this]
        ring
      rwa [hcast] at this
    rw [lt_div_iff₀ hβ] at hlt
    linarith
  · intro h
    have hlt : ((capacity 1 β : ℝ) - 1) < (1 - r) / β := by
      rw [lt_div_iff₀ hβ]
      linarith
    have hge : capacity 1 β ≤ chainLength β r := by
      by_contra hcon
      push Not at hcon
      have hle : (chainLength β r : ℝ) ≤ (capacity 1 β : ℝ) - 1 := by
        have : chainLength β r + 1 ≤ capacity 1 β := hcon
        have : (chainLength β r : ℝ) + 1 ≤ (capacity 1 β : ℝ) := by exact_mod_cast this
        linarith
      have := Nat.le_ceil (R := ℝ) ((1 - r) / β)
      have hcl : (1 - r) / β ≤ (chainLength β r : ℝ) := this
      linarith
    have hle := chainLength_le_capacity β r hβ hr0
    omega

/-! ### Chain coordinates

Every point `x ∈ [0,1)` lies in exactly one chain, at a well-defined position
along it. Writing `x = r + jβ` with `r ∈ [0, β)` the base point and
`j ∈ ℕ` the step index (the coordinates `s = r + ky` of the paper's
Section 3), these are the coordinates in which `W` acts as the
path-graph adjacency matrix. -/

/-- The position of `x` along its chain: `j = ⌊x/β⌋`. -/
noncomputable def chainPos (β x : ℝ) : ℕ := ⌊x / β⌋₊

/-- The base point of the chain through `x`: `r = x - jβ ∈ [0, β)`. -/
noncomputable def chainBase (β x : ℝ) : ℝ := x - (chainPos β x : ℝ) * β

/-- Reconstruction: `x = r + jβ`. -/
theorem chainBase_add (β x : ℝ) :
    chainBase β x + (chainPos β x : ℝ) * β = x := by
  unfold chainBase
  ring

theorem chainBase_nonneg (β x : ℝ) (hβ : 0 < β) (hx : 0 ≤ x) :
    0 ≤ chainBase β x := by
  unfold chainBase chainPos
  have h : (⌊x / β⌋₊ : ℝ) ≤ x / β := Nat.floor_le (by positivity)
  rw [sub_nonneg, ← le_div_iff₀ hβ]
  exact h

theorem chainBase_lt (β x : ℝ) (hβ : 0 < β) :
    chainBase β x < β := by
  unfold chainBase chainPos
  have h : x / β < (⌊x / β⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [sub_lt_iff_lt_add, ← sub_lt_iff_lt_add']
  rw [div_lt_iff₀ hβ] at h
  linarith

/-- **The key structural fact.** A point of the circle sits at a position
strictly inside its own chain: `j < ℓ(r)`. Equivalently, the chain through
`x` is long enough to contain `x` — which is exactly the statement that the
orbit has not yet wrapped past `1`. -/
theorem chainPos_lt_chainLength (β x : ℝ) (hβ : 0 < β) (hx1 : x < 1) :
    chainPos β x < chainLength β (chainBase β x) := by
  unfold chainLength
  rw [Nat.lt_ceil]
  rw [lt_div_iff₀ hβ]
  have hrec := chainBase_add β x
  nlinarith [hrec]

/-! ### The chain weight

The chain weight is the top eigenvector of the path graph, evaluated at the
chain position: `w(x) = sin((j+1)π/(k+1))` where `j` is the position and `k`
the length of the chain through `x`. This is `pathEigenvector` of
`Cvs.PathLaw.Spectrum` transported to the circle. The Schur weight of
`Cvs.PathLaw.Weight` is the ratio `√(w(z)/w(z+β))`. -/

/-- The chain weight `w(x) = sin((j+1)π/(k+1))`. -/
noncomputable def chainWeight (β x : ℝ) : ℝ :=
  Real.sin (((chainPos β x : ℝ) + 1) * π
    / ((chainLength β (chainBase β x) : ℝ) + 1))

/-- **The chain weight is strictly positive.** This is what makes it usable
as a Schur weight: the angle `(j+1)π/(k+1)` lies strictly between `0` and `π`
precisely because `j < k` (`chainPos_lt_chainLength`). -/
theorem chainWeight_pos (β x : ℝ) (hβ : 0 < β) (hx1 : x < 1) :
    0 < chainWeight β x := by
  unfold chainWeight
  set j := chainPos β x with hj
  set k := chainLength β (chainBase β x) with hk
  have hjk : j < k := chainPos_lt_chainLength β x hβ hx1
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_
  · have : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    positivity
  · rw [div_lt_iff₀ hk1]
    have hcast : ((j : ℝ) + 1) < (k : ℝ) + 1 := by
      have : (j : ℝ) < (k : ℝ) := by exact_mod_cast hjk
      linarith
    nlinarith [pi_pos]

/-- The chain weight is bounded above by `1`. -/
theorem chainWeight_le_one (β x : ℝ) : chainWeight β x ≤ 1 :=
  Real.sin_le_one _

/-! ### The chain weight is bounded away from zero

For the Schur factorization the *reciprocal* weight must also be bounded, so
the weight needs a positive lower bound. Since the chain position satisfies
`0 ≤ j < k`, the angle `(j+1)π/(k+1)` lies in the symmetric interval
`[π/(k+1), π - π/(k+1)]`, where sine is at least `sin(π/(k+1))`. -/

/-- On the symmetric interval `[a, π - a]`, sine is bounded below by `sin a`. -/
private lemma sin_ge_of_mem_symm (a θ : ℝ) (ha0 : 0 ≤ a) (ha2 : a ≤ π / 2)
    (h1 : a ≤ θ) (h2 : θ ≤ π - a) : Real.sin a ≤ Real.sin θ := by
  rcases le_total θ (π / 2) with h | h
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) h h1
  · rw [← Real.sin_pi_sub θ]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith)
      (by linarith)

/-- **Positive lower bound for the chain weight.** If every chain has length
at most `m`, then `w(x) ≥ sin(π/(m+1)) > 0`. This is what makes the
reciprocal weight `1/w` bounded, and hence `M_{1/√w}` a bounded operator. -/
theorem chainWeight_ge (β x : ℝ) (hβ : 0 < β) (hx1 : x < 1) (m : ℕ)
    (hm : chainLength β (chainBase β x) ≤ m) :
    Real.sin (π / ((m : ℝ) + 1)) ≤ chainWeight β x := by
  have hjk : chainPos β x < chainLength β (chainBase β x) :=
    chainPos_lt_chainLength β x hβ hx1
  unfold chainWeight
  set j := chainPos β x with hjdef
  set k := chainLength β (chainBase β x) with hkdef
  have hk1 : 1 ≤ k := by omega
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hmR : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hjk' : ((j : ℝ) + 1) ≤ (k : ℝ) := by
    have : j + 1 ≤ k := hjk
    exact_mod_cast this
  have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hmpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hka : π / ((k : ℝ) + 1) ≤ π / 2 := by
    rw [div_le_div_iff₀ hkpos (by norm_num : (0:ℝ) < 2)]
    nlinarith [pi_pos]
  -- inner bound: `sin(π/(k+1)) ≤ w(x)`
  have hstep1 : Real.sin (π / ((k : ℝ) + 1))
      ≤ Real.sin (((j : ℝ) + 1) * π / ((k : ℝ) + 1)) := by
    refine sin_ge_of_mem_symm _ _ (by positivity) hka ?_ ?_
    · rw [div_le_div_iff₀ hkpos hkpos]
      nlinarith [pi_pos, mul_nonneg (mul_nonneg hj0 pi_pos.le) hkpos.le]
    · have hrw : π - π / ((k : ℝ) + 1) = (k : ℝ) * π / ((k : ℝ) + 1) := by
        field_simp
        ring
      rw [hrw, div_le_div_iff₀ hkpos hkpos]
      nlinarith [pi_pos,
        mul_nonneg (mul_nonneg (sub_nonneg.mpr hjk') pi_pos.le) hkpos.le]
  -- outer bound: `sin(π/(m+1)) ≤ sin(π/(k+1))`
  have hstep2 : Real.sin (π / ((m : ℝ) + 1)) ≤ Real.sin (π / ((k : ℝ) + 1)) := by
    have hnn : (0 : ℝ) ≤ π / ((m : ℝ) + 1) := by positivity
    refine Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) hka ?_
    gcongr
  linarith

/-- The lower bound at the capacity: every chain weight is at least
`sin(π/(m+1))` with `m = ⌈1/β⌉`. -/
theorem chainWeight_ge_capacity (β x : ℝ) (hβ : 0 < β) (hx0 : 0 ≤ x)
    (hx1 : x < 1) :
    Real.sin (π / ((capacity 1 β : ℝ) + 1)) ≤ chainWeight β x :=
  chainWeight_ge β x hβ hx1 _
    (chainLength_le_capacity β _ hβ (chainBase_nonneg β x hβ hx0))

/-! ### How the chain coordinates transform under a rotation step

Advancing by one rotation step moves a point one place along its chain,
leaving the base point — hence the chain and its length — unchanged. -/

theorem chainPos_add_step (β x : ℝ) (hβ : 0 < β) (hx : 0 ≤ x) :
    chainPos β (x + β) = chainPos β x + 1 := by
  unfold chainPos
  have h : (x + β) / β = x / β + 1 := by field_simp
  rw [h, Nat.floor_add_one (by positivity)]

theorem chainBase_add_step (β x : ℝ) (hβ : 0 < β) (hx : 0 ≤ x) :
    chainBase β (x + β) = chainBase β x := by
  unfold chainBase
  rw [chainPos_add_step β x hβ hx]
  push_cast
  ring

/-- A point at a nonzero chain position came from the previous position. -/
theorem chainPos_sub_step (β x : ℝ) (hβ : 0 < β) (hpos : 1 ≤ chainPos β x) :
    chainPos β (x - β) + 1 = chainPos β x := by
  have hxβ : β ≤ x := by
    by_contra hcon
    push Not at hcon
    have : x / β < 1 := by
      rw [div_lt_one hβ]
      exact hcon
    have : chainPos β x = 0 := by
      unfold chainPos
      exact Nat.floor_eq_zero.mpr this
    omega
  have h0 : 0 ≤ x - β := by linarith
  have h := chainPos_add_step β (x - β) hβ h0
  rw [sub_add_cancel] at h
  exact h.symm

theorem chainBase_sub_step (β x : ℝ) (hβ : 0 < β) (hpos : 1 ≤ chainPos β x) :
    chainBase β (x - β) = chainBase β x := by
  have hxβ : β ≤ x := by
    by_contra hcon
    push Not at hcon
    have hlt : x / β < 1 := by rw [div_lt_one hβ]; exact hcon
    have : chainPos β x = 0 := by
      unfold chainPos
      exact Nat.floor_eq_zero.mpr hlt
    omega
  have h0 : 0 ≤ x - β := by linarith
  have h := chainBase_add_step β (x - β) hβ h0
  rw [sub_add_cancel] at h
  exact h.symm

/-! ### The weight recurrence — the Schur condition

The chain weight satisfies the path-graph eigenvector equation along each
chain. This is `sin_rung` of `Cvs.PathLaw.Spectrum` transported to the circle,
and it is exactly the Schur condition that will bound the masked rotation by
the Chebyshev factor. -/

theorem chainWeight_add_step (β x : ℝ) (hβ : 0 < β) (hx : 0 ≤ x) :
    chainWeight β (x + β)
      = Real.sin (((chainPos β x : ℝ) + 2) * π
          / ((chainLength β (chainBase β x) : ℝ) + 1)) := by
  unfold chainWeight
  rw [chainPos_add_step β x hβ hx, chainBase_add_step β x hβ hx]
  push_cast
  ring_nf

theorem chainWeight_sub_step (β x : ℝ) (hβ : 0 < β) (hpos : 1 ≤ chainPos β x) :
    chainWeight β (x - β)
      = Real.sin ((chainPos β x : ℝ) * π
          / ((chainLength β (chainBase β x) : ℝ) + 1)) := by
  unfold chainWeight
  rw [chainBase_sub_step β x hβ hpos]
  congr 1
  have hstep := chainPos_sub_step β x hβ hpos
  have hc : ((chainPos β (x - β) : ℝ) + 1) = (chainPos β x : ℝ) := by
    exact_mod_cast hstep
  rw [hc]

/-- **The Schur condition.** At an interior chain position the weight
satisfies the path-graph eigenvector equation
`w(x-β) + w(x+β) = 2cos(π/(k+1)) · w(x)`, with `k` the length of the chain
through `x`. -/
theorem chainWeight_recurrence (β x : ℝ) (hβ : 0 < β) (hx : 0 ≤ x)
    (hpos : 1 ≤ chainPos β x) :
    chainWeight β (x - β) + chainWeight β (x + β)
      = 2 * Real.cos (π / ((chainLength β (chainBase β x) : ℝ) + 1))
        * chainWeight β x := by
  rw [chainWeight_sub_step β x hβ hpos, chainWeight_add_step β x hβ hx]
  unfold chainWeight
  have hrung := sin_rung (π / ((chainLength β (chainBase β x) : ℝ) + 1))
    (chainPos β x)
  simp only [mul_div_assoc]
  linarith [hrung]

/-! ### The pointwise Schur bound

Combining the recurrence with positivity of the weight gives the inequality
that drives the whole estimate: at every point, the weights of the *admissible*
neighbours sum to at most `chebFactor m` times the weight at the point. The
two `if`s are the masks — a neighbour contributes only when the hop stays
inside the chain. -/

lemma chainPos_ge_one (β r : ℝ) (hβ : 0 < β) (h : β ≤ r) :
    1 ≤ chainPos β r := by
  unfold chainPos
  apply Nat.le_floor
  rw [Nat.cast_one, le_div_iff₀ hβ, one_mul]
  exact h

/-- **The pointwise Schur bound.** -/
theorem chainWeight_schur (β r : ℝ) (hβ : 0 < β) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (m : ℕ) (hm : chainLength β (chainBase β r) ≤ m) :
    (if r + β < 1 then chainWeight β (r + β) else 0)
        + (if β ≤ r then chainWeight β (r - β) else 0)
      ≤ chebFactor m * chainWeight β r := by
  have hjk : chainPos β r < chainLength β (chainBase β r) :=
    chainPos_lt_chainLength β r hβ hr1
  set j := chainPos β r with hjdef
  set k := chainLength β (chainBase β r) with hkdef
  have hk1 : 1 ≤ k := by omega
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hjk' : ((j : ℝ) + 1) ≤ (k : ℝ) := by
    have : j + 1 ≤ k := hjk
    exact_mod_cast this
  set θ := π / ((k : ℝ) + 1) with hθ
  have hθpos : 0 < θ := by rw [hθ]; positivity
  -- the two neighbour weights, as sines
  have e_fwd : chainWeight β (r + β) = Real.sin (((j : ℝ) + 2) * θ) := by
    rw [chainWeight_add_step β r hβ hr0, hθ, mul_div_assoc]
  have e_bwd : β ≤ r → chainWeight β (r - β) = Real.sin ((j : ℝ) * θ) := by
    intro hbr
    rw [chainWeight_sub_step β r hβ (chainPos_ge_one β r hβ hbr), hθ, mul_div_assoc]
  -- both are nonnegative
  have hfwd_nn : 0 ≤ Real.sin (((j : ℝ) + 2) * θ) := by
    refine Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) ?_
    rw [hθ, mul_div_assoc' , div_le_iff₀ hkpos]
    nlinarith [pi_pos]
  have hbwd_nn : 0 ≤ Real.sin ((j : ℝ) * θ) := by
    refine Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) ?_
    rw [hθ, mul_div_assoc', div_le_iff₀ hkpos]
    nlinarith [pi_pos]
  -- drop the masks
  have h1 : (if r + β < 1 then chainWeight β (r + β) else 0)
      ≤ Real.sin (((j : ℝ) + 2) * θ) := by
    split_ifs with h
    · rw [e_fwd]
    · exact hfwd_nn
  have h2 : (if β ≤ r then chainWeight β (r - β) else 0)
      ≤ Real.sin ((j : ℝ) * θ) := by
    split_ifs with h
    · rw [e_bwd h]
    · exact hbwd_nn
  -- the recurrence
  have hrung := sin_rung θ j
  -- the weight at `r`
  have hw : chainWeight β r = Real.sin (((j : ℝ) + 1) * θ) := by
    unfold chainWeight
    rw [← hjdef, ← hkdef, hθ, mul_div_assoc]
  have hwpos : 0 < chainWeight β r := chainWeight_pos β r hβ hr1
  -- compare the Chebyshev factors
  have hcos : Real.cos θ ≤ Real.cos (π / ((m : ℝ) + 1)) := by
    have hmR : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    refine Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) ?_ ?_
    · rw [hθ]
      exact div_le_self pi_pos.le (by linarith)
    · rw [hθ]
      gcongr
  have hfinal : 2 * Real.cos θ * chainWeight β r
      ≤ chebFactor m * chainWeight β r := by
    unfold chebFactor
    have := mul_le_mul_of_nonneg_right hcos hwpos.le
    linarith
  rw [hw] at hwpos hfinal ⊢
  linarith [hrung, h1, h2, hfinal]

/-! ### The Schur bound is an equality

The masks only ever delete terms that already vanish: at the start of a chain
the backward weight is `sin 0 = 0`, at the end the forward weight is
`sin π = 0`. So the pointwise bound is in fact an identity — the chain weight
is an exact eigenvector of the masked rotation. -/

/-- A point whose forward hop would wrap is the last of its chain. -/
theorem chainPos_succ_eq_chainLength (β r : ℝ) (hβ : 0 < β) (hr1 : r < 1)
    (h : 1 ≤ r + β) :
    chainPos β r + 1 = chainLength β (chainBase β r) := by
  unfold chainLength
  symm
  rw [Nat.ceil_eq_iff (by omega)]
  have hbase : chainBase β r = r - (chainPos β r : ℝ) * β := rfl
  constructor
  · have hcast : ((chainPos β r + 1 - 1 : ℕ) : ℝ) = (chainPos β r : ℝ) := by
      simp
    rw [hcast, hbase, lt_div_iff₀ hβ]
    linarith
  · push_cast
    rw [hbase, div_le_iff₀ hβ]
    linarith

/-- **The pointwise Schur bound is an equality.** -/
theorem chainWeight_schur_eq (β r : ℝ) (hβ : 0 < β) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (if r + β < 1 then chainWeight β (r + β) else 0)
        + (if β ≤ r then chainWeight β (r - β) else 0)
      = 2 * Real.cos (π / ((chainLength β (chainBase β r) : ℝ) + 1))
        * chainWeight β r := by
  have hjk : chainPos β r < chainLength β (chainBase β r) :=
    chainPos_lt_chainLength β r hβ hr1
  set j := chainPos β r with hjdef
  set k := chainLength β (chainBase β r) with hkdef
  have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  set θ := π / ((k : ℝ) + 1) with hθ
  -- the forward term
  have e_fwd : (if r + β < 1 then chainWeight β (r + β) else 0)
      = Real.sin (((j : ℝ) + 2) * θ) := by
    split_ifs with hf
    · rw [chainWeight_add_step β r hβ hr0, hθ, mul_div_assoc]
    · -- the hop wraps, so `r` is last: `(j+2)θ = π` and the sine vanishes
      push Not at hf
      have hlast : j + 1 = k := chainPos_succ_eq_chainLength β r hβ hr1 hf
      have hcast : ((j : ℝ) + 2) * θ = π := by
        rw [hθ]
        have : ((k : ℝ) + 1) = (j : ℝ) + 2 := by
          have : (j : ℝ) + 1 = (k : ℝ) := by exact_mod_cast hlast
          linarith
        rw [this]
        field_simp
      rw [hcast, Real.sin_pi]
  -- the backward term
  have e_bwd : (if β ≤ r then chainWeight β (r - β) else 0)
      = Real.sin ((j : ℝ) * θ) := by
    split_ifs with hb
    · rw [chainWeight_sub_step β r hβ (chainPos_ge_one β r hβ hb), hθ, mul_div_assoc]
    · -- no backward neighbour, and `j = 0` so the sine vanishes
      push Not at hb
      have hj0 : j = 0 := by
        unfold chainPos at hjdef
        rw [hjdef]
        exact Nat.floor_eq_zero.mpr (by rw [div_lt_one hβ]; exact hb)
      rw [hj0]
      simp
  rw [e_fwd, e_bwd]
  have hrung := sin_rung θ j
  have hw : chainWeight β r = Real.sin (((j : ℝ) + 1) * θ) := by
    unfold chainWeight
    rw [← hjdef, ← hkdef, hθ, mul_div_assoc]
  rw [hw]
  linarith [hrung]

end Cvs.PathLaw
