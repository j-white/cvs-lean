import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Cvs.WeilForm.MaskedShift.PathGraphSpectrum

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

open Real

namespace Cvs.Operator

/-!
# Chain arithmetic on `[0,1)`

The three-distance skeleton, as pure real arithmetic: no operators, no measure theory.
-/

/-- The chain capacity: `⌈L / y⌉`. -/
noncomputable def cap (L y : ℝ) : ℕ := ⌈L / y⌉₊

/-- The chain length of a base point `r ∈ [0, β)`: the number of steps of
size `β` the orbit takes before wrapping past `1` (the paper's `ℓ(r)`). -/
noncomputable def chainLength (β r : ℝ) : ℕ := ⌈(1 - r) / β⌉₊

/-- Normalising the circle: `⌈1/(y/L)⌉ = ⌈L/y⌉`, so the chain cap in the
normalised picture is the paper's `m`. -/
theorem cap_one_div (L y : ℝ) :
    cap 1 (y / L) = cap L y := by
  unfold cap
  congr 1
  rw [one_div_div]

/-! ### The two bounds -/

/-- A chain is never longer than the cap. -/
theorem chainLength_le_cap (β r : ℝ) (hβ : 0 < β) (hr0 : 0 ≤ r) :
    chainLength β r ≤ cap 1 β := by
  unfold chainLength cap
  apply Nat.ceil_mono
  gcongr
  linarith

/-! ### The two-length dichotomy -/

/-! ### The long-chain criterion and the measure split -/

/-- **The long-chain criterion.** A base point generates a chain of the full cap `m` exactly when
`r < 1 - (m-1)β`. -/
theorem chainLength_eq_cap_iff (β r : ℝ) (hβ : 0 < β) (hr0 : 0 ≤ r)
    (hcap : 1 ≤ cap 1 β) :
    chainLength β r = cap 1 β
      ↔ ((cap 1 β : ℝ) - 1) * β < 1 - r := by
  constructor
  · intro h
    have hlt : ((cap 1 β : ℝ) - 1) < (1 - r) / β := by
      have hnat : cap 1 β - 1 < chainLength β r := by omega
      have := (Nat.lt_ceil (α := ℝ)).mp (by simpa [chainLength] using hnat)
      have hcast : ((cap 1 β - 1 : ℕ) : ℝ) = (cap 1 β : ℝ) - 1 := by
        have : (1 : ℕ) ≤ cap 1 β := hcap
        push_cast [Nat.cast_sub this]
        ring
      rwa [hcast] at this
    rw [lt_div_iff₀ hβ] at hlt
    linarith
  · intro h
    have hlt : ((cap 1 β : ℝ) - 1) < (1 - r) / β := by
      rw [lt_div_iff₀ hβ]
      linarith
    have hge : cap 1 β ≤ chainLength β r := by
      by_contra hcon
      push Not at hcon
      have hle : (chainLength β r : ℝ) ≤ (cap 1 β : ℝ) - 1 := by
        have : chainLength β r + 1 ≤ cap 1 β := hcon
        have : (chainLength β r : ℝ) + 1 ≤ (cap 1 β : ℝ) := by exact_mod_cast this
        linarith
      have := Nat.le_ceil (R := ℝ) ((1 - r) / β)
      have hcl : (1 - r) / β ≤ (chainLength β r : ℝ) := this
      linarith
    have hle := chainLength_le_cap β r hβ hr0
    omega

/-!
### Chain coordinates

Every point `x ∈ [0,1)` lies in exactly one chain, at a well-defined position along it.
-/

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

/-- **The key structural fact.** A point of the circle sits at a position strictly inside its own
chain: `j < ℓ(r)`. -/
theorem chainPos_lt_chainLength (β x : ℝ) (hβ : 0 < β) (hx1 : x < 1) :
    chainPos β x < chainLength β (chainBase β x) := by
  unfold chainLength
  rw [Nat.lt_ceil]
  rw [lt_div_iff₀ hβ]
  have hrec := chainBase_add β x
  nlinarith [hrec]

/-! ### The chain weight

The Schur weight of the Three-Distance argument is the top eigenvector of the
path graph, evaluated at the chain position: `w(x) = sin((j+1)π/(k+1))` where
`j` is the position and `k` the length of the chain through `x`. This is
`pathEigenvector` of `Cvs.Zeta.Spectrum` transported to the circle. -/

/-- The Three-Distance chain weight `w(x) = sin((j+1)π/(k+1))`. -/
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

/-- The lower bound at the cap: every chain weight is at least
`sin(π/(m+1))` with `m = ⌈1/β⌉`. -/
theorem chainWeight_ge_cap (β x : ℝ) (hβ : 0 < β) (hx0 : 0 ≤ x)
    (hx1 : x < 1) :
    Real.sin (π / ((cap 1 β : ℝ) + 1)) ≤ chainWeight β x :=
  chainWeight_ge β x hβ hx1 _
    (chainLength_le_cap β _ hβ (chainBase_nonneg β x hβ hx0))

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
chain. This is `sin_rung` of `Cvs.Zeta.Spectrum` transported to the circle,
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

/-- **The Schur condition.** At an interior chain position the weight satisfies the path-graph
eigenvector equation `w(x-β) + w(x+β) = 2cos(π/(k+1)) · w(x)`, with `k` the length of the
chain through `x`. -/
theorem chainWeight_recurrence (β x : ℝ) (hβ : 0 < β) (hx : 0 ≤ x)
    (hpos : 1 ≤ chainPos β x) :
    chainWeight β (x - β) + chainWeight β (x + β)
      = 2 * Real.cos (π / ((chainLength β (chainBase β x) : ℝ) + 1))
        * chainWeight β x := by
  rw [chainWeight_sub_step β x hβ hpos, chainWeight_add_step β x hβ hx]
  unfold chainWeight
  have hrung := Cvs.Operator.sin_rung (π / ((chainLength β (chainBase β x) : ℝ) + 1))
    (chainPos β x)
  simp only [mul_div_assoc]
  linarith [hrung]

end Cvs.Operator
