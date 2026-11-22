/-
The parity fold: the odd sector inherits the norm.

The reflection `R f(z) = f(−z)` commutes with the masked rotation, splitting
`L²(𝕋)` into even and odd sectors; the paper's odd-sector matrix `ΔO_q` is
`−Λ(q)/√q` times the odd-sector compression (up to the DTFT). This file proves, at the operator level (no `N → ∞`
limit), that the fold inherits the full norm:

  `‖compress oddSpace (pathLawW β)‖ = chebFactor ⌈1/β⌉`.

The mechanism is delicate: the top sine envelope is *reversal-even* along
each chain, so the odd eigenvector cannot be the plain envelope. Instead,
reflection acts on the long-chain base interval `[0, ℓ)` by `r ↦ ℓ − r`, and
the eigenvector `(base − ℓ/2) · envelope · 1_long` — the top envelope
modulated by an odd function of the base — is an exact `R`-odd eigenvector
of `W` with the top eigenvalue. Masked hops never change the base, so any
base modulation of an envelope eigenfunction is again an eigenfunction.
-/
import Cvs.PathLaw.SpectralSet
import Cvs.PathLaw.Compression

open MeasureTheory Polynomial Real

namespace Cvs.PathLaw

local notation "L2c" => Lp ℝ 2 (volume : Measure (AddCircle (1 : ℝ)))

/-! ### The reflection operator -/

/-- The reflection `f ↦ f(−·)` on `L²(𝕋)`, a linear isometry since Haar
measure is negation-invariant. -/
noncomputable def reflectL2 : L2c →L[ℝ] L2c :=
  (Lp.compMeasurePreservingₗᵢ ℝ (fun x : AddCircle (1 : ℝ) => -x)
    (Measure.measurePreserving_neg volume)).toContinuousLinearMap

lemma reflect_ae (f : L2c) :
    (reflectL2 f : AddCircle (1 : ℝ) → ℝ)
      =ᵐ[volume] fun z => f (-z) := by
  filter_upwards [Lp.coeFn_compMeasurePreserving f
    (Measure.measurePreserving_neg volume)] with z hz using hz

/-! ### Null singletons on the circle -/

lemma volume_singleton_addCircle (z : AddCircle (1 : ℝ)) :
    volume ({z} : Set (AddCircle (1 : ℝ))) = 0 := by
  have hproj := AddCircle.add_projection_respects_measure (T := (1 : ℝ)) 0
    (measurableSet_singleton z)
  rw [hproj]
  refine Set.Subsingleton.measure_zero ?_ _
  rintro y₁ ⟨hy₁, hIoc₁⟩ y₂ ⟨hy₂, hIoc₂⟩
  have h₁ : ((y₁ : ℝ) : AddCircle (1 : ℝ)) = z := hy₁
  have h₂ : ((y₂ : ℝ) : AddCircle (1 : ℝ)) = z := hy₂
  have hIoc₁' : y₁ ∈ Set.Ioc (0 : ℝ) (0 + 1) := hIoc₁
  have hIoc₂' : y₂ ∈ Set.Ioc (0 : ℝ) (0 + 1) := hIoc₂
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ioc hIoc₁' hIoc₂').mp
    (h₁.trans h₂.symm)

/-- Finitely many representative values cut out a null set of the circle. -/
lemma volume_rep_mem_null {B : Set ℝ} (hB : B.Finite) :
    volume {z : AddCircle (1 : ℝ) | rep z ∈ B} = 0 := by
  have hsub : {z : AddCircle (1 : ℝ) | rep z ∈ B}
      ⊆ ⋃ b ∈ B, {((b : ℝ) : AddCircle (1 : ℝ))} := by
    intro z hz
    refine Set.mem_biUnion hz ?_
    show z ∈ {((rep z : ℝ) : AddCircle (1 : ℝ))}
    rw [Set.mem_singleton_iff, coe_rep]
  refine measure_mono_null hsub ?_
  refine (measure_biUnion_null_iff hB.countable).mpr fun b _ =>
    volume_singleton_addCircle _

/-! ### Reflection of representatives and chains -/

/-- `rep(−z) = 1 − rep z` away from the base point. -/
lemma rep_neg (z : AddCircle (1 : ℝ)) (hz : rep z ≠ 0) :
    rep (-z) = 1 - rep z := by
  have h0 : 0 < rep z := lt_of_le_of_ne (rep_nonneg z) (Ne.symm hz)
  have h1 : rep z < 1 := rep_lt_one z
  have hadd : ((1 - rep z : ℝ) : AddCircle (1 : ℝ))
      + ((rep z : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    rw [← AddCircle.coe_add]
    norm_num
  rw [coe_rep z] at hadd
  have hneg : -z = ((1 - rep z : ℝ) : AddCircle (1 : ℝ)) :=
    neg_eq_of_add_eq_zero_left hadd
  rw [hneg, rep_coe _ (by linarith) (by linarith)]

/-- **Chain reversal.** Reflection `x ↦ 1 − x` maps the chain through `x`
(base `r`, position `j`, length `len`) to a chain of the same length with
base `1 − r − (len−1)β` and position `len − 1 − j`, provided the reflected
base does not hit the boundary (`r + len·β ≠ 1`, a null condition). -/
lemma chain_reflect (β x : ℝ) (hβ : 0 < β) (hx0 : 0 < x) (hx1 : x < 1)
    (hbase0 : 0 < chainBase β x)
    (hne : chainBase β x + (chainLength β (chainBase β x) : ℝ) * β ≠ 1) :
    chainPos β (1 - x)
        = chainLength β (chainBase β x) - 1 - chainPos β x
      ∧ chainBase β (1 - x)
        = 1 - chainBase β x - ((chainLength β (chainBase β x) : ℝ) - 1) * β
      ∧ chainLength β (chainBase β (1 - x))
        = chainLength β (chainBase β x) := by
  set r := chainBase β x with hr
  set j := chainPos β x with hj
  set len := chainLength β r with hlen
  have hr0 : 0 ≤ r := chainBase_nonneg β x hβ hx0.le
  have hrβ : r < β := chainBase_lt β x hβ
  have hrecon : r + (j : ℝ) * β = x := chainBase_add β x
  have hjlen : j < len := chainPos_lt_chainLength β x hβ hx1
  have hjβ : (0 : ℝ) ≤ (j : ℝ) * β := by positivity
  have hr1 : r < 1 := by
    have : r ≤ x := by linarith [hrecon]
    linarith
  have hdivpos : (0 : ℝ) ≤ (1 - r) / β := by
    apply div_nonneg _ hβ.le
    linarith
  -- the chain-length inequalities: (len−1)β < 1 − r ≤ len·β
  have hlen_up : (1 - r) / β ≤ (len : ℝ) := by
    rw [hlen]
    unfold chainLength
    exact Nat.le_ceil _
  have hlen_lo : ((len : ℝ)) - 1 < (1 - r) / β := by
    have hceil := Nat.ceil_lt_add_one hdivpos
    rw [hlen]
    unfold chainLength
    linarith [hceil]
  have hup : 1 - r ≤ (len : ℝ) * β := by
    rw [div_le_iff₀ hβ] at hlen_up
    linarith
  have hlo : ((len : ℝ) - 1) * β < 1 - r :=
    (lt_div_iff₀ hβ).mp hlen_lo
  have hstrict : 1 - r < (len : ℝ) * β := by
    rcases lt_or_eq_of_le hup with h | h
    · exact h
    · exact absurd (by linarith : r + (len : ℝ) * β = 1) hne
  -- the reflected base
  set r' : ℝ := 1 - r - ((len : ℝ) - 1) * β with hr'
  have hr'0 : 0 < r' := by rw [hr']; linarith
  have hr'β : r' < β := by rw [hr']; nlinarith
  -- 1 − x = r' + (len − 1 − j)β
  have hj1 : j + 1 ≤ len := hjlen
  have hcast : ((len - 1 - j : ℕ) : ℝ) = (len : ℝ) - 1 - (j : ℝ) := by
    have h1 : ((len - 1 - j : ℕ) : ℤ) = (len : ℤ) - 1 - j := by omega
    exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) h1
  have hdecomp : 1 - x = r' + ((len - 1 - j : ℕ) : ℝ) * β := by
    rw [hcast, hr']
    linarith [hrecon]
  have hposj : chainPos β (1 - x) = len - 1 - j := by
    unfold chainPos
    rw [Nat.floor_eq_iff (by positivity)]
    constructor
    · rw [le_div_iff₀ hβ]
      rw [hdecomp]
      linarith
    · rw [div_lt_iff₀ hβ]
      rw [hdecomp]
      linarith
  have hbase' : chainBase β (1 - x) = r' := by
    unfold chainBase
    rw [hposj, hcast]
    rw [hr']
    linarith [hrecon]
  refine ⟨hposj, by rw [hbase', hr'], ?_⟩
  -- the reflected chain has the same length: (len−1)β < 1 − r' ≤ len β
  rw [hbase']
  unfold chainLength
  have hlen1 : 1 ≤ len := by omega
  rw [Nat.ceil_eq_iff (by omega)]
  have hc1 : ((len - 1 : ℕ) : ℝ) = (len : ℝ) - 1 := by
    push_cast [Nat.cast_sub hlen1]
    ring
  constructor
  · rw [hc1, lt_div_iff₀ hβ, hr']
    nlinarith
  · rw [div_le_iff₀ hβ, hr']
    nlinarith

/-! ### Base-modulated envelope eigenfunctions -/

/-- The guarded sine recurrence: the two-sided hop identity with the
boundary terms dropped by the guards (they vanish anyway). -/
lemma guard_sin_rung (L : ℕ) (j : Fin L) (pos : ℕ) (hpos : pos < L) :
    (if pos + 1 < L then Real.sin (((pos : ℝ) + 2) * pathAngle L j) else 0)
      + (if 1 ≤ pos then Real.sin ((pos : ℝ) * pathAngle L j) else 0)
    = 2 * Real.cos (pathAngle L j)
        * Real.sin (((pos : ℝ) + 1) * pathAngle L j) := by
  have hrung := sin_rung (pathAngle L j) pos
  by_cases h1 : pos + 1 < L
  · rw [ite_eq_left h1]
    by_cases h2 : 1 ≤ pos
    · rw [ite_eq_left h2]
      linarith
    · rw [ite_eq_right h2]
      have hp0 : pos = 0 := by omega
      rw [hp0] at hrung ⊢
      push_cast at hrung ⊢
      norm_num at hrung ⊢
      linarith
  · rw [ite_eq_right h1]
    have hptop : pos + 1 = L := by omega
    have hc1 : ((pos : ℝ)) + 1 = (L : ℝ) := by exact_mod_cast hptop
    have htop : Real.sin (((pos : ℝ) + 2) * pathAngle L j) = 0 := by
      rw [show ((pos : ℝ) + 2) = (L : ℝ) + 1 from by linarith]
      exact sin_top L j
    by_cases h2 : 1 ≤ pos
    · rw [ite_eq_left h2]
      linarith
    · rw [ite_eq_right h2]
      have hp0 : pos = 0 := by omega
      rw [hp0] at hrung htop ⊢
      push_cast at hrung htop ⊢
      norm_num at hrung htop
      rw [zero_add, zero_add, one_mul, ← hrung, htop]

lemma ite_mul_zero (P : Prop) [Decidable P] (c a : ℝ) :
    (if P then c * a else 0) = c * (if P then a else 0) := by
  split <;> simp

/-- **Base modulation preserves eigenfunctions.** Masked hops never change
the chain base, so multiplying the sine envelope by any function of the base
gives another pointwise eigenfunction with the same eigenvalue. -/
lemma wStep_baseEnv (β : ℝ) (hβ : 0 < β) (L : ℕ) (j : Fin L) (c : ℝ → ℝ)
    (z : AddCircle (1 : ℝ)) :
    wStep β ((chainSet β L).indicator
      (fun w => c (chainBase β (rep w)) * chainEnv β L j w)) z
      = 2 * Real.cos (pathAngle L j)
        * (chainSet β L).indicator
            (fun w => c (chainBase β (rep w)) * chainEnv β L j w) z := by
  set g := (chainSet β L).indicator
    (fun w => c (chainBase β (rep w)) * chainEnv β L j w) with hg
  rw [wStep_apply]
  by_cases hzS : z ∈ chainSet β L
  · have hlenz : chainLength β (chainBase β (rep z)) = L := hzS
    have hposlt : chainPos β (rep z) < L := by
      have := chainPos_lt_chainLength β (rep z) hβ (rep_lt_one z)
      omega
    have hfwd : (maskFwd β).indicator (fun w => g (w + bcirc β)) z
        = if chainPos β (rep z) + 1 < L then
            c (chainBase β (rep z))
              * Real.sin (((chainPos β (rep z) : ℝ) + 2) * pathAngle L j)
          else 0 := by
      by_cases hf : z ∈ maskFwd β
      · have hguard : chainPos β (rep z) + 1 < L := by
          have := (mem_maskFwd_iff β hβ z).mp hf
          omega
        have hrep' : rep (z + bcirc β) = rep z + β :=
          rep_add_step β z hβ.le hf
        have hcb : chainBase β (rep (z + bcirc β)) = chainBase β (rep z) := by
          rw [hrep', chainBase_add_step β (rep z) hβ (rep_nonneg z)]
        rw [Set.indicator_of_mem hf, ite_eq_left hguard, hg,
          Set.indicator_of_mem ((chainSet_add_step β hβ L z hf).mpr hzS),
          hcb, chainEnv_add_step β hβ L j z hf]
      · have hguard : ¬(chainPos β (rep z) + 1 < L) := by
          intro hcon
          exact hf ((mem_maskFwd_iff β hβ z).mpr (by omega))
        rw [Set.indicator_of_notMem hf, ite_eq_right hguard]
    have hbwd : (maskBwd β).indicator (fun w => g (w - bcirc β)) z
        = if 1 ≤ chainPos β (rep z) then
            c (chainBase β (rep z))
              * Real.sin ((chainPos β (rep z) : ℝ) * pathAngle L j)
          else 0 := by
      by_cases hb : z ∈ maskBwd β
      · have hguard : 1 ≤ chainPos β (rep z) :=
          (mem_maskBwd_iff β hβ z).mp hb
        have hbr : β ≤ rep z := hb
        have hrep' : rep (z - bcirc β) = rep z - β :=
          rep_sub_step β z hβ.le hbr
        have hcb : chainBase β (rep (z - bcirc β)) = chainBase β (rep z) := by
          rw [hrep', chainBase_sub_step β (rep z) hβ hguard]
        rw [Set.indicator_of_mem hb, ite_eq_left hguard, hg,
          Set.indicator_of_mem ((chainSet_sub_step β hβ L z hb).mpr hzS),
          hcb, chainEnv_sub_step β hβ L j z hb]
      · have hguard : ¬(1 ≤ chainPos β (rep z)) := by
          intro hcon
          exact hb ((mem_maskBwd_iff β hβ z).mpr hcon)
        rw [Set.indicator_of_notMem hb, ite_eq_right hguard]
    rw [hfwd, hbwd, hg, Set.indicator_of_mem hzS]
    rw [ite_mul_zero, ite_mul_zero, ← mul_add,
      guard_sin_rung L j (chainPos β (rep z)) hposlt]
    unfold chainEnv
    ring
  · have hfwd : (maskFwd β).indicator (fun w => g (w + bcirc β)) z = 0 := by
      by_cases hf : z ∈ maskFwd β
      · rw [Set.indicator_of_mem hf, hg, Set.indicator_of_notMem
          (fun hc => hzS ((chainSet_add_step β hβ L z hf).mp hc))]
      · rw [Set.indicator_of_notMem hf]
    have hbwd : (maskBwd β).indicator (fun w => g (w - bcirc β)) z = 0 := by
      by_cases hb : z ∈ maskBwd β
      · rw [Set.indicator_of_mem hb, hg, Set.indicator_of_notMem
          (fun hc => hzS ((chainSet_sub_step β hβ L z hb).mp hc))]
      · rw [Set.indicator_of_notMem hb]
    rw [hfwd, hbwd, hg, Set.indicator_of_notMem hzS]
    ring

/-! ### The odd top eigenfunction -/

/-- The odd base modulation: `r ↦ r − ℓ/2`, an odd function about the
midpoint of the long base interval `[0, ℓ)`. -/
noncomputable def foldBase (β : ℝ) : ℝ → ℝ := fun r =>
  r - (1 - ((capacity 1 β : ℝ) - 1) * β) / 2

/-- The odd top eigenfunction: the top envelope on the long chains,
modulated by the odd base function. -/
noncomputable def oddEig (β : ℝ) (hm : 0 < capacity 1 β) :
    AddCircle (1 : ℝ) → ℝ :=
  (chainSet β (capacity 1 β)).indicator
    (fun w => foldBase β (chainBase β (rep w))
      * chainEnv β (capacity 1 β) ⟨0, hm⟩ w)

/-- The bad set for the reflection computation: base point, chain starts,
and reflected-boundary points — finitely many representatives, hence null. -/
lemma oddEig_null_set (β : ℝ) (hβ : 0 < β) :
    volume {z : AddCircle (1 : ℝ) |
      rep z = 0 ∨ chainBase β (rep z) = 0
        ∨ chainBase β (rep z)
            + (chainLength β (chainBase β (rep z)) : ℝ) * β = 1} = 0 := by
  have hsub : {z : AddCircle (1 : ℝ) |
      rep z = 0 ∨ chainBase β (rep z) = 0
        ∨ chainBase β (rep z)
            + (chainLength β (chainBase β (rep z)) : ℝ) * β = 1}
      ⊆ {z : AddCircle (1 : ℝ) | rep z ∈
          ((fun k : ℕ => (k : ℝ) * β) '' {k | k ≤ capacity 1 β})
            ∪ ((fun k : ℕ => 1 - (k : ℝ) * β)
                '' {k | k ≤ capacity 1 β})} := by
    intro z hz
    have hrecon := chainBase_add β (rep z)
    have hposle : chainPos β (rep z)
        ≤ chainLength β (chainBase β (rep z)) :=
      (chainPos_lt_chainLength β (rep z) hβ (rep_lt_one z)).le
    have hlenle : chainLength β (chainBase β (rep z)) ≤ capacity 1 β :=
      chainLength_le_capacity β _ hβ
        (chainBase_nonneg β (rep z) hβ (rep_nonneg z))
    rcases hz with h | h | h
    · exact Or.inl ⟨0, Nat.zero_le _, by simp [h]⟩
    · refine Or.inl ⟨chainPos β (rep z), le_trans hposle hlenle, ?_⟩
      rw [h] at hrecon
      linarith
    · refine Or.inr ⟨chainLength β (chainBase β (rep z))
        - chainPos β (rep z), le_trans (Nat.sub_le _ _) hlenle, ?_⟩
      have hcast : ((chainLength β (chainBase β (rep z))
          - chainPos β (rep z) : ℕ) : ℝ)
          = (chainLength β (chainBase β (rep z)) : ℝ)
            - (chainPos β (rep z) : ℝ) := by
        have h1 : ((chainLength β (chainBase β (rep z))
            - chainPos β (rep z) : ℕ) : ℤ)
            = (chainLength β (chainBase β (rep z)) : ℤ)
              - (chainPos β (rep z) : ℤ) := by omega
        exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) h1
      show 1 - _ * β = rep z
      rw [hcast]
      have := hrecon
      nlinarith [h]
  refine measure_mono_null hsub (volume_rep_mem_null ?_)
  exact Set.Finite.union
    (((Set.finite_Icc 0 (capacity 1 β)).subset (fun k hk =>
      Set.mem_Icc.mpr ⟨Nat.zero_le _, hk⟩)).image _)
    (((Set.finite_Icc 0 (capacity 1 β)).subset (fun k hk =>
      Set.mem_Icc.mpr ⟨Nat.zero_le _, hk⟩)).image _)

/-- Negation transport for a.e. equalities. -/
lemma ae_neg {γ : Type*} {F H : AddCircle (1 : ℝ) → γ}
    (h : F =ᵐ[volume] H) :
    ∀ᵐ z ∂(volume : Measure (AddCircle (1 : ℝ))), F (-z) = H (-z) :=
  (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae_eq_comp h

/-- **The odd symmetry.** `oddEig(−z) = −oddEig(z)` almost everywhere: on
the long chains the reflection flips the base modulation
(`foldBase(ℓ−r) = −foldBase(r)`) while the top envelope is reversal-even
(`sin((m−j)π/(m+1)) = sin((j+1)π/(m+1))`). -/
lemma oddEig_neg (β : ℝ) (hβ : 0 < β) (hm : 0 < capacity 1 β) :
    ∀ᵐ z ∂(volume : Measure (AddCircle (1 : ℝ))),
      oddEig β hm (-z) = - oddEig β hm z := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (oddEig_null_set β hβ)]
    with z hz
  have hz' : ¬(rep z = 0 ∨ chainBase β (rep z) = 0
      ∨ chainBase β (rep z)
          + (chainLength β (chainBase β (rep z)) : ℝ) * β = 1) := hz
  push Not at hz'
  obtain ⟨h1, h2, h3⟩ := hz'
  have hx0 : 0 < rep z := lt_of_le_of_ne (rep_nonneg z) (Ne.symm h1)
  have hb0 : 0 < chainBase β (rep z) :=
    lt_of_le_of_ne (chainBase_nonneg β (rep z) hβ (rep_nonneg z))
      (Ne.symm h2)
  obtain ⟨hpos', hbase', hlen'⟩ :=
    chain_reflect β (rep z) hβ hx0 (rep_lt_one z) hb0 h3
  have hrepneg : rep (-z) = 1 - rep z := rep_neg z h1
  unfold oddEig
  by_cases hzS : z ∈ chainSet β (capacity 1 β)
  · have hlenz : chainLength β (chainBase β (rep z)) = capacity 1 β := hzS
    have hmemneg : (-z) ∈ chainSet β (capacity 1 β) := by
      show chainLength β (chainBase β (rep (-z))) = _
      rw [hrepneg, hlen', hlenz]
    simp only [Set.indicator_of_mem hmemneg, Set.indicator_of_mem hzS]
    have hbc : chainBase β (rep (-z))
        = 1 - chainBase β (rep z) - ((capacity 1 β : ℝ) - 1) * β := by
      rw [hrepneg, hbase', hlenz]
    have hpc : chainPos β (rep (-z))
        = capacity 1 β - 1 - chainPos β (rep z) := by
      rw [hrepneg, hpos', hlenz]
    have hjlt : chainPos β (rep z) < capacity 1 β := by
      have := chainPos_lt_chainLength β (rep z) hβ (rep_lt_one z)
      omega
    have hcastp : ((capacity 1 β - 1 - chainPos β (rep z) : ℕ) : ℝ)
        = (capacity 1 β : ℝ) - 1 - (chainPos β (rep z) : ℝ) := by
      have hint : ((capacity 1 β - 1 - chainPos β (rep z) : ℕ) : ℤ)
          = (capacity 1 β : ℤ) - 1 - (chainPos β (rep z) : ℤ) := by omega
      exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) hint
    have hangle : pathAngle (capacity 1 β) ⟨0, hm⟩
        = π / ((capacity 1 β : ℝ) + 1) := by
      unfold pathAngle
      push_cast
      ring
    have hne0 : ((capacity 1 β : ℝ) + 1) ≠ 0 := by positivity
    have harg : ((capacity 1 β : ℝ) - 1 - (chainPos β (rep z) : ℝ) + 1)
          * (π / ((capacity 1 β : ℝ) + 1))
        = π - ((chainPos β (rep z) : ℝ) + 1)
            * (π / ((capacity 1 β : ℝ) + 1)) := by
      field_simp
      ring
    unfold chainEnv foldBase
    rw [hbc, hpc, hcastp, hangle, harg, Real.sin_pi_sub]
    ring
  · have hmemneg : (-z) ∉ chainSet β (capacity 1 β) := by
      intro hc
      apply hzS
      show chainLength β (chainBase β (rep z)) = capacity 1 β
      have hc' : chainLength β (chainBase β (rep (-z))) = capacity 1 β := hc
      rw [hrepneg, hlen'] at hc'
      exact hc'
    simp only [Set.indicator_of_notMem hmemneg,
      Set.indicator_of_notMem hzS, neg_zero]

/-! ### The odd eigenfunction as an `L²` element -/

lemma memLp_oddEig (β : ℝ) (hβ : 0 < β) (hm : 0 < capacity 1 β) :
    MemLp (oddEig β hm) 2 (volume : Measure (AddCircle (1 : ℝ))) := by
  have hmeas : Measurable (fun w : AddCircle (1 : ℝ) =>
      foldBase β (chainBase β (rep w))
        * chainEnv β (capacity 1 β) ⟨0, hm⟩ w) := by
    refine Measurable.mul ?_ (measurable_chainEnv β _ _)
    exact ((measurable_chainBase β).comp measurable_rep).sub_const _
  refine MemLp.of_bound
    ((hmeas.indicator (measurableSet_chainSet β _)).aestronglyMeasurable)
    (β + 1) ?_
  have hℓ1 : (1 - ((capacity 1 β : ℝ) - 1) * β) ≤ 1 := by
    have hcap1 : (1 : ℝ) ≤ (capacity 1 β : ℝ) := by
      exact_mod_cast one_le_capacity β hβ
    nlinarith
  have hℓ0 : 0 < 1 - ((capacity 1 β : ℝ) - 1) * β := by
    have := capacity_sub_one_mul_lt β hβ
    linarith
  filter_upwards with z
  rw [Real.norm_eq_abs]
  unfold oddEig
  by_cases h : z ∈ chainSet β (capacity 1 β)
  · rw [Set.indicator_of_mem h]
    have hb0 : 0 ≤ chainBase β (rep z) :=
      chainBase_nonneg β (rep z) hβ (rep_nonneg z)
    have hbβ : chainBase β (rep z) < β := chainBase_lt β (rep z) hβ
    have habs1 : |foldBase β (chainBase β (rep z))| ≤ β + 1 := by
      unfold foldBase
      rw [abs_le]
      constructor <;> [nlinarith; nlinarith]
    have habs2 : |chainEnv β (capacity 1 β) ⟨0, hm⟩ z| ≤ 1 := by
      unfold chainEnv
      exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
    calc |foldBase β (chainBase β (rep z))
          * chainEnv β (capacity 1 β) ⟨0, hm⟩ z|
        = |foldBase β (chainBase β (rep z))|
            * |chainEnv β (capacity 1 β) ⟨0, hm⟩ z| := abs_mul _ _
      _ ≤ (β + 1) * 1 :=
          mul_le_mul habs1 habs2 (abs_nonneg _) (by linarith)
      _ = β + 1 := mul_one _
  · rw [Set.indicator_of_notMem h]
    simp
    linarith

/-- The odd top eigenfunction as an `L²` element. -/
noncomputable def oddEigL2 (β : ℝ) (hβ : 0 < β) (hm : 0 < capacity 1 β) :
    L2c :=
  MemLp.toLp _ (memLp_oddEig β hβ hm)

lemma coeFn_oddEigL2 (β : ℝ) (hβ : 0 < β) (hm : 0 < capacity 1 β) :
    (oddEigL2 β hβ hm : AddCircle (1 : ℝ) → ℝ) =ᵐ[volume] oddEig β hm :=
  MemLp.coeFn_toLp _

/-- **The eigenvector equation** for the odd eigenfunction. -/
theorem pathLawW_oddEigL2 (β : ℝ) (hβ : 0 < β) (hm : 0 < capacity 1 β) :
    pathLawW β (oddEigL2 β hβ hm)
      = chebFactor (capacity 1 β) • oddEigL2 β hβ hm := by
  have hangle : chebFactor (capacity 1 β)
      = 2 * Real.cos (pathAngle (capacity 1 β) ⟨0, hm⟩) := by
    unfold chebFactor pathAngle
    congr 2
    push_cast
    ring
  apply Lp.ext
  filter_upwards [coeFn_pathLawW_step β (oddEigL2 β hβ hm) _
      (coeFn_oddEigL2 β hβ hm),
    Lp.coeFn_smul (chebFactor (capacity 1 β)) (oddEigL2 β hβ hm),
    coeFn_oddEigL2 β hβ hm] with z h1 h2 h3
  rw [h1, h2, Pi.smul_apply, smul_eq_mul, h3, hangle]
  exact wStep_baseEnv β hβ (capacity 1 β) ⟨0, hm⟩ (foldBase β) z

/-- The odd eigenfunction is genuinely odd: `R f = −f` in `L²`. -/
theorem reflect_oddEigL2 (β : ℝ) (hβ : 0 < β) (hm : 0 < capacity 1 β) :
    reflectL2 (oddEigL2 β hβ hm) = - oddEigL2 β hβ hm := by
  apply Lp.ext
  filter_upwards [reflect_ae (oddEigL2 β hβ hm),
    ae_neg (coeFn_oddEigL2 β hβ hm), oddEig_neg β hβ hm,
    Lp.coeFn_neg (oddEigL2 β hβ hm), coeFn_oddEigL2 β hβ hm]
    with z h1 h2 h3 h4 h5
  rw [h1, h2, h3, h4, Pi.neg_apply, h5]

/-! ### Nonvanishing -/

/-- The support slice: position 0 of a long chain, base strictly inside the
lower half of the base interval. It has positive measure. -/
lemma volume_oddEig_slice_pos (β : ℝ) (hβ : 0 < β) :
    0 < volume {z : AddCircle (1 : ℝ) |
      z ∈ chainSet β (capacity 1 β) ∧ chainPos β (rep z) = 0
        ∧ 0 < chainBase β (rep z)
        ∧ chainBase β (rep z)
            < (1 - ((capacity 1 β : ℝ) - 1) * β) / 2} := by
  have hℓ0 : 0 < 1 - ((capacity 1 β : ℝ) - 1) * β := by
    have := capacity_sub_one_mul_lt β hβ
    linarith
  set d := min (min (longThreshold β) (1 / 2))
    ((1 - ((capacity 1 β : ℝ) - 1) * β) / 2) with hd
  have hdpos : 0 < d :=
    lt_min (lt_min (longThreshold_pos β hβ) (by norm_num)) (by linarith)
  have hdt : d ≤ longThreshold β :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have hd2 : d ≤ 1 / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hdℓ : d ≤ (1 - ((capacity 1 β : ℝ) - 1) * β) / 2 := min_le_right _ _
  have htβ : longThreshold β ≤ β := min_le_left _ _
  have hsub : Set.Ioo (0 : ℝ) d
      ⊆ (QuotientAddGroup.mk ⁻¹' {z : AddCircle (1 : ℝ) |
          z ∈ chainSet β (capacity 1 β) ∧ chainPos β (rep z) = 0
            ∧ 0 < chainBase β (rep z)
            ∧ chainBase β (rep z)
                < (1 - ((capacity 1 β : ℝ) - 1) * β) / 2})
        ∩ Set.Ioc (0 : ℝ) (0 + 1) := by
    intro y hy
    have hrep : rep ((y : ℝ) : AddCircle (1 : ℝ)) = y :=
      rep_coe y hy.1.le (by linarith [hy.2])
    have hposy : chainPos β y = 0 := by
      unfold chainPos
      refine Nat.floor_eq_zero.mpr ?_
      rw [div_lt_one hβ]
      calc y < d := hy.2
        _ ≤ β := le_trans hdt htβ
    have hbase : chainBase β y = y := by
      unfold chainBase
      rw [hposy]
      push_cast
      ring
    constructor
    · show ((y : ℝ) : AddCircle (1 : ℝ)) ∈ {z : AddCircle (1 : ℝ) | _}
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact mem_longSet_of_rep_lt β hβ _
          (by rw [hrep]; exact lt_of_lt_of_le hy.2 hdt)
      · rw [hrep]
        exact hposy
      · rw [hrep, hbase]
        exact hy.1
      · rw [hrep, hbase]
        exact lt_of_lt_of_le hy.2 hdℓ
    · exact Set.mem_Ioc.mpr ⟨hy.1, by linarith [hy.2]⟩
  have hms : MeasurableSet {z : AddCircle (1 : ℝ) |
      z ∈ chainSet β (capacity 1 β) ∧ chainPos β (rep z) = 0
        ∧ 0 < chainBase β (rep z)
        ∧ chainBase β (rep z)
            < (1 - ((capacity 1 β : ℝ) - 1) * β) / 2} := by
    show MeasurableSet (chainSet β (capacity 1 β) ∩ ((chainPos β ∘ rep) ⁻¹' {0}
      ∩ ({z : AddCircle (1 : ℝ) | 0 < chainBase β (rep z)}
      ∩ {z : AddCircle (1 : ℝ) | chainBase β (rep z)
            < (1 - ((capacity 1 β : ℝ) - 1) * β) / 2})))
    refine ((measurableSet_chainSet β _).inter
      ((((measurable_chainPos β).comp measurable_rep)
        (measurableSet_singleton 0)).inter ?_))
    exact (measurableSet_lt measurable_const
        ((measurable_chainBase β).comp measurable_rep)).inter
      (measurableSet_lt ((measurable_chainBase β).comp measurable_rep)
        measurable_const)
  have hproj := AddCircle.add_projection_respects_measure (T := (1 : ℝ)) 0 hms
  rw [hproj]
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioo]
  simp only [sub_zero]
  exact ENNReal.ofReal_pos.mpr hdpos

/-- The odd eigenfunction is a nonzero `L²` element. -/
theorem oddEigL2_ne_zero (β : ℝ) (hβ : 0 < β) (hm : 0 < capacity 1 β) :
    oddEigL2 β hβ hm ≠ 0 := by
  intro hzero
  have hco := coeFn_oddEigL2 β hβ hm
  rw [hzero] at hco
  have h0 : oddEig β hm =ᵐ[volume] 0 :=
    hco.symm.trans (Lp.coeFn_zero ℝ 2 volume)
  have hsub : {z : AddCircle (1 : ℝ) |
      z ∈ chainSet β (capacity 1 β) ∧ chainPos β (rep z) = 0
        ∧ 0 < chainBase β (rep z)
        ∧ chainBase β (rep z)
            < (1 - ((capacity 1 β : ℝ) - 1) * β) / 2}
      ⊆ {z | oddEig β hm z ≠ 0} := by
    rintro z ⟨hzS, hzpos, hzb0, hzbℓ⟩
    show oddEig β hm z ≠ 0
    unfold oddEig
    rw [Set.indicator_of_mem hzS]
    have hfold : foldBase β (chainBase β (rep z)) < 0 := by
      unfold foldBase
      linarith
    have hsin : 0 < chainEnv β (capacity 1 β) ⟨0, hm⟩ z := by
      unfold chainEnv
      rw [hzpos]
      push_cast
      rw [zero_add, one_mul]
      exact Real.sin_pos_of_pos_of_lt_pi (pathAngle_pos _ _)
        (pathAngle_lt_pi _ _)
    exact ne_of_lt (mul_neg_of_neg_of_pos hfold hsin)
  have hmeas0 : volume {z : AddCircle (1 : ℝ) | oddEig β hm z ≠ 0} = 0 := by
    rw [← ae_iff]
    exact h0
  have hle := measure_mono
    (μ := (volume : Measure (AddCircle (1 : ℝ)))) hsub
  rw [hmeas0] at hle
  exact absurd (le_antisymm hle bot_le)
    (ne_of_gt (volume_oddEig_slice_pos β hβ))

/-! ### The odd sector and the folded norm -/

/-- The odd sector: the `−1` eigenspace of the reflection. This is the
domain of the folded operator. -/
noncomputable def reflectPlusOne : L2c →L[ℝ] L2c := reflectL2 + 1

noncomputable def oddSpace : Submodule ℝ L2c :=
  LinearMap.ker (reflectPlusOne : L2c →ₗ[ℝ] L2c)

instance : CompleteSpace oddSpace :=
  (ContinuousLinearMap.isClosed_ker reflectPlusOne).completeSpace_coe

theorem oddEigL2_mem_oddSpace (β : ℝ) (hβ : 0 < β)
    (hm : 0 < capacity 1 β) : oddEigL2 β hβ hm ∈ oddSpace := by
  rw [oddSpace, LinearMap.mem_ker]
  show reflectPlusOne (oddEigL2 β hβ hm) = 0
  rw [reflectPlusOne, add_apply, one_apply_eq_self,
    reflect_oddEigL2 β hβ hm]
  exact neg_add_cancel _

/-- **The parity fold inherits the norm.** The compression of the masked
rotation to the odd sector — the folded operator — has the full
Path Law norm: the base-modulated odd eigenvector attains it. -/
theorem norm_compress_oddSpace (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ‖compress oddSpace (pathLawW β)‖ = chebFactor (capacity 1 β) := by
  have hm : 0 < capacity 1 β := one_le_capacity β hβ
  refine le_antisymm
    ((norm_compress_le _ _).trans_eq (norm_pathLawW β hβ hβ1)) ?_
  have hmem := oddEigL2_mem_oddSpace β hβ hm
  set go : oddSpace := ⟨oddEigL2 β hβ hm, hmem⟩ with hgo
  have hP : oddSpace.orthogonalProjectionOnto (oddEigL2 β hβ hm) = go :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self go
  have heig : compress oddSpace (pathLawW β) go
      = chebFactor (capacity 1 β) • go := by
    apply Subtype.ext
    show ((oddSpace.orthogonalProjectionOnto
        (pathLawW β (oddEigL2 β hβ hm)) : oddSpace) : L2c)
      = ((chebFactor (capacity 1 β) • go : oddSpace) : L2c)
    rw [pathLawW_oddEigL2 β hβ hm, map_smul, hP]
  have hg0 : go ≠ 0 := by
    intro hcon
    apply oddEigL2_ne_zero β hβ hm
    simpa [hgo] using congrArg Subtype.val hcon
  have hnormpos : 0 < ‖go‖ := norm_pos_iff.mpr hg0
  have hle := (compress oddSpace (pathLawW β)).le_opNorm go
  rw [heig, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (chebFactor_nonneg _ hm)] at hle
  exact le_of_mul_le_mul_right hle hnormpos


/-! ### Reflection commutes with the masked rotation -/

/-- Under reflection the forward mask becomes the backward mask (away from
two null representatives). -/
lemma neg_mem_maskFwd_iff (β : ℝ) (z : AddCircle (1 : ℝ))
    (h0 : rep z ≠ 0) (hβne : rep z ≠ β) :
    (-z) ∈ maskFwd β ↔ z ∈ maskBwd β := by
  have hrn := rep_neg z h0
  constructor
  · intro h
    have hh : rep (-z) + β < 1 := h
    rw [hrn] at hh
    show β ≤ rep z
    linarith
  · intro h
    have hb : β ≤ rep z := h
    have hb' : β < rep z := lt_of_le_of_ne hb (Ne.symm hβne)
    show rep (-z) + β < 1
    rw [hrn]
    linarith

/-- Under reflection the backward mask becomes the forward mask (away from
two null representatives). -/
lemma neg_mem_maskBwd_iff (β : ℝ) (z : AddCircle (1 : ℝ))
    (h0 : rep z ≠ 0) (h1βne : rep z ≠ 1 - β) :
    (-z) ∈ maskBwd β ↔ z ∈ maskFwd β := by
  have hrn := rep_neg z h0
  constructor
  · intro h
    have hh : β ≤ rep (-z) := h
    rw [hrn] at hh
    show rep z + β < 1
    have hle : rep z ≤ 1 - β := by linarith
    rcases lt_or_eq_of_le hle with h' | h'
    · linarith
    · exact absurd h' h1βne
  · intro h
    have hh : rep z + β < 1 := h
    show β ≤ rep (-z)
    rw [hrn]
    linarith

/-- **Reflection commutes with the masked rotation**: the parity sectors are
invariant, so the odd-sector compression is a genuine restriction. -/
theorem reflect_comm_pathLawW (β : ℝ) :
    reflectL2 ∘L pathLawW β = pathLawW β ∘L reflectL2 := by
  ext f
  have hW : (pathLawW β f : AddCircle (1 : ℝ) → ℝ)
      =ᵐ[volume] wStep β (f : AddCircle (1 : ℝ) → ℝ) :=
    coeFn_pathLawW_step β f _ Filter.EventuallyEq.rfl
  have hWRf : (pathLawW β (reflectL2 f) : AddCircle (1 : ℝ) → ℝ)
      =ᵐ[volume] wStep β (fun z => (f : AddCircle (1 : ℝ) → ℝ) (-z)) :=
    coeFn_pathLawW_step β _ _ (reflect_ae f)
  have hRWf : (reflectL2 (pathLawW β f) : AddCircle (1 : ℝ) → ℝ)
      =ᵐ[volume] fun z => wStep β (f : AddCircle (1 : ℝ) → ℝ) (-z) :=
    (reflect_ae _).trans (ae_neg hW)
  show (reflectL2 (pathLawW β f) : AddCircle (1 : ℝ) → ℝ)
      =ᵐ[volume] (pathLawW β (reflectL2 f) : AddCircle (1 : ℝ) → ℝ)
  filter_upwards [hRWf, hWRf,
    measure_eq_zero_iff_ae_notMem.mp
      (volume_rep_mem_null (Set.toFinite {0, β, 1 - β}))] with z h1 h2 h3
  rw [h1, h2]
  have h0 : rep z ≠ 0 := fun hc => h3 (by simp [hc])
  have hbne : rep z ≠ β := fun hc => h3 (by simp [hc])
  have h1βne : rep z ≠ 1 - β := fun hc => h3 (by simp [hc])
  rw [wStep_apply, wStep_apply]
  have e1 : -z + bcirc β = -(z - bcirc β) := by abel
  have e2 : -z - bcirc β = -(z + bcirc β) := by abel
  have hfwd : (maskFwd β).indicator
      (fun w => (f : AddCircle (1 : ℝ) → ℝ) (w + bcirc β)) (-z)
      = (maskBwd β).indicator
          (fun w => (f : AddCircle (1 : ℝ) → ℝ) (-(w - bcirc β))) z := by
    by_cases hb : z ∈ maskBwd β
    · rw [Set.indicator_of_mem
        ((neg_mem_maskFwd_iff β z h0 hbne).mpr hb),
        Set.indicator_of_mem hb]
      rw [e1]
    · rw [Set.indicator_of_notMem
        (fun hc => hb ((neg_mem_maskFwd_iff β z h0 hbne).mp hc)),
        Set.indicator_of_notMem hb]
  have hbwd : (maskBwd β).indicator
      (fun w => (f : AddCircle (1 : ℝ) → ℝ) (w - bcirc β)) (-z)
      = (maskFwd β).indicator
          (fun w => (f : AddCircle (1 : ℝ) → ℝ) (-(w + bcirc β))) z := by
    by_cases hfm : z ∈ maskFwd β
    · rw [Set.indicator_of_mem
        ((neg_mem_maskBwd_iff β z h0 h1βne).mpr hfm),
        Set.indicator_of_mem hfm]
      rw [e2]
    · rw [Set.indicator_of_notMem
        (fun hc => hfm ((neg_mem_maskBwd_iff β z h0 h1βne).mp hc)),
        Set.indicator_of_notMem hfm]
  rw [hfwd, hbwd]
  ring

/-! ### The folded spectrum -/

/-- The odd sector is invariant under the masked rotation. -/
theorem oddSpace_invariant (β : ℝ) :
    ∀ f ∈ oddSpace, pathLawW β f ∈ oddSpace := by
  intro f hf
  have hf' : reflectPlusOne f = 0 := hf
  rw [reflectPlusOne, add_apply, one_apply_eq_self] at hf'
  have hRf : reflectL2 f = -f := eq_neg_of_add_eq_zero_left hf'
  show reflectPlusOne (pathLawW β f) = 0
  rw [reflectPlusOne, add_apply, one_apply_eq_self]
  have hswap : reflectL2 (pathLawW β f) = pathLawW β (reflectL2 f) := by
    calc reflectL2 (pathLawW β f)
        = (reflectL2 ∘L pathLawW β) f := rfl
      _ = (pathLawW β ∘L reflectL2) f := by rw [reflect_comm_pathLawW β]
      _ = pathLawW β (reflectL2 f) := rfl
  rw [hswap, hRf, map_neg]
  exact neg_add_cancel _

/-- The annihilating polynomial descends to the fold. -/
theorem aeval_chainPoly_compress_oddSpace (β : ℝ) (hβ : 0 < β) :
    aeval (compress oddSpace (pathLawW β)) (chainPoly β) = 0 := by
  rw [aeval_compress_of_invariant (oddSpace_invariant β),
    aeval_chainPoly_pathLawW β hβ, compress_zero]

/-- **The folded spectrum, set form.** The folded spectrum is
contained in the unfolded Chebyshev root set. -/
theorem spectrum_compress_oddSpace_subset (β : ℝ) (hβ : 0 < β) :
    spectrum ℝ (compress oddSpace (pathLawW β))
      ⊆ {μ : ℝ | (chainPoly β).eval μ = 0} :=
  spectrum_subset_roots_of_aeval_eq_zero
    (aeval_chainPoly_compress_oddSpace β hβ)

/-- **The folded spectrum, numerical form.** Every folded
spectral value satisfies `|μ| ≤ chebFactor m = ‖W‖`: no folded eigenvalue
escapes the unfolded spectral interval. -/
theorem abs_le_of_mem_spectrum_compress_oddSpace (β : ℝ) (hβ : 0 < β)
    {μ : ℝ} (hμ : μ ∈ spectrum ℝ (compress oddSpace (pathLawW β))) :
    |μ| ≤ chebFactor (capacity 1 β) := by
  have h := spectrum_compress_oddSpace_subset β hβ hμ
  rw [Set.mem_ofPred_eq, chainPoly, eval_mul, mul_eq_zero] at h
  rcases h with h | h
  · obtain ⟨j, rfl⟩ := (eval_pathCharPoly_eq_zero_iff _ _).mp h
    exact abs_eigenvalue_le_chebFactor (hasEigenvalue_pathAdj _ j)
  · obtain ⟨j, rfl⟩ := (eval_pathCharPoly_eq_zero_iff _ _).mp h
    exact le_trans
      (abs_eigenvalue_le_chebFactor (hasEigenvalue_pathAdj _ j))
      (chebFactor_monotone (Nat.sub_le _ 1))

/-! ### Odd eigenvectors of every rung -/

lemma sin_nat_mul_pi_sub (k : ℕ) (x : ℝ) :
    Real.sin ((k : ℝ) * π - x) = -((-1 : ℝ) ^ k * Real.sin x) := by
  rw [Real.sin_sub, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
  ring

/-- The general rung function: envelope `j` on the chains of length `L`,
modulated by a base function `c`. -/
noncomputable def rungFun (β : ℝ) (L : ℕ) (j : Fin L) (c : ℝ → ℝ) :
    AddCircle (1 : ℝ) → ℝ :=
  (chainSet β L).indicator
    (fun w => c (chainBase β (rep w)) * chainEnv β L j w)

/-- **Reflection parity of rung functions.** If the base modulation has
parity `ε` about the midpoint of the length-`L` base interval, then the
rung-`j` function has reflection parity `ε·(−1)^j` (the envelope itself is
reversal-parity `(−1)^j`). -/
lemma rungFun_neg (β : ℝ) (hβ : 0 < β) (L : ℕ) (j : Fin L)
    (c : ℝ → ℝ) (ε : ℝ)
    (hc : ∀ r, c (1 - ((L : ℝ) - 1) * β - r) = ε * c r) :
    ∀ᵐ z ∂(volume : Measure (AddCircle (1 : ℝ))),
      rungFun β L j c (-z)
        = ε * (-1 : ℝ) ^ (j : ℕ) * rungFun β L j c z := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (oddEig_null_set β hβ)]
    with z hz
  have hz' : ¬(rep z = 0 ∨ chainBase β (rep z) = 0
      ∨ chainBase β (rep z)
          + (chainLength β (chainBase β (rep z)) : ℝ) * β = 1) := hz
  push Not at hz'
  obtain ⟨h1, h2, h3⟩ := hz'
  have hx0 : 0 < rep z := lt_of_le_of_ne (rep_nonneg z) (Ne.symm h1)
  have hb0 : 0 < chainBase β (rep z) :=
    lt_of_le_of_ne (chainBase_nonneg β (rep z) hβ (rep_nonneg z))
      (Ne.symm h2)
  obtain ⟨hpos', hbase', hlen'⟩ :=
    chain_reflect β (rep z) hβ hx0 (rep_lt_one z) hb0 h3
  have hrepneg : rep (-z) = 1 - rep z := rep_neg z h1
  unfold rungFun
  by_cases hzS : z ∈ chainSet β L
  · have hlenz : chainLength β (chainBase β (rep z)) = L := hzS
    have hmemneg : (-z) ∈ chainSet β L := by
      show chainLength β (chainBase β (rep (-z))) = _
      rw [hrepneg, hlen', hlenz]
    simp only [Set.indicator_of_mem hmemneg, Set.indicator_of_mem hzS]
    have hbc : chainBase β (rep (-z))
        = 1 - ((L : ℝ) - 1) * β - chainBase β (rep z) := by
      rw [hrepneg, hbase', hlenz]
      ring
    have hpc : chainPos β (rep (-z)) = L - 1 - chainPos β (rep z) := by
      rw [hrepneg, hpos', hlenz]
    have hjlt : chainPos β (rep z) < L := by
      have := chainPos_lt_chainLength β (rep z) hβ (rep_lt_one z)
      omega
    have hcastp : ((L - 1 - chainPos β (rep z) : ℕ) : ℝ)
        = (L : ℝ) - 1 - (chainPos β (rep z) : ℝ) := by
      have hint : ((L - 1 - chainPos β (rep z) : ℕ) : ℤ)
          = (L : ℤ) - 1 - (chainPos β (rep z) : ℤ) := by omega
      exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) hint
    have hangle : ((L : ℝ) - 1 - (chainPos β (rep z) : ℝ) + 1)
          * pathAngle L j
        = ((j : ℕ) + 1 : ℝ) * π
          - ((chainPos β (rep z) : ℝ) + 1) * pathAngle L j := by
      unfold pathAngle
      have hL1 : ((L : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    have henv : Real.sin ((((L - 1 - chainPos β (rep z) : ℕ) : ℝ) + 1)
          * pathAngle L j)
        = (-1 : ℝ) ^ (j : ℕ)
          * Real.sin (((chainPos β (rep z) : ℝ) + 1) * pathAngle L j) := by
      rw [hcastp, hangle]
      have hs := sin_nat_mul_pi_sub ((j : ℕ) + 1)
        (((chainPos β (rep z) : ℝ) + 1) * pathAngle L j)
      push_cast at hs
      rw [hs, pow_succ]
      ring
    unfold chainEnv
    rw [hbc, hpc, hc (chainBase β (rep z)), henv]
    ring
  · have hmemneg : (-z) ∉ chainSet β L := by
      intro hcon
      apply hzS
      show chainLength β (chainBase β (rep z)) = L
      have hc' : chainLength β (chainBase β (rep (-z))) = L := hcon
      rw [hrepneg, hlen'] at hc'
      exact hc'
    simp only [Set.indicator_of_notMem hmemneg,
      Set.indicator_of_notMem hzS, mul_zero]

/-- The rung function is square-integrable for base modulations bounded on
the base interval. -/
lemma memLp_rungFun (β : ℝ) (hβ : 0 < β) (L : ℕ) (j : Fin L)
    (c : ℝ → ℝ) (hcm : Measurable c) (B : ℝ) (hB : 0 ≤ B)
    (hbd : ∀ r, 0 ≤ r → r < β → |c r| ≤ B) :
    MemLp (rungFun β L j c) 2 (volume : Measure (AddCircle (1 : ℝ))) := by
  have hmeas : Measurable (fun w : AddCircle (1 : ℝ) =>
      c (chainBase β (rep w)) * chainEnv β L j w) :=
    (hcm.comp ((measurable_chainBase β).comp measurable_rep)).mul
      (measurable_chainEnv β L j)
  refine MemLp.of_bound
    ((hmeas.indicator (measurableSet_chainSet β L)).aestronglyMeasurable)
    B ?_
  filter_upwards with z
  rw [Real.norm_eq_abs]
  unfold rungFun
  by_cases h : z ∈ chainSet β L
  · rw [Set.indicator_of_mem h]
    have h1 : |c (chainBase β (rep z))| ≤ B :=
      hbd _ (chainBase_nonneg β (rep z) hβ (rep_nonneg z))
        (chainBase_lt β (rep z) hβ)
    have h2 : |chainEnv β L j z| ≤ 1 := by
      unfold chainEnv
      exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
    calc |c (chainBase β (rep z)) * chainEnv β L j z|
        = |c (chainBase β (rep z))| * |chainEnv β L j z| := abs_mul _ _
      _ ≤ B * 1 := mul_le_mul h1 h2 (abs_nonneg _) hB
      _ = B := mul_one _
  · rw [Set.indicator_of_notMem h]
    simpa using hB

/-- The rung function as an `L²` element. -/
noncomputable def rungFunL2 (β : ℝ) (hβ : 0 < β) (L : ℕ) (j : Fin L)
    (c : ℝ → ℝ) (hcm : Measurable c) (B : ℝ) (hB : 0 ≤ B)
    (hbd : ∀ r, 0 ≤ r → r < β → |c r| ≤ B) : L2c :=
  MemLp.toLp _ (memLp_rungFun β hβ L j c hcm B hB hbd)

/-- **Generic fold membership.** Every Chebyshev value of every occurring
chain length lies in the spectrum of the folded operator, witnessed by a
rung function whose base modulation makes it reflection-odd and which does
not vanish. -/
theorem mem_spectrum_fold_of (β : ℝ) (hβ : 0 < β) (L : ℕ) (j : Fin L)
    (c : ℝ → ℝ) (hcm : Measurable c) (B : ℝ) (hB : 0 ≤ B)
    (hbd : ∀ r, 0 ≤ r → r < β → |c r| ≤ B) (ε : ℝ)
    (hc : ∀ r, c (1 - ((L : ℝ) - 1) * β - r) = ε * c r)
    (hodd : ε * (-1 : ℝ) ^ (j : ℕ) = -1)
    (hvol : 0 < volume {z : AddCircle (1 : ℝ) |
      z ∈ chainSet β L ∧ chainPos β (rep z) = 0
        ∧ c (chainBase β (rep z)) ≠ 0}) :
    2 * Real.cos (pathAngle L j)
      ∈ spectrum ℝ (compress oddSpace (pathLawW β)) := by
  set g : L2c := rungFunL2 β hβ L j c hcm B hB hbd with hgdef
  have hco : (g : AddCircle (1 : ℝ) → ℝ) =ᵐ[volume] rungFun β L j c :=
    MemLp.coeFn_toLp _
  -- eigen equation
  have hWg : pathLawW β g = (2 * Real.cos (pathAngle L j)) • g := by
    apply Lp.ext
    filter_upwards [coeFn_pathLawW_step β g _ hco,
      Lp.coeFn_smul (2 * Real.cos (pathAngle L j)) g, hco] with z hh1 hh2 hh3
    rw [hh1, hh2, Pi.smul_apply, smul_eq_mul, hh3]
    exact wStep_baseEnv β hβ L j c z
  -- reflection oddness
  have hRg : reflectL2 g = -g := by
    apply Lp.ext
    filter_upwards [reflect_ae g, ae_neg hco,
      rungFun_neg β hβ L j c ε hc, Lp.coeFn_neg g, hco]
      with z hh1 hh2 hh3 hh4 hh5
    rw [hh1, hh2, hh3, hodd, hh4, Pi.neg_apply, hh5]
    ring
  have hmem : g ∈ oddSpace := by
    show reflectPlusOne g = 0
    rw [reflectPlusOne, add_apply, one_apply_eq_self, hRg]
    exact neg_add_cancel _
  -- nonvanishing
  have hg0 : g ≠ 0 := by
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
    exact absurd (le_antisymm hle bot_le) (ne_of_gt hvol)
  -- eigenvector of the compression
  have hP : oddSpace.orthogonalProjectionOnto g = ⟨g, hmem⟩ :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
      (⟨g, hmem⟩ : oddSpace)
  have heig : compress oddSpace (pathLawW β) ⟨g, hmem⟩
      = (2 * Real.cos (pathAngle L j)) • (⟨g, hmem⟩ : oddSpace) := by
    apply Subtype.ext
    show ((oddSpace.orthogonalProjectionOnto (pathLawW β g) : oddSpace) : L2c)
      = (((2 * Real.cos (pathAngle L j)) • (⟨g, hmem⟩ : oddSpace)
          : oddSpace) : L2c)
    rw [hWg, map_smul, hP]
  have hg0' : (⟨g, hmem⟩ : oddSpace) ≠ 0 := by
    intro hcon
    exact hg0 (by simpa using congrArg Subtype.val hcon)
  exact mem_spectrum_of_eigenvector hg0' heig

/-- Positive-measure slice for the short-chain affine modulation: position
zero, base strictly below the short base midpoint. -/
lemma volume_short_slice_pos (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hshort : 1 < (capacity 1 β : ℝ) * β) :
    0 < volume {z : AddCircle (1 : ℝ) |
      z ∈ chainSet β (capacity 1 β - 1) ∧ chainPos β (rep z) = 0
        ∧ chainBase β (rep z)
            < (1 - (((capacity 1 β - 1 : ℕ) : ℝ) - 1) * β) / 2} := by
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
  set hi : ℝ := (1 - (((capacity 1 β - 1 : ℕ) : ℝ) - 1) * β) / 2 with hhi
  have hhi' : hi = (lo + β) / 2 := by
    rw [hhi, hlo, hcast1]
    ring
  have hlopos : 0 < lo := by rw [hlo]; linarith
  have hloβ : lo < β := by rw [hlo]; nlinarith
  have hlohi : lo < hi := by rw [hhi']; linarith
  have hhiβ : hi < β := by rw [hhi']; linarith
  have hsub : Set.Ioo lo hi
      ⊆ (QuotientAddGroup.mk ⁻¹' {z : AddCircle (1 : ℝ) |
          z ∈ chainSet β (capacity 1 β - 1) ∧ chainPos β (rep z) = 0
            ∧ chainBase β (rep z)
                < (1 - (((capacity 1 β - 1 : ℕ) : ℝ) - 1) * β) / 2})
        ∩ Set.Ioc (0 : ℝ) (0 + 1) := by
    intro y hy
    have hy0 : 0 < y := lt_trans hlopos hy.1
    have hyβ : y < β := lt_trans hy.2 hhiβ
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
        have hup : ⌈(1 - y) / β⌉₊ ≤ capacity 1 β - 1 := by
          rw [Nat.ceil_le, hcast1, div_le_iff₀ hβ]
          have := hy.1
          rw [hlo] at this
          nlinarith
        have hdown : capacity 1 β - 2 < ⌈(1 - y) / β⌉₊ := by
          rw [Nat.lt_ceil, hcast2, lt_div_iff₀ hβ]
          nlinarith
        omega
      · rw [hrep]
        exact hposy
      · rw [hrep, hbase]
        exact hy.2
    · exact Set.mem_Ioc.mpr ⟨hy0, by linarith [hy.2, hhiβ]⟩
  have hms : MeasurableSet {z : AddCircle (1 : ℝ) |
      z ∈ chainSet β (capacity 1 β - 1) ∧ chainPos β (rep z) = 0
        ∧ chainBase β (rep z)
            < (1 - (((capacity 1 β - 1 : ℕ) : ℝ) - 1) * β) / 2} :=
    (measurableSet_chainSet β _).inter
      ((((measurable_chainPos β).comp measurable_rep)
        (measurableSet_singleton 0)).inter
        (measurableSet_lt ((measurable_chainBase β).comp measurable_rep)
          measurable_const))
  have hproj := AddCircle.add_projection_respects_measure (T := (1 : ℝ)) 0 hms
  rw [hproj]
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioo]
  exact ENNReal.ofReal_pos.mpr (by linarith)

/-- **The exact folded spectrum.** In the non-degenerate case the folded
operator has exactly the unfolded spectrum: parity folding creates no new
spectral points and loses none. -/
theorem spectrum_compress_oddSpace_eq (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hshort : 1 < (capacity 1 β : ℝ) * β) :
    spectrum ℝ (compress oddSpace (pathLawW β))
      = (Set.range fun j : Fin (capacity 1 β) =>
          2 * Real.cos (pathAngle (capacity 1 β) j))
        ∪ (Set.range fun j : Fin (capacity 1 β - 1) =>
            2 * Real.cos (pathAngle (capacity 1 β - 1) j)) := by
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
  apply Set.eq_of_subset_of_subset
  · intro μ hμ
    have h := spectrum_compress_oddSpace_subset β hβ hμ
    rw [Set.mem_ofPred_eq, chainPoly, eval_mul, mul_eq_zero] at h
    rcases h with h | h
    · obtain ⟨j, hj⟩ := (eval_pathCharPoly_eq_zero_iff _ _).mp h
      exact Or.inl ⟨j, hj.symm⟩
    · obtain ⟨j, hj⟩ := (eval_pathCharPoly_eq_zero_iff _ _).mp h
      exact Or.inr ⟨j, hj.symm⟩
  · intro μ hμ
    rcases hμ with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rcases Nat.even_or_odd (j : ℕ) with hev | hod
      · refine mem_spectrum_fold_of β hβ _ j
          (fun r => r - (1 - (((capacity 1 β : ℕ) : ℝ) - 1) * β) / 2)
          (measurable_id.sub_const _) (β + 1) (by linarith) ?_ (-1) ?_ ?_ ?_
        · intro r hr0 hrβ
          rw [abs_le]
          constructor <;> nlinarith
        · intro r
          ring
        · rw [hev.neg_one_pow]
          ring
        · refine lt_of_lt_of_le (volume_oddEig_slice_pos β hβ)
            (measure_mono ?_)
          rintro z ⟨hS, hp, hb0, hbl⟩
          refine ⟨hS, hp, ?_⟩
          show chainBase β (rep z)
              - (1 - (((capacity 1 β : ℕ) : ℝ) - 1) * β) / 2 ≠ 0
          have : chainBase β (rep z)
              - (1 - ((capacity 1 β : ℝ) - 1) * β) / 2 < 0 := by linarith
          exact ne_of_lt this
      · refine mem_spectrum_fold_of β hβ _ j (fun _ => (1 : ℝ))
          measurable_const 1 zero_le_one (fun _ _ _ => by norm_num) 1
          (fun r => by ring) ?_ ?_
        · rw [hod.neg_one_pow]
          ring
        · refine lt_of_lt_of_le (volume_chainSet_capacity_pos β hβ)
            (measure_mono ?_)
          rintro z ⟨hS, hp⟩
          exact ⟨hS, hp, one_ne_zero⟩
    · rcases Nat.even_or_odd (j : ℕ) with hev | hod
      · refine mem_spectrum_fold_of β hβ _ j
          (fun r => r - (1 - (((capacity 1 β - 1 : ℕ) : ℝ) - 1) * β) / 2)
          (measurable_id.sub_const _) (β + 1) (by linarith) ?_ (-1) ?_ ?_ ?_
        · intro r hr0 hrβ
          rw [abs_le, hcast1]
          constructor <;> nlinarith
        · intro r
          ring
        · rw [hev.neg_one_pow]
          ring
        · refine lt_of_lt_of_le (volume_short_slice_pos β hβ hβ1 hshort)
            (measure_mono ?_)
          rintro z ⟨hS, hp, hbl⟩
          refine ⟨hS, hp, ?_⟩
          show chainBase β (rep z)
              - (1 - (((capacity 1 β - 1 : ℕ) : ℝ) - 1) * β) / 2 ≠ 0
          exact ne_of_lt (by linarith)
      · refine mem_spectrum_fold_of β hβ _ j (fun _ => (1 : ℝ))
          measurable_const 1 zero_le_one (fun _ _ _ => by norm_num) 1
          (fun r => by ring) ?_ ?_
        · rw [hod.neg_one_pow]
          ring
        · refine lt_of_lt_of_le (volume_chainSet_short_pos β hβ hβ1 hshort)
            (measure_mono ?_)
          rintro z ⟨hS, hp⟩
          exact ⟨hS, hp, one_ne_zero⟩

/-- **The fold is spectrally invisible**: the folded and unfolded operators
have identical spectra. -/
theorem spectrum_fold_eq_spectrum (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hshort : 1 < (capacity 1 β : ℝ) * β) :
    spectrum ℝ (compress oddSpace (pathLawW β))
      = spectrum ℝ (pathLawW β) := by
  rw [spectrum_compress_oddSpace_eq β hβ hβ1 hshort,
    spectrum_pathLawW β hβ hβ1 hshort]

/-! ### The Envelope Parity Law -/

/-- **The alternating carrier.** The bottom-rung envelope is the top
envelope times the sign character of the chain position:
`sin((p+1)·mπ/(m+1)) = (−1)^p · sin((p+1)·π/(m+1))`. -/
lemma chainEnv_last_alternating (β : ℝ) (m : ℕ) (hm : 0 < m)
    (hlast : m - 1 < m) (z : AddCircle (1 : ℝ)) :
    chainEnv β m ⟨m - 1, hlast⟩ z
      = (-1 : ℝ) ^ (chainPos β (rep z)) * chainEnv β m ⟨0, hm⟩ z := by
  unfold chainEnv
  have hangle1 : pathAngle m ⟨m - 1, hlast⟩
      = (m : ℝ) * (π / ((m : ℝ) + 1)) := by
    unfold pathAngle
    have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      push_cast [Nat.cast_sub hm]
      ring
    show (((m - 1 : ℕ) : ℝ) + 1) * π / ((m : ℝ) + 1) = _
    rw [hcast]
    ring
  have hangle0 : pathAngle m ⟨0, hm⟩ = π / ((m : ℝ) + 1) := by
    unfold pathAngle
    push_cast
    ring
  rw [hangle1, hangle0]
  have hne : ((m : ℝ) + 1) ≠ 0 := by positivity
  have harg : ((chainPos β (rep z) : ℝ) + 1) * ((m : ℝ) * (π / ((m : ℝ) + 1)))
      = ((chainPos β (rep z) + 1 : ℕ) : ℝ) * π
        - ((chainPos β (rep z) : ℝ) + 1) * (π / ((m : ℝ) + 1)) := by
    push_cast
    field_simp
    ring
  rw [harg]
  have hs := sin_nat_mul_pi_sub (chainPos β (rep z) + 1)
    (((chainPos β (rep z) : ℝ) + 1) * (π / ((m : ℝ) + 1)))
  rw [hs, pow_succ]
  ring

/-- The bottom-rung eigenvalue is the negated Chebyshev factor:
`2cos(mπ/(m+1)) = −chebFactor m`. -/
lemma two_cos_pathAngle_last (m : ℕ) (hm : 0 < m) (hlast : m - 1 < m) :
    2 * Real.cos (pathAngle m ⟨m - 1, hlast⟩) = - chebFactor m := by
  have hne : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hangle1 : pathAngle m ⟨m - 1, hlast⟩ = π - π / ((m : ℝ) + 1) := by
    unfold pathAngle
    have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      push_cast [Nat.cast_sub hm]
      ring
    show (((m - 1 : ℕ) : ℝ) + 1) * π / ((m : ℝ) + 1) = _
    rw [hcast]
    field_simp
    ring
  rw [hangle1, Real.cos_pi_sub]
  unfold chebFactor
  ring

/-- **The Envelope Parity Law.** A base modulation with parity `(−1)^m`
about the base midpoint turns the alternating carrier (the bottom rung)
into a reflection-ODD eigenfunction of the masked rotation with eigenvalue
`−chebFactor m` — exactly the folded top modes of `ΔO = −W|_O`. -/
theorem envelope_parity_law (β : ℝ) (hβ : 0 < β)
    (c : ℝ → ℝ) (hcm : Measurable c) (B : ℝ) (hB : 0 ≤ B)
    (hbd : ∀ r, 0 ≤ r → r < β → |c r| ≤ B)
    (hlast : capacity 1 β - 1 < capacity 1 β)
    (hc : ∀ r, c (1 - ((capacity 1 β : ℝ) - 1) * β - r)
        = (-1 : ℝ) ^ (capacity 1 β) * c r) :
    rungFunL2 β hβ (capacity 1 β) ⟨capacity 1 β - 1, hlast⟩ c hcm B hB hbd
        ∈ oddSpace
      ∧ pathLawW β (rungFunL2 β hβ (capacity 1 β)
            ⟨capacity 1 β - 1, hlast⟩ c hcm B hB hbd)
        = (- chebFactor (capacity 1 β))
            • rungFunL2 β hβ (capacity 1 β) ⟨capacity 1 β - 1, hlast⟩
                c hcm B hB hbd := by
  have hm1 : 1 ≤ capacity 1 β := one_le_capacity β hβ
  set g : L2c := rungFunL2 β hβ (capacity 1 β)
    ⟨capacity 1 β - 1, hlast⟩ c hcm B hB hbd with hgdef
  have hco : (g : AddCircle (1 : ℝ) → ℝ)
      =ᵐ[volume] rungFun β (capacity 1 β) ⟨capacity 1 β - 1, hlast⟩ c :=
    MemLp.coeFn_toLp _
  have hodd : (-1 : ℝ) ^ (capacity 1 β)
      * (-1 : ℝ) ^ ((⟨capacity 1 β - 1, hlast⟩ : Fin (capacity 1 β)) : ℕ)
      = -1 := by
    show (-1 : ℝ) ^ (capacity 1 β) * (-1 : ℝ) ^ (capacity 1 β - 1) = -1
    rw [← pow_add]
    exact Odd.neg_one_pow ⟨capacity 1 β - 1, by omega⟩
  have hRg : reflectL2 g = -g := by
    apply Lp.ext
    filter_upwards [reflect_ae g, ae_neg hco,
      rungFun_neg β hβ (capacity 1 β) ⟨capacity 1 β - 1, hlast⟩ c
        ((-1 : ℝ) ^ (capacity 1 β)) hc,
      Lp.coeFn_neg g, hco] with z hh1 hh2 hh3 hh4 hh5
    rw [hh1, hh2, hh3, hodd, hh4, Pi.neg_apply, hh5]
    ring
  refine ⟨?_, ?_⟩
  · show reflectPlusOne g = 0
    rw [reflectPlusOne, add_apply, one_apply_eq_self, hRg]
    exact neg_add_cancel _
  · have hWg : pathLawW β g
        = (2 * Real.cos (pathAngle (capacity 1 β)
            ⟨capacity 1 β - 1, hlast⟩)) • g := by
      apply Lp.ext
      filter_upwards [coeFn_pathLawW_step β g _ hco,
        Lp.coeFn_smul (2 * Real.cos (pathAngle (capacity 1 β)
          ⟨capacity 1 β - 1, hlast⟩)) g, hco] with z hh1 hh2 hh3
      rw [hh1, hh2, Pi.smul_apply, smul_eq_mul, hh3]
      exact wStep_baseEnv β hβ (capacity 1 β)
        ⟨capacity 1 β - 1, hlast⟩ c z
    rw [hWg, two_cos_pathAngle_last (capacity 1 β) (by omega) hlast]

/-- **The parity dichotomy.** A base modulation with the opposite parity
`(−1)^{m+1}` makes the bottom-rung function reflection-EVEN: the `(−1)^m`
constraint is exactly the odd-sector condition. -/
theorem envelope_parity_law_even (β : ℝ) (hβ : 0 < β)
    (c : ℝ → ℝ) (hcm : Measurable c) (B : ℝ) (hB : 0 ≤ B)
    (hbd : ∀ r, 0 ≤ r → r < β → |c r| ≤ B)
    (hlast : capacity 1 β - 1 < capacity 1 β)
    (hc : ∀ r, c (1 - ((capacity 1 β : ℝ) - 1) * β - r)
        = (-1 : ℝ) ^ (capacity 1 β + 1) * c r) :
    reflectL2 (rungFunL2 β hβ (capacity 1 β)
        ⟨capacity 1 β - 1, hlast⟩ c hcm B hB hbd)
      = rungFunL2 β hβ (capacity 1 β)
          ⟨capacity 1 β - 1, hlast⟩ c hcm B hB hbd := by
  have hm1 : 1 ≤ capacity 1 β := one_le_capacity β hβ
  set g : L2c := rungFunL2 β hβ (capacity 1 β)
    ⟨capacity 1 β - 1, hlast⟩ c hcm B hB hbd with hgdef
  have hco : (g : AddCircle (1 : ℝ) → ℝ)
      =ᵐ[volume] rungFun β (capacity 1 β) ⟨capacity 1 β - 1, hlast⟩ c :=
    MemLp.coeFn_toLp _
  have heven : (-1 : ℝ) ^ (capacity 1 β + 1)
      * (-1 : ℝ) ^ ((⟨capacity 1 β - 1, hlast⟩ : Fin (capacity 1 β)) : ℕ)
      = 1 := by
    show (-1 : ℝ) ^ (capacity 1 β + 1) * (-1 : ℝ) ^ (capacity 1 β - 1) = 1
    rw [← pow_add]
    exact Even.neg_one_pow ⟨capacity 1 β, by omega⟩
  apply Lp.ext
  filter_upwards [reflect_ae g, ae_neg hco,
    rungFun_neg β hβ (capacity 1 β) ⟨capacity 1 β - 1, hlast⟩ c
      ((-1 : ℝ) ^ (capacity 1 β + 1)) hc, hco] with z hh1 hh2 hh3 hh5
  rw [hh1, hh2, hh3, heven, hh5]
  ring

end Cvs.PathLaw
