/-
The exact spectral set of the masked rotation — the annihilation route.

The paper's Theorem 1.1(a) describes `spec(W)` as the union of the Chebyshev
spectra of the two chain lengths `m = ⌈1/β⌉` and `m − 1`. The containment
`spec(W) ⊆ …` is proved here WITHOUT direct integrals: the masked rotation
satisfies the polynomial identity

  `pathCharPoly m (W) * pathCharPoly (m-1) (W) = 0`,

because every point sits at position `j` on a chain of length `m` or `m − 1`,
iterating the masked hops walks the chain exactly as the path adjacency
matrix does (`wStep_iterate`), and the Chebyshev product annihilates both
path matrices (`Annihilate.lean`). Polynomial spectral mapping
(`SpectralMapping.lean`) then traps the spectrum in the finite root set.

Structure:
* `wStep` — the pointwise model of one masked hop; no measure theory.
* `mem_maskFwd_iff` / `mem_maskBwd_iff` — the masks are exactly the
  "neighbour exists" guards of the chain position.
* `wStep_iterate` — the chain walk: `n` pointwise hops = the `n`-th power of
  the path adjacency matrix, read off in the chain frame.
-/
import Cvs.PathLaw.Weight
import Cvs.PathLaw.Annihilate
import Cvs.PathLaw.SpectralMapping

open MeasureTheory Polynomial

namespace Cvs.PathLaw

local notation "L2c" => Lp ℝ 2 (volume : Measure (AddCircle (1 : ℝ)))

/-- The rotation step as a point of the circle. -/
noncomputable def bcirc (β : ℝ) : AddCircle (1 : ℝ) := ((β : ℝ) : AddCircle (1 : ℝ))

/-- The pointwise model of one masked hop:
`(wStep g)(z) = 1_fwd(z)·g(z + β) + 1_bwd(z)·g(z − β)`. Pure functions, no
measure theory. -/
noncomputable def wStep (β : ℝ) (g : AddCircle (1 : ℝ) → ℝ) :
    AddCircle (1 : ℝ) → ℝ := fun z =>
  (maskFwd β).indicator (fun w => g (w + bcirc β)) z
    + (maskBwd β).indicator (fun w => g (w - bcirc β)) z

lemma wStep_apply (β : ℝ) (g : AddCircle (1 : ℝ) → ℝ) (z : AddCircle (1 : ℝ)) :
    wStep β g z
      = (maskFwd β).indicator (fun w => g (w + bcirc β)) z
        + (maskBwd β).indicator (fun w => g (w - bcirc β)) z := rfl

/-! ### The masks are the chain-position guards -/

/-- The forward mask holds exactly when the forward neighbour exists on the
chain: `j + 1 < ℓ`. -/
lemma mem_maskFwd_iff (β : ℝ) (hβ : 0 < β) (z : AddCircle (1 : ℝ)) :
    z ∈ maskFwd β
      ↔ chainPos β (rep z) + 1 < chainLength β (chainBase β (rep z)) := by
  have hx := chainBase_add β (rep z)
  have hexp : ((chainPos β (rep z) : ℝ) + 1) * β
      = (chainPos β (rep z) : ℝ) * β + β := by ring
  constructor
  · intro h
    have h1 : rep z + β < 1 := h
    unfold chainLength
    rw [Nat.lt_ceil]
    push_cast
    rw [lt_div_iff₀ hβ]
    linarith
  · intro h
    show rep z + β < 1
    unfold chainLength at h
    rw [Nat.lt_ceil] at h
    push_cast at h
    rw [lt_div_iff₀ hβ] at h
    linarith

/-- The backward mask holds exactly when the backward neighbour exists on the
chain: `1 ≤ j`. -/
lemma mem_maskBwd_iff (β : ℝ) (hβ : 0 < β) (z : AddCircle (1 : ℝ)) :
    z ∈ maskBwd β ↔ 1 ≤ chainPos β (rep z) := by
  constructor
  · intro h
    exact chainPos_ge_one β (rep z) hβ h
  · intro h
    show β ≤ rep z
    unfold chainPos at h
    have h1 : (1 : ℝ) ≤ rep z / β := by
      have h2 := (Nat.le_floor_iff (n := 1)
        (div_nonneg (rep_nonneg z) hβ.le)).mp h
      exact_mod_cast h2
    calc β = 1 * β := (one_mul β).symm
      _ ≤ (rep z / β) * β := mul_le_mul_of_nonneg_right h1 hβ.le
      _ = rep z := by field_simp

/-! ### Circle-step arithmetic in the chain frame -/

lemma add_step_zsmul (z b : AddCircle (1 : ℝ)) (k : ℤ) :
    z + b + (k - 1) • b = z + k • b := by
  rw [add_assoc]
  congr 1
  rw [sub_zsmul, one_zsmul]
  abel

lemma sub_step_zsmul (z b : AddCircle (1 : ℝ)) (k : ℤ) :
    z - b + (k + 1) • b = z + k • b := by
  rw [sub_eq_add_neg, add_assoc]
  congr 1
  rw [add_zsmul, one_zsmul]
  abel

/-! ### The chain walk -/

/-- **The chain walk.** `n` pointwise masked hops read off the `n`-th power
of the path adjacency matrix in the chain frame: for a point at position
`pos` on a chain of length `len`,

  `(wStep^[n] g)(z) = Σ_p (A(P_len)^n)_{pos,p} · g(z + (p − pos)β)`.

The chain data enter only through the two mask guards, which by
`mem_maskFwd_iff` / `mem_maskBwd_iff` mirror the tridiagonal row expansion
`mulVec_pathAdj` exactly. -/
theorem wStep_iterate (β : ℝ) (hβ : 0 < β) (g : AddCircle (1 : ℝ) → ℝ) :
    ∀ (n : ℕ) (z : AddCircle (1 : ℝ)) (len : ℕ)
      (_hlen : chainLength β (chainBase β (rep z)) = len) (pos : Fin len)
      (_hpos : (pos : ℕ) = chainPos β (rep z)),
      (wStep β)^[n] g z
        = ((pathAdj len ^ n).mulVec
            (fun p => g (z + ((p : ℤ) - (pos : ℤ)) • bcirc β))) pos := by
  intro n
  induction n with
  | zero =>
    intro z len hlen pos hpos
    rw [Function.iterate_zero_apply, pow_zero, Matrix.one_mulVec]
    rw [sub_self, zero_zsmul, add_zero]
  | succ n IH =>
    intro z len hlen pos hpos
    rw [Function.iterate_succ_apply', wStep_apply, pow_succ',
      ← Matrix.mulVec_mulVec, mulVec_pathAdj]
    have hfwd : (maskFwd β).indicator
        (fun w => (wStep β)^[n] g (w + bcirc β)) z
        = (if h : (pos : ℕ) + 1 < len then
            ((pathAdj len ^ n).mulVec
              (fun p => g (z + ((p : ℤ) - (pos : ℤ)) • bcirc β)))
              ⟨(pos : ℕ) + 1, h⟩
          else 0) := by
      by_cases hf : z ∈ maskFwd β
      · have hmf := (mem_maskFwd_iff β hβ z).mp hf
        have hlt : (pos : ℕ) + 1 < len := by omega
        rw [Set.indicator_of_mem hf, dif_pos hlt]
        have hrep' : rep (z + bcirc β) = rep z + β :=
          rep_add_step β z hβ.le hf
        have hlen' : chainLength β (chainBase β (rep (z + bcirc β))) = len := by
          rw [hrep', chainBase_add_step β (rep z) hβ (rep_nonneg z), hlen]
        have hpos' : (((⟨(pos : ℕ) + 1, hlt⟩ : Fin len)) : ℕ)
            = chainPos β (rep (z + bcirc β)) := by
          show (pos : ℕ) + 1 = _
          rw [hrep', chainPos_add_step β (rep z) hβ (rep_nonneg z), hpos]
        rw [IH (z + bcirc β) len hlen' ⟨(pos : ℕ) + 1, hlt⟩ hpos']
        congr 1
        funext p
        have hcoe : (((⟨(pos : ℕ) + 1, hlt⟩ : Fin len)) : ℤ) = (pos : ℤ) + 1 := by
          show (((pos : ℕ) + 1 : ℕ) : ℤ) = _
          push_cast
          rfl
        rw [hcoe, show (p : ℤ) - ((pos : ℤ) + 1) = ((p : ℤ) - (pos : ℤ)) - 1
          from by ring]
        exact congrArg g (add_step_zsmul z (bcirc β) ((p : ℤ) - (pos : ℤ)))
      · have hnlt : ¬((pos : ℕ) + 1 < len) := by
          intro hcon
          exact hf ((mem_maskFwd_iff β hβ z).mpr (by omega))
        rw [Set.indicator_of_notMem hf, dif_neg hnlt]
    have hbwd : (maskBwd β).indicator
        (fun w => (wStep β)^[n] g (w - bcirc β)) z
        = (if _h : 1 ≤ (pos : ℕ) then
            ((pathAdj len ^ n).mulVec
              (fun p => g (z + ((p : ℤ) - (pos : ℤ)) • bcirc β)))
              ⟨(pos : ℕ) - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) pos.isLt⟩
          else 0) := by
      by_cases hb : z ∈ maskBwd β
      · have hmb := (mem_maskBwd_iff β hβ z).mp hb
        have h1p : 1 ≤ (pos : ℕ) := by omega
        rw [Set.indicator_of_mem hb, dif_pos h1p]
        have hrep' : rep (z - bcirc β) = rep z - β :=
          rep_sub_step β z hβ.le hb
        have hstep := chainPos_sub_step β (rep z) hβ (by omega)
        have hlen' : chainLength β (chainBase β (rep (z - bcirc β))) = len := by
          rw [hrep', chainBase_sub_step β (rep z) hβ (by omega), hlen]
        have hpos' : (((⟨(pos : ℕ) - 1,
            Nat.lt_of_le_of_lt (Nat.sub_le _ _) pos.isLt⟩ : Fin len)) : ℕ)
            = chainPos β (rep (z - bcirc β)) := by
          show (pos : ℕ) - 1 = _
          rw [hrep']
          omega
        rw [IH (z - bcirc β) len hlen'
          ⟨(pos : ℕ) - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) pos.isLt⟩ hpos']
        congr 1
        funext p
        have hcoe : (((⟨(pos : ℕ) - 1,
            Nat.lt_of_le_of_lt (Nat.sub_le _ _) pos.isLt⟩ : Fin len)) : ℤ)
            = (pos : ℤ) - 1 := by
          show (((pos : ℕ) - 1 : ℕ) : ℤ) = (((pos : ℕ) : ℤ)) - 1
          omega
        rw [hcoe, show (p : ℤ) - ((pos : ℤ) - 1) = ((p : ℤ) - (pos : ℤ)) + 1
          from by ring]
        exact congrArg g (sub_step_zsmul z (bcirc β) ((p : ℤ) - (pos : ℤ)))
      · have hn1 : ¬(1 ≤ (pos : ℕ)) := by
          intro hcon
          exact hb ((mem_maskBwd_iff β hβ z).mpr (by omega))
        rw [Set.indicator_of_notMem hb, dif_neg hn1]
    rw [hfwd, hbwd]

/-! ### Transfer: the operator matches the pointwise model a.e. -/

/-- One masked hop of `pathLawW` agrees a.e. with the pointwise model applied
to any representative. -/
lemma coeFn_pathLawW_step (β : ℝ) (u : L2c) (g : AddCircle (1 : ℝ) → ℝ)
    (hg : (u : AddCircle (1 : ℝ) → ℝ) =ᵐ[volume] g) :
    (pathLawW β u : AddCircle (1 : ℝ) → ℝ) =ᵐ[volume] wStep β g := by
  set bc : AddCircle (1 : ℝ) := ((β : ℝ) : AddCircle (1 : ℝ)) with hbc
  have hmr : pathLawW β u
      = maskCLM volume (maskFwd β) (measurableSet_maskFwd β) (koopman bc u)
        + maskCLM volume (maskBwd β) (measurableSet_maskBwd β)
            (koopman (-bc) u) := rfl
  filter_upwards [Lp.coeFn_add
      (maskCLM volume (maskFwd β) (measurableSet_maskFwd β) (koopman bc u))
      (maskCLM volume (maskBwd β) (measurableSet_maskBwd β) (koopman (-bc) u)),
    coeFn_maskCLM volume (maskFwd β) (measurableSet_maskFwd β) (koopman bc u),
    coeFn_maskCLM volume (maskBwd β) (measurableSet_maskBwd β)
      (koopman (-bc) u),
    koopman_ae bc u, koopman_ae (-bc) u,
    ae_translate bc hg, ae_translate (-bc) hg] with z h1 h2 h3 h4 h5 h6 h7
  rw [hmr, h1, Pi.add_apply, h2, h3, wStep_apply]
  congr 1
  · by_cases hm : z ∈ maskFwd β
    · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm, h4, h6]
      rfl
    · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm]
  · by_cases hm : z ∈ maskBwd β
    · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm, h5, h7]
      show g (z + -bc) = g (z - bc)
      rw [sub_eq_add_neg]
    · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm]

/-- Powers of `pathLawW` agree a.e. with iterates of the pointwise model. -/
lemma coeFn_pathLawW_pow (β : ℝ) (u : L2c) (g : AddCircle (1 : ℝ) → ℝ)
    (hg : (u : AddCircle (1 : ℝ) → ℝ) =ᵐ[volume] g) (n : ℕ) :
    ((pathLawW β ^ n) u : AddCircle (1 : ℝ) → ℝ)
      =ᵐ[volume] (wStep β)^[n] g := by
  induction n with
  | zero =>
    rw [pow_zero, Function.iterate_zero_apply]
    simpa [one_apply_eq_self] using hg
  | succ n IH =>
    have hpow : (pathLawW β ^ (n + 1)) u
        = pathLawW β ((pathLawW β ^ n) u) := by
      rw [pow_succ']
      rfl
    rw [hpow, Function.iterate_succ_apply']
    exact coeFn_pathLawW_step β ((pathLawW β ^ n) u) _ IH

/-- Coefficient functions of finite sums in `Lp`. -/
lemma coeFn_finset_sum {ι : Type*} (s : Finset ι) (F : ι → L2c) :
    ((∑ i ∈ s, F i : L2c) : AddCircle (1 : ℝ) → ℝ)
      =ᵐ[volume] fun z => ∑ i ∈ s, (F i : AddCircle (1 : ℝ) → ℝ) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℝ 2 volume
  | insert i s hi IH =>
    rw [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (F i) (∑ j ∈ s, F j), IH] with z h1 h2
    rw [h1, Pi.add_apply, h2, Finset.sum_insert hi]

/-! ### The annihilating polynomial of the masked rotation -/

/-- The Chebyshev product for the two chain lengths `m = ⌈1/β⌉` and `m − 1`:
the annihilating polynomial of the masked rotation. -/
noncomputable def chainPoly (β : ℝ) : Polynomial ℝ :=
  pathCharPoly (capacity 1 β) * pathCharPoly (capacity 1 β - 1)

/-- Sums pull out of `mulVec` in the matrix argument. -/
lemma sum_mulVec {n' : Type*} [Fintype n'] {ι : Type*} (s : Finset ι)
    (M : ι → Matrix n' n' ℝ) (v : n' → ℝ) :
    (∑ i ∈ s, M i).mulVec v = ∑ i ∈ s, (M i).mulVec v :=
  map_sum (Matrix.mulVec.addMonoidHomLeft v) M s

/-- The chain polynomial annihilates the path matrix of every chain length
that occurs: `len ∈ {m, m−1}`. -/
lemma aeval_pathAdj_chainPoly (β : ℝ) {len : ℕ}
    (hor : len = capacity 1 β ∨ len + 1 = capacity 1 β) :
    aeval (pathAdj len) (chainPoly β) = 0 := by
  rw [chainPoly, map_mul]
  rcases hor with h | h
  · rw [← h, aeval_pathAdj, zero_mul]
  · have hlen : capacity 1 β - 1 = len := by omega
    rw [hlen, aeval_pathAdj, mul_zero]

/-- **The pointwise annihilation, parameterized.** At a point of the circle,
any polynomial that kills the path matrix of the local chain length kills the
combination of masked hops. -/
lemma sum_coeff_wStep_iterate_of (β : ℝ) (hβ : 0 < β) (q : Polynomial ℝ)
    (g : AddCircle (1 : ℝ) → ℝ) (z : AddCircle (1 : ℝ))
    (hann : aeval (pathAdj (chainLength β (chainBase β (rep z)))) q = 0) :
    ∑ k ∈ Finset.range (q.natDegree + 1),
      q.coeff k * (wStep β)^[k] g z = 0 := by
  have hlt : chainPos β (rep z) < chainLength β (chainBase β (rep z)) :=
    chainPos_lt_chainLength β (rep z) hβ (rep_lt_one z)
  set len := chainLength β (chainBase β (rep z)) with hlen
  set pos : Fin len := ⟨chainPos β (rep z), hlt⟩ with hposdef
  set v : Fin len → ℝ :=
    fun p => g (z + ((p : ℤ) - (pos : ℤ)) • bcirc β) with hv
  have hiter : ∀ k, (wStep β)^[k] g z = ((pathAdj len ^ k).mulVec v) pos :=
    fun k => wStep_iterate β hβ g k z len rfl pos rfl
  calc ∑ k ∈ Finset.range (q.natDegree + 1),
        q.coeff k * (wStep β)^[k] g z
      = ∑ k ∈ Finset.range (q.natDegree + 1),
          ((q.coeff k • pathAdj len ^ k).mulVec v) pos := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hiter k, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
    _ = ((∑ k ∈ Finset.range (q.natDegree + 1),
          q.coeff k • pathAdj len ^ k).mulVec v) pos := by
        rw [sum_mulVec, Finset.sum_apply]
    _ = ((aeval (pathAdj len) q).mulVec v) pos := by
        rw [← aeval_eq_sum_range]
    _ = 0 := by
        rw [hann, Matrix.zero_mulVec]
        rfl

/-- **The annihilation transfer, parameterized.** Any polynomial killing the
path matrix of every occurring chain length annihilates the masked rotation
itself. -/
theorem aeval_pathLawW_of (β : ℝ) (hβ : 0 < β) (q : Polynomial ℝ)
    (hann : ∀ z : AddCircle (1 : ℝ),
      aeval (pathAdj (chainLength β (chainBase β (rep z)))) q = 0) :
    aeval (pathLawW β) q = 0 := by
  ext u
  rw [zero_apply]
  set N := q.natDegree + 1 with hN
  set g : AddCircle (1 : ℝ) → ℝ := (u : AddCircle (1 : ℝ) → ℝ) with hgdef
  have haev : aeval (pathLawW β) q u
      = ∑ k ∈ Finset.range N,
          q.coeff k • ((pathLawW β ^ k) u) := by
    rw [aeval_eq_sum_range]
    rw [sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_apply]
  have hk : ∀ k, ((q.coeff k • ((pathLawW β ^ k) u) : L2c) :
      AddCircle (1 : ℝ) → ℝ)
      =ᵐ[volume] fun z => q.coeff k * (wStep β)^[k] g z := by
    intro k
    filter_upwards [Lp.coeFn_smul (q.coeff k) ((pathLawW β ^ k) u),
      coeFn_pathLawW_pow β u g Filter.EventuallyEq.rfl k] with z h1 h2
    rw [h1, Pi.smul_apply, smul_eq_mul, h2]
  have hall : ∀ᵐ z ∂(volume : Measure (AddCircle (1 : ℝ))), ∀ k, k ∈ Finset.range N →
      (((q.coeff k • ((pathLawW β ^ k) u)) : L2c) :
        AddCircle (1 : ℝ) → ℝ) z
        = q.coeff k * (wStep β)^[k] g z := by
    rw [MeasureTheory.ae_all_iff]
    intro k
    filter_upwards [hk k] with z hz _
    exact hz
  rw [haev]
  filter_upwards [coeFn_finset_sum (Finset.range N)
      (fun k => q.coeff k • ((pathLawW β ^ k) u)), hall,
    Lp.coeFn_zero ℝ 2 (volume : Measure (AddCircle (1 : ℝ)))] with z h1 h2 h3
  rw [h1, h3]
  calc ∑ k ∈ Finset.range N,
        (((q.coeff k • ((pathLawW β ^ k) u)) : L2c) :
          AddCircle (1 : ℝ) → ℝ) z
      = ∑ k ∈ Finset.range N,
          q.coeff k * (wStep β)^[k] g z :=
        Finset.sum_congr rfl fun k hkmem => h2 k hkmem
    _ = 0 := sum_coeff_wStep_iterate_of β hβ q g z (hann z)

/-- **The annihilation identity.** The masked rotation satisfies the
Chebyshev polynomial identity
`pathCharPoly m (W) ∘ pathCharPoly (m−1) (W) = 0`, `m = ⌈1/β⌉`. This is the
operator-level form of the chain decomposition — no direct integrals. -/
theorem aeval_chainPoly_pathLawW (β : ℝ) (hβ : 0 < β) :
    aeval (pathLawW β) (chainPoly β) = 0 :=
  aeval_pathLawW_of β hβ _ fun z =>
    aeval_pathAdj_chainPoly β
      (chainLength_eq_or β (chainBase β (rep z)) hβ
        (chainBase_nonneg β (rep z) hβ (rep_nonneg z))
        (chainBase_lt β (rep z) hβ))

/-- In the degenerate case `mβ = 1` (all chains long), every chain has length
exactly `m`. -/
lemma chainLength_eq_capacity_of_deg (β : ℝ) (hβ : 0 < β)
    (hdeg : (capacity 1 β : ℝ) * β = 1) (r : ℝ) (hr0 : 0 ≤ r) (hrβ : r < β) :
    chainLength β r = capacity 1 β := by
  have hm1 : 1 ≤ capacity 1 β := one_le_capacity β hβ
  unfold chainLength
  rw [Nat.ceil_eq_iff (by omega)]
  have hcast : ((capacity 1 β - 1 : ℕ) : ℝ) = (capacity 1 β : ℝ) - 1 := by
    push_cast [Nat.cast_sub hm1]
    ring
  constructor
  · rw [hcast, lt_div_iff₀ hβ]
    nlinarith
  · rw [div_le_iff₀ hβ]
    nlinarith

/-- In the degenerate case, the single Chebyshev factor `pathCharPoly m`
already annihilates the masked rotation. -/
theorem aeval_pathCharPoly_pathLawW_deg (β : ℝ) (hβ : 0 < β)
    (hdeg : (capacity 1 β : ℝ) * β = 1) :
    aeval (pathLawW β) (pathCharPoly (capacity 1 β)) = 0 :=
  aeval_pathLawW_of β hβ _ fun z => by
    rw [chainLength_eq_capacity_of_deg β hβ hdeg (chainBase β (rep z))
      (chainBase_nonneg β (rep z) hβ (rep_nonneg z))
      (chainBase_lt β (rep z) hβ)]
    exact aeval_pathAdj (capacity 1 β)

/-- **Spectral-set containment.** The spectrum of the masked rotation is
contained in the root set of the Chebyshev chain polynomial — the union of
the path-graph spectra of `P_m` and `P_{m−1}`. -/
theorem spectrum_pathLawW_subset (β : ℝ) (hβ : 0 < β) :
    spectrum ℝ (pathLawW β) ⊆ {μ : ℝ | (chainPoly β).eval μ = 0} :=
  spectrum_subset_roots_of_aeval_eq_zero (aeval_chainPoly_pathLawW β hβ)

/-! ### Eigenfunctions: every Chebyshev value is attained

The `j`-th sine envelope on the chains of length exactly `L` is an exact
eigenvector of the masked rotation with eigenvalue `2cos((j+1)π/(L+1))` —
the general-`j`, both-lengths version of `pathLawW_testFun`. -/

/-- The union of the chains of length exactly `L`. -/
def chainSet (β : ℝ) (L : ℕ) : Set (AddCircle (1 : ℝ)) :=
  {z | chainLength β (chainBase β (rep z)) = L}

theorem measurableSet_chainSet (β : ℝ) (L : ℕ) :
    MeasurableSet (chainSet β L) :=
  ((measurable_chainLength β).comp measurable_rep) (measurableSet_singleton _)

theorem chainSet_add_step (β : ℝ) (hβ : 0 < β) (L : ℕ)
    (z : AddCircle (1 : ℝ)) (hz : z ∈ maskFwd β) :
    (z + bcirc β) ∈ chainSet β L ↔ z ∈ chainSet β L := by
  have hrep : rep (z + bcirc β) = rep z + β := rep_add_step β z hβ.le hz
  show chainLength β (chainBase β (rep (z + _))) = L ↔ _
  rw [hrep, chainBase_add_step β (rep z) hβ (rep_nonneg z)]
  rfl

theorem chainSet_sub_step (β : ℝ) (hβ : 0 < β) (L : ℕ)
    (z : AddCircle (1 : ℝ)) (hz : z ∈ maskBwd β) :
    (z - bcirc β) ∈ chainSet β L ↔ z ∈ chainSet β L := by
  have hb : β ≤ rep z := hz
  have hrep : rep (z - bcirc β) = rep z - β := rep_sub_step β z hβ.le hb
  have hpos : 1 ≤ chainPos β (rep z) := chainPos_ge_one β (rep z) hβ hb
  show chainLength β (chainBase β (rep (z - _))) = L ↔ _
  rw [hrep, chainBase_sub_step β (rep z) hβ hpos]
  rfl

/-- The `j`-th sine envelope in the chain frame:
`sin((pos+1)·(j+1)π/(L+1))`. -/
noncomputable def chainEnv (β : ℝ) (L : ℕ) (j : Fin L)
    (z : AddCircle (1 : ℝ)) : ℝ :=
  Real.sin (((chainPos β (rep z) : ℝ) + 1) * pathAngle L j)

lemma chainEnv_add_step (β : ℝ) (hβ : 0 < β) (L : ℕ) (j : Fin L)
    (z : AddCircle (1 : ℝ)) (hz : z ∈ maskFwd β) :
    chainEnv β L j (z + bcirc β)
      = Real.sin (((chainPos β (rep z) : ℝ) + 2) * pathAngle L j) := by
  have hrep : rep (z + bcirc β) = rep z + β := rep_add_step β z hβ.le hz
  unfold chainEnv
  rw [hrep, chainPos_add_step β (rep z) hβ (rep_nonneg z)]
  congr 1
  push_cast
  ring

lemma chainEnv_sub_step (β : ℝ) (hβ : 0 < β) (L : ℕ) (j : Fin L)
    (z : AddCircle (1 : ℝ)) (hz : z ∈ maskBwd β) :
    chainEnv β L j (z - bcirc β)
      = Real.sin ((chainPos β (rep z) : ℝ) * pathAngle L j) := by
  have hb : β ≤ rep z := hz
  have h1 := chainPos_ge_one β (rep z) hβ hb
  have hstep := chainPos_sub_step β (rep z) hβ h1
  have hrep : rep (z - bcirc β) = rep z - β := rep_sub_step β z hβ.le hb
  unfold chainEnv
  rw [hrep]
  congr 1
  have hcast : ((chainPos β (rep z - β) : ℝ)) + 1
      = (chainPos β (rep z) : ℝ) := by exact_mod_cast congrArg Nat.cast hstep
  rw [hcast]

/-- **The pointwise eigen-equation.** The masked hop acts on the indicator
sine envelope as multiplication by the Chebyshev value: the mask guards drop
exactly the vanishing boundary terms of `sin_rung`. -/
lemma wStep_chainEnv (β : ℝ) (hβ : 0 < β) (L : ℕ) (j : Fin L)
    (z : AddCircle (1 : ℝ)) :
    wStep β ((chainSet β L).indicator (chainEnv β L j)) z
      = 2 * Real.cos (pathAngle L j)
        * (chainSet β L).indicator (chainEnv β L j) z := by
  set g := (chainSet β L).indicator (chainEnv β L j) with hg
  rw [wStep_apply]
  by_cases hzS : z ∈ chainSet β L
  · have hlenz : chainLength β (chainBase β (rep z)) = L := hzS
    have hposlt : chainPos β (rep z) < L := by
      have := chainPos_lt_chainLength β (rep z) hβ (rep_lt_one z)
      omega
    have hfwd : (maskFwd β).indicator (fun w => g (w + bcirc β)) z
        = if chainPos β (rep z) + 1 < L then
            Real.sin (((chainPos β (rep z) : ℝ) + 2) * pathAngle L j)
          else 0 := by
      by_cases hf : z ∈ maskFwd β
      · have hguard : chainPos β (rep z) + 1 < L := by
          have := (mem_maskFwd_iff β hβ z).mp hf
          omega
        rw [Set.indicator_of_mem hf, if_pos hguard, hg,
          Set.indicator_of_mem ((chainSet_add_step β hβ L z hf).mpr hzS),
          chainEnv_add_step β hβ L j z hf]
      · have hguard : ¬(chainPos β (rep z) + 1 < L) := by
          intro hcon
          exact hf ((mem_maskFwd_iff β hβ z).mpr (by omega))
        rw [Set.indicator_of_notMem hf, if_neg hguard]
    have hbwd : (maskBwd β).indicator (fun w => g (w - bcirc β)) z
        = if 1 ≤ chainPos β (rep z) then
            Real.sin ((chainPos β (rep z) : ℝ) * pathAngle L j)
          else 0 := by
      by_cases hb : z ∈ maskBwd β
      · have hguard : 1 ≤ chainPos β (rep z) :=
          (mem_maskBwd_iff β hβ z).mp hb
        rw [Set.indicator_of_mem hb, if_pos hguard, hg,
          Set.indicator_of_mem ((chainSet_sub_step β hβ L z hb).mpr hzS),
          chainEnv_sub_step β hβ L j z hb]
      · have hguard : ¬(1 ≤ chainPos β (rep z)) := by
          intro hcon
          exact hb ((mem_maskBwd_iff β hβ z).mpr hcon)
        rw [Set.indicator_of_notMem hb, if_neg hguard]
    rw [hfwd, hbwd, hg, Set.indicator_of_mem hzS]
    have hrung := sin_rung (pathAngle L j) (chainPos β (rep z))
    unfold chainEnv
    by_cases h1 : chainPos β (rep z) + 1 < L
    · rw [if_pos h1]
      by_cases h2 : 1 ≤ chainPos β (rep z)
      · rw [if_pos h2]
        linarith
      · rw [if_neg h2]
        have hp0 : chainPos β (rep z) = 0 := by omega
        rw [hp0] at hrung ⊢
        push_cast at hrung ⊢
        norm_num at hrung ⊢
        linarith
    · rw [if_neg h1]
      have hptop : chainPos β (rep z) + 1 = L := by omega
      have hc1 : ((chainPos β (rep z) : ℝ)) + 1 = (L : ℝ) := by
        exact_mod_cast hptop
      have htopcast : ((chainPos β (rep z) : ℝ)) + 2 = (L : ℝ) + 1 := by
        linarith
      have htop : Real.sin (((chainPos β (rep z) : ℝ) + 2) * pathAngle L j)
          = 0 := by
        rw [htopcast]
        exact sin_top L j
      by_cases h2 : 1 ≤ chainPos β (rep z)
      · rw [if_pos h2]
        linarith
      · rw [if_neg h2]
        have hp0 : chainPos β (rep z) = 0 := by omega
        rw [hp0] at hrung htop ⊢
        push_cast at hrung htop ⊢
        norm_num at hrung htop
        rw [zero_add, zero_add, one_mul, ← hrung, htop]
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

/-! ### The eigenfunctions as `L²` elements -/

lemma measurable_chainEnv (β : ℝ) (L : ℕ) (j : Fin L) :
    Measurable (chainEnv β L j) := by
  unfold chainEnv
  exact Real.measurable_sin.comp
    ((((measurable_from_top.comp
      ((measurable_chainPos β).comp measurable_rep)).add_const 1).mul_const
        (pathAngle L j)))

theorem memLp_chainEigenFun (β : ℝ) (L : ℕ) (j : Fin L) :
    MemLp ((chainSet β L).indicator (chainEnv β L j)) 2
      (volume : Measure (AddCircle (1 : ℝ))) := by
  refine MemLp.of_bound
    (((measurable_chainEnv β L j).indicator
      (measurableSet_chainSet β L)).aestronglyMeasurable) 1 ?_
  filter_upwards with z
  rw [Real.norm_eq_abs]
  by_cases h : z ∈ chainSet β L
  · rw [Set.indicator_of_mem h]
    exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  · rw [Set.indicator_of_notMem h]
    norm_num

/-- The `j`-th eigenfunction of the chains of length `L`. -/
noncomputable def chainEigenFun (β : ℝ) (L : ℕ) (j : Fin L) : L2c :=
  MemLp.toLp _ (memLp_chainEigenFun β L j)

theorem coeFn_chainEigenFun (β : ℝ) (L : ℕ) (j : Fin L) :
    (chainEigenFun β L j : AddCircle (1 : ℝ) → ℝ)
      =ᵐ[volume] (chainSet β L).indicator (chainEnv β L j) :=
  MemLp.coeFn_toLp _

/-- **The eigenvector equation.** Every Chebyshev value of every occurring
chain length is an exact eigenvalue of the masked rotation. -/
theorem pathLawW_chainEigenFun (β : ℝ) (hβ : 0 < β) (L : ℕ) (j : Fin L) :
    pathLawW β (chainEigenFun β L j)
      = (2 * Real.cos (pathAngle L j)) • chainEigenFun β L j := by
  apply Lp.ext
  filter_upwards [coeFn_pathLawW_step β (chainEigenFun β L j) _
      (coeFn_chainEigenFun β L j),
    Lp.coeFn_smul (2 * Real.cos (pathAngle L j)) (chainEigenFun β L j),
    coeFn_chainEigenFun β L j] with z h1 h2 h3
  rw [h1, h2, Pi.smul_apply, smul_eq_mul, h3, wStep_chainEnv β hβ L j z]

/-! ### Nonvanishing: position-0 slices have positive measure -/

/-- If the position-0 slice of the length-`L` chains has positive measure,
the `j`-th eigenfunction is a nonzero `L²` element (the envelope at position
`0` is `sin θ_j > 0`). -/
theorem chainEigenFun_ne_zero (β : ℝ) (L : ℕ) (j : Fin L)
    (hvol : 0 < volume {z : AddCircle (1 : ℝ) |
      z ∈ chainSet β L ∧ chainPos β (rep z) = 0}) :
    chainEigenFun β L j ≠ 0 := by
  intro hzero
  have hco := coeFn_chainEigenFun β L j
  rw [hzero] at hco
  have h0 : (chainSet β L).indicator (chainEnv β L j) =ᵐ[volume] 0 :=
    hco.symm.trans (Lp.coeFn_zero ℝ 2 volume)
  have hsub : {z : AddCircle (1 : ℝ) |
        z ∈ chainSet β L ∧ chainPos β (rep z) = 0}
      ⊆ {z | (chainSet β L).indicator (chainEnv β L j) z ≠ 0} := by
    intro z hz
    show (chainSet β L).indicator (chainEnv β L j) z ≠ 0
    rw [Set.indicator_of_mem hz.1]
    unfold chainEnv
    rw [hz.2]
    push_cast
    rw [zero_add, one_mul]
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (pathAngle_pos L j)
      (pathAngle_lt_pi L j))
  have hmeas0 : volume {z : AddCircle (1 : ℝ) |
      (chainSet β L).indicator (chainEnv β L j) z ≠ 0} = 0 := by
    rw [← ae_iff]
    exact h0
  have hle := measure_mono
    (μ := (volume : Measure (AddCircle (1 : ℝ)))) hsub
  rw [hmeas0] at hle
  exact absurd (le_antisymm hle bot_le) (ne_of_gt hvol)

/-- The position-0 slice of the full-capacity (long) chains has positive
measure: the base interval `(0, longThreshold)` projects into it. -/
theorem volume_chainSet_capacity_pos (β : ℝ) (hβ : 0 < β) :
    0 < volume {z : AddCircle (1 : ℝ) |
      z ∈ chainSet β (capacity 1 β) ∧ chainPos β (rep z) = 0} := by
  set d := min (longThreshold β) (1 / 2) with hd
  have hdpos : 0 < d := lt_min (longThreshold_pos β hβ) (by norm_num)
  have hd2 : d ≤ 1 / 2 := min_le_right _ _
  have hdt : d ≤ longThreshold β := min_le_left _ _
  have htβ : longThreshold β ≤ β := min_le_left _ _
  have hsub : Set.Ioo (0 : ℝ) d
      ⊆ (QuotientAddGroup.mk ⁻¹' {z : AddCircle (1 : ℝ) |
          z ∈ chainSet β (capacity 1 β) ∧ chainPos β (rep z) = 0})
        ∩ Set.Ioc (0 : ℝ) (0 + 1) := by
    intro y hy
    have hrep : rep ((y : ℝ) : AddCircle (1 : ℝ)) = y :=
      rep_coe y hy.1.le (by linarith [hy.2])
    constructor
    · show ((y : ℝ) : AddCircle (1 : ℝ)) ∈ {z : AddCircle (1 : ℝ) | _ ∧ _}
      refine ⟨?_, ?_⟩
      · exact mem_longSet_of_rep_lt β hβ _
          (by rw [hrep]; exact lt_of_lt_of_le hy.2 hdt)
      · rw [hrep]
        unfold chainPos
        refine Nat.floor_eq_zero.mpr ?_
        rw [div_lt_one hβ]
        calc y < d := hy.2
          _ ≤ β := le_trans hdt htβ
    · exact Set.mem_Ioc.mpr ⟨hy.1, by linarith [hy.2]⟩
  have hms : MeasurableSet {z : AddCircle (1 : ℝ) |
      z ∈ chainSet β (capacity 1 β) ∧ chainPos β (rep z) = 0} :=
    (measurableSet_chainSet β _).inter
      (((measurable_chainPos β).comp measurable_rep)
        (measurableSet_singleton 0))
  have hproj := AddCircle.add_projection_respects_measure (T := (1 : ℝ)) 0 hms
  rw [hproj]
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioo]
  simp only [sub_zero]
  exact ENNReal.ofReal_pos.mpr hdpos

/-- The position-0 slice of the short chains has positive measure whenever
short chains occur (`1 < mβ`, i.e. `frac(1/β) ≠ 0`): the base interval
`(1 − (m−1)β, β)` projects into it. -/
theorem volume_chainSet_short_pos (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hshort : 1 < (capacity 1 β : ℝ) * β) :
    0 < volume {z : AddCircle (1 : ℝ) |
      z ∈ chainSet β (capacity 1 β - 1) ∧ chainPos β (rep z) = 0} := by
  set m := capacity 1 β with hm
  have hmul : ((m : ℝ) - 1) * β < 1 := capacity_sub_one_mul_lt β hβ
  have hm2 : 2 ≤ m := by
    by_contra hcon
    have hm1 : m ≤ 1 := by omega
    have : (m : ℝ) * β ≤ 1 := by
      calc (m : ℝ) * β ≤ 1 * β := by
            apply mul_le_mul_of_nonneg_right _ hβ.le
            exact_mod_cast hm1
        _ ≤ 1 := by linarith
    linarith
  have hlo : 0 < 1 - ((m : ℝ) - 1) * β := by linarith
  have hlt : 1 - ((m : ℝ) - 1) * β < β := by nlinarith
  have hsub : Set.Ioo (1 - ((m : ℝ) - 1) * β) β
      ⊆ (QuotientAddGroup.mk ⁻¹' {z : AddCircle (1 : ℝ) |
          z ∈ chainSet β (m - 1) ∧ chainPos β (rep z) = 0})
        ∩ Set.Ioc (0 : ℝ) (0 + 1) := by
    intro y hy
    have hy0 : 0 < y := lt_trans hlo hy.1
    have hy1 : y < 1 := lt_of_lt_of_le hy.2 hβ1
    have hrep : rep ((y : ℝ) : AddCircle (1 : ℝ)) = y := rep_coe y hy0.le hy1
    have hposy : chainPos β y = 0 :=
      Nat.floor_eq_zero.mpr ((div_lt_one hβ).mpr hy.2)
    have hbase : chainBase β y = y := by
      unfold chainBase
      rw [hposy]
      push_cast
      ring
    constructor
    · show ((y : ℝ) : AddCircle (1 : ℝ)) ∈ {z : AddCircle (1 : ℝ) | _ ∧ _}
      refine ⟨?_, ?_⟩
      · show chainLength β (chainBase β (rep _)) = m - 1
        rw [hrep, hbase]
        unfold chainLength
        have hcast1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
          push_cast [Nat.cast_sub (by omega : 1 ≤ m)]
          ring
        have hcast2 : ((m - 2 : ℕ) : ℝ) = (m : ℝ) - 2 := by
          push_cast [Nat.cast_sub hm2]
          ring
        have hup : ⌈(1 - y) / β⌉₊ ≤ m - 1 := by
          rw [Nat.ceil_le, hcast1, div_le_iff₀ hβ]
          nlinarith [hy.1]
        have hdown : m - 2 < ⌈(1 - y) / β⌉₊ := by
          rw [Nat.lt_ceil, hcast2, lt_div_iff₀ hβ]
          nlinarith [hy.2, hmul]
        omega
      · rw [hrep]
        exact hposy
    · exact Set.mem_Ioc.mpr ⟨hy0, by linarith⟩
  have hms : MeasurableSet {z : AddCircle (1 : ℝ) |
      z ∈ chainSet β (m - 1) ∧ chainPos β (rep z) = 0} :=
    (measurableSet_chainSet β _).inter
      (((measurable_chainPos β).comp measurable_rep)
        (measurableSet_singleton 0))
  have hproj := AddCircle.add_projection_respects_measure (T := (1 : ℝ)) 0 hms
  rw [hproj]
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioo]
  refine ENNReal.ofReal_pos.mpr ?_
  nlinarith

/-! ### The exact spectral set -/

/-- Every long-chain Chebyshev value is in the spectrum. -/
theorem chebRung_mem_spectrum_long (β : ℝ) (hβ : 0 < β)
    (j : Fin (capacity 1 β)) :
    2 * Real.cos (pathAngle (capacity 1 β) j) ∈ spectrum ℝ (pathLawW β) :=
  mem_spectrum_of_eigenvector
    (chainEigenFun_ne_zero β _ j (volume_chainSet_capacity_pos β hβ))
    (pathLawW_chainEigenFun β hβ _ j)

/-- Every short-chain Chebyshev value is in the spectrum, whenever short
chains occur. -/
theorem chebRung_mem_spectrum_short (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hshort : 1 < (capacity 1 β : ℝ) * β) (j : Fin (capacity 1 β - 1)) :
    2 * Real.cos (pathAngle (capacity 1 β - 1) j)
      ∈ spectrum ℝ (pathLawW β) :=
  mem_spectrum_of_eigenvector
    (chainEigenFun_ne_zero β _ j (volume_chainSet_short_pos β hβ hβ1 hshort))
    (pathLawW_chainEigenFun β hβ _ j)

/-- Roots of the path-graph annihilating polynomial are exactly the Chebyshev
values. -/
lemma eval_pathCharPoly_eq_zero_iff (L : ℕ) (μ : ℝ) :
    (pathCharPoly L).eval μ = 0
      ↔ ∃ j : Fin L, μ = 2 * Real.cos (pathAngle L j) := by
  rw [pathCharPoly, eval_prod]
  rw [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨j, -, hj⟩
    rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hj
    exact ⟨j, hj⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, Finset.mem_univ j,
      by rw [eval_sub, eval_X, eval_C, sub_eq_zero]; exact hj⟩

/-- **The exact spectral set of the masked rotation** (paper Theorem 1.1(a)):
whenever both chain lengths occur (`1 < mβ`, i.e. `frac(1/β) ≠ 0`),

  `spec(W) = {2cos(jπ/(m+1))}_{j=1..m} ∪ {2cos(jπ/m)}_{j=1..m−1}`,

the union of the path-graph spectra of `P_m` and `P_{m−1}` with
`m = ⌈1/β⌉`. -/
theorem spectrum_pathLawW (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hshort : 1 < (capacity 1 β : ℝ) * β) :
    spectrum ℝ (pathLawW β)
      = (Set.range fun j : Fin (capacity 1 β) =>
          2 * Real.cos (pathAngle (capacity 1 β) j))
        ∪ (Set.range fun j : Fin (capacity 1 β - 1) =>
            2 * Real.cos (pathAngle (capacity 1 β - 1) j)) := by
  apply Set.eq_of_subset_of_subset
  · intro μ hμ
    have h := spectrum_pathLawW_subset β hβ hμ
    rw [Set.mem_ofPred_eq, chainPoly, eval_mul, mul_eq_zero] at h
    rcases h with h | h
    · obtain ⟨j, hj⟩ := (eval_pathCharPoly_eq_zero_iff _ _).mp h
      exact Or.inl ⟨j, hj.symm⟩
    · obtain ⟨j, hj⟩ := (eval_pathCharPoly_eq_zero_iff _ _).mp h
      exact Or.inr ⟨j, hj.symm⟩
  · intro μ hμ
    rcases hμ with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact chebRung_mem_spectrum_long β hβ j
    · exact chebRung_mem_spectrum_short β hβ hβ1 hshort j
/-- **The degenerate spectral set.** When `1/β ∈ ℤ` (all chains long, no
short family), the spectrum is exactly the Chebyshev family of `P_m`. -/
theorem spectrum_pathLawW_deg (β : ℝ) (hβ : 0 < β)
    (hdeg : (capacity 1 β : ℝ) * β = 1) :
    spectrum ℝ (pathLawW β)
      = Set.range fun j : Fin (capacity 1 β) =>
          2 * Real.cos (pathAngle (capacity 1 β) j) := by
  apply Set.eq_of_subset_of_subset
  · intro μ hμ
    have h := spectrum_subset_roots_of_aeval_eq_zero
      (aeval_pathCharPoly_pathLawW_deg β hβ hdeg) hμ
    obtain ⟨j, hj⟩ := (eval_pathCharPoly_eq_zero_iff _ _).mp h
    exact ⟨j, hj.symm⟩
  · rintro μ ⟨j, rfl⟩
    exact chebRung_mem_spectrum_long β hβ j

end Cvs.PathLaw
