import Mathlib
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.EvenLevelIndexLemma
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.LandauHalfEvenSpectrum
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.SlepianEvenOrdering
import Cvs.Prolate.SturmPolyGaussComparison

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The converse level count: no `k + 1` zeros leave at most `k + 1` even levels below

Each odd level below `Λ` leaves a zero of `regSol Q Λ` in `(0, 1)`, and an odd level separates
any two consecutive even levels, so `#even ≤ #odd + 1 ≤ #zeros + 1`. At `Q = c²ξ²` every even level
of index `k + 1` or more lies at or above `Λ`, every level of index `≤ 3` exists for `c ≥ 4π + 1`,
and the level of index one lies at or above `3γ² + 2`.
-/

noncomputable section

open Real Set Filter Topology Cvs.Prolate.RegularSolutionEdge Cvs.Prolate.EdgeCentreSign Cvs.Prolate.EvenLevelIndexLemma Cvs.Prolate.EvenRungsByIndex

namespace Cvs.Prolate.ConverseLevelCount

/-! ### Counting below a level -/

/-- The largest element of a finite nonempty `P ∩ Iio χ` has one fewer element of `P` below it. -/
theorem exists_max_Iio {P : Set ℝ} {χ : ℝ} (hfin : (P ∩ Iio χ).Finite)
    (hne : (P ∩ Iio χ).Nonempty) :
    ∃ m ∈ P, m < χ ∧ (∀ z ∈ P, z < χ → z ≤ m) ∧ (P ∩ Iio m).ncard + 1 = (P ∩ Iio χ).ncard := by
  obtain ⟨m, hmS, hmax⟩ := Set.exists_max_image (P ∩ Iio χ) id hfin hne
  have hS : P ∩ Iio m = (P ∩ Iio χ) \ {m} := by
    ext z
    constructor
    · rintro ⟨hz, hzm⟩
      exact ⟨⟨hz, mem_Iio.mpr (lt_trans (mem_Iio.mp hzm) (mem_Iio.mp hmS.2))⟩,
        ne_of_lt (mem_Iio.mp hzm)⟩
    · rintro ⟨⟨hz, hzχ⟩, hzm⟩
      exact ⟨hz, lt_of_le_of_ne (hmax z ⟨hz, hzχ⟩) hzm⟩
  refine ⟨m, hmS.1, hmS.2, fun z hz hzχ => hmax z ⟨hz, hzχ⟩, ?_⟩
  rw [hS, Set.ncard_sdiff_singleton_add_one hmS hfin]

/-! ### Zeros persist and gain one at each odd level -/

/-- Past zeros `a 0 < … < a (n − 1)` in `(−1, 1)` of `regSol Q χ`, a smaller `Q' − χ'` gives zeros
`a i < w i` of `regSol Q' χ'`, each before the next `a` and before `1`. -/
theorem exists_zeros_of_lt {Q Q' : C(ℝ, ℝ)} {χ χ' : ℝ} {n : ℕ} {a : Fin n → ℝ}
    (ha : StrictMono a) (ha1 : ∀ i, -1 < a i ∧ a i < 1) (ha0 : ∀ i, regSol Q χ (a i) = 0)
    (hlt : ∀ i, ∀ t ∈ Ioo (a i) 1, Q' t - χ' < Q t - χ) :
    ∃ w : Fin n → ℝ, StrictMono w ∧ (∀ i, a i < w i ∧ w i < 1) ∧ ∀ i, regSol Q' χ' (w i) = 0 := by
  set nx : Fin n → ℝ := fun i => if hi : i.val + 1 < n then a ⟨i.val + 1, hi⟩ else 1 with hnx
  have hnx1 : ∀ i, nx i ≤ 1 := fun i => by
    simp only [hnx]
    split_ifs
    · exact (ha1 _).2.le
    · exact le_rfl
  have key : ∀ i, ∃ t ∈ Ioo (a i) (nx i), regSol Q' χ' t = 0 := by
    intro i
    by_cases hi : i.val + 1 < n
    · simp only [hnx, dif_pos hi]
      have hlt' : a i < a ⟨i.val + 1, hi⟩ := ha (Fin.mk_lt_mk.mpr (Nat.lt_succ_self _))
      exact Cvs.Prolate.SturmPolyGaussComparison.exists_zero_Ioo_of_lt (ha1 i).1 hlt' (ha1 _).2
        (fun t ht => hlt i t ⟨ht.1, ht.2.trans (ha1 _).2⟩) (ha0 i) (ha0 _)
    · simp only [hnx, dif_neg hi]
      exact Cvs.Prolate.SturmPolyGaussComparison.exists_zero_Ioo_one (ha1 i).1 (ha1 i).2 (hlt i) (ha0 i)
  choose w hw hw0 using key
  refine ⟨w, fun i j hij => ?_, fun i => ⟨(hw i).1, (hw i).2.trans_le (hnx1 i)⟩, hw0⟩
  have hi : i.val + 1 < n := lt_of_le_of_lt (Nat.succ_le_of_lt hij) j.isLt
  have h1 : nx i = a ⟨i.val + 1, hi⟩ := by simp only [hnx, dif_pos hi]
  have h2 : a ⟨i.val + 1, hi⟩ ≤ a j := ha.monotone (Fin.mk_le_mk.mpr (Nat.succ_le_of_lt hij))
  linarith [(hw i).2, (hw j).1]

/-- `k` zeros in `(0, 1)` and a zero at the centre give `k + 1` zeros in `(0, 1)` once `Q − χ`
decreases on `(0, 1)`. -/
theorem hasZeros_succ_of_lt {Q Q' : C(ℝ, ℝ)} {χ χ' : ℝ} {k : ℕ} (h0 : regSol Q χ 0 = 0)
    (h : HasZeros Q χ k) (hlt : ∀ t ∈ Ioo (0 : ℝ) 1, Q' t - χ' < Q t - χ) :
    HasZeros Q' χ' (k + 1) := by
  obtain ⟨w, hw, hw01, hw0⟩ := h
  set a : Fin (k + 1) → ℝ := Fin.cons 0 w with hadef
  have ha : StrictMono a := Fin.strictMono_cons.2 ⟨fun j => (hw01 j).1, hw⟩
  have ha00 : a 0 = 0 := by simp [hadef]
  have hnn : ∀ i, 0 ≤ a i := fun i => ha00 ▸ ha.monotone (Fin.zero_le i)
  have ha1 : ∀ i, -1 < a i ∧ a i < 1 := by
    refine Fin.cases ?_ (fun j => ?_)
    · simp only [hadef, Fin.cons_zero]; norm_num
    · simp only [hadef, Fin.cons_succ]; exact ⟨by linarith [(hw01 j).1], (hw01 j).2⟩
  have ha0 : ∀ i, regSol Q χ (a i) = 0 := by
    refine Fin.cases ?_ (fun j => ?_)
    · simpa [hadef] using h0
    · simpa [hadef] using hw0 j
  obtain ⟨w', hw', hw'I, hw'0⟩ := exists_zeros_of_lt ha ha1 ha0
    (fun i t ht => hlt t ⟨lt_of_le_of_lt (hnn i) ht.1, ht.2⟩)
  exact ⟨w', hw', fun i => ⟨lt_of_le_of_lt (hnn i) (hw'I i).1, (hw'I i).2⟩, hw'0⟩

/-- Fewer zeros: `k` zeros in `(0, 1)` give any `j ≤ k`. -/
theorem hasZeros_of_le {Q : C(ℝ, ℝ)} {χ : ℝ} {j k : ℕ} (h : HasZeros Q χ k) (hjk : j ≤ k) :
    HasZeros Q χ j := by
  obtain ⟨w, hw, hw01, hw0⟩ := h
  exact ⟨w ∘ Fin.castLE hjk, hw.comp (Fin.strictMono_castLE hjk), fun i => hw01 _,
    fun i => hw0 _⟩

/-- **Each odd level below `χ` leaves a zero**: `regSol Q χ` has as many zeros in `(0, 1)` as there
are odd levels below `χ`. -/
theorem hasZeros_ncard_oddSpec (Q : C(ℝ, ℝ)) (χ : ℝ) :
    HasZeros Q χ (oddSpec Q ∩ Iio χ).ncard := by
  suffices H : ∀ n : ℕ, ∀ χ : ℝ, (oddSpec Q ∩ Iio χ).ncard = n → HasZeros Q χ n from H _ χ rfl
  intro n
  induction n with
  | zero => intro χ _; exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    intro χ hn
    have hfin := finite_oddSpec_Iio Q χ
    have hne : (oddSpec Q ∩ Iio χ).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
    obtain ⟨m, hm, hmχ, -, hcard⟩ := exists_max_Iio hfin hne
    exact hasZeros_succ_of_lt hm (ih m (by omega)) (fun t _ => by linarith)

/-! ### An odd level separates consecutive even levels -/

/-- An even level with `n` even levels below it has at least `n` odd levels below it. -/
theorem le_ncard_odd_of_even (Q : C(ℝ, ℝ)) : ∀ n : ℕ, ∀ e ∈ evenSpec Q,
    (evenSpec Q ∩ Iio e).ncard = n → n ≤ (oddSpec Q ∩ Iio e).ncard := by
  intro n
  induction n with
  | zero => intro e _ _; exact Nat.zero_le _
  | succ n ih =>
    intro e he hn
    have hne : (evenSpec Q ∩ Iio e).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
    obtain ⟨m, hm, hme, hmax, hcard⟩ := exists_max_Iio (finite_evenSpec_Iio Q e) hne
    have hih := ih m hm (by omega)
    have hcons : ∀ t ∈ Ioo m e, regU Q t 0 ≠ 0 := fun t ht h0 => by
      have := hmax t h0 ht.2
      linarith [ht.1]
    have halt := Cvs.Prolate.SlepianEvenOrdering.centre_alternates Q hme hm he hcons
    obtain ⟨o, ho, ho0⟩ := exists_zero_of_mul_neg hme.le
      (continuous_regSol_level Q 0).continuousOn halt
    have hsub : insert o (oddSpec Q ∩ Iio m) ⊆ oddSpec Q ∩ Iio e := by
      intro z hz
      rcases hz with rfl | hz
      · exact ⟨ho0, ho.2⟩
      · exact ⟨hz.1, mem_Iio.mpr (lt_trans (mem_Iio.mp hz.2) hme)⟩
    have hnot : o ∉ oddSpec Q ∩ Iio m := fun h => absurd h.2 (not_lt.mpr ho.1.le)
    have := Set.ncard_le_ncard hsub (finite_oddSpec_Iio Q e)
    rw [Set.ncard_insert_of_notMem hnot (finite_oddSpec_Iio Q m)] at this
    omega

/-- **Even levels exceed odd ones by at most one** below any level. -/
theorem ncard_even_le_odd_add_one (Q : C(ℝ, ℝ)) (χ : ℝ) :
    (evenSpec Q ∩ Iio χ).ncard ≤ (oddSpec Q ∩ Iio χ).ncard + 1 := by
  rcases (evenSpec Q ∩ Iio χ).eq_empty_or_nonempty with h | hne
  · rw [h, Set.ncard_empty]; exact Nat.zero_le _
  obtain ⟨m, hm, hmχ, -, hcard⟩ := exists_max_Iio (finite_evenSpec_Iio Q χ) hne
  have h1 := le_ncard_odd_of_even Q _ m hm rfl
  have hsub : oddSpec Q ∩ Iio m ⊆ oddSpec Q ∩ Iio χ :=
    fun z hz => ⟨hz.1, mem_Iio.mpr (lt_trans (mem_Iio.mp hz.2) hmχ)⟩
  have h2 := Set.ncard_le_ncard hsub (finite_oddSpec_Iio Q χ)
  omega

/-! ### The converse count -/

/-- **The converse level count**: if `regSol Q Λ` has no `k + 1` zeros in `(0, 1)`, at most `k + 1`
even levels lie below `Λ`. -/
theorem ncard_evenSpec_le {Q : C(ℝ, ℝ)} {Λ : ℝ} {k : ℕ} (h : ¬HasZeros Q Λ (k + 1)) :
    (evenSpec Q ∩ Iio Λ).ncard ≤ k + 1 := by
  have hodd : (oddSpec Q ∩ Iio Λ).ncard ≤ k := by
    by_contra hlt
    exact h (hasZeros_of_le (hasZeros_ncard_oddSpec Q Λ) (by omega))
  have := ncard_even_le_odd_add_one Q Λ
  omega

/-- **Levels above a zero-free threshold**: if `regSol (sqC c) Λ` has no `k + 1` zeros in `(0, 1)`,
every even level of index at least `k + 1` lies at or above `Λ`. -/
theorem le_of_not_hasZeros {c Λ χ : ℝ} {j k : ℕ} (h : ¬HasZeros (sqC c) Λ (k + 1))
    (hχ : IsLevelIdx c j χ) (hj : k + 1 ≤ j) : Λ ≤ χ :=
  Cvs.Prolate.LandauHalfEvenSpectrum.le_of_ncard_le hχ.1 ((ncard_evenSpec_le h).trans (hχ.2 ▸ hj))

/-! ### Levels at real `c` -/

/-- **Levels by index exist below `c² − σ`** when `(k + 1)π ≤ c − σ/c − (σ/4c) log(2c²/σ)`, for
`1 < c` and `0 < σ ≤ c`. -/
theorem exists_isLevelIdx_of_phase {c σ : ℝ} {k : ℕ} (hc : 1 < c) (hσ : 0 < σ) (hσc : σ ≤ c)
    (hk : ((k : ℝ) + 1) * π ≤ c - σ / c - σ / (4 * c) * Real.log (2 * c ^ 2 / σ)) :
    ∃ χ < c ^ 2 - σ, IsLevelIdx c k χ :=
  exists_isLevelIdx_of_lt_ncard (Nat.lt_of_succ_le (le_ncard_of_phase hc hσ hσc
    (by push_cast; exact hk)))

/-- **Levels by index exist** below `c² − 1` once `(k + 1)π + 1 ≤ c`. -/
theorem exists_isLevelIdx {c : ℝ} {k : ℕ} (hk : ((k : ℝ) + 1) * π + 1 ≤ c) :
    ∃ χ < c ^ 2 - 1, IsLevelIdx c k χ := by
  have hpi := Real.pi_gt_three
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hc : 4 ≤ c := by nlinarith
  have hc0 : 0 < c := by linarith
  refine exists_isLevelIdx_of_phase (by linarith) one_pos (by linarith) ?_
  have hlog : Real.log (2 * c ^ 2 / 1) ≤ 2 * c := by
    rw [div_one, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    have hc' := Real.log_le_sub_one_of_pos hc0
    push_cast
    linarith
  have h1 : 1 / (4 * c) * Real.log (2 * c ^ 2 / 1) ≤ 1 / 2 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    linarith
  have h2 : 1 / c ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hc0 (by norm_num)]
    linarith
  linarith

/-- **The levels of index `0` to `3` exist** for `4π + 1 ≤ c`. -/
theorem exists_isLevelIdx_of_le_three {c : ℝ} (hc : 4 * π + 1 ≤ c) {k : ℕ} (hk : k ≤ 3) :
    ∃ χ, IsLevelIdx c k χ := by
  have hk' : ((k : ℝ) + 1) * π + 1 ≤ c := by
    have : (k : ℝ) ≤ 3 := by exact_mod_cast hk
    nlinarith [Real.pi_pos]
  obtain ⟨χ, -, h⟩ := exists_isLevelIdx hk'
  exact ⟨χ, h⟩

/-- **Every even level of index at least one lies at or above `3γ² + 2`**, `γ² = gOne c`. -/
theorem le_of_isLevelIdx_one_le {c χ : ℝ} {j : ℕ} (hc : c ≠ 0) (hχ : IsLevelIdx c j χ)
    (hj : 1 ≤ j) : 3 * Cvs.Prolate.SturmPolyGaussComparison.gOne c + 2 ≤ χ :=
  le_of_not_hasZeros (k := 0) (Cvs.Prolate.SturmPolyGaussComparison.not_hasZeros_one hc le_rfl) hχ hj

end Cvs.Prolate.ConverseLevelCount
