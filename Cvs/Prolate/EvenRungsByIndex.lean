import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.AngularBesselInequality
import Cvs.Prolate.AngularEdgeValueNonzero
import Cvs.Prolate.CosineTransformEigenRelation
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.EvenSpectrumGroundLevel
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.RungMirrorIdentity
import Cvs.Prolate.SlepianEvenOrdering

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The even rungs by index

The level of even index `k` is the even level of `c²s²` with exactly `k` even levels below it. Each such level
carries an `L²`-normalised even `C²` eigenfunction `rung c k` of the finite cosine transform, with eigenvalue
`muR c k = ψ(1)/rung(1)` and concentration `lamR c k = (muR c k √(c/2π))²`, antitone in `k`.
-/

noncomputable section

open Real Set MeasureTheory Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.RegularSolutionEdge Cvs.Prolate.EdgeCentreSign Cvs.Prolate.SlepianEvenOrdering Cvs.Prolate.EvenSpectrumGroundLevel

namespace Cvs.Prolate.EvenRungsByIndex

/-! ### Levels by index -/

/-- `χ` is the even level of index `k`: an even level with exactly `k` even levels below it. -/
def IsLevelIdx (c : ℝ) (k : ℕ) (χ : ℝ) : Prop :=
  χ ∈ evenSpec (sqC c) ∧ (evenSpec (sqC c) ∩ Iio χ).ncard = k

/-- **The count is strictly monotone across an even level.** -/
theorem ncard_lt_of_lt {c χ χ' : ℝ} (hχ : χ ∈ evenSpec (sqC c)) (h : χ < χ') :
    (evenSpec (sqC c) ∩ Iio χ).ncard < (evenSpec (sqC c) ∩ Iio χ').ncard := by
  refine Set.ncard_lt_ncard ⟨fun z hz => ⟨hz.1, lt_trans hz.2 h⟩, fun hsub => ?_⟩
    (finite_evenSpec_Iio _ χ')
  exact lt_irrefl χ (hsub ⟨hχ, h⟩).2

/-- **Levels are ordered by index.** -/
theorem IsLevelIdx.le {c χ χ' : ℝ} {k k' : ℕ} (h : IsLevelIdx c k χ) (h' : IsLevelIdx c k' χ')
    (hk : k ≤ k') : χ ≤ χ' := by
  by_contra hlt
  push Not at hlt
  have := ncard_lt_of_lt h'.1 hlt
  rw [h.2, h'.2] at this
  omega

/-- **The level of a given index is unique.** -/
theorem IsLevelIdx.unique {c χ χ' : ℝ} {k : ℕ} (h : IsLevelIdx c k χ) (h' : IsLevelIdx c k χ') : χ = χ' :=
  le_antisymm (h.le h' le_rfl) (h'.le h le_rfl)

/-- Levels of distinct indices are strictly ordered. -/
theorem IsLevelIdx.lt {c χ χ' : ℝ} {k k' : ℕ} (h : IsLevelIdx c k χ) (h' : IsLevelIdx c k' χ')
    (hk : k < k') : χ < χ' := by
  refine lt_of_le_of_ne (h.le h' hk.le) fun he => ?_
  subst he
  have := h.2.symm.trans h'.2
  omega

/-- **Every index below the count at `χ` has a level below `χ`.** -/
theorem exists_isLevelIdx_of_lt_ncard {c χ : ℝ} {k : ℕ} (hk : k < (evenSpec (sqC c) ∩ Iio χ).ncard) :
    ∃ χ' < χ, IsLevelIdx c k χ' := by
  suffices H : ∀ n : ℕ, ∀ χ : ℝ, (evenSpec (sqC c) ∩ Iio χ).ncard = n → ∀ k < n, ∃ χ' < χ, IsLevelIdx c k χ' from
    H _ χ rfl k hk
  intro n
  induction n with
  | zero => intro χ _ k hk; omega
  | succ n ih =>
    intro χ hn k hk
    set T := evenSpec (sqC c) ∩ Iio χ with hT
    have hfin : T.Finite := finite_evenSpec_Iio _ χ
    have hne : T.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
    obtain ⟨m, hmT, hmax⟩ := Set.exists_max_image T id hfin hne
    have hset : evenSpec (sqC c) ∩ Iio m = T \ {m} := by
      ext z
      simp only [hT, mem_inter_iff, mem_Iio, mem_sdiff, mem_singleton_iff]
      refine ⟨fun hz => ⟨⟨hz.1, lt_trans hz.2 hmT.2⟩, hz.2.ne⟩, fun hz => ⟨hz.1.1, ?_⟩⟩
      exact lt_of_le_of_ne (hmax z hz.1) hz.2
    have hcount : (evenSpec (sqC c) ∩ Iio m).ncard = n := by
      rw [hset, Set.ncard_sdiff_singleton_of_mem hmT, hn]
      omega
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | heq
    · obtain ⟨χ', hχ', hidx⟩ := ih m hcount k hlt
      exact ⟨χ', lt_trans hχ' hmT.2, hidx⟩
    · exact ⟨m, hmT.2, hmT.1, heq ▸ hcount⟩

/-- **Every smaller index has a level.** -/
theorem exists_isLevelIdx_of_le {c χ : ℝ} {k k' : ℕ} (h : IsLevelIdx c k χ) (hk : k' ≤ k) :
    ∃ χ', IsLevelIdx c k' χ' := by
  rcases eq_or_lt_of_le hk with he | hlt
  · exact ⟨χ, he ▸ h⟩
  · obtain ⟨χ', -, h'⟩ := exists_isLevelIdx_of_lt_ncard (c := c) (χ := χ) (k := k') (by rw [h.2]; exact hlt)
    exact ⟨χ', h'⟩

/-- **The ground level has index `0`.** -/
theorem isLevelIdx_zero (c : ℝ) : IsLevelIdx c 0 (groundLevel c) :=
  ⟨groundLevel_mem c, ncard_groundLevel c⟩

/-- The level of index `0` exists. -/
theorem exists_isLevelIdx_zero (c : ℝ) : ∃ χ, IsLevelIdx c 0 χ :=
  ⟨groundLevel c, isLevelIdx_zero c⟩

open Classical in
/-- The level of index `k` (`0` when there is none). -/
def lev (c : ℝ) (k : ℕ) : ℝ := if h : ∃ χ, IsLevelIdx c k χ then h.choose else 0

/-- `lev c k` is the level of index `k` when that level exists. -/
theorem lev_spec {c : ℝ} {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) : IsLevelIdx c k (lev c k) := by
  unfold lev
  rw [dif_pos h]
  exact h.choose_spec

/-- `lev c k` is the level of index `k`. -/
theorem lev_eq {c χ : ℝ} {k : ℕ} (h : IsLevelIdx c k χ) : lev c k = χ :=
  (lev_spec ⟨χ, h⟩).unique h

/-- The level of index `0` is the ground level. -/
theorem lev_zero (c : ℝ) : lev c 0 = groundLevel c :=
  lev_eq (isLevelIdx_zero c)

/-- **The levels by index are monotone.** -/
theorem lev_le {c : ℝ} {k k' : ℕ} (h : ∃ χ, IsLevelIdx c k' χ) (hk : k ≤ k') : lev c k ≤ lev c k' := by
  obtain ⟨χ', h'⟩ := h
  exact (lev_spec (exists_isLevelIdx_of_le h' hk)).le (lev_spec ⟨χ', h'⟩) hk

/-- **The levels by index are strictly monotone.** -/
theorem lev_lt {c : ℝ} {k k' : ℕ} (h : ∃ χ, IsLevelIdx c k' χ) (hk : k < k') : lev c k < lev c k' := by
  obtain ⟨χ', h'⟩ := h
  exact (lev_spec (exists_isLevelIdx_of_le h' hk.le)).lt (lev_spec ⟨χ', h'⟩) hk

/-! ### The normalised rungs -/

open Classical in
/-- The regular even eigenfunction at an even level, with its two derivatives (`0` off the even spectrum). -/
def rawRung (c χ : ℝ) : (ℝ → ℝ) × (ℝ → ℝ) × (ℝ → ℝ) :=
  if hχ : χ ∈ evenSpec (sqC c) then
    ((exists_regular_even c χ hχ).choose, (exists_regular_even c χ hχ).choose_spec.choose,
      (exists_regular_even c χ hχ).choose_spec.choose_spec.choose)
  else 0

/-- The defining properties of `rawRung` at an even level. -/
theorem rawRung_spec {c χ : ℝ} (hχ : χ ∈ evenSpec (sqC c)) :
    (∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (rawRung c χ).1 ((rawRung c χ).2.1 s) s) ∧
      (∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (rawRung c χ).2.1 ((rawRung c χ).2.2 s) s) ∧
      ContinuousOn (rawRung c χ).2.2 (uIcc (-1) 1) ∧
      (∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * (rawRung c χ).2.2 s - 2 * s * (rawRung c χ).2.1 s -
        c ^ 2 * s ^ 2 * (rawRung c χ).1 s + χ * (rawRung c χ).1 s = 0) ∧
      (∀ s ∈ Icc (-1 : ℝ) 1, (rawRung c χ).1 (-s) = (rawRung c χ).1 s) ∧
      ∃ s ∈ Icc (-1 : ℝ) 1, (rawRung c χ).1 s ≠ 0 := by
  unfold rawRung
  rw [dif_pos hχ]
  exact (exists_regular_even c χ hχ).choose_spec.choose_spec.choose_spec

/-- **A continuous function nonzero somewhere on `[−1, 1]` has `∫_{−1}^{1} g² > 0`.** -/
theorem integral_sq_pos {g : ℝ → ℝ} (hgc : ContinuousOn g (Icc (-1 : ℝ) 1))
    (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0) : 0 < ∫ s in (-1 : ℝ)..1, g s ^ 2 := by
  obtain ⟨s₀, hs₀, hne⟩ := hg0
  exact intervalIntegral.integral_pos (by norm_num) (hgc.pow 2) (fun x _ => sq_nonneg _)
    ⟨s₀, hs₀, by positivity⟩

/-- The `L²` norm on `[−1, 1]` of the raw rung of index `k`. -/
def rungNorm (c : ℝ) (k : ℕ) : ℝ := √(∫ s in (-1 : ℝ)..1, (rawRung c (lev c k)).1 s ^ 2)

/-- The `L²`-normalised even eigenfunction of index `k`. -/
def rung (c : ℝ) (k : ℕ) (s : ℝ) : ℝ := (rawRung c (lev c k)).1 s / rungNorm c k

/-- The derivative of `rung c k`. -/
def rung₁ (c : ℝ) (k : ℕ) (s : ℝ) : ℝ := (rawRung c (lev c k)).2.1 s / rungNorm c k

/-- The second derivative of `rung c k`. -/
def rung₂ (c : ℝ) (k : ℕ) (s : ℝ) : ℝ := (rawRung c (lev c k)).2.2 s / rungNorm c k

/-- The squared norm of the raw rung is positive, and `rungNorm` is its square root. -/
theorem rungNorm_spec {c : ℝ} {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) :
    0 < ∫ s in (-1 : ℝ)..1, (rawRung c (lev c k)).1 s ^ 2 ∧
      rungNorm c k ^ 2 = ∫ s in (-1 : ℝ)..1, (rawRung c (lev c k)).1 s ^ 2 := by
  obtain ⟨hg, -, -, -, -, hg0⟩ := rawRung_spec (lev_spec h).1
  have hI : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hgc : ContinuousOn (rawRung c (lev c k)).1 (Icc (-1 : ℝ) 1) := fun s hs =>
    (hg s (by rwa [hI])).continuousAt.continuousWithinAt
  have hpos := integral_sq_pos hgc hg0
  exact ⟨hpos, Real.sq_sqrt hpos.le⟩

/-- `rungNorm c k > 0` when the level of index `k` exists. -/
theorem rungNorm_pos {c : ℝ} {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) : 0 < rungNorm c k :=
  Real.sqrt_pos.mpr (rungNorm_spec h).1

/-- **The rung of index `k`**: `C²` on `[−1, 1]` with continuous second derivative, solving the angular equation at
`lev c k`, even, and `L²`-normalised. -/
theorem rung_spec {c : ℝ} {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) :
    (∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (rung c k) (rung₁ c k s) s) ∧
      (∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (rung₁ c k) (rung₂ c k s) s) ∧
      ContinuousOn (rung₂ c k) (uIcc (-1) 1) ∧
      (∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * rung₂ c k s - 2 * s * rung₁ c k s - c ^ 2 * s ^ 2 * rung c k s +
        lev c k * rung c k s = 0) ∧
      (∀ s ∈ Icc (-1 : ℝ) 1, rung c k (-s) = rung c k s) ∧ ∫ s in (-1 : ℝ)..1, rung c k s ^ 2 = 1 := by
  obtain ⟨hg, hg₁, hg₂c, hang, heven, -⟩ := rawRung_spec (lev_spec h).1
  obtain ⟨hpos, hsq⟩ := rungNorm_spec h
  set N := rungNorm c k with hN
  have hN0 : N ≠ 0 := (rungNorm_pos h).ne'
  refine ⟨fun s hs => (hg s hs).div_const N, fun s hs => (hg₁ s hs).div_const N, hg₂c.div_const N,
    fun s hs => ?_, fun s hs => ?_, ?_⟩
  · simp only [rung, rung₁, rung₂, ← hN]
    rw [show (1 - s ^ 2) * ((rawRung c (lev c k)).2.2 s / N) - 2 * s * ((rawRung c (lev c k)).2.1 s / N) -
        c ^ 2 * s ^ 2 * ((rawRung c (lev c k)).1 s / N) + lev c k * ((rawRung c (lev c k)).1 s / N) =
        ((1 - s ^ 2) * (rawRung c (lev c k)).2.2 s - 2 * s * (rawRung c (lev c k)).2.1 s -
        c ^ 2 * s ^ 2 * (rawRung c (lev c k)).1 s + lev c k * (rawRung c (lev c k)).1 s) / N by ring,
      hang s hs, zero_div]
  · simp only [rung, heven s hs]
  · simp only [rung, ← hN, div_pow]
    rw [intervalIntegral.integral_div, ← hsq, div_self (pow_ne_zero 2 hN0)]

/-- The rung of index `k` is nonzero somewhere on `[−1, 1]`. -/
theorem rung_ne_zero {c : ℝ} {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) : ∃ s ∈ Icc (-1 : ℝ) 1, rung c k s ≠ 0 := by
  obtain ⟨-, -, -, -, -, s₀, hs₀, hne⟩ := rawRung_spec (lev_spec h).1
  exact ⟨s₀, hs₀, div_ne_zero hne (rungNorm_pos h).ne'⟩

/-- The rung of index `k` is continuous on `[−1, 1]`. -/
theorem continuousOn_rung {c : ℝ} {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) : ContinuousOn (rung c k) (Icc (-1) 1) :=
  fun s hs => ((rung_spec h).1 s (by rwa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)])).continuousAt.continuousWithinAt

/-- The rung of index `k` is nonzero at the edge `s = 1`. -/
theorem rung_one_ne_zero {c : ℝ} {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) : rung c k 1 ≠ 0 := by
  obtain ⟨hg, hg₁, -, hang, -, -⟩ := rung_spec h
  obtain ⟨s₀, hs₀, hne⟩ := rung_ne_zero h
  exact Cvs.Prolate.AngularEdgeValueNonzero.edge_ne_zero hg hg₁ hang hs₀ hne

/-! ### The eigenvalues -/

/-- The finite cosine transform eigenvalue of the rung of index `k`. -/
def muR (c : ℝ) (k : ℕ) : ℝ := psi c (rung c k) 1 / rung c k 1

/-- **The eigen relation**: `ψ(rung c k) = muR c k · rung c k` on `[−1, 1]`. -/
theorem psi_rung {c : ℝ} {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) :
    ∀ s ∈ Icc (-1 : ℝ) 1, psi c (rung c k) s = muR c k * rung c k s := by
  obtain ⟨hg, hg₁, hg₂c, hang, -, -⟩ := rung_spec h
  obtain ⟨μ, hμ⟩ := Cvs.Prolate.CosineTransformEigenRelation.eigen_relation hg hg₁ hg₂c hang
  have h1 : muR c k = μ := by
    unfold muR
    rw [hμ 1 ⟨by norm_num, le_rfl⟩, mul_div_assoc, div_self (rung_one_ne_zero h), mul_one]
  rw [h1]
  exact hμ

/-- The concentration eigenvalue of the rung of index `k`. -/
def lamR (c : ℝ) (k : ℕ) : ℝ := (muR c k * √(c / (2 * π))) ^ 2

/-- **`λ` is antitone in the index.** -/
theorem lamR_anti {c : ℝ} {k k' : ℕ} (hc : 0 < c) (h : ∃ χ, IsLevelIdx c k' χ) (hk : k ≤ k') :
    lamR c k' ≤ lamR c k := by
  obtain ⟨χ', h'⟩ := h
  have hk' : ∃ χ, IsLevelIdx c k χ := exists_isLevelIdx_of_le h' hk
  obtain ⟨hg, hg₁, hg₂c, hang, heven, -⟩ := rung_spec hk'
  obtain ⟨hh, hh₁, hh₂c, hang', heven', -⟩ := rung_spec ⟨χ', h'⟩
  exact lam_le_of_chi_le hc hg hg₁ hg₂c hang heven (rung_ne_zero hk') hh hh₁ hh₂c hang' heven'
    (rung_ne_zero ⟨χ', h'⟩) (psi_rung hk') (psi_rung ⟨χ', h'⟩) (lev_le ⟨χ', h'⟩ hk)

/-- `λ₀ ≤ 1`. -/
theorem lamR_zero_le_one {c : ℝ} (hc : 0 < c) : lamR c 0 ≤ 1 := by
  have h0 := exists_isLevelIdx_zero c
  obtain ⟨-, -, -, -, heven, -⟩ := rung_spec h0
  have habs := Cvs.Prolate.RungMirrorIdentity.abs_tau_le_one hc (continuousOn_rung h0) heven (psi_rung h0)
    (rung_ne_zero h0)
  unfold lamR
  rw [← sq_abs]
  exact pow_le_one₀ (abs_nonneg _) habs

/-- **`λ_k < 1` past the ground**: `λ_k < λ₀ ≤ 1` for `k ≥ 1`. -/
theorem lamR_lt_one {c : ℝ} {k : ℕ} (hc : 0 < c) (h : ∃ χ, IsLevelIdx c k χ) (hk : 1 ≤ k) : lamR c k < 1 := by
  have h0 := exists_isLevelIdx_zero c
  obtain ⟨hg, hg₁, hg₂c, hang, heven, -⟩ := rung_spec h0
  obtain ⟨hh, hh₁, hh₂c, hang', heven', -⟩ := rung_spec h
  have hlt := mu_sq_lt hc hg hg₁ hg₂c hang heven (rung_ne_zero h0) hh hh₁ hh₂c hang' heven'
    (rung_ne_zero h) (psi_rung h0) (psi_rung h) (lev_lt h (by omega : 0 < k))
  have hpos : 0 < c / (2 * π) := by positivity
  have hlam : ∀ j, lamR c j = muR c j ^ 2 * (c / (2 * π)) := fun j => by
    unfold lamR
    rw [mul_pow, Real.sq_sqrt hpos.le]
  have := lamR_zero_le_one hc
  rw [hlam] at this ⊢
  nlinarith

/-- **The rungs of even index have positive eigenvalue.** -/
theorem muR_pos_of_even {c : ℝ} {k : ℕ} (hc : 0 < c) (h : ∃ χ, IsLevelIdx c k χ) (hk : Even k) :
    0 < muR c k := by
  obtain ⟨hg, hg₁, hg₂c, hang, heven, -⟩ := rung_spec h
  refine mu_pos_of_even_index hc hg hg₁ hg₂c hang heven (rung_ne_zero h) (psi_rung h) ?_
  rw [(lev_spec h).2]
  exact hk

/-- `λ₀ > 0`. -/
theorem lamR_zero_pos {c : ℝ} (hc : 0 < c) : 0 < lamR c 0 := by
  have hμ := muR_pos_of_even hc (exists_isLevelIdx_zero c) (⟨0, rfl⟩ : Even 0)
  have hs : 0 < √(c / (2 * π)) := Real.sqrt_pos.mpr (by positivity)
  unfold lamR
  positivity

/-- **The ground rung has nonzero integral**: `∫ h₀ = μ₀ h₀(0)` with `μ₀ > 0` and `h₀(0)² ≥ ½`. -/
theorem integral_rung_zero_ne {c : ℝ} (hc : 0 < c) : ∫ s in (-1 : ℝ)..1, rung c 0 s ≠ 0 := by
  have h0 := exists_isLevelIdx_zero c
  obtain ⟨hg, hg₁, -, hang, heven, hnorm⟩ := rung_spec h0
  rw [Cvs.Prolate.AngularBesselInequality.integral_eq_mu_mul (psi_rung h0)]
  have hhalf := Cvs.Prolate.AngularBesselInequality.half_le_ground_sq hg hg₁ hang heven (lev_spec h0).2 hnorm
  have hne : rung c 0 0 ≠ 0 := fun he => by rw [he] at hhalf; norm_num at hhalf
  exact mul_ne_zero (muR_pos_of_even hc h0 (⟨0, rfl⟩ : Even 0)).ne' hne

end Cvs.Prolate.EvenRungsByIndex
