import Mathlib
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RegularSolutionChiVariation
import Cvs.Prolate.RegularSolutionEdge

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The index lemma: `2x − 1` even levels lie below `c² − 4c/log c` at `c = 2πx`

Zeros of `regSol Q χ` in `(0, 1)` move right as `χ` grows and leave through `ξ = 0` only at odd levels, which
interlace the even ones; so `k` zeros give `k` even levels below `χ`. Sturm comparison at `χ = c² − σ` with
`sin Θ/√m`, `Θ = cξ − (σ/4c) log((1+ξ)/(1−ξ))`, counts `⌊Θ(1 − σ/c²)/π⌋` zeros.
-/

noncomputable section

open Real Set Filter Topology Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.VolterraResolventEdge Cvs.Prolate.RegularSolutionEdge Cvs.Prolate.RegularSolutionChiVariation Cvs.Prolate.EdgeCentreSign

namespace Cvs.Prolate.EvenLevelIndexLemma

/-! ### The odd spectrum and its interlacing with the even spectrum -/

/-- The odd spectrum of `Q`: the levels at which the regular solution vanishes at the centre. -/
def oddSpec (Q : C(ℝ, ℝ)) : Set ℝ := {χ | regSol Q χ 0 = 0}

/-- The regular solution at a fixed point is continuous in the level. -/
theorem continuous_regSol_level (Q : C(ℝ, ℝ)) (ξ : ℝ) : Continuous fun χ => regSol Q χ ξ :=
  continuous_iff_continuousAt.2 fun χ => (hasDerivAt_regSol_regDot Q χ ξ).continuousAt

/-- On the odd spectrum the centre value has nonzero `χ`-derivative. -/
theorem regDot_ne_zero_of_mem (Q : C(ℝ, ℝ)) {χ : ℝ} (hχ : χ ∈ oddSpec Q) : regDot Q χ 0 ≠ 0 := by
  intro h
  have := wronskian_neg Q χ (ξ := 0) (by norm_num) (by norm_num)
  have hχ' : regSol Q χ 0 = 0 := hχ
  rw [hχ', h] at this
  simp at this

/-- Every odd level lies at or above any level below `Q` on `[0, 1]`. -/
theorem le_of_mem_oddSpec (Q : C(ℝ, ℝ)) {m : ℝ} (hm : ∀ χ < m, ∀ s ∈ Icc (0:ℝ) 1, χ < Q s)
    {χ : ℝ} (hχ : χ ∈ oddSpec Q) : m ≤ χ := by
  by_contra hlt
  push Not at hlt
  have h1 := one_le_regSol_of_lt Q (ξ := 0) (by norm_num) zero_le_one (fun s hs => hm χ hlt s hs) 0
    ⟨le_rfl, zero_le_one⟩
  have h0 : regSol Q χ 0 = 0 := hχ
  linarith

/-- **The odd spectrum below any level is finite.** -/
theorem finite_oddSpec_Iio (Q : C(ℝ, ℝ)) (χ : ℝ) : (oddSpec Q ∩ Iio χ).Finite := by
  obtain ⟨m, hm⟩ := exists_lt_potential Q
  have hsub : oddSpec Q ∩ Iio χ ⊆ oddSpec Q ∩ Icc m χ := fun x hx =>
    ⟨hx.1, le_of_mem_oddSpec Q hm hx.1, (mem_Iio.mp hx.2).le⟩
  refine Set.Finite.subset ?_ hsub
  have hcl : IsClosed (oddSpec Q) := isClosed_eq (continuous_regSol_level Q 0) continuous_const
  refine IsCompact.finite (isCompact_Icc.inter_left hcl) ?_
  rw [isDiscrete_iff_nhdsNE]
  intro x hx
  have hev := (hasDerivAt_regSol_regDot Q x 0).eventually_ne (c := (0:ℝ)) (regDot_ne_zero_of_mem Q hx.1)
  rw [inf_principal_eq_bot]
  filter_upwards [hev] with z hz hzS
  exact hz hzS.1

/-- **Odd levels interlace even ones**: an odd level with `n` odd levels below it has at least `n + 1` even levels
below it, and `(−1)ⁿ U(0) < 0` there. -/
theorem odd_interlace (Q : C(ℝ, ℝ)) : ∀ n : ℕ, ∀ o ∈ oddSpec Q, (oddSpec Q ∩ Iio o).ncard = n →
    n + 1 ≤ (evenSpec Q ∩ Iio o).ncard ∧ (-1) ^ n * regU Q o 0 < 0 := by
  obtain ⟨m, hm⟩ := exists_lt_potential Q
  have hB : ∀ t, HasDerivAt (fun χ => regSol Q χ 0) (regDot Q t 0) t :=
    fun t => hasDerivAt_regSol_regDot Q t 0
  have hW : ∀ t, regSol Q t 0 * regUDot Q t 0 - regU Q t 0 * regDot Q t 0 < 0 :=
    fun t => wronskian_neg Q t (by norm_num) (by norm_num)
  have hUc : Continuous fun χ => regU Q χ 0 := continuous_regU_zero Q
  intro n
  induction n with
  | zero =>
    intro o ho hn
    have hemp : oddSpec Q ∩ Iio o = ∅ := (Set.ncard_eq_zero (finite_oddSpec_Iio Q o)).mp hn
    have hmo := le_of_mem_oddSpec Q hm ho
    have hlt : ∀ s ∈ Icc (0:ℝ) 1, m - 1 < Q s := fun s hs => hm (m - 1) (by linarith) s hs
    have hy0 : 0 < regSol Q (m - 1) 0 := lt_of_lt_of_le one_pos
      (one_le_regSol_of_lt Q (by norm_num) zero_le_one hlt 0 ⟨le_rfl, zero_le_one⟩)
    have hU0 : 0 < regU Q (m - 1) 0 := regU_pos_of_lt Q (by norm_num) (by norm_num) hlt
    have hpos : ∀ t ∈ Ico (m - 1) o, 0 < regSol Q t 0 := by
      intro t ht
      have := mul_pos_of_ne_zero (f := fun χ => regSol Q χ 0) (a := m - 1) (b := t)
        (continuous_regSol_level Q 0).continuousOn (fun s hs h0 => by
          have : s ∈ oddSpec Q ∩ Iio o := ⟨h0, lt_of_le_of_lt hs.2 ht.2⟩
          rw [hemp] at this
          exact this) t ⟨ht.1, le_rfl⟩
      exact (pos_iff_pos_of_mul_pos this).mp hy0
    have ho0 : regSol Q o 0 = 0 := ho
    have hD : regDot Q o 0 ≤ 0 := deriv_nonpos_of_left (hB o) (by
      filter_upwards [Ioo_mem_nhdsLT (show m - 1 < o by linarith)] with t ht
      rw [ho0]
      exact (hpos t ⟨ht.1.le, ht.2⟩).le)
    have hWo := hW o
    rw [ho0, zero_mul, zero_sub, neg_lt_zero] at hWo
    have hUo : regU Q o 0 < 0 := by
      rcases lt_or_eq_of_le hD with h | h
      · nlinarith
      · rw [h, mul_zero] at hWo
        exact absurd hWo (lt_irrefl 0)
    refine ⟨?_, by simpa using hUo⟩
    obtain ⟨e, he, he0⟩ : ∃ e ∈ Ioo (m - 1) o, regU Q e 0 = 0 :=
      intermediate_value_Ioo' (show m - 1 ≤ o by linarith) hUc.continuousOn ⟨hUo, hU0⟩
    have hne : (evenSpec Q ∩ Iio o).Nonempty := ⟨e, he0, he.2⟩
    have := (Set.ncard_pos (finite_evenSpec_Iio Q o)).mpr hne
    omega
  | succ k ih =>
    intro o ho hn
    set S := oddSpec Q ∩ Iio o with hSdef
    have hfin : S.Finite := finite_oddSpec_Iio Q o
    have hne : S.Nonempty := by rw [← Set.ncard_pos hfin]; omega
    obtain ⟨om, homS, hmax⟩ := Set.exists_max_image S id hfin hne
    have hS' : oddSpec Q ∩ Iio om = S \ {om} := by
      ext z
      constructor
      · rintro ⟨hz, hzm⟩
        exact ⟨⟨hz, mem_Iio.mpr (lt_trans (mem_Iio.mp hzm) (mem_Iio.mp homS.2))⟩,
          ne_of_lt (mem_Iio.mp hzm)⟩
      · rintro ⟨⟨hz, hzχ⟩, hzm⟩
        exact ⟨hz, lt_of_le_of_ne (hmax z ⟨hz, hzχ⟩) hzm⟩
    have hk : (oddSpec Q ∩ Iio om).ncard = k := by
      rw [hS', Set.ncard_sdiff_singleton_of_mem homS]; omega
    obtain ⟨ihc, ihs⟩ := ih om homS.1 hk
    have hom0 : regSol Q om 0 = 0 := homS.1
    have ho0 : regSol Q o 0 = 0 := ho
    have hWm := hW om
    have hWo := hW o
    rw [hom0, zero_mul, zero_sub] at hWm
    rw [ho0, zero_mul, zero_sub] at hWo
    have halt := rotation_alternates (A := fun χ => -regU Q χ 0) (B := fun χ => regSol Q χ 0)
      (B' := fun t => regDot Q t 0) (x := om) (y := o) homS.2 (fun t _ => hB t) hom0 ho0
      (fun t ht h0 => by
        have := hmax t ⟨h0, ht.2⟩
        simp only [id] at this
        linarith [ht.1]) (by simpa [neg_mul] using hWm) (by simpa [neg_mul] using hWo)
    have hprod : regU Q om 0 * regU Q o 0 < 0 := by
      have e : (-regU Q om 0) * (-regU Q o 0) = regU Q om 0 * regU Q o 0 := by ring
      simpa [e] using halt
    have hsq : ((-1 : ℝ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have hsgn : 0 < (-1) ^ k * regU Q o 0 := by
      have e : ((-1) ^ k * regU Q om 0) * ((-1) ^ k * regU Q o 0) =
          ((-1 : ℝ) ^ k) ^ 2 * (regU Q om 0 * regU Q o 0) := by ring
      rw [hsq, one_mul] at e
      nlinarith
    constructor
    · obtain ⟨e, he, he0⟩ : ∃ e ∈ Ioo om o, regU Q e 0 = 0 := by
        rcases lt_or_gt_of_ne (show regU Q om 0 ≠ 0 from fun h => by
            rw [h, zero_mul] at hprod; exact lt_irrefl 0 hprod) with h | h
        · exact intermediate_value_Ioo homS.2.le hUc.continuousOn ⟨h, by nlinarith⟩
        · exact intermediate_value_Ioo' homS.2.le hUc.continuousOn ⟨by nlinarith, h⟩
      have hsub : insert e (evenSpec Q ∩ Iio om) ⊆ evenSpec Q ∩ Iio o := by
        intro z hz
        rcases hz with rfl | hz
        · exact ⟨he0, he.2⟩
        · exact ⟨hz.1, mem_Iio.mpr (lt_trans (mem_Iio.mp hz.2) (mem_Iio.mp homS.2))⟩
      have hnot : e ∉ evenSpec Q ∩ Iio om := fun h => absurd h.2 (not_lt.mpr he.1.le)
      have := Set.ncard_le_ncard hsub (finite_evenSpec_Iio Q o)
      rw [Set.ncard_insert_of_notMem hnot (finite_evenSpec_Iio Q om)] at this
      omega
    · rw [pow_succ]
      nlinarith

/-- **At most as many odd levels as even levels lie below any level.** -/
theorem ncard_odd_le_even (Q : C(ℝ, ℝ)) (χ : ℝ) :
    (oddSpec Q ∩ Iio χ).ncard ≤ (evenSpec Q ∩ Iio χ).ncard := by
  set S := oddSpec Q ∩ Iio χ with hSdef
  have hfin : S.Finite := finite_oddSpec_Iio Q χ
  rcases S.eq_empty_or_nonempty with h | hne
  · rw [h, Set.ncard_empty]; exact Nat.zero_le _
  obtain ⟨om, homS, hmax⟩ := Set.exists_max_image S id hfin hne
  have hS' : oddSpec Q ∩ Iio om = S \ {om} := by
    ext z
    constructor
    · rintro ⟨hz, hzm⟩
      exact ⟨⟨hz, mem_Iio.mpr (lt_trans (mem_Iio.mp hzm) (mem_Iio.mp homS.2))⟩,
        ne_of_lt (mem_Iio.mp hzm)⟩
    · rintro ⟨⟨hz, hzχ⟩, hzm⟩
      exact ⟨hz, lt_of_le_of_ne (hmax z ⟨hz, hzχ⟩) hzm⟩
  have hcard : (oddSpec Q ∩ Iio om).ncard + 1 = S.ncard := by
    rw [hS', Set.ncard_sdiff_singleton_add_one homS hfin]
  have h1 := (odd_interlace Q _ om homS.1 rfl).1
  have hsub : evenSpec Q ∩ Iio om ⊆ evenSpec Q ∩ Iio χ := fun x hx => ⟨hx.1, mem_Iio.mpr (lt_trans (mem_Iio.mp hx.2) (mem_Iio.mp homS.2))⟩
  have h2 := Set.ncard_le_ncard hsub (finite_evenSpec_Iio Q χ)
  omega

/-! ### Zeros in `(0, 1)` persist, have limits, and leave through the centre -/

/-- `regSol Q χ` has `k` distinct zeros in `(0, 1)`. -/
def HasZeros (Q : C(ℝ, ℝ)) (χ : ℝ) (k : ℕ) : Prop :=
  ∃ w : Fin k → ℝ, StrictMono w ∧ (∀ i, 0 < w i ∧ w i < 1) ∧ ∀ i, regSol Q χ (w i) = 0

/-- A continuous function of opposite signs at `a ≤ b` vanishes in `(a, b)`. -/
theorem exists_zero_of_mul_neg {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (h : f a * f b < 0) : ∃ x ∈ Ioo a b, f x = 0 := by
  rcases lt_or_gt_of_ne (show f a ≠ 0 from fun h0 => by rw [h0, zero_mul] at h; exact lt_irrefl 0 h)
    with ha | ha
  · exact intermediate_value_Ioo hab hf ⟨ha, by nlinarith⟩
  · exact intermediate_value_Ioo' hab hf ⟨by nlinarith, ha⟩

/-- **Zeros persist**: `k` zeros in `(0, 1)` at `χ` give `k` zeros in `(0, 1)` at every level near `χ`. -/
theorem hasZeros_eventually {Q : C(ℝ, ℝ)} {χ : ℝ} {k : ℕ} (h : HasZeros Q χ k) :
    ∀ᶠ t in 𝓝 χ, HasZeros Q t k := by
  obtain ⟨w, hmono, hw, hz⟩ := h
  obtain ⟨δ, hδ0, hδ1, hδ2⟩ : ∃ δ : ℝ, 0 < δ ∧ (∀ i, 0 < w i - δ ∧ w i + δ < 1) ∧
      ∀ i j, i < j → w i + δ < w j - δ := by
    have h1 : ∀ i, ∀ᶠ δ in 𝓝 (0:ℝ), 0 < w i - δ ∧ w i + δ < 1 := fun i => by
      have ha : Tendsto (fun δ : ℝ => w i - δ) (𝓝 0) (𝓝 (w i - 0)) :=
        (continuous_const.sub continuous_id).continuousAt
      have hb : Tendsto (fun δ : ℝ => w i + δ) (𝓝 0) (𝓝 (w i + 0)) :=
        (continuous_const.add continuous_id).continuousAt
      rw [sub_zero] at ha
      rw [add_zero] at hb
      exact (ha.eventually (lt_mem_nhds (hw i).1)).and (hb.eventually (gt_mem_nhds (hw i).2))
    have h2 : ∀ i j : Fin k, ∀ᶠ δ in 𝓝 (0:ℝ), i < j → w i + δ < w j - δ := fun i j => by
      by_cases hij : i < j
      · have hc : Tendsto (fun δ : ℝ => (w j - δ) - (w i + δ)) (𝓝 0) (𝓝 ((w j - 0) - (w i + 0))) :=
          ((continuous_const.sub continuous_id).sub (continuous_const.add continuous_id)).continuousAt
        rw [sub_zero, add_zero] at hc
        filter_upwards [hc.eventually (lt_mem_nhds (sub_pos.2 (hmono hij)))] with δ hδ _
        linarith
      · exact Eventually.of_forall fun _ h => absurd h hij
    have hall := ((eventually_all.2 h1).and (eventually_all.2 fun i => eventually_all.2 (h2 i)))
    obtain ⟨δ, hδ, hpos⟩ := ((hall.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : Ioi (0:ℝ) ∈ 𝓝[>] 0)).exists
    exact ⟨δ, hpos, hδ.1, hδ.2⟩
  have hw1 : ∀ i, -1 < w i := fun i => by linarith [(hw i).1]
  have hV : ∀ i, regV Q χ (w i) ≠ 0 := fun i =>
    regV_ne_zero_of_regSol_eq_zero Q χ (hw1 i) (hw i).2 (hz i)
  have hd : ∀ i, HasDerivAt (regSol Q χ) (regV Q χ (w i)) (w i) := fun i => hasDerivAt_regSol Q χ (hw1 i)
  have hr : ∀ i, ∃ r ∈ Ioo (w i) (w i + δ), 0 < regSol Q χ r * regV Q χ (w i) := fun i => by
    obtain ⟨r, hr1, hr2⟩ := ((eventually_mul_deriv_pos (hd i) (hz i) (hV i)).and
      (Ioo_mem_nhdsGT (show w i < w i + δ by linarith))).exists
    exact ⟨r, hr2, hr1⟩
  have hl : ∀ i, ∃ l ∈ Ioo (w i - δ) (w i), regSol Q χ l * regV Q χ (w i) < 0 := fun i => by
    obtain ⟨l, hl1, hl2⟩ := ((eventually_mul_deriv_neg (hd i) (hz i) (hV i)).and
      (Ioo_mem_nhdsLT (show w i - δ < w i by linarith))).exists
    exact ⟨l, hl2, hl1⟩
  choose r hrI hrs using hr
  choose l hlI hls using hl
  have hev : ∀ᶠ t in 𝓝 χ, ∀ i, 0 < regSol Q t (r i) * regV Q χ (w i) ∧
      regSol Q t (l i) * regV Q χ (w i) < 0 := by
    refine eventually_all.2 fun i => ?_
    have hcr : ContinuousAt (fun t => regSol Q t (r i) * regV Q χ (w i)) χ :=
      ((continuous_regSol_level Q (r i)).mul continuous_const).continuousAt
    have hcl : ContinuousAt (fun t => regSol Q t (l i) * regV Q χ (w i)) χ :=
      ((continuous_regSol_level Q (l i)).mul continuous_const).continuousAt
    exact (hcr.eventually (lt_mem_nhds (hrs i))).and (hcl.eventually (gt_mem_nhds (hls i)))
  filter_upwards [hev] with t ht
  have hzero : ∀ i, ∃ x ∈ Ioo (l i) (r i), regSol Q t x = 0 := fun i => by
    refine exists_zero_of_mul_neg (by linarith [(hlI i).2, (hrI i).1])
      (continuousOn_regSol_Icc Q t (by linarith [(hlI i).1, (hδ1 i).1])) ?_
    by_contra hge
    push Not at hge
    have h3 := mul_neg_of_neg_of_pos (ht i).2 (ht i).1
    have e : regSol Q t (l i) * regV Q χ (w i) * (regSol Q t (r i) * regV Q χ (w i)) =
        (regSol Q t (l i) * regSol Q t (r i)) * regV Q χ (w i) ^ 2 := by ring
    rw [e] at h3
    nlinarith [mul_nonneg hge (sq_nonneg (regV Q χ (w i)))]
  choose x hxI hx0 using hzero
  refine ⟨x, fun i j hij => ?_, fun i => ⟨?_, ?_⟩, hx0⟩
  · have := hδ2 i j hij
    linarith [(hxI i).2, (hrI i).2, (hlI j).1, (hxI j).1]
  · linarith [(hxI i).1, (hlI i).1, (hδ1 i).1]
  · linarith [(hxI i).2, (hrI i).2, (hδ1 i).2]

/-- `{t : HasZeros Q t k}` is open. -/
theorem isOpen_hasZeros (Q : C(ℝ, ℝ)) (k : ℕ) : IsOpen {t | HasZeros Q t k} :=
  isOpen_iff_mem_nhds.2 fun _ ht => hasZeros_eventually ht

/-- **Limits of zeros**: if `t n → t₀` and each `regSol Q (t n)` has `k` zeros in `(0, 1)`, then `regSol Q t₀` has
`k` distinct zeros in `[0, 1)`; coalescing zeros would force a common zero of `regSol` and `regU` (Rolle). -/
theorem hasZeros_limit {Q : C(ℝ, ℝ)} {t : ℕ → ℝ} {t₀ : ℝ} {k : ℕ} (ht : Tendsto t atTop (𝓝 t₀))
    (hZ : ∀ n, HasZeros Q (t n) k) :
    ∃ w : Fin k → ℝ, StrictMono w ∧ (∀ i, 0 ≤ w i ∧ w i < 1) ∧ ∀ i, regSol Q t₀ (w i) = 0 := by
  choose W hWm hWb hWz using hZ
  have hK : IsCompact (Set.pi univ fun _ : Fin k => Icc (0:ℝ) 1) := isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨w, hw, φ, hφ, hlim⟩ := hK.tendsto_subseq (x := W)
    (fun n i _ => ⟨(hWb n i).1.le, (hWb n i).2.le⟩)
  have hlimi : ∀ i, Tendsto (fun n => W (φ n) i) atTop (𝓝 (w i)) := fun i =>
    ((continuous_apply i).continuousAt.tendsto).comp hlim
  have htφ : Tendsto (fun n => t (φ n)) atTop (𝓝 t₀) := ht.comp hφ.tendsto_atTop
  have hw01 : ∀ i, w i ∈ Icc (0:ℝ) 1 := fun i => hw i (mem_univ i)
  have hjoint : ∀ ξ, -1 < ξ → ContinuousAt (fun p : ℝ × ℝ => regSol Q p.1 p.2) (t₀, ξ) := fun ξ hξ =>
    (continuousOn_regSol_joint Q).continuousAt (prod_mem_nhds univ_mem (Ioi_mem_nhds hξ))
  have hjointU : ∀ ξ, -1 < ξ → ContinuousAt (fun p : ℝ × ℝ => regU Q p.1 p.2) (t₀, ξ) := fun ξ hξ =>
    (continuousOn_regU_joint Q).continuousAt (prod_mem_nhds univ_mem (Ioi_mem_nhds hξ))
  have hzero : ∀ i, regSol Q t₀ (w i) = 0 := fun i => by
    have h := (hjoint (w i) (by linarith [(hw01 i).1])).tendsto.comp (htφ.prodMk_nhds (hlimi i))
    have h0 : (fun n => regSol Q (t (φ n)) (W (φ n) i)) = fun _ => (0:ℝ) := funext fun n => hWz _ i
    have h' : Tendsto (fun n => regSol Q (t (φ n)) (W (φ n) i)) atTop (𝓝 (regSol Q t₀ (w i))) := h
    rw [h0] at h'
    exact (tendsto_nhds_unique h' tendsto_const_nhds)
  have hw1 : ∀ i, w i < 1 := fun i => lt_of_le_of_ne (hw01 i).2 (fun h1 => by
    have := hzero i
    rw [h1, regSol_one] at this
    exact one_ne_zero this)
  refine ⟨w, fun i j hij => ?_, fun i => ⟨(hw01 i).1, hw1 i⟩, hzero⟩
  have hle : w i ≤ w j :=
    le_of_tendsto_of_tendsto' (hlimi i) (hlimi j) (fun n => (hWm (φ n) hij).le)
  refine lt_of_le_of_ne hle (fun heq => ?_)
  have hv : ∀ n, ∃ v ∈ Ioo (W (φ n) i) (W (φ n) j), regU Q (t (φ n)) v = 0 := fun n => by
    have hlt := hWm (φ n) hij
    have hi0 := (hWb (φ n) i).1
    obtain ⟨v, hv, hv0⟩ := exists_hasDerivAt_eq_zero hlt
      (continuousOn_regSol_Icc Q _ (by linarith)) (by rw [hWz, hWz])
      (fun x hx => hasDerivAt_regSol Q _ (by linarith [hx.1]))
    exact ⟨v, hv, by rw [← pP_mul_regV Q _ (by linarith [hv.1]), hv0, mul_zero]⟩
  choose v hvI hv0 using hv
  have hj' : Tendsto (fun n => W (φ n) j) atTop (𝓝 (w i)) := heq ▸ hlimi j
  have hvlim : Tendsto v atTop (𝓝 (w i)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le (hlimi i) hj' (fun n => (hvI n).1.le) (fun n => (hvI n).2.le)
  have hU := (hjointU (w i) (by linarith [(hw01 i).1])).tendsto.comp (htφ.prodMk_nhds hvlim)
  have h0 : (fun n => regU Q (t (φ n)) (v n)) = fun _ => (0:ℝ) := funext fun n => hv0 n
  have hU' : Tendsto (fun n => regU Q (t (φ n)) (v n)) atTop (𝓝 (regU Q t₀ (w i))) := hU
  rw [h0] at hU'
  exact regU_ne_zero_of_regSol_eq_zero Q t₀ (by linarith [(hw01 i).1]) (hw1 i) (hzero i)
    (tendsto_nhds_unique hU' tendsto_const_nhds)

/-- **Each zero in `(0, 1)` costs an odd level below**: `k` zeros of `regSol Q χ` in `(0, 1)` give at least `k` odd
levels below `χ`. Lowering the level, the zeros leave through `ξ = 0` one at a time. -/
theorem le_ncard_oddSpec (Q : C(ℝ, ℝ)) : ∀ k : ℕ, ∀ χ, HasZeros Q χ k → k ≤ (oddSpec Q ∩ Iio χ).ncard := by
  obtain ⟨m, hm⟩ := exists_lt_potential Q
  have hnone : ∀ k, ∀ t < m, HasZeros Q t (k + 1) → False := by
    rintro k t ht ⟨w, -, hw, hz⟩
    have := one_le_regSol_of_lt Q (ξ := 0) (by norm_num) zero_le_one (fun s hs => hm t ht s hs) (w 0)
      ⟨(hw 0).1.le, (hw 0).2.le⟩
    rw [hz 0] at this
    linarith
  intro k
  induction k with
  | zero => intro χ _; exact Nat.zero_le _
  | succ k ih =>
    intro χ hχ
    have hmχ : m ≤ χ := by
      by_contra h
      push Not at h
      exact hnone k χ h hχ
    set B := Icc (m - 1) χ ∩ {t | ¬ HasZeros Q t (k + 1)} with hBdef
    have hBc : IsClosed B := isClosed_Icc.inter (isOpen_hasZeros Q (k + 1)).isClosed_compl
    have hBne : B.Nonempty := ⟨m - 1, ⟨le_rfl, by linarith⟩, fun h => hnone k (m - 1) (by linarith) h⟩
    have hBb : BddAbove B := ⟨χ, fun t ht => ht.1.2⟩
    set t₁ := sSup B with ht₁def
    have ht₁ : t₁ ∈ B := hBc.csSup_mem hBne hBb
    have ht₁χ : t₁ < χ := lt_of_le_of_ne ht₁.1.2 (fun h => ht₁.2 (h ▸ hχ))
    have hafter : ∀ s ∈ Ioc t₁ χ, HasZeros Q s (k + 1) := by
      intro s hs
      by_contra hns
      have : s ≤ t₁ := le_csSup hBb ⟨⟨by linarith [ht₁.1.1, hs.1], hs.2⟩, hns⟩
      linarith [hs.1]
    set ts : ℕ → ℝ := fun n => t₁ + (χ - t₁) / ((n : ℝ) + 2) with htsdef
    have hts : Tendsto ts atTop (𝓝 t₁) := by
      have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
      have h2 := (tendsto_const_nhds (x := χ - t₁)).div_atTop h1
      have h3 := (tendsto_const_nhds (x := t₁)).add h2
      rw [add_zero] at h3
      exact h3
    have htsZ : ∀ n, HasZeros Q (ts n) (k + 1) := fun n => by
      have hn : (0:ℝ) < (n : ℝ) + 2 := by positivity
      have hpos : 0 < (χ - t₁) / ((n : ℝ) + 2) := div_pos (by linarith) hn
      have hle : (χ - t₁) / ((n : ℝ) + 2) ≤ χ - t₁ :=
        div_le_self (by linarith) (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
      exact hafter _ ⟨by simp only [htsdef]; linarith, by simp only [htsdef]; linarith⟩
    obtain ⟨w, hwm, hwb, hwz⟩ := hasZeros_limit hts htsZ
    have hw0 : w 0 = 0 := by
      by_contra hne
      have hpos : 0 < w 0 := lt_of_le_of_ne (hwb 0).1 (Ne.symm hne)
      exact ht₁.2 ⟨w, hwm, fun i => ⟨lt_of_lt_of_le hpos (hwm.monotone (Fin.zero_le i)), (hwb i).2⟩, hwz⟩
    have hodd : t₁ ∈ oddSpec Q := by
      have := hwz 0
      rwa [hw0] at this
    have hZk : HasZeros Q t₁ k := ⟨fun i => w i.succ, hwm.comp Fin.strictMono_succ,
      fun i => ⟨by rw [← hw0]; exact hwm (Fin.succ_pos i), (hwb _).2⟩, fun i => hwz _⟩
    have hk := ih t₁ hZk
    have hsub : insert t₁ (oddSpec Q ∩ Iio t₁) ⊆ oddSpec Q ∩ Iio χ := by
      intro z hz
      rcases hz with rfl | hz
      · exact ⟨hodd, ht₁χ⟩
      · exact ⟨hz.1, mem_Iio.mpr (lt_trans (mem_Iio.mp hz.2) ht₁χ)⟩
    have hnot : t₁ ∉ oddSpec Q ∩ Iio t₁ := fun h => lt_irrefl _ (mem_Iio.mp h.2)
    have := Set.ncard_le_ncard hsub (finite_oddSpec_Iio Q χ)
    rw [Set.ncard_insert_of_notMem hnot (finite_oddSpec_Iio Q t₁)] at this
    omega

/-- **The Sturm count**: `k` zeros of `regSol Q χ` in `(0, 1)` give at least `k` even levels below `χ`. -/
theorem le_ncard_evenSpec {Q : C(ℝ, ℝ)} {χ : ℝ} {k : ℕ} (h : HasZeros Q χ k) :
    k ≤ (evenSpec Q ∩ Iio χ).ncard :=
  (le_ncard_oddSpec Q k χ h).trans (ncard_odd_le_even Q χ)

/-! ### Sturm comparison against an explicit solution -/

/-- **Sturm comparison** for `y' = U/pP`, `U' = −(Q − χ)y` against `z' = Z/pP`, `Z' = −Rz` on `[α, β] ⊂ (−1, 1)`:
if `z` vanishes at `α, β` and not between, and `Q − χ < R` on `(α, β)`, then `y` vanishes in `(α, β)`. -/
theorem exists_zero_of_comparison {Q R y U z Z : ℝ → ℝ} {χ α β : ℝ} (hα : -1 < α) (hαβ : α < β)
    (hβ : β < 1) (hy : ∀ ξ ∈ Icc α β, HasDerivAt y (U ξ / pP ξ) ξ)
    (hU : ∀ ξ ∈ Icc α β, HasDerivAt U (-((Q ξ - χ) * y ξ)) ξ)
    (hz : ∀ ξ ∈ Icc α β, HasDerivAt z (Z ξ / pP ξ) ξ) (hZ : ∀ ξ ∈ Icc α β, HasDerivAt Z (-(R ξ * z ξ)) ξ)
    (hzα : z α = 0) (hzβ : z β = 0) (hz0 : ∀ ξ ∈ Ioo α β, z ξ ≠ 0)
    (hR : ∀ ξ ∈ Ioo α β, Q ξ - χ < R ξ) : ∃ ξ ∈ Ioo α β, y ξ = 0 := by
  by_contra hcon
  push Not at hcon
  set μ := (α + β) / 2 with hμdef
  have hμ : μ ∈ Ioo α β := ⟨by rw [hμdef]; linarith, by rw [hμdef]; linarith⟩
  have hαI : α ∈ Icc α β := ⟨le_rfl, hαβ.le⟩
  have hβI : β ∈ Icc α β := ⟨hαβ.le, le_rfl⟩
  have hpP : ∀ ξ ∈ Icc α β, pP ξ < 0 := fun ξ hξ => by
    unfold pP; nlinarith [hξ.1, hξ.2]
  have hsgn : ∀ f : ℝ → ℝ, (∀ ξ ∈ Icc α β, ContinuousAt f ξ) → (∀ ξ ∈ Ioo α β, f ξ ≠ 0) →
      ∀ ξ ∈ Ioo α β, 0 < f μ * f ξ := by
    intro f hf hne ξ hξ
    have hcf : ∀ a b, α < a → b < β → ContinuousOn f (Icc a b) := fun a b ha hb s hs =>
      (hf s ⟨by linarith [hs.1], by linarith [hs.2]⟩).continuousWithinAt
    rcases le_total μ ξ with h | h
    · exact mul_pos_of_ne_zero (hcf μ ξ hμ.1 hξ.2)
        (fun s hs => hne s ⟨by linarith [hs.1, hμ.1], by linarith [hs.2, hξ.2]⟩) ξ ⟨h, le_rfl⟩
    · have := mul_pos_of_ne_zero (hcf ξ μ hξ.1 hμ.2)
        (fun s hs => hne s ⟨by linarith [hs.1, hξ.1], by linarith [hs.2, hμ.2]⟩) μ ⟨h, le_rfl⟩
      rwa [mul_comm] at this
  have hyc : ∀ ξ ∈ Icc α β, ContinuousAt y ξ := fun ξ hξ => (hy ξ hξ).continuousAt
  have hzc : ∀ ξ ∈ Icc α β, ContinuousAt z ξ := fun ξ hξ => (hz ξ hξ).continuousAt
  have hys := hsgn y hyc hcon
  have hzs := hsgn z hzc hz0
  -- the endpoint signs
  have hyα : 0 ≤ y μ * y α :=
    ge_of_tendsto (((hyc α hαI).const_mul (y μ)).tendsto.mono_left nhdsWithin_le_nhds)
      (by filter_upwards [Ioo_mem_nhdsGT hαβ] with ξ hξ using (hys ξ hξ).le)
  have hyβ : 0 ≤ y μ * y β :=
    ge_of_tendsto (((hyc β hβI).const_mul (y μ)).tendsto.mono_left nhdsWithin_le_nhds)
      (by filter_upwards [Ioo_mem_nhdsLT hαβ] with ξ hξ using (hys ξ hξ).le)
  have hZα : z μ * Z α ≤ 0 := by
    have hd := deriv_nonneg_of_right ((hz α hαI).const_mul (z μ)) (by
      filter_upwards [Ioo_mem_nhdsGT hαβ] with ξ hξ
      rw [hzα, mul_zero]; exact (hzs ξ hξ).le)
    have hp := hpP α hαI
    have hp' := hp.ne
    have e : z μ * Z α = z μ * (Z α / pP α) * pP α := by field_simp
    rw [e]
    exact mul_nonpos_of_nonneg_of_nonpos hd hp.le
  have hZβ : 0 ≤ z μ * Z β := by
    have hd := deriv_nonpos_of_left ((hz β hβI).const_mul (z μ)) (by
      filter_upwards [Ioo_mem_nhdsLT hαβ] with ξ hξ
      rw [hzβ, mul_zero]; exact (hzs ξ hξ).le)
    have hp := hpP β hβI
    have hp' := hp.ne
    have e : z μ * Z β = z μ * (Z β / pP β) * pP β := by field_simp
    rw [e]
    exact mul_nonneg_of_nonpos_of_nonpos hd hp.le
  -- the Wronskian `ε(yZ − Uz)` decreases strictly
  set ε := y μ * z μ with hεdef
  set F : ℝ → ℝ := fun ξ => ε * (y ξ * Z ξ - U ξ * z ξ) with hFdef
  have hF : ∀ ξ ∈ Icc α β, HasDerivAt F (ε * (((Q ξ - χ) - R ξ) * (y ξ * z ξ))) ξ := by
    intro ξ hξ
    have d := (((hy ξ hξ).mul (hZ ξ hξ)).sub ((hU ξ hξ).mul (hz ξ hξ))).const_mul ε
    refine d.congr_deriv ?_
    have hp := (hpP ξ hξ).ne
    field_simp
    ring
  obtain ⟨c0, hc0, hslope⟩ := exists_hasDerivAt_eq_slope F
    (fun ξ => ε * (((Q ξ - χ) - R ξ) * (y ξ * z ξ))) hαβ
    (fun ξ hξ => (hF ξ hξ).continuousAt.continuousWithinAt) (fun ξ hξ => hF ξ (Ioo_subset_Icc_self hξ))
  have hneg : ε * (((Q c0 - χ) - R c0) * (y c0 * z c0)) < 0 := by
    have h1 : 0 < ε * (y c0 * z c0) := by
      have e : ε * (y c0 * z c0) = (y μ * y c0) * (z μ * z c0) := by rw [hεdef]; ring
      rw [e]; exact mul_pos (hys c0 hc0) (hzs c0 hc0)
    have h2 : (Q c0 - χ) - R c0 < 0 := by linarith [hR c0 hc0]
    have e : ε * (((Q c0 - χ) - R c0) * (y c0 * z c0)) = ((Q c0 - χ) - R c0) * (ε * (y c0 * z c0)) := by
      ring
    rw [e]; exact mul_neg_of_neg_of_pos h2 h1
  have hFα : F α ≤ 0 := by
    have e : F α = (y μ * y α) * (z μ * Z α) := by simp only [hFdef, hεdef, hzα]; ring
    rw [e]; exact mul_nonpos_of_nonneg_of_nonpos hyα hZα
  have hFβ : 0 ≤ F β := by
    have e : F β = (y μ * y β) * (z μ * Z β) := by simp only [hFdef, hεdef, hzβ]; ring
    rw [e]; exact mul_nonneg hyβ hZβ
  have : (F β - F α) / (β - α) < 0 := by rw [← hslope]; exact hneg
  have hba : 0 < β - α := by linarith
  have : F β - F α < 0 := by
    by_contra hc
    push Not at hc
    exact absurd this (not_lt.mpr (div_nonneg hc hba.le))
  linarith

/-! ### The comparison function at `χ = c² − σ` -/

/-- `m(ξ) = c(1 − ξ²) − σ/(2c)`. -/
def mW (c σ ξ : ℝ) : ℝ := c * (1 - ξ ^ 2) - σ / (2 * c)

/-- The phase `Θ(ξ) = cξ − (σ/4c)(log(1 + ξ) − log(1 − ξ))`, with `Θ' = m/(1 − ξ²)`. -/
def thW (c σ ξ : ℝ) : ℝ := c * ξ - σ / (4 * c) * (Real.log (1 + ξ) - Real.log (1 - ξ))

/-- The comparison function `z = sin Θ/√m`. -/
def zW (c σ ξ : ℝ) : ℝ := sin (thW c σ ξ) / √(mW c σ ξ)

/-- The flux `(ξ² − 1)z'` of the comparison function. -/
def fW (c σ ξ : ℝ) : ℝ :=
  -(√(mW c σ ξ) * cos (thW c σ ξ) + (1 - ξ ^ 2) * c * ξ * sin (thW c σ ξ) / √(mW c σ ξ) ^ 3)

/-- The comparison potential: `((ξ² − 1)z')' = −R z`. -/
def rW (c σ ξ : ℝ) : ℝ :=
  -(mW c σ ξ ^ 2 / (1 - ξ ^ 2) - c * (1 - 3 * ξ ^ 2) / mW c σ ξ - 3 * c ^ 2 * ξ ^ 2 * (1 - ξ ^ 2) / mW c σ ξ ^ 2)

theorem hasDerivAt_mW (c σ ξ : ℝ) : HasDerivAt (mW c σ) (-(2 * c * ξ)) ξ := by
  have h := ((((hasDerivAt_id ξ).pow 2).const_sub 1).const_mul c).sub_const (σ / (2 * c))
  refine h.congr_deriv ?_
  simp only [id, Nat.cast_ofNat]
  ring

theorem hasDerivAt_thW {c σ ξ : ℝ} (hc : c ≠ 0) (h1 : -1 < ξ) (h2 : ξ < 1) :
    HasDerivAt (thW c σ) (mW c σ ξ / (1 - ξ ^ 2)) ξ := by
  have ha : 1 + ξ ≠ 0 := by linarith
  have hb : 1 - ξ ≠ 0 := by linarith
  have hla := ((hasDerivAt_id ξ).const_add 1).log ha
  have hlb := ((hasDerivAt_id ξ).const_sub 1).log hb
  have h := ((hasDerivAt_id ξ).const_mul c).sub ((hla.sub hlb).const_mul (σ / (4 * c)))
  refine h.congr_deriv ?_
  have hp : 1 - ξ ^ 2 ≠ 0 := by
    have : 1 - ξ ^ 2 = (1 + ξ) * (1 - ξ) := by ring
    rw [this]; exact mul_ne_zero ha hb
  simp only [mW, id]
  field_simp
  ring

theorem hasDerivAt_sqrt_mW {c σ ξ : ℝ} (hm : 0 < mW c σ ξ) :
    HasDerivAt (fun y => √(mW c σ y)) (-(c * ξ) / √(mW c σ ξ)) ξ := by
  have h := (hasDerivAt_mW c σ ξ).sqrt hm.ne'
  refine h.congr_deriv ?_
  have hs : √(mW c σ ξ) ≠ 0 := (Real.sqrt_pos.2 hm).ne'
  field_simp

/-- `z' = fW/pP`. -/
theorem hasDerivAt_zW {c σ ξ : ℝ} (hc : c ≠ 0) (h1 : -1 < ξ) (h2 : ξ < 1) (hm : 0 < mW c σ ξ) :
    HasDerivAt (zW c σ) (fW c σ ξ / pP ξ) ξ := by
  have hθ := hasDerivAt_thW (σ := σ) hc h1 h2
  have hS := hasDerivAt_sqrt_mW hm
  have hS0 : √(mW c σ ξ) ≠ 0 := (Real.sqrt_pos.2 hm).ne'
  have d := hθ.sin.div hS hS0
  show HasDerivAt (fun y => sin (thW c σ y) / √(mW c σ y)) _ ξ
  refine d.congr_deriv ?_
  have hq : 1 - ξ ^ 2 ≠ 0 := by nlinarith
  have hm2 : mW c σ ξ = √(mW c σ ξ) ^ 2 := (sq_sqrt hm.le).symm
  rw [show pP ξ = -(1 - ξ ^ 2) by unfold pP; ring]
  simp only [fW]
  generalize √(mW c σ ξ) = S at hS0 hm2 ⊢
  rw [hm2]
  field_simp
  ring

/-- `(fW)' = −rW · zW`. -/
theorem hasDerivAt_fW {c σ ξ : ℝ} (hc : c ≠ 0) (h1 : -1 < ξ) (h2 : ξ < 1) (hm : 0 < mW c σ ξ) :
    HasDerivAt (fW c σ) (-(rW c σ ξ * zW c σ ξ)) ξ := by
  have hθ := hasDerivAt_thW (σ := σ) hc h1 h2
  have hS := hasDerivAt_sqrt_mW hm
  have hS0 : √(mW c σ ξ) ≠ 0 := (Real.sqrt_pos.2 hm).ne'
  have hpoly : HasDerivAt (fun y => (1 - y ^ 2) * c * y) (c * (1 - 3 * ξ ^ 2)) ξ := by
    have h := ((((hasDerivAt_id ξ).pow 2).const_sub 1).mul_const c).mul (hasDerivAt_id ξ)
    refine h.congr_deriv ?_
    simp
    ring
  have hS3 : √(mW c σ ξ) ^ 3 ≠ 0 := pow_ne_zero 3 hS0
  have d := ((hS.mul hθ.cos).add ((hpoly.mul hθ.sin).div (hS.pow 3) hS3)).neg
  show HasDerivAt (fun y => -(√(mW c σ y) * cos (thW c σ y) +
    (1 - y ^ 2) * c * y * sin (thW c σ y) / √(mW c σ y) ^ 3)) _ ξ
  refine d.congr_deriv ?_
  have hq : 1 - ξ ^ 2 ≠ 0 := by nlinarith
  have hm2 : mW c σ ξ = √(mW c σ ξ) ^ 2 := (sq_sqrt hm.le).symm
  simp only [rW, zW, Pi.pow_apply, Pi.mul_apply, Nat.cast_ofNat]
  generalize √(mW c σ ξ) = S at hS0 hS3 hm2 ⊢
  rw [hm2]
  field_simp
  ring

/-- **The comparison inequality**: for `0 < σ ≤ c` and `σ ≤ c²(1 − ξ²)`, `c²ξ² − (c² − σ) < rW`. -/
theorem sub_lt_rW {c σ ξ : ℝ} (hc : 0 < c) (hσ : 0 < σ) (hσc : σ ≤ c) (hξ1 : ξ ^ 2 < 1)
    (hξ : σ ≤ c ^ 2 * (1 - ξ ^ 2)) : c ^ 2 * ξ ^ 2 - (c ^ 2 - σ) < rW c σ ξ := by
  set p := 1 - ξ ^ 2 with hpdef
  set d := σ / (2 * c) with hddef
  have hp : 0 < p := by rw [hpdef]; linarith
  have hp1 : p ≤ 1 := by rw [hpdef]; nlinarith
  have hd : 0 < d := div_pos hσ (by positivity)
  have hd2 : d ≤ 1 / 2 := by
    rw [hddef, div_le_iff₀ (by positivity)]; linarith
  have hdc : 2 * d ≤ c * p := by
    rw [hddef]
    have : 2 * (σ / (2 * c)) = σ / c := by field_simp
    rw [this, div_le_iff₀ hc]; nlinarith
  have hm : mW c σ ξ = c * p - d := by simp only [mW, hpdef, hddef]
  have hm0 : 0 < c * p - d := by nlinarith
  have hmle : c * p - d ≤ c * p := by linarith
  have hN : 0 < c ^ 2 * p ^ 2 - c * p * d * (1 - 3 * ξ ^ 2) - d ^ 2 * (c * p - d) ^ 2 := by
    have hcp : 0 < c * p := mul_pos hc hp
    have h1 : c * p * d * (1 - 3 * ξ ^ 2) ≤ c * p * d := by
      have : 0 ≤ c * p * d := by positivity
      nlinarith [sq_nonneg ξ]
    have h2 : d ^ 2 * (c * p - d) ^ 2 ≤ d ^ 2 * (c * p) ^ 2 := by
      have : (c * p - d) ^ 2 ≤ (c * p) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have hd4 : d ^ 2 ≤ 1 / 4 := by nlinarith
    have h3 : d ^ 2 * (c * p) ≤ c * p / 4 := by
      have := mul_le_mul_of_nonneg_right hd4 hcp.le
      linarith
    have h4 : 0 < c * p * (c * p - d - d ^ 2 * (c * p)) := by
      apply mul_pos hcp; nlinarith
    have e : c ^ 2 * p ^ 2 - c * p * d * (1 - 3 * ξ ^ 2) - d ^ 2 * (c * p - d) ^ 2 =
        c * p * (c * p - d - d ^ 2 * (c * p)) + (c * p * d - c * p * d * (1 - 3 * ξ ^ 2)) +
          (d ^ 2 * (c * p) ^ 2 - d ^ 2 * (c * p - d) ^ 2) := by ring
    rw [e]
    linarith
  have e : rW c σ ξ - (c ^ 2 * ξ ^ 2 - (c ^ 2 - σ)) =
      (c ^ 2 * p ^ 2 - c * p * d * (1 - 3 * ξ ^ 2) - d ^ 2 * (c * p - d) ^ 2) / (p * (c * p - d) ^ 2) := by
    rw [rW, hm]
    have hσd : σ = 2 * c * d := by rw [hddef]; field_simp
    rw [hσd, hpdef]
    rw [hpdef] at hm0 hp
    field_simp
    ring
  have : 0 < rW c σ ξ - (c ^ 2 * ξ ^ 2 - (c ^ 2 - σ)) := by
    rw [e]; exact div_pos hN (by positivity)
  linarith

/-! ### Counting zeros of `regSol` at `χ = c² − σ` -/

/-- **`J` zeros at `χ = c² − σ`**: for `1 < c`, `0 < σ ≤ c` and `Jπ ≤ Θ(1 − σ/c²)`, `regSol (sqC c) (c² − σ)` has `J`
zeros in `(0, 1)`, one between consecutive zeros of `sin Θ`. -/
theorem hasZeros_of_phase {c σ : ℝ} {J : ℕ} (hc : 1 < c) (hσ : 0 < σ) (hσc : σ ≤ c)
    (hJ : (J : ℝ) * π ≤ thW c σ (1 - σ / c ^ 2)) : HasZeros (sqC c) (c ^ 2 - σ) J := by
  have hc0 : 0 < c := by linarith
  set ξ₁ := 1 - σ / c ^ 2 with hξ₁
  have hσc2 : σ / c ^ 2 < 1 := by rw [div_lt_one (by positivity)]; nlinarith
  have hσc2' : 0 < σ / c ^ 2 := by positivity
  have hξ₁0 : 0 < ξ₁ := by linarith
  have hξ₁1 : ξ₁ < 1 := by linarith
  have hreg : ∀ ξ ∈ Icc 0 ξ₁, ξ ^ 2 < 1 ∧ σ ≤ c ^ 2 * (1 - ξ ^ 2) ∧ 0 < mW c σ ξ := by
    intro ξ hξ
    have hx2 : ξ ^ 2 ≤ ξ₁ ^ 2 := pow_le_pow_left₀ hξ.1 hξ.2 2
    have h1 : 1 - ξ₁ ^ 2 = σ / c ^ 2 * (2 - σ / c ^ 2) := by rw [hξ₁]; ring
    have h2 : σ / c ^ 2 ≤ 1 - ξ ^ 2 := by nlinarith
    have h3 : σ ≤ c ^ 2 * (1 - ξ ^ 2) := by
      rw [div_le_iff₀ (by positivity)] at h2; linarith
    refine ⟨by nlinarith, h3, ?_⟩
    simp only [mW]
    have h4 : σ / c ≤ c * (1 - ξ ^ 2) := by rw [div_le_iff₀ hc0]; nlinarith
    have h5 : σ / (2 * c) < σ / c := div_lt_div_of_pos_left hσ hc0 (by linarith)
    linarith
  have hθd : ∀ ξ ∈ Icc 0 ξ₁, HasDerivAt (thW c σ) (mW c σ ξ / (1 - ξ ^ 2)) ξ := fun ξ hξ =>
    hasDerivAt_thW hc0.ne' (by linarith [hξ.1]) (by linarith [hξ.2])
  have hθc : ContinuousOn (thW c σ) (Icc 0 ξ₁) := fun ξ hξ => (hθd ξ hξ).continuousAt.continuousWithinAt
  have hθmono : StrictMonoOn (thW c σ) (Icc 0 ξ₁) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 ξ₁) hθc (fun ξ hξ => ?_)
    rw [interior_Icc] at hξ
    rw [(hθd ξ (Ioo_subset_Icc_self hξ)).deriv]
    obtain ⟨h1, -, h3⟩ := hreg ξ (Ioo_subset_Icc_self hξ)
    exact div_pos h3 (by linarith)
  have hθ0 : thW c σ 0 = 0 := by simp [thW]
  have hζ : ∀ j : Fin (J + 1), ∃ ζ ∈ Icc 0 ξ₁, thW c σ ζ = ((j : ℕ) : ℝ) * π := by
    intro j
    have hj : ((j : ℕ) : ℝ) * π ∈ Icc (thW c σ 0) (thW c σ ξ₁) := by
      rw [hθ0]
      refine ⟨by positivity, le_trans ?_ hJ⟩
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.lt_succ_iff.mp j.2) pi_pos.le
    exact intermediate_value_Icc hξ₁0.le hθc hj
  choose ζ hζI hζθ using hζ
  have hζmono : StrictMono ζ := by
    intro i j hij
    have : thW c σ (ζ i) < thW c σ (ζ j) := by
      rw [hζθ, hζθ]
      exact mul_lt_mul_of_pos_right (by exact_mod_cast Fin.lt_def.mp hij) pi_pos
    exact (hθmono.lt_iff_lt (hζI i) (hζI j)).mp this
  have hz : ∀ i : Fin J, ∃ x ∈ Ioo (ζ i.castSucc) (ζ i.succ), regSol (sqC c) (c ^ 2 - σ) x = 0 := by
    intro i
    have hαβ : ζ i.castSucc < ζ i.succ := hζmono Fin.castSucc_lt_succ
    have hα := hζI i.castSucc
    have hβ := hζI i.succ
    have hsub : Icc (ζ i.castSucc) (ζ i.succ) ⊆ Icc 0 ξ₁ := Icc_subset_Icc hα.1 hβ.2
    have hlo : ∀ ξ ∈ Icc (ζ i.castSucc) (ζ i.succ), -1 < ξ := fun ξ hξ => by linarith [(hsub hξ).1]
    have hhi : ∀ ξ ∈ Icc (ζ i.castSucc) (ζ i.succ), ξ < 1 := fun ξ hξ => by linarith [(hsub hξ).2]
    refine exists_zero_of_comparison (Q := fun ξ => sqC c ξ) (R := rW c σ)
      (U := regU (sqC c) (c ^ 2 - σ)) (χ := c ^ 2 - σ) (z := zW c σ) (Z := fW c σ) (by linarith [hα.1]) hαβ
      (by linarith [hβ.2]) (fun ξ hξ => ?_) (fun ξ hξ => ?_) (fun ξ hξ => ?_) (fun ξ hξ => ?_) ?_ ?_
      (fun ξ hξ => ?_) (fun ξ hξ => ?_)
    · have hp : pP ξ ≠ 0 := by
        have := (hreg ξ (hsub hξ)).1; unfold pP; nlinarith
      have h := hasDerivAt_regSol (sqC c) (c ^ 2 - σ) (hlo ξ hξ)
      rwa [← pP_mul_regV (sqC c) (c ^ 2 - σ) (hlo ξ hξ), mul_div_cancel_left₀ _ hp]
    · exact hasDerivAt_regU (sqC c) (c ^ 2 - σ) (hlo ξ hξ)
    · exact hasDerivAt_zW hc0.ne' (hlo ξ hξ) (hhi ξ hξ) (hreg ξ (hsub hξ)).2.2
    · exact hasDerivAt_fW hc0.ne' (hlo ξ hξ) (hhi ξ hξ) (hreg ξ (hsub hξ)).2.2
    · simp only [zW, hζθ, Real.sin_nat_mul_pi, zero_div]
    · simp only [zW, hζθ, Real.sin_nat_mul_pi, zero_div]
    · have hξI : ξ ∈ Icc 0 ξ₁ := hsub (Ioo_subset_Icc_self hξ)
      have hlt1 : thW c σ (ζ i.castSucc) < thW c σ ξ := hθmono hα hξI hξ.1
      have hlt2 : thW c σ ξ < thW c σ (ζ i.succ) := hθmono hξI hβ hξ.2
      rw [hζθ] at hlt1 hlt2
      refine div_ne_zero (fun hs => ?_) (Real.sqrt_pos.2 (hreg ξ hξI).2.2).ne'
      obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hs
      rw [← hn] at hlt1 hlt2
      have h1 : ((i : ℕ) : ℝ) < n := lt_of_mul_lt_mul_right (by simpa using hlt1) pi_pos.le
      have h2 : (n : ℝ) < ((i : ℕ) : ℝ) + 1 := by
        have : (n : ℝ) * π < (((i : ℕ) : ℝ) + 1) * π := by simpa using hlt2
        exact lt_of_mul_lt_mul_right this pi_pos.le
      have h1' : ((i : ℕ) : ℤ) < n := by exact_mod_cast h1
      have h2' : n < ((i : ℕ) : ℤ) + 1 := by exact_mod_cast h2
      omega
    · obtain ⟨h1, h2, -⟩ := hreg ξ (hsub (Ioo_subset_Icc_self hξ))
      exact sub_lt_rW hc0 hσ hσc h1 h2
  choose x hxI hx0 using hz
  refine ⟨x, fun i j hij => ?_, fun i => ⟨?_, ?_⟩, hx0⟩
  · have h1 : ζ i.succ ≤ ζ j.castSucc := hζmono.monotone (Fin.succ_le_castSucc_iff.mpr hij)
    linarith [(hxI i).2, (hxI j).1]
  · linarith [(hxI i).1, (hζI i.castSucc).1]
  · linarith [(hxI i).2, (hζI i.succ).2]

/-- **The phase at the cut**: `Θ(1 − σ/c²) ≥ c − σ/c − (σ/4c) log(2c²/σ)` for `1 < c`, `0 < σ ≤ c`. -/
theorem thW_ge {c σ : ℝ} (hc : 1 < c) (hσ : 0 < σ) (hσc : σ ≤ c) :
    c - σ / c - σ / (4 * c) * Real.log (2 * c ^ 2 / σ) ≤ thW c σ (1 - σ / c ^ 2) := by
  have hc0 : 0 < c := by linarith
  have hu : 0 < σ / c ^ 2 := by positivity
  have hu1 : σ / c ^ 2 < 1 := by rw [div_lt_one (by positivity)]; nlinarith
  simp only [thW]
  have e1 : c * (1 - σ / c ^ 2) = c - σ / c := by field_simp
  have e2 : 1 - (1 - σ / c ^ 2) = σ / c ^ 2 := by ring
  rw [e1, e2]
  have hlog : Real.log (1 + (1 - σ / c ^ 2)) - Real.log (σ / c ^ 2) ≤ Real.log (2 * c ^ 2 / σ) := by
    have h1 : Real.log (1 + (1 - σ / c ^ 2)) ≤ Real.log 2 := Real.log_le_log (by linarith) (by linarith)
    have h2 : Real.log (2 * c ^ 2 / σ) = Real.log 2 - Real.log (σ / c ^ 2) := by
      rw [show 2 * c ^ 2 / σ = 2 / (σ / c ^ 2) by field_simp, Real.log_div (by norm_num) hu.ne']
    linarith
  have hk : 0 < σ / (4 * c) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hlog hk.le]

/-- **Even levels below `c² − σ`**: `Jπ ≤ c − σ/c − (σ/4c) log(2c²/σ)` with `1 < c`, `0 < σ ≤ c` gives at least
`J` even levels of `c²ξ²` below `c² − σ`. -/
theorem le_ncard_of_phase {c σ : ℝ} {J : ℕ} (hc : 1 < c) (hσ : 0 < σ) (hσc : σ ≤ c)
    (hJ : (J : ℝ) * π ≤ c - σ / c - σ / (4 * c) * Real.log (2 * c ^ 2 / σ)) :
    J ≤ (evenSpec (sqC c) ∩ Iio (c ^ 2 - σ)).ncard :=
  le_ncard_evenSpec (hasZeros_of_phase hc hσ hσc (hJ.trans (thW_ge hc hσ hσc)))

/-! ### The index lemma at `c = 2πx` -/

/-- The index margin `σ̲(c) = 4c/log c`. -/
def sigmaLow (c : ℝ) : ℝ := 4 * c / Real.log c

theorem four_le_log {c : ℝ} (hc : 80 ≤ c) : 4 ≤ Real.log c := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have h := Real.exp_one_lt_d9
  have e : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  have h0 : 0 < Real.exp 1 := Real.exp_pos 1
  have h1 := pow_le_pow_left₀ h0.le h.le 4
  have h2 : (2.7182818286 : ℝ) ^ 4 < 80 := by norm_num
  linarith

theorem sigmaLow_pos_le {c : ℝ} (hc : 80 ≤ c) : 0 < sigmaLow c ∧ sigmaLow c ≤ c := by
  have hL := four_le_log hc
  have hL0 : 0 < Real.log c := by linarith
  have hc0 : 0 < c := by linarith
  refine ⟨div_pos (by positivity) hL0, ?_⟩
  rw [sigmaLow, div_le_iff₀ hL0]
  nlinarith

/-- **The phase budget at `σ̲`**: `c − π ≤ c − σ̲/c − (σ̲/4c) log(2c²/σ̲)` for `c ≥ 80`. -/
theorem phase_sigmaLow {c : ℝ} (hc : 80 ≤ c) :
    c - π ≤ c - sigmaLow c / c - sigmaLow c / (4 * c) * Real.log (2 * c ^ 2 / sigmaLow c) := by
  have hL := four_le_log hc
  have hc0 : 0 < c := by linarith
  set L := Real.log c with hLdef
  have hL0 : 0 < L := by linarith
  have e1 : sigmaLow c / c = 4 / L := by unfold sigmaLow; rw [← hLdef]; field_simp
  have e2 : sigmaLow c / (4 * c) = 1 / L := by unfold sigmaLow; rw [← hLdef]; field_simp
  have e3 : 2 * c ^ 2 / sigmaLow c = c * (L / 2) := by unfold sigmaLow; rw [← hLdef]; field_simp; ring
  rw [e1, e2, e3, Real.log_mul hc0.ne' (by positivity)]
  have hl : Real.log (L / 2) ≤ L / 2 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h4 : 1 / L * (L + Real.log (L / 2)) ≤ 1 / L * (L + (L / 2 - 1)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have e4 : 1 / L * (L + (L / 2 - 1)) = 3 / 2 - 1 / L := by field_simp; ring
  have h5 : 4 / L ≤ 1 := by rw [div_le_one hL0]; linarith
  have h6 : 0 < 1 / L := by positivity
  linarith [Real.pi_gt_three]

/-- **`2x − 1` even levels below `c² − σ̲(c)`** at `c = 2πx ≥ 80`. -/
theorem le_ncard_sigmaLow {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    2 * x - 1 ≤ (evenSpec (sqC (2 * π * x)) ∩ Iio ((2 * π * x) ^ 2 - sigmaLow (2 * π * x))).ncard := by
  have hx1 : 1 ≤ x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · rw [h] at hx; simp at hx; linarith
    · exact h
  obtain ⟨hs0, hsc⟩ := sigmaLow_pos_le hx
  refine le_ncard_of_phase (by linarith) hs0 hsc ?_
  have hcast : ((2 * x - 1 : ℕ) : ℝ) = 2 * (x : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hcast]
  have := phase_sigmaLow hx
  have e : (2 * (x : ℝ) - 1) * π = 2 * π * x - π := by ring
  linarith

/-- **The index lemma**: at `c = 2πx ≥ 80`, a level with at most `2x − 2` even levels below it lies below
`c² − 4c/log c`. -/
theorem index_lemma {x : ℕ} {χ : ℝ} (hx : 80 ≤ 2 * π * x)
    (hk : (evenSpec (sqC (2 * π * x)) ∩ Iio χ).ncard + 2 ≤ 2 * x) :
    sigmaLow (2 * π * x) < (2 * π * x) ^ 2 - χ := by
  by_contra hle
  push Not at hle
  have h1 := le_ncard_sigmaLow hx
  have hsub : evenSpec (sqC (2 * π * x)) ∩ Iio ((2 * π * x) ^ 2 - sigmaLow (2 * π * x)) ⊆
      evenSpec (sqC (2 * π * x)) ∩ Iio χ :=
    fun z hz => ⟨hz.1, mem_Iio.mpr (lt_of_lt_of_le (mem_Iio.mp hz.2) (by linarith))⟩
  have h2 := Set.ncard_le_ncard hsub (finite_evenSpec_Iio _ χ)
  omega

end Cvs.Prolate.EvenLevelIndexLemma
