import Mathlib
import Cvs.Prolate.ConverseLevelCount
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.EvenLevelIndexLemma
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RegularSolutionChiVariation
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.TopRungZeroSplitHalf

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Sturm oscillation at a point `a`: the Dirichlet nodes below `χ` number the zeros of `y_χ` in `(a, 1)`

As in Cvs.Prolate.EvenLevelIndexLemma/Cvs.Prolate.ConverseLevelCount with `0` replaced by `a ∈ [0, 1)`: zeros of `regSol Q χ` in `(a, 1)` move left as `χ` grows, persist,
and are created only through `a`, at the nodes `regSol Q σ a = 0`; so `y_χ` has exactly `#{σ < χ : y_σ(a) = 0}` zeros
there.
-/

noncomputable section

open Real Set Filter Topology Cvs.Prolate.RegularSolutionEdge Cvs.Prolate.RegularSolutionChiVariation Cvs.Prolate.EdgeCentreSign
open Cvs.Prolate.TopRungZeroSplitHalf (ZerosOn)

namespace Cvs.Prolate.SturmOscillationAtPoint

variable (Q : C(ℝ, ℝ)) {a : ℝ}

/-- The nodes at `a`: the levels at which the regular solution vanishes at `a`. -/
def nodeSpec (Q : C(ℝ, ℝ)) (a : ℝ) : Set ℝ := {χ | regSol Q χ a = 0}

theorem regDot_ne_zero_of_node (ha : -1 < a) (ha1 : a < 1) {χ : ℝ} (hχ : χ ∈ nodeSpec Q a) :
    regDot Q χ a ≠ 0 := by
  intro h
  have := wronskian_neg Q χ ha ha1
  have hχ' : regSol Q χ a = 0 := hχ
  rw [hχ', h] at this
  simp at this

/-- Every node at `a` lies at or above any level below `Q` on `[a, 1]`. -/
theorem le_of_mem_nodeSpec (ha : -1 < a) (ha1 : a ≤ 1) {m : ℝ} (hm : ∀ χ < m, ∀ s ∈ Icc a 1, χ < Q s)
    {χ : ℝ} (hχ : χ ∈ nodeSpec Q a) : m ≤ χ := by
  by_contra hlt
  push Not at hlt
  have h1 := one_le_regSol_of_lt Q (ξ := a) ha ha1 (fun s hs => hm χ hlt s hs) a ⟨le_rfl, ha1⟩
  have h0 : regSol Q χ a = 0 := hχ
  linarith

theorem exists_lt_potential' (Q : C(ℝ, ℝ)) (a : ℝ) : ∃ m : ℝ, ∀ χ < m, ∀ s ∈ Icc a 1, χ < Q s := by
  obtain ⟨s₀, -, hs₀⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr (min_le_right a 1))
    Q.continuous.continuousOn
  exact ⟨Q s₀, fun χ hχ s hs => lt_of_lt_of_le hχ (hs₀ ⟨(min_le_left a 1).trans hs.1, hs.2⟩)⟩

/-- **The nodes below any level are finite.** -/
theorem finite_nodeSpec_Iio (ha : -1 < a) (ha1 : a < 1) (χ : ℝ) : (nodeSpec Q a ∩ Iio χ).Finite := by
  obtain ⟨m, hm⟩ := exists_lt_potential' Q a
  have hsub : nodeSpec Q a ∩ Iio χ ⊆ nodeSpec Q a ∩ Icc m χ := fun x hx =>
    ⟨hx.1, le_of_mem_nodeSpec Q ha ha1.le hm hx.1, (mem_Iio.mp hx.2).le⟩
  refine Set.Finite.subset ?_ hsub
  have hcl : IsClosed (nodeSpec Q a) := isClosed_eq (Cvs.Prolate.EvenLevelIndexLemma.continuous_regSol_level Q a) continuous_const
  refine IsCompact.finite (isCompact_Icc.inter_left hcl) ?_
  rw [isDiscrete_iff_nhdsNE]
  intro x hx
  have hev := (hasDerivAt_regSol_regDot Q x a).eventually_ne (c := (0:ℝ)) (regDot_ne_zero_of_node Q ha ha1 hx.1)
  rw [inf_principal_eq_bot]
  filter_upwards [hev] with z hz hzS
  exact hz hzS.1

/-! ### Zeros persist, have limits, and leave through `a` -/

/-- **Zeros persist**: `k` zeros in `(a, 1)` at `χ` give `k` zeros in `(a, 1)` at every level near `χ`. -/
theorem zerosOn_eventually {Q : C(ℝ, ℝ)} {a χ : ℝ} (ha : -1 < a) {k : ℕ}
    (h : ZerosOn (regSol Q χ) (Ioo a 1) k) : ∀ᶠ t in 𝓝 χ, ZerosOn (regSol Q t) (Ioo a 1) k := by
  obtain ⟨w, hmono, hw, hz⟩ := h
  obtain ⟨δ, hδ0, hδ1, hδ2⟩ : ∃ δ : ℝ, 0 < δ ∧ (∀ i, a < w i - δ ∧ w i + δ < 1) ∧
      ∀ i j, i < j → w i + δ < w j - δ := by
    have h1 : ∀ i, ∀ᶠ δ in 𝓝 (0:ℝ), a < w i - δ ∧ w i + δ < 1 := fun i => by
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
  have hw1 : ∀ i, -1 < w i := fun i => by linarith [(hw i).1, ha]
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
      ((Cvs.Prolate.EvenLevelIndexLemma.continuous_regSol_level Q (r i)).mul continuous_const).continuousAt
    have hcl : ContinuousAt (fun t => regSol Q t (l i) * regV Q χ (w i)) χ :=
      ((Cvs.Prolate.EvenLevelIndexLemma.continuous_regSol_level Q (l i)).mul continuous_const).continuousAt
    exact (hcr.eventually (lt_mem_nhds (hrs i))).and (hcl.eventually (gt_mem_nhds (hls i)))
  filter_upwards [hev] with t ht
  have hzero : ∀ i, ∃ x ∈ Ioo (l i) (r i), regSol Q t x = 0 := fun i => by
    refine Cvs.Prolate.EvenLevelIndexLemma.exists_zero_of_mul_neg (by linarith [(hlI i).2, (hrI i).1])
      (continuousOn_regSol_Icc Q t (by linarith [(hlI i).1, (hδ1 i).1, ha])) ?_
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

/-- `{t : y_t has k zeros in (a, 1)}` is open. -/
theorem isOpen_zerosOn (ha : -1 < a) (k : ℕ) : IsOpen {t | ZerosOn (regSol Q t) (Ioo a 1) k} :=
  isOpen_iff_mem_nhds.2 fun _ ht => zerosOn_eventually ha ht

/-- **Limits of zeros**: if `t n → t₀` and each `regSol Q (t n)` has `k` zeros in `(a, 1)`, then `regSol Q t₀` has
`k` distinct zeros in `[a, 1)`. -/
theorem zerosOn_limit {Q : C(ℝ, ℝ)} {a : ℝ} (ha : -1 < a) {t : ℕ → ℝ} {t₀ : ℝ} {k : ℕ}
    (ht : Tendsto t atTop (𝓝 t₀)) (hZ : ∀ n, ZerosOn (regSol Q (t n)) (Ioo a 1) k) :
    ∃ w : Fin k → ℝ, StrictMono w ∧ (∀ i, a ≤ w i ∧ w i < 1) ∧ ∀ i, regSol Q t₀ (w i) = 0 := by
  choose W hWm hWb hWz using hZ
  have hK : IsCompact (Set.pi univ fun _ : Fin k => Icc a 1) := isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨w, hw, φ, hφ, hlim⟩ := hK.tendsto_subseq (x := W)
    (fun n i _ => ⟨(hWb n i).1.le, (hWb n i).2.le⟩)
  have hlimi : ∀ i, Tendsto (fun n => W (φ n) i) atTop (𝓝 (w i)) := fun i =>
    ((continuous_apply i).continuousAt.tendsto).comp hlim
  have htφ : Tendsto (fun n => t (φ n)) atTop (𝓝 t₀) := ht.comp hφ.tendsto_atTop
  have hw01 : ∀ i, w i ∈ Icc a 1 := fun i => hw i (mem_univ i)
  have hjoint : ∀ ξ, -1 < ξ → ContinuousAt (fun p : ℝ × ℝ => regSol Q p.1 p.2) (t₀, ξ) := fun ξ hξ =>
    (continuousOn_regSol_joint Q).continuousAt (prod_mem_nhds univ_mem (Ioi_mem_nhds hξ))
  have hjointU : ∀ ξ, -1 < ξ → ContinuousAt (fun p : ℝ × ℝ => regU Q p.1 p.2) (t₀, ξ) := fun ξ hξ =>
    (continuousOn_regU_joint Q).continuousAt (prod_mem_nhds univ_mem (Ioi_mem_nhds hξ))
  have hzero : ∀ i, regSol Q t₀ (w i) = 0 := fun i => by
    have h := (hjoint (w i) (by linarith [(hw01 i).1, ha])).tendsto.comp (htφ.prodMk_nhds (hlimi i))
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
      (continuousOn_regSol_Icc Q _ (by linarith [ha])) (by rw [hWz, hWz])
      (fun x hx => hasDerivAt_regSol Q _ (by linarith [hx.1, ha]))
    exact ⟨v, hv, by rw [← pP_mul_regV Q _ (by linarith [hv.1, ha]), hv0, mul_zero]⟩
  choose v hvI hv0 using hv
  have hj' : Tendsto (fun n => W (φ n) j) atTop (𝓝 (w i)) := heq ▸ hlimi j
  have hvlim : Tendsto v atTop (𝓝 (w i)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le (hlimi i) hj' (fun n => (hvI n).1.le) (fun n => (hvI n).2.le)
  have hU := (hjointU (w i) (by linarith [(hw01 i).1, ha])).tendsto.comp (htφ.prodMk_nhds hvlim)
  have h0 : (fun n => regU Q (t (φ n)) (v n)) = fun _ => (0:ℝ) := funext fun n => hv0 n
  have hU' : Tendsto (fun n => regU Q (t (φ n)) (v n)) atTop (𝓝 (regU Q t₀ (w i))) := hU
  rw [h0] at hU'
  exact regU_ne_zero_of_regSol_eq_zero Q t₀ (by linarith [(hw01 i).1, ha]) (hw1 i) (hzero i)
    (tendsto_nhds_unique hU' tendsto_const_nhds)

/-- **Each zero in `(a, 1)` costs a node below**: `k` zeros of `regSol Q χ` in `(a, 1)` give at least `k` nodes at
`a` below `χ`. -/
theorem le_ncard_nodeSpec (ha : -1 < a) (ha1 : a < 1) :
    ∀ k : ℕ, ∀ χ, ZerosOn (regSol Q χ) (Ioo a 1) k → k ≤ (nodeSpec Q a ∩ Iio χ).ncard := by
  obtain ⟨m, hm⟩ := exists_lt_potential' Q a
  have hnone : ∀ k, ∀ t < m, ZerosOn (regSol Q t) (Ioo a 1) (k + 1) → False := by
    rintro k t ht ⟨w, -, hw, hz⟩
    have := one_le_regSol_of_lt Q (ξ := a) ha ha1.le (fun s hs => hm t ht s hs) (w 0)
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
    set B := Icc (m - 1) χ ∩ {t | ¬ ZerosOn (regSol Q t) (Ioo a 1) (k + 1)} with hBdef
    have hBc : IsClosed B := isClosed_Icc.inter (isOpen_zerosOn Q ha (k + 1)).isClosed_compl
    have hBne : B.Nonempty := ⟨m - 1, ⟨le_rfl, by linarith⟩, fun h => hnone k (m - 1) (by linarith) h⟩
    have hBb : BddAbove B := ⟨χ, fun t ht => ht.1.2⟩
    set t₁ := sSup B with ht₁def
    have ht₁ : t₁ ∈ B := hBc.csSup_mem hBne hBb
    have ht₁χ : t₁ < χ := lt_of_le_of_ne ht₁.1.2 (fun h => ht₁.2 (h ▸ hχ))
    have hafter : ∀ s ∈ Ioc t₁ χ, ZerosOn (regSol Q s) (Ioo a 1) (k + 1) := by
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
    have htsZ : ∀ n, ZerosOn (regSol Q (ts n)) (Ioo a 1) (k + 1) := fun n => by
      have hn : (0:ℝ) < (n : ℝ) + 2 := by positivity
      have hpos : 0 < (χ - t₁) / ((n : ℝ) + 2) := div_pos (by linarith) hn
      have hle : (χ - t₁) / ((n : ℝ) + 2) ≤ χ - t₁ :=
        div_le_self (by linarith) (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
      exact hafter _ ⟨by simp only [htsdef]; linarith, by simp only [htsdef]; linarith⟩
    obtain ⟨w, hwm, hwb, hwz⟩ := zerosOn_limit ha hts htsZ
    have hw0 : w 0 = a := by
      by_contra hne
      have hpos : a < w 0 := lt_of_le_of_ne (hwb 0).1 (Ne.symm hne)
      exact ht₁.2 ⟨w, hwm, fun i => ⟨lt_of_lt_of_le hpos (hwm.monotone (Fin.zero_le i)), (hwb i).2⟩, hwz⟩
    have hodd : t₁ ∈ nodeSpec Q a := by
      have := hwz 0
      rwa [hw0] at this
    have hZk : ZerosOn (regSol Q t₁) (Ioo a 1) k := ⟨fun i => w i.succ, hwm.comp Fin.strictMono_succ,
      fun i => ⟨by rw [← hw0]; exact hwm (Fin.succ_pos i), (hwb _).2⟩, fun i => hwz _⟩
    have hk := ih t₁ hZk
    have hsub : insert t₁ (nodeSpec Q a ∩ Iio t₁) ⊆ nodeSpec Q a ∩ Iio χ := by
      intro z hz
      rcases hz with rfl | hz
      · exact ⟨hodd, ht₁χ⟩
      · exact ⟨hz.1, mem_Iio.mpr (lt_trans (mem_Iio.mp hz.2) ht₁χ)⟩
    have hnot : t₁ ∉ nodeSpec Q a ∩ Iio t₁ := fun h => lt_irrefl _ (mem_Iio.mp h.2)
    have := Set.ncard_le_ncard hsub (finite_nodeSpec_Iio Q ha ha1 χ)
    rw [Set.ncard_insert_of_notMem hnot (finite_nodeSpec_Iio Q ha ha1 t₁)] at this
    omega

/-! ### Each node below `χ` leaves a zero -/

/-- `k` zeros in `(a, 1)` and a zero at `a` give `k + 1` zeros in `(a, 1)` once `Q − χ` decreases there. -/
theorem zerosOn_succ_of_lt {Q Q' : C(ℝ, ℝ)} {χ χ' : ℝ} {k : ℕ} (ha : -1 < a) (ha1 : a < 1)
    (h0 : regSol Q χ a = 0) (h : ZerosOn (regSol Q χ) (Ioo a 1) k)
    (hlt : ∀ t ∈ Ioo a 1, Q' t - χ' < Q t - χ) : ZerosOn (regSol Q' χ') (Ioo a 1) (k + 1) := by
  obtain ⟨w, hw, hw01, hw0⟩ := h
  set b : Fin (k + 1) → ℝ := Fin.cons a w with hbdef
  have hb : StrictMono b := Fin.strictMono_cons.2 ⟨fun j => (hw01 j).1, hw⟩
  have hb00 : b 0 = a := by simp [hbdef]
  have hnn : ∀ i, a ≤ b i := fun i => hb00 ▸ hb.monotone (Fin.zero_le i)
  have hb1 : ∀ i, -1 < b i ∧ b i < 1 := by
    refine Fin.cases ?_ (fun j => ?_)
    · simp only [hbdef, Fin.cons_zero]; exact ⟨ha, ha1⟩
    · simp only [hbdef, Fin.cons_succ]; exact ⟨by linarith [(hw01 j).1], (hw01 j).2⟩
  have hb0 : ∀ i, regSol Q χ (b i) = 0 := by
    refine Fin.cases ?_ (fun j => ?_)
    · simpa [hbdef] using h0
    · simpa [hbdef] using hw0 j
  obtain ⟨w', hw', hw'I, hw'0⟩ := Cvs.Prolate.ConverseLevelCount.exists_zeros_of_lt hb hb1 hb0
    (fun i t ht => hlt t ⟨lt_of_le_of_lt (hnn i) ht.1, ht.2⟩)
  exact ⟨w', hw', fun i => ⟨lt_of_le_of_lt (hnn i) (hw'I i).1, (hw'I i).2⟩, hw'0⟩

/-- **Each node below `χ` leaves a zero**: `regSol Q χ` has as many zeros in `(a, 1)` as there are nodes at `a`
below `χ`. -/
theorem zerosOn_ncard_nodeSpec (ha : -1 < a) (ha1 : a < 1) (χ : ℝ) :
    ZerosOn (regSol Q χ) (Ioo a 1) (nodeSpec Q a ∩ Iio χ).ncard := by
  suffices H : ∀ n : ℕ, ∀ χ : ℝ, (nodeSpec Q a ∩ Iio χ).ncard = n → ZerosOn (regSol Q χ) (Ioo a 1) n from
    H _ χ rfl
  intro n
  induction n with
  | zero => intro χ _; exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    intro χ hn
    have hfin := finite_nodeSpec_Iio Q ha ha1 χ
    have hne : (nodeSpec Q a ∩ Iio χ).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
    obtain ⟨m, hm, hmχ, -, hcard⟩ := Cvs.Prolate.ConverseLevelCount.exists_max_Iio hfin hne
    exact zerosOn_succ_of_lt ha ha1 hm (ih m (by omega)) (fun t _ => by linarith)

end Cvs.Prolate.SturmOscillationAtPoint

end
