import Mathlib
import Cvs.Prolate.EvenLevelIndexLemma
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.TopRungDepthBound

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The top rung splits its zeros at `½`: `x` in `(0, ½)`, `x − 2` in `(½, 1)`

From the centre, an even regular solution at `χ = c² − Kc` has Prüfer phase `Θ(0) ∈ πℤ`; `TopRungDepthBound`'s majorant bounds
`Θ(β) − Θ(0)` above, and the minorant `c − K/2p − K²/2cp²` with `(log a)' = ωw` bounds it below. At `β = ½`,
`0 ≤ K ≤ 5` and `c = 2πx ≥ 62π` the two bounds pin the count in `(0, ½]` to `x`, so the top rung has `x − 2` zeros in
`(½, 1)`: `k* = t − 1`.
-/

noncomputable section

namespace Cvs.Prolate.TopRungZeroSplitHalf

open Real Set Filter Topology MeasureTheory

/-! ### Zeros in a set -/

/-- `f` has `k` distinct zeros in `I`. -/
def ZerosOn (f : ℝ → ℝ) (I : Set ℝ) (k : ℕ) : Prop :=
  ∃ w : Fin k → ℝ, StrictMono w ∧ (∀ i, w i ∈ I) ∧ ∀ i, f (w i) = 0

/-- `HasZeros` is `ZerosOn` the interval `(0, 1)`. -/
theorem hasZeros_iff {Q : C(ℝ, ℝ)} {χ : ℝ} {k : ℕ} :
    Cvs.Prolate.EvenLevelIndexLemma.HasZeros Q χ k ↔ ZerosOn (Cvs.Prolate.RegularSolutionEdge.regSol Q χ) (Ioo 0 1) k :=
  Iff.rfl

/-- If `m + n` zeros lie in `(a, d)` and `m + 1` never lie in `(a, b]`, the last `n` lie in `(b, d)`. -/
theorem zerosOn_tail {f : ℝ → ℝ} {a b d : ℝ} {m n : ℕ} (h : ZerosOn f (Ioo a d) (m + n))
    (hn : ¬ZerosOn f (Ioc a b) (m + 1)) : ZerosOn f (Ioo b d) n := by
  obtain ⟨w, hw, hwI, hw0⟩ := h
  refine ⟨fun i => w (Fin.natAdd m i), fun i j hij => hw ?_, fun i => ?_, fun i => hw0 _⟩
  · rw [Fin.lt_def, Fin.val_natAdd, Fin.val_natAdd]; exact Nat.add_lt_add_left hij m
  refine ⟨?_, (hwI _).2⟩
  by_contra hle
  push Not at hle
  have hmn : m + 1 ≤ m + n := by have := i.2; omega
  refine hn ⟨fun j => w (Fin.castLE hmn j), hw.comp (Fin.strictMono_castLE hmn), fun j => ⟨(hwI _).1, ?_⟩,
    fun j => hw0 _⟩
  refine le_trans (hw.monotone ?_) hle
  simp only [Fin.le_def, Fin.val_castLE, Fin.val_natAdd]
  have := j.2; omega

/-! ### The phase from below -/

/-- **Crossings**: if `sin Θ(α) = 0` and `Θ(β) > Θ(α) + (k − ½)π`, `cos Θ` has `k` increasing zeros in `(α, β)`. -/
theorem crossings {Θ : ℝ → ℝ} {α β : ℝ} {k : ℕ} (hαβ : α ≤ β) (hc : ContinuousOn Θ (Icc α β))
    (hα : sin (Θ α) = 0) (hk : Θ α + ((k : ℝ) - 1 / 2) * π < Θ β) :
    ∃ w : Fin k → ℝ, StrictMono w ∧ (∀ i, w i ∈ Ioo α β) ∧ ∀ i, cos (Θ (w i)) = 0 := by
  obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp hα
  set L : ℕ → ℝ := fun n => Θ α + ((n : ℝ) + 1 / 2) * π with hLdef
  have hLα : ∀ n, Θ α < L n := fun n => lt_add_of_pos_right _ (by positivity)
  have hLβ : ∀ n < k, L n < Θ β := fun n hn => by
    have h1 : (n : ℝ) + 1 ≤ k := by exact_mod_cast hn
    simp only [L]; nlinarith [Real.pi_pos]
  have hLmono : StrictMono L := fun n n' h => by
    have : (n : ℝ) < n' := by exact_mod_cast h
    simp only [L]; nlinarith [Real.pi_pos]
  have hcosL : ∀ n, cos (L n) = 0 := fun n => by
    simp only [L]
    rw [← hm, show (m : ℝ) * π + ((n : ℝ) + 1 / 2) * π = (2 * ((m + n : ℤ) : ℝ) + 1) * π / 2 by push_cast; ring]
    exact Real.cos_eq_zero_iff.mpr ⟨m + n, rfl⟩
  set S : ℕ → Set ℝ := fun n => Icc α β ∩ {t | L n ≤ Θ t} with hS
  have hSc : ∀ n, IsClosed (S n) := fun n => hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hSb : ∀ n, BddBelow (S n) := fun n => ⟨α, fun t ht => ht.1.1⟩
  have hSne : ∀ n < k, (S n).Nonempty := fun n hn => ⟨β, ⟨hαβ, le_rfl⟩, (hLβ n hn).le⟩
  set v : ℕ → ℝ := fun n => sInf (S n) with hv
  have hvS : ∀ n < k, v n ∈ S n := fun n hn => (hSc n).csInf_mem (hSne n hn) (hSb n)
  have hvL : ∀ n < k, Θ (v n) = L n := fun n hn => by
    obtain ⟨⟨h1, h2⟩, h3⟩ := hvS n hn
    have h3' : L n ≤ Θ (v n) := h3
    refine le_antisymm ?_ h3'
    by_contra hgt; push Not at hgt
    obtain ⟨r, hrI, hr⟩ := intermediate_value_Icc h1 (hc.mono (Icc_subset_Icc le_rfl h2))
      ⟨(hLα n).le, hgt.le⟩
    have hrS : r ∈ S n := ⟨⟨hrI.1, hrI.2.trans h2⟩, by simp [hr]⟩
    have hle : v n ≤ r := csInf_le (hSb n) hrS
    have : r = v n := le_antisymm hrI.2 hle
    rw [this] at hr; linarith
  have hvle : ∀ n n', n ≤ n' → n' < k → v n ≤ v n' := fun n n' h hn' =>
    csInf_le_csInf (hSb n) (hSne n' hn') (fun t ht => ⟨ht.1, (hLmono.monotone h).trans ht.2⟩)
  refine ⟨fun i => v i, fun i j hij => ?_, fun i => ?_, fun i => ?_⟩
  · refine lt_of_le_of_ne (hvle i j hij.le j.2) (fun h => ?_)
    have := congrArg Θ h
    simp only at this
    rw [hvL i i.2, hvL j j.2] at this
    exact (hLmono hij).ne this
  · obtain ⟨⟨h1, h2⟩, -⟩ := hvS i i.2
    have hL := hvL i i.2
    refine ⟨lt_of_le_of_ne h1 (fun h => ?_), lt_of_le_of_ne h2 (fun h => ?_)⟩
    · have h' : v i = α := h.symm
      rw [h'] at hL; linarith [hLα i]
    · have h' : v i = β := h
      rw [h'] at hL; linarith [hLβ i i.2]
  · simp only; rw [hvL i i.2]; exact hcosL i

/-! ### The Prüfer phase from the centre -/

open Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Upstream.SturmLiouvillePrufer Cvs.Prolate.RegularSolutionEdge Cvs.Prolate.TopRungDepthBound

variable {c K β : ℝ}

/-! ### The frequency minorant -/

/-- `(log a)' = ωw` where `q > 0`. -/
theorem hasDerivAt_log_af {s : ℝ} (hs : s ^ 2 < 1) (hq : 0 < qf c K s) :
    HasDerivAt (fun t => Real.log (af c K t)) (af c K s / (1 - s ^ 2) * wf c K s) s := by
  have ha := af_pos hs hq
  have ha2 := af_sq hs hq
  have hp : 0 < 1 - s ^ 2 := by linarith
  refine ((hasDerivAt_af hs hq).log ha.ne').congr_deriv ?_
  field_simp
  rw [ha2]; ring

/-! ### Counting from the centre -/

open Cvs.Prolate.EdgeCentreSign (evenSpec)

/-! ### The half-interval at `0 ≤ K ≤ 5`, `c ≥ 194` -/

/-! ### The top rung -/

open Cvs.Prolate.EvenRungsByIndex (lev IsLevelIdx)

end Cvs.Prolate.TopRungZeroSplitHalf
