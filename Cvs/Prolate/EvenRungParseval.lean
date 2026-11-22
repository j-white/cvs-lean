import Mathlib
import Cvs.Prolate.AngularBesselInequality
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.EvenRungsComplete
import Cvs.Prolate.SincTopIsRung
import Cvs.Prolate.SlepianEvenOrdering
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowCutBoundedBridge
import Cvs.WeilForm.WindowOrthogonalComplement
import Cvs.WeilForm.WindowRepresentative

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Parseval over the even rungs

An orthonormal family of even continuous functions on `[−1, 1]` whose window classes have trivial
orthogonal complement gives a Hilbert basis of `L²(0, 1]`, hence Parseval for even continuous `f`.
For `c ≠ 0` the rungs `rung c k` are such a family.
-/

noncomputable section

open Real Set MeasureTheory Filter
open scoped Interval

namespace Cvs.Prolate.EvenRungParseval
open Cvs.ZeroCounting

open Cvs.WeilForm.WeilFormOnWindowL2 (window)
open Cvs.Prolate.SincTopIsRung (cutCls clampExt wCls compl continuous_clampExt)
open Cvs.Prolate.EvenRungsByIndex (IsLevelIdx rung rung_spec lev)

/-! ### Window classes of even continuous functions -/

/-- The class of `1_{(0,1]} f` for `f` continuous on `[−1, 1]`. -/
def evCls {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1) 1)) : window 1 :=
  cutCls (continuous_clampExt hf)

/-- The class `evCls` is represented by `1_{(0,1]} f`. -/
theorem rep_evCls {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1) 1)) :
    Cvs.WeilForm.WindowRepresentative.rep (evCls hf) =ᵐ[volume] Cvs.WeilForm.WindowCutBoundedBridge.cut 1 f :=
  Cvs.Prolate.SincTopIsRung.rep_wCls (w := fun _ : Unit => f) (fun _ => hf) ()

/-- **Inner products of even classes**: `⟪f, g⟫ = ½ ∫_{−1}^{1} f g` for even continuous `f, g`. -/
theorem inner_evCls {f g : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1) 1))
    (hfe : ∀ s ∈ Icc (-1 : ℝ) 1, f (-s) = f s) (hg : ContinuousOn g (Icc (-1) 1))
    (hge : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) :
    (inner ℝ (evCls hf) (evCls hg) : ℝ) = (1 / 2) * ∫ s in (-1 : ℝ)..1, f s * g s := by
  rw [Cvs.Prolate.SincTopIsRung.inner_cut_classes (rep_evCls hf) (rep_evCls hg),
    Cvs.Prolate.SlepianEvenOrdering.integral_even_fold (F := fun s => f s * g s) (hf.mul hg)
      (fun s hs => by
        have hs' : s ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hs.1], hs.2⟩
        rw [hfe s hs', hge s hs'])]
  ring

/-! ### A Hilbert basis from a complete orthonormal even family -/

section Basis

variable {ι : Type*} {w : ι → ℝ → ℝ}

/-- The scaled classes `√2 · w i` in `L²(0, 1]`. -/
def basisVec (hwc : ∀ i, ContinuousOn (w i) (Icc (-1) 1)) (i : ι) : window 1 :=
  √2 • wCls hwc i

/-- `⟪√2 · w i, f⟫ = (√2/2) ∫_{−1}^{1} w i · f` for even continuous `f`. -/
theorem inner_basisVec_left (hwc : ∀ i, ContinuousOn (w i) (Icc (-1) 1))
    (hwe : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, w i (-s) = w i s) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1) 1)) (hfe : ∀ s ∈ Icc (-1 : ℝ) 1, f (-s) = f s) (i : ι) :
    (inner ℝ (basisVec hwc i) (evCls hf) : ℝ) = √2 / 2 * ∫ s in (-1 : ℝ)..1, w i s * f s := by
  rw [basisVec, Cvs.Prolate.SincTopIsRung.inner_smul_left']
  rw [show wCls hwc i = evCls (hwc i) from rfl, inner_evCls (hwc i) (hwe i) hf hfe]
  ring

/-- `⟪f, √2 · w i⟫ = (√2/2) ∫_{−1}^{1} f · w i` for even continuous `f`. -/
theorem inner_basisVec_right (hwc : ∀ i, ContinuousOn (w i) (Icc (-1) 1))
    (hwe : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, w i (-s) = w i s) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1) 1)) (hfe : ∀ s ∈ Icc (-1 : ℝ) 1, f (-s) = f s) (i : ι) :
    (inner ℝ (evCls hf) (basisVec hwc i) : ℝ) = √2 / 2 * ∫ s in (-1 : ℝ)..1, f s * w i s := by
  rw [real_inner_comm, inner_basisVec_left hwc hwe hf hfe]
  simp_rw [mul_comm (w i _)]

/-- The scaled classes are orthonormal when the `w i` are orthonormal on `[−1, 1]`. -/
theorem orthonormal_basisVec (hwc : ∀ i, ContinuousOn (w i) (Icc (-1) 1))
    (hwe : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, w i (-s) = w i s)
    (hnorm : ∀ i, ∫ s in (-1 : ℝ)..1, w i s ^ 2 = 1)
    (horth : Pairwise fun i j => ∫ s in (-1 : ℝ)..1, w i s * w j s = 0) :
    Orthonormal ℝ (basisVec hwc) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [basisVec, basisVec, Cvs.Prolate.SincTopIsRung.inner_smul_left',
    Cvs.Prolate.SincTopIsRung.inner_smul_right', show wCls hwc i = evCls (hwc i) from rfl,
    show wCls hwc j = evCls (hwc j) from rfl, inner_evCls (hwc i) (hwe i) (hwc j) (hwe j)]
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    have hn : ∫ s in (-1 : ℝ)..1, w i s * w i s = 1 := by simpa [sq] using hnorm i
    rw [hn]
    linear_combination (1 / 2 : ℝ) * h2
  · rw [if_neg hij, horth hij]
    ring

/-- The scaled classes span a subspace with trivial orthogonal complement when `compl = ⊥`. -/
theorem orthogonal_span_basisVec (hwc : ∀ i, ContinuousOn (w i) (Icc (-1) 1))
    (hcompl : compl hwc = ⊥) :
    (Submodule.span ℝ (Set.range (basisVec hwc)))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  have hv' : v ∈ compl hwc := by
    rw [Cvs.Prolate.SincTopIsRung.mem_compl]
    intro i
    have h := Submodule.inner_right_of_mem_orthogonal
      (Submodule.subset_span ⟨i, rfl⟩ :
        basisVec hwc i ∈ Submodule.span ℝ (Set.range (basisVec hwc)))
      hv
    rw [basisVec, Cvs.Prolate.SincTopIsRung.inner_smul_left'] at h
    exact (mul_eq_zero.1 h).resolve_left (by positivity)
  rw [hcompl] at hv'
  exact (Submodule.mem_bot ℝ).1 hv'

/-- **The Hilbert basis** of `L²(0, 1]` given by a complete orthonormal even family. -/
def hilbertBasis (hwc : ∀ i, ContinuousOn (w i) (Icc (-1) 1))
    (hwe : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, w i (-s) = w i s)
    (hnorm : ∀ i, ∫ s in (-1 : ℝ)..1, w i s ^ 2 = 1)
    (horth : Pairwise fun i j => ∫ s in (-1 : ℝ)..1, w i s * w j s = 0)
    (hcompl : compl hwc = ⊥) : HilbertBasis ι ℝ (window 1) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_basisVec hwc hwe hnorm horth)
    (orthogonal_span_basisVec hwc hcompl)

/-- The vectors of `hilbertBasis` are the scaled classes. -/
theorem coe_hilbertBasis (hwc : ∀ i, ContinuousOn (w i) (Icc (-1) 1))
    (hwe : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, w i (-s) = w i s)
    (hnorm : ∀ i, ∫ s in (-1 : ℝ)..1, w i s ^ 2 = 1)
    (horth : Pairwise fun i j => ∫ s in (-1 : ℝ)..1, w i s * w j s = 0)
    (hcompl : compl hwc = ⊥) :
    ⇑(hilbertBasis hwc hwe hnorm horth hcompl) = basisVec hwc :=
  HilbertBasis.coe_mkOfOrthogonalEqBot _ _

/-- **Parseval, bilinear form**: `Σᵢ (∫ f wᵢ)(∫ wᵢ g) = ∫_{−1}^{1} f g` for even continuous
`f, g`. -/
theorem hasSum_integral_mul (hwc : ∀ i, ContinuousOn (w i) (Icc (-1) 1))
    (hwe : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, w i (-s) = w i s)
    (hnorm : ∀ i, ∫ s in (-1 : ℝ)..1, w i s ^ 2 = 1)
    (horth : Pairwise fun i j => ∫ s in (-1 : ℝ)..1, w i s * w j s = 0)
    (hcompl : compl hwc = ⊥) {f g : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1) 1))
    (hfe : ∀ s ∈ Icc (-1 : ℝ) 1, f (-s) = f s) (hg : ContinuousOn g (Icc (-1) 1))
    (hge : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) :
    HasSum (fun i => (∫ s in (-1 : ℝ)..1, f s * w i s) * ∫ s in (-1 : ℝ)..1, w i s * g s)
      (∫ s in (-1 : ℝ)..1, f s * g s) := by
  have h := (hilbertBasis hwc hwe hnorm horth hcompl).hasSum_inner_mul_inner (evCls hf) (evCls hg)
  rw [coe_hilbertBasis, inner_evCls hf hfe hg hge] at h
  simp_rw [inner_basisVec_right hwc hwe hf hfe, inner_basisVec_left hwc hwe hg hge] at h
  have key : ∀ a b : ℝ, √2 / 2 * a * (√2 / 2 * b) = 1 / 2 * (a * b) := fun a b => by
    have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
    linear_combination (a * b / 4) * h2
  simp_rw [key] at h
  exact (hasSum_mul_left_iff (by norm_num : (1 / 2 : ℝ) ≠ 0)).1 h

/-- **Parseval**: `Σᵢ (∫ f wᵢ)² = ∫_{−1}^{1} f²` for even continuous `f`. -/
theorem hasSum_sq_integral_mul (hwc : ∀ i, ContinuousOn (w i) (Icc (-1) 1))
    (hwe : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, w i (-s) = w i s)
    (hnorm : ∀ i, ∫ s in (-1 : ℝ)..1, w i s ^ 2 = 1)
    (horth : Pairwise fun i j => ∫ s in (-1 : ℝ)..1, w i s * w j s = 0)
    (hcompl : compl hwc = ⊥) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1) 1))
    (hfe : ∀ s ∈ Icc (-1 : ℝ) 1, f (-s) = f s) :
    HasSum (fun i => (∫ s in (-1 : ℝ)..1, f s * w i s) ^ 2) (∫ s in (-1 : ℝ)..1, f s ^ 2) := by
  have h := hasSum_integral_mul hwc hwe hnorm horth hcompl hf hfe hf hfe
  simp_rw [mul_comm (w _ _) (f _)] at h
  simpa only [sq] using h

end Basis

/-! ### The even rungs -/

/-- The level indices of `c`, which index the even rungs. -/
abbrev LevelIdx (c : ℝ) : Type := {k : ℕ // ∃ χ, IsLevelIdx c k χ}

/-- **Distinct even rungs are orthogonal** on `[−1, 1]`. -/
theorem integral_rung_mul_rung {c : ℝ} {k j : LevelIdx c} (hkj : k ≠ j) :
    ∫ s in (-1 : ℝ)..1, rung c k s * rung c j s = 0 := by
  obtain ⟨hk, hk₁, -, hkang, -, -⟩ := rung_spec k.2
  obtain ⟨hj, hj₁, -, hjang, -, -⟩ := rung_spec j.2
  have hne : lev c k ≠ lev c j := by
    have hkj' : (k : ℕ) ≠ j := fun h => hkj (Subtype.ext h)
    rcases lt_or_gt_of_ne hkj' with h | h
    · exact (Cvs.Prolate.EvenRungsByIndex.lev_lt j.2 h).ne
    · exact (Cvs.Prolate.EvenRungsByIndex.lev_lt k.2 h).ne'
  exact Cvs.Prolate.AngularBesselInequality.integral_mul_eq_zero hk hk₁ hkang hj hj₁ hjang hne

/-- **The Hilbert basis of even rungs** of `L²(0, 1]` for `c ≠ 0`: the classes `√2 · rung c k`. -/
def rungBasis {c : ℝ} (hc : c ≠ 0) : HilbertBasis (LevelIdx c) ℝ (window 1) :=
  hilbertBasis (fun k => Cvs.Prolate.EvenRungsByIndex.continuousOn_rung k.2)
    (fun k => (rung_spec k.2).2.2.2.2.1) (fun k => (rung_spec k.2).2.2.2.2.2)
    (fun _ _ hkj => integral_rung_mul_rung hkj) (Cvs.Prolate.EvenRungsComplete.compl_rungs_eq_bot hc)

/-- **Parseval over the even rungs, bilinear form**, for even continuous `f, g` and `c ≠ 0`. -/
theorem hasSum_integral_mul_rung {c : ℝ} (hc : c ≠ 0) {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1) 1)) (hfe : ∀ s ∈ Icc (-1 : ℝ) 1, f (-s) = f s)
    (hg : ContinuousOn g (Icc (-1) 1)) (hge : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) :
    HasSum (fun k : LevelIdx c =>
        (∫ s in (-1 : ℝ)..1, f s * rung c k s) * ∫ s in (-1 : ℝ)..1, rung c k s * g s)
      (∫ s in (-1 : ℝ)..1, f s * g s) :=
  hasSum_integral_mul (w := fun k : LevelIdx c => rung c k)
    (fun k => Cvs.Prolate.EvenRungsByIndex.continuousOn_rung k.2)
    (fun k => (rung_spec k.2).2.2.2.2.1) (fun k => (rung_spec k.2).2.2.2.2.2)
    (fun _ _ hkj => integral_rung_mul_rung hkj) (Cvs.Prolate.EvenRungsComplete.compl_rungs_eq_bot hc)
    hf hfe hg hge

/-- **Parseval over the even rungs**: `Σₖ (∫_{−1}^{1} f · rung c k)² = ∫_{−1}^{1} f²` for even
continuous `f` and `c ≠ 0`. -/
theorem hasSum_sq_integral_mul_rung {c : ℝ} (hc : c ≠ 0) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1) 1)) (hfe : ∀ s ∈ Icc (-1 : ℝ) 1, f (-s) = f s) :
    HasSum (fun k : LevelIdx c => (∫ s in (-1 : ℝ)..1, f s * rung c k s) ^ 2)
      (∫ s in (-1 : ℝ)..1, f s ^ 2) :=
  hasSum_sq_integral_mul (w := fun k : LevelIdx c => rung c k)
    (fun k => Cvs.Prolate.EvenRungsByIndex.continuousOn_rung k.2)
    (fun k => (rung_spec k.2).2.2.2.2.1) (fun k => (rung_spec k.2).2.2.2.2.2)
    (fun _ _ hkj => integral_rung_mul_rung hkj) (Cvs.Prolate.EvenRungsComplete.compl_rungs_eq_bot hc)
    hf hfe

end Cvs.Prolate.EvenRungParseval
