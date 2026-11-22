import Mathlib
import Cvs.L2a.CleanBandDilation
import Cvs.L2a.CoreArmIdentity
import Cvs.L2a.DilationCornerSplit
import Cvs.L2a.FrameFloorJumpAbsorption
import Cvs.L2a.ReflectionFloor
import Cvs.Upstream.CosineTransformHalfLine
import Cvs.Upstream.QuinticSmoothStep

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The corner split and the `√N` floor for any step

For a monotone step `St` (`[0, 1]`-valued, `0` below `0`, `1` above `1`, `St u + St (1 − u) = 1`) the weights
`1 − St((x − m)/δ)`, `1 − St((X − x)/δ)` and their complement split `Dil` as in Cvs.L2a.DilationCornerSplit, the top weight is common at
integer `X`, and `ParametricFloorSqrtN`'s floor holds for these corners. For the quintic step of Cvs.Upstream.QuinticSmoothStep the weights are complex `C²`
weights, `1` with zero slope at the cut and `0` with zero slope at the far end, of norms `(181/462)δ`, `(10/7)/δ`, `(120/7)/δ³`.
-/

noncomputable section

open MeasureTheory Set Real Cvs.L2a.AngularProlateTailPositive Cvs.L2a.PositionTruncatedTail Cvs.Upstream.CosineTransformHalfLine Cvs.L2a.MirrorFloor Cvs.L2a.ReflectionFloor Cvs.Upstream.CosineTransformDilation Cvs.L2a.MirrorSplitDefect Cvs.L2a.CoreArmIdentity Cvs.L2a.FrameFloorJumpAbsorption Cvs.L2a.CleanBandDilation Cvs.L2a.DilationCornerSplit

namespace Cvs.L2a.CornerSplitSqrtFloor

local notation "μ₀" => (volume.restrict (Ioi (0 : ℝ)))
local notation "H₀" => Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))
local notation "μ₁" => (volume.restrict (Ioi (1 : ℝ)))

/-! ### Steps -/

/-- A step profile: measurable, monotone, valued in `[0, 1]`, `0` on `(−∞, 0]`, `1` on `[1, ∞)`,
`St u + St (1 − u) = 1`. -/
structure IsStep (St : ℝ → ℝ) : Prop where
  meas : Measurable St
  mono : Monotone St
  mem_Icc : ∀ u, St u ∈ Icc (0 : ℝ) 1
  zero_of_nonpos : ∀ u, u ≤ 0 → St u = 0
  one_of_one_le : ∀ u, 1 ≤ u → St u = 1
  add_one_sub : ∀ u, St u + St (1 - u) = 1

theorem isStep_S : IsStep Cvs.Upstream.QuinticSmoothStep.S where
  meas := Cvs.Upstream.QuinticSmoothStep.contDiff_S.continuous.measurable
  mono := monotone_of_hasDerivAt_nonneg Cvs.Upstream.QuinticSmoothStep.hasDerivAt_S fun u => (Cvs.Upstream.QuinticSmoothStep.dS_mem_Icc u).1
  mem_Icc := Cvs.Upstream.QuinticSmoothStep.S_mem_Icc
  zero_of_nonpos _ h := Cvs.Upstream.QuinticSmoothStep.S_of_nonpos h
  one_of_one_le _ h := Cvs.Upstream.QuinticSmoothStep.S_of_one_le h
  add_one_sub u := by rw [Cvs.Upstream.QuinticSmoothStep.S_one_sub]; ring

/-! ### The weights of a step -/

/-- The bottom weight `1 − St((x − m)/δ)`. -/
def wBotG (St : ℝ → ℝ) (δ m x : ℝ) : ℝ := 1 - St ((x - m) / δ)

/-- The top weight `1 − St((X − x)/δ)`. -/
def wTopG (St : ℝ → ℝ) (δ X x : ℝ) : ℝ := 1 - St ((X - x) / δ)

/-- The middle weight `1 − w_b − w_t`. -/
def wMidG (St : ℝ → ℝ) (δ X m x : ℝ) : ℝ := 1 - wBotG St δ m x - wTopG St δ X x

theorem measurable_wBotG {St : ℝ → ℝ} (hS : IsStep St) (δ m : ℝ) : Measurable fun x => wBotG St δ m x :=
  measurable_const.sub (hS.meas.comp ((measurable_id.sub_const m).div_const δ))

theorem measurable_wTopG {St : ℝ → ℝ} (hS : IsStep St) (δ X : ℝ) : Measurable fun x => wTopG St δ X x :=
  measurable_const.sub (hS.meas.comp ((measurable_const.sub measurable_id).div_const δ))

theorem measurable_wMidG {St : ℝ → ℝ} (hS : IsStep St) (δ X m : ℝ) :
    Measurable fun x => wMidG St δ X m x :=
  (measurable_const.sub (measurable_wBotG hS δ m)).sub (measurable_wTopG hS δ X)

theorem abs_wBotG_le_one {St : ℝ → ℝ} (hS : IsStep St) (δ m x : ℝ) : |wBotG St δ m x| ≤ 1 := by
  unfold wBotG
  have := hS.mem_Icc ((x - m) / δ)
  exact abs_le.2 ⟨by linarith [this.2], by linarith [this.1]⟩

theorem abs_wTopG_le_one {St : ℝ → ℝ} (hS : IsStep St) (δ X x : ℝ) : |wTopG St δ X x| ≤ 1 := by
  unfold wTopG
  have := hS.mem_Icc ((X - x) / δ)
  exact abs_le.2 ⟨by linarith [this.2], by linarith [this.1]⟩

theorem abs_wMidG_le_one {St : ℝ → ℝ} (hS : IsStep St) (δ X m x : ℝ) : |wMidG St δ X m x| ≤ 1 := by
  unfold wMidG wBotG wTopG
  have h1 := hS.mem_Icc ((x - m) / δ)
  have h2 := hS.mem_Icc ((X - x) / δ)
  exact abs_le.2 ⟨by linarith [h1.1, h2.1], by linarith [h1.2, h2.2]⟩

theorem wBotG_eq_zero {St : ℝ → ℝ} (hS : IsStep St) {δ m x : ℝ} (hδ : 0 < δ) (h : m + δ ≤ x) :
    wBotG St δ m x = 0 := by
  unfold wBotG
  rw [hS.one_of_one_le _ ((le_div_iff₀ hδ).2 (by rw [one_mul]; linarith)), sub_self]

theorem wTopG_eq_zero {St : ℝ → ℝ} (hS : IsStep St) {δ X x : ℝ} (hδ : 0 < δ) (h : x ≤ X - δ) :
    wTopG St δ X x = 0 := by
  unfold wTopG
  rw [hS.one_of_one_le _ ((le_div_iff₀ hδ).2 (by rw [one_mul]; linarith)), sub_self]

/-! ### The corner split -/

/-- **The corner split for any partition of unity** on the cuts. -/
theorem coreDil_eq_partition {c : ℝ} (hc : 0 < c) {Φ χ : ℝ → ℝ} {X : ℝ} (hX : 1 ≤ X)
    (hχX : ∀ x, X < x → χ x = 1) (hΦ : MemLp Φ 2 μ₁) {wb wm wt : ℕ → ℝ → ℝ}
    (hbm : ∀ m, Measurable (wb m)) (hmm : ∀ m, Measurable (wm m)) (htm : ∀ m, Measurable (wt m))
    (hb1 : ∀ m x, |wb m x| ≤ 1) (hm1 : ∀ m x, |wm m x| ≤ 1) (ht1 : ∀ m x, |wt m x| ≤ 1)
    (hsum : ∀ m x, wb m x + wm m x + wt m x = 1) {u aB aF e : H₀}
    (hu : (u : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioi 1).indicator (fun x => (1 - χ x) * Φ x) x : ℝ) : ℂ))
    (haB : (aB : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioc 1 X).indicator (fun x => χ x * Φ x) x : ℝ) : ℂ))
    (haF : (aF : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioi X).indicator Φ x : ℝ) : ℂ))
    (he : (e : ℝ → ℂ) =ᵐ[μ₀] fun x => ((dilSum Φ X x : ℝ) : ℂ)) :
    coreDil c Φ χ X
      = dilPart c Φ χ X wb + dilPart c Φ χ X wm + dilPart c Φ χ X wt
        + 2 * RCLike.re (inner ℂ (Uop hc (u + (aB + aF)) + (u + (aB + aF))) e) := by
  rw [coreDil_eq_dilate hc hX hχX hΦ hu haB haF he]
  congr 1
  unfold dilPart
  rw [← mul_add, ← mul_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmn : 1 ≤ m := by have := (Finset.mem_Icc.1 hm).1; omega
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hmn
  have hB := memLp_weight₀ (hbm m) (hb1 m) (memLp_cut hΦ X hmn)
  have hM := memLp_weight₀ (hmm m) (hm1 m) (memLp_cut hΦ X hmn)
  have hT := memLp_weight₀ (htm m) (ht1 m) (memLp_cut hΦ X hmn)
  have hψ : ∀ w : ℝ → ℝ, ∀ x, x ≤ 1 → w x * (Ioc (m : ℝ) X).indicator Φ x = 0 := fun w x hx => by
    have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hmn
    rw [indicator_of_notMem (fun h => by linarith [h.1]), mul_zero]
  have hg : ((memLp_cut hΦ X hmn).toLp _ : ℝ → ℂ)
      =ᵐ[μ₀] fun x => ((1 * (Ioc (m : ℝ) X).indicator Φ x : ℝ) : ℂ) :=
    (memLp_cut hΦ X hmn).coeFn_toLp.trans (ae_of_all _ fun x => by simp only [one_mul])
  have hsplit : (memLp_cut hΦ X hmn).toLp _ = hB.toLp _ + hM.toLp _ + hT.toLp _ := by
    refine Lp.ext ?_
    filter_upwards [(memLp_cut hΦ X hmn).coeFn_toLp, Lp.coeFn_add (hB.toLp _ + hM.toLp _) (hT.toLp _),
      Lp.coeFn_add (hB.toLp _) (hM.toLp _), hB.coeFn_toLp, hM.coeFn_toLp, hT.coeFn_toLp]
      with x h1 h2 h3 h4 h5 h6
    rw [h1, h2, Pi.add_apply, h3, Pi.add_apply, h4, h5, h6, ← Complex.ofReal_add, ← Complex.ofReal_add,
      ← add_mul, ← add_mul, hsum, one_mul]
  rw [← re_inner_Uop_dilU_eq hc hX hχX hu haF hm' hB.coeFn_toLp (hψ _),
    ← re_inner_Uop_dilU_eq hc hX hχX hu haF hm' hM.coeFn_toLp (hψ _),
    ← re_inner_Uop_dilU_eq hc hX hχX hu haF hm' hT.coeFn_toLp (hψ _),
    ← re_inner_Uop_dilU_eq hc hX hχX hu haF hm' hg (hψ _), ← map_add, ← map_add, ← inner_add_right,
    ← inner_add_right, hsplit]

/-- The bottom corner part of `Dil` for the step `St`. -/
def DbotG (St : ℝ → ℝ) (c : ℝ) (Φ χ : ℝ → ℝ) (X δ : ℝ) : ℝ := dilPart c Φ χ X fun m x => wBotG St δ m x

/-- The middle part of `Dil` for the step `St`. -/
def DmidG (St : ℝ → ℝ) (c : ℝ) (Φ χ : ℝ → ℝ) (X δ : ℝ) : ℝ := dilPart c Φ χ X fun m x => wMidG St δ X m x

/-- The top corner part of `Dil` for the step `St`. -/
def DtopG (St : ℝ → ℝ) (c : ℝ) (Φ χ : ℝ → ℝ) (X δ : ℝ) : ℝ := dilPart c Φ χ X fun _ x => wTopG St δ X x

/-- **Lemma 3 for any step**: `coreDil = Dbot + Dmid + Dtop + 2re⟨e₁, E⟩`. -/
theorem coreDil_eq_cornerG {St : ℝ → ℝ} (hS : IsStep St) {c : ℝ} (hc : 0 < c) {Φ χ : ℝ → ℝ} {X : ℝ}
    (hX : 1 ≤ X) (hχX : ∀ x, X < x → χ x = 1) (hΦ : MemLp Φ 2 μ₁) (δ : ℝ) {u aB aF e : H₀}
    (hu : (u : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioi 1).indicator (fun x => (1 - χ x) * Φ x) x : ℝ) : ℂ))
    (haB : (aB : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioc 1 X).indicator (fun x => χ x * Φ x) x : ℝ) : ℂ))
    (haF : (aF : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioi X).indicator Φ x : ℝ) : ℂ))
    (he : (e : ℝ → ℂ) =ᵐ[μ₀] fun x => ((dilSum Φ X x : ℝ) : ℂ)) :
    coreDil c Φ χ X
      = DbotG St c Φ χ X δ + DmidG St c Φ χ X δ + DtopG St c Φ χ X δ
        + 2 * RCLike.re (inner ℂ (Uop hc (u + (aB + aF)) + (u + (aB + aF))) e) :=
  coreDil_eq_partition hc hX hχX hΦ (fun m => measurable_wBotG hS δ m)
    (fun m => measurable_wMidG hS δ X m) (fun _ => measurable_wTopG hS δ X)
    (fun m x => abs_wBotG_le_one hS δ m x) (fun m x => abs_wMidG_le_one hS δ X m x)
    (fun _ x => abs_wTopG_le_one hS δ X x) (fun m x => by unfold wMidG; ring) hu haB haF he

/-! ### The floor through `√N` -/

/-! ### The quintic weights -/

/-- `w_b` for the quintic step, as a complex weight. -/
def wbC (δ m : ℝ) (x : ℝ) : ℂ := ((wBotG Cvs.Upstream.QuinticSmoothStep.S δ m x : ℝ) : ℂ)

/-- `w_b′ = −S′((x − m)/δ)/δ`. -/
def wbC₁ (δ m : ℝ) (x : ℝ) : ℂ := ((-(Cvs.Upstream.QuinticSmoothStep.dS ((x - m) / δ) / δ) : ℝ) : ℂ)

/-- `w_b″ = −S″((x − m)/δ)/δ²`. -/
def wbC₂ (δ m : ℝ) (x : ℝ) : ℂ := ((-(Cvs.Upstream.QuinticSmoothStep.d2S ((x - m) / δ) / δ ^ 2) : ℝ) : ℂ)

/-- `w_t` for the quintic step, as a complex weight. -/
def wtC (δ X : ℝ) (x : ℝ) : ℂ := ((wTopG Cvs.Upstream.QuinticSmoothStep.S δ X x : ℝ) : ℂ)

/-- `w_t′ = S′((X − x)/δ)/δ`. -/
def wtC₁ (δ X : ℝ) (x : ℝ) : ℂ := ((Cvs.Upstream.QuinticSmoothStep.dS ((X - x) / δ) / δ : ℝ) : ℂ)

/-- `w_t″ = −S″((X − x)/δ)/δ²`. -/
def wtC₂ (δ X : ℝ) (x : ℝ) : ℂ := ((-(Cvs.Upstream.QuinticSmoothStep.d2S ((X - x) / δ) / δ ^ 2) : ℝ) : ℂ)

theorem hasDerivAt_wbC (δ m x : ℝ) : HasDerivAt (wbC δ m) (wbC₁ δ m x) x := by
  have h := ((Cvs.Upstream.QuinticSmoothStep.hasDerivAt_S ((x - m) / δ)).comp x
    (((hasDerivAt_id x).sub_const m).div_const δ)).const_sub 1
  have h' := h.ofReal_comp
  unfold wbC wbC₁ wBotG
  convert h' using 2
  simp only [id, Function.comp_def]
  ring

theorem hasDerivAt_wbC₁ (δ m x : ℝ) : HasDerivAt (wbC₁ δ m) (wbC₂ δ m x) x := by
  have h : HasDerivAt (fun y => -(Cvs.Upstream.QuinticSmoothStep.dS ((y - m) / δ) / δ))
      (-(Cvs.Upstream.QuinticSmoothStep.d2S ((x - m) / δ) * (1 / δ) / δ)) x :=
    (((Cvs.Upstream.QuinticSmoothStep.hasDerivAt_dS ((x - m) / δ)).comp x
      (((hasDerivAt_id x).sub_const m).div_const δ)).div_const δ).neg
  have h' := h.ofReal_comp
  unfold wbC₁ wbC₂
  convert h' using 2
  ring

theorem continuous_wbC₂ (δ m : ℝ) : Continuous (wbC₂ δ m) := by
  unfold wbC₂
  exact Complex.continuous_ofReal.comp
    ((Cvs.Upstream.QuinticSmoothStep.continuous_d2S.comp ((continuous_id.sub continuous_const).div_const δ)).div_const _).neg

theorem hasDerivAt_wtC (δ X x : ℝ) : HasDerivAt (wtC δ X) (wtC₁ δ X x) x := by
  have h := ((Cvs.Upstream.QuinticSmoothStep.hasDerivAt_S ((X - x) / δ)).comp x
    (((hasDerivAt_id x).const_sub X).div_const δ)).const_sub 1
  have h' := h.ofReal_comp
  unfold wtC wtC₁ wTopG
  convert h' using 2
  simp only [id, Function.comp_def]
  ring

theorem hasDerivAt_wtC₁ (δ X x : ℝ) : HasDerivAt (wtC₁ δ X) (wtC₂ δ X x) x := by
  have h := ((Cvs.Upstream.QuinticSmoothStep.hasDerivAt_dS ((X - x) / δ)).comp x
    (((hasDerivAt_id x).const_sub X).div_const δ)).div_const δ
  have h' := h.ofReal_comp
  unfold wtC₁ wtC₂
  convert h' using 2
  simp only [id, Function.comp_def]
  ring

theorem continuous_wtC₂ (δ X : ℝ) : Continuous (wtC₂ δ X) := by
  unfold wtC₂
  exact Complex.continuous_ofReal.comp
    ((Cvs.Upstream.QuinticSmoothStep.continuous_d2S.comp ((continuous_const.sub continuous_id).div_const δ)).div_const _).neg

/-- At the cut `w_b = 1`, `w_b′ = 0`; at the far end `m + δ` both vanish. -/
theorem wbC_cut_far {δ : ℝ} (hδ : δ ≠ 0) (m : ℝ) :
    wbC δ m m = 1 ∧ wbC₁ δ m m = 0 ∧ wbC δ m (m + δ) = 0 ∧ wbC₁ δ m (m + δ) = 0 := by
  simp only [wbC, wbC₁, wBotG, sub_self, zero_div, add_sub_cancel_left, div_self hδ, Cvs.Upstream.QuinticSmoothStep.S_zero,
    Cvs.Upstream.QuinticSmoothStep.dS_zero, Cvs.Upstream.QuinticSmoothStep.S_one, Cvs.Upstream.QuinticSmoothStep.dS_one]
  norm_num

/-- At the cut `w_t = 1`, `w_t′ = 0`; at the far end `X − δ` both vanish. -/
theorem wtC_cut_far {δ : ℝ} (hδ : δ ≠ 0) (X : ℝ) :
    wtC δ X X = 1 ∧ wtC₁ δ X X = 0 ∧ wtC δ X (X - δ) = 0 ∧ wtC₁ δ X (X - δ) = 0 := by
  simp only [wtC, wtC₁, wTopG, sub_self, zero_div, sub_sub_cancel, div_self hδ, Cvs.Upstream.QuinticSmoothStep.S_zero,
    Cvs.Upstream.QuinticSmoothStep.dS_zero, Cvs.Upstream.QuinticSmoothStep.S_one, Cvs.Upstream.QuinticSmoothStep.dS_one]
  norm_num

end Cvs.L2a.CornerSplitSqrtFloor
