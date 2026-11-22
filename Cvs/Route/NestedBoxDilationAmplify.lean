import Mathlib
import Cvs.Finite.WindowMatrixSymbolKernel
import Cvs.Route.DilationLatticeCriterion
import Cvs.Route.NestedBoxInduction
import Cvs.Route.OneCellBeforeFirstPrime
import Cvs.Route.OneCellLaplaceTransform
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Dilation amplification on the nested boxes
One negative direction of the box form forces, for all large `N`, a test with form `≤ −κN` times its squared
coefficient norm: average its exact `log k`-translates, `k ∈ [qs, qs + s)`. Hence `RH` iff some lower bound
`qf N c ≥ −r N ‖c‖²` with `r N / N → 0` holds frequently.
-/

noncomputable section

open Real Finset Filter Topology

namespace Cvs.Route.NestedBoxDilationAmplify
open Cvs.ZeroCounting

open Cvs.Route.OneCellLaplaceTransform (G ladder primeSide)
open Cvs.Finite.WindowMatrixSymbolKernel (bk bk_pos)
open Cvs.Route.NestedBoxInduction (K qf)

/-! ### Continuity of `G` on `[0, ∞)` -/

theorem ladder_zero : ladder 0 = 0 := by
  unfold ladder; simp

theorem tendsto_ladder_aux : Tendsto (fun L : ℝ => ∑' k : ℕ, (1 - Real.exp (-(bk k * L))) / bk k ^ 2) (𝓝[≥] 0)
    (𝓝 (∑' k : ℕ, (1 - Real.exp (-(bk k * 0))) / bk k ^ 2)) := by
  refine tendsto_tsum_of_dominated_convergence (bound := fun k => 1 / bk k ^ 2)
    Cvs.Route.OneCellLaplaceTransform.summable_inv_bk_sq (fun k => ?_) ?_
  · have hc : Continuous fun L : ℝ => (1 - Real.exp (-(bk k * L))) / bk k ^ 2 := by fun_prop
    exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with L hL k
    have hL : (0:ℝ) ≤ L := hL
    have hb := bk_pos k
    have h1 : Real.exp (-(bk k * L)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have h2 : 0 < Real.exp (-(bk k * L)) := Real.exp_pos _
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by linarith) (sq_nonneg _))]
    exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)

theorem tendsto_ladder_zero : Tendsto ladder (𝓝[≥] 0) (𝓝 0) := by
  have h : Tendsto ladder (𝓝[≥] 0) (𝓝 (ladder 0)) := by
    unfold ladder
    exact tendsto_ladder_aux
  rwa [ladder_zero] at h

theorem G_zero : G 0 = 0 := Cvs.Route.DilationLatticeCriterion.G_zero

theorem tendsto_G_zero : Tendsto G (𝓝[≥] 0) (𝓝 0) := by
  have hev : (fun L => 16 * (Real.cosh (L / 2) - 1) + Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * L + 2 * ladder L)
      =ᶠ[𝓝[≥] 0] G := by
    have : Set.Ico (0:ℝ) (Real.log 2) ∈ 𝓝[≥] (0:ℝ) :=
      Ico_mem_nhdsGE (Real.log_pos (by norm_num))
    filter_upwards [this] with L hL
    exact (Cvs.Route.OneCellBeforeFirstPrime.G_eq hL.2.le).symm
  refine Tendsto.congr' hev ?_
  have h1 : Tendsto (fun L : ℝ => 16 * (Real.cosh (L / 2) - 1) + Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * L)
      (𝓝[≥] 0) (𝓝 (16 * (Real.cosh (0 / 2) - 1) + Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * 0)) :=
    ((by fun_prop : Continuous fun L : ℝ => 16 * (Real.cosh (L / 2) - 1)
      + Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * L).tendsto 0).mono_left nhdsWithin_le_nhds
  have h2 := (h1.add (tendsto_ladder_zero.const_mul 2))
  simpa using h2

/-- `t ↦ G(|t + a|)` is continuous at `0`. -/
theorem continuousAt_G_abs (a : ℝ) : ContinuousAt (fun t => G |t + a|) 0 := by
  rcases eq_or_ne a 0 with ha | ha
  · subst ha
    simp only [add_zero, ContinuousAt, abs_zero, G_zero]
    have habs : Tendsto (fun t : ℝ => |t|) (𝓝 0) (𝓝[≥] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨by simpa using (continuous_abs.tendsto (0:ℝ)),
        Eventually.of_forall fun t => abs_nonneg t⟩
    exact tendsto_G_zero.comp habs
  · have hpos : 0 < |0 + a| := by rw [zero_add]; exact abs_pos.2 ha
    exact ContinuousAt.comp (f := fun t : ℝ => |t + a|) (x := 0) (Cvs.Route.DilationLatticeCriterion.continuousAt_G hpos)
      (by fun_prop)

/-! ### The zero-sum form -/

/-- The box form over a finite set of indices. -/
def QS (S : Finset ℕ) (d : ℕ → ℝ) : ℝ := ∑ m ∈ S, ∑ n ∈ S, d m * d n * K (Real.log m) (Real.log n)

/-- The dilation energy: `−½ ∑ d_m d_n G(|log m − log n|)`. -/
def E (S : Finset ℕ) (d : ℕ → ℝ) : ℝ :=
  -(1 / 2) * ∑ m ∈ S, ∑ n ∈ S, d m * d n * G |Real.log m - Real.log n|

theorem QS_eq_E {S : Finset ℕ} {d : ℕ → ℝ} (hd : ∑ n ∈ S, d n = 0) : QS S d = E S d := by
  unfold QS E K
  have h : ∀ m ∈ S, ∑ n ∈ S, d m * d n * ((G (Real.log m) + G (Real.log n) - G |Real.log m - Real.log n|) / 2)
      = (1 / 2) * (d m * G (Real.log m)) * (∑ n ∈ S, d n) + (1 / 2) * d m * (∑ n ∈ S, d n * G (Real.log n))
        - (1 / 2) * ∑ n ∈ S, d m * d n * G |Real.log m - Real.log n| := by
    intro m _
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => by ring
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, Finset.sum_add_distrib, hd]
  simp only [mul_zero, Finset.sum_const_zero, zero_add]
  rw [← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum, hd]
  ring

theorem K_zero_left {y : ℝ} (hy : 0 ≤ y) : K 0 y = 0 := by
  unfold K; rw [zero_sub, abs_neg, abs_of_nonneg hy, G_zero]; ring

theorem K_zero_right {x : ℝ} (hx : 0 ≤ x) : K x 0 = 0 := by
  unfold K; rw [sub_zero, abs_of_nonneg hx, G_zero]; ring

/-- Adding the zero box `n = 1` changes nothing. -/
theorem QS_Icc_one (M : ℕ) (d : ℕ → ℝ) : QS (Icc 1 M) d = QS (Icc 2 M) d := by
  unfold QS
  have hsub : Icc 2 M ⊆ Icc 1 M := Finset.Icc_subset_Icc (by norm_num) le_rfl
  have hone : ∀ k ∈ Icc 1 M, k ∉ Icc 2 M → k = 1 := by
    intro k hk hk'; simp only [Finset.mem_Icc] at hk hk'; omega
  have inner : ∀ m, ∑ n ∈ Icc 1 M, d m * d n * K (Real.log m) (Real.log n)
      = ∑ n ∈ Icc 2 M, d m * d n * K (Real.log m) (Real.log n) := fun m =>
    (Finset.sum_subset hsub fun n hn hn' => by
      rw [hone n hn hn', Nat.cast_one, Real.log_one, K_zero_right (Real.log_natCast_nonneg m)]; ring).symm
  rw [Finset.sum_congr rfl fun m _ => inner m]
  exact (Finset.sum_subset hsub fun m hm hm' => by
    rw [hone m hm hm']
    refine Finset.sum_eq_zero fun n _ => ?_
    rw [Nat.cast_one, Real.log_one, K_zero_left (Real.log_natCast_nonneg n)]; ring).symm

/-! ### Pushing weights forward along a position map -/

/-- The coefficient vector of weights `a i` placed at positions `p i`. -/
def push (A : Finset (ℕ × ℕ)) (p : ℕ × ℕ → ℕ) (a : ℕ × ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ A, if p i = j then a i else 0

theorem sum_push {S : Finset ℕ} {A : Finset (ℕ × ℕ)} {p : ℕ × ℕ → ℕ} (a : ℕ × ℕ → ℝ)
    (hp : ∀ i ∈ A, p i ∈ S) (h : ℕ → ℝ) :
    ∑ j ∈ S, push A p a j * h j = ∑ i ∈ A, a i * h (p i) := by
  unfold push
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp [hp i hi]

theorem double_push {S : Finset ℕ} {A : Finset (ℕ × ℕ)} {p : ℕ × ℕ → ℕ} (a : ℕ × ℕ → ℝ)
    (hp : ∀ i ∈ A, p i ∈ S) (Φ : ℕ → ℕ → ℝ) :
    ∑ j ∈ S, ∑ j' ∈ S, push A p a j * push A p a j' * Φ j j'
      = ∑ i ∈ A, ∑ i' ∈ A, a i * a i' * Φ (p i) (p i') := by
  have h1 : ∀ j, ∑ j' ∈ S, push A p a j * push A p a j' * Φ j j'
      = push A p a j * ∑ i' ∈ A, a i' * Φ j (p i') := by
    intro j
    rw [← sum_push a hp (Φ j), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j' _ => by ring
  simp_rw [h1]
  rw [sum_push a hp (fun j => ∑ i' ∈ A, a i' * Φ j (p i'))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i' _ => by ring

theorem sq_sum_of_disjoint {I : Finset ℕ} {f : ℕ → ℝ} (h : ∀ k ∈ I, ∀ l ∈ I, k ≠ l → f k * f l = 0) :
    (∑ k ∈ I, f k) ^ 2 = ∑ k ∈ I, f k ^ 2 := by
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.sum_eq_single_of_mem k hk (fun l hl hlk => h k hk l hl (Ne.symm hlk)), sq]

/-! ### The averaged test -/

section avg

variable (M q s : ℕ) (d : ℕ → ℝ)

/-- The translates `k ∈ [qs, qs + s)`. -/
def I : Finset ℕ := Finset.Ico (q * s) (q * s + s)

def A : Finset (ℕ × ℕ) := Finset.Icc 1 M ×ˢ I q s

def pos : ℕ × ℕ → ℕ := fun i => i.1 * i.2

def wt : ℕ × ℕ → ℝ := fun i => d i.1 / s

/-- The averaged coefficient vector: `v_j = (1/s) ∑_{n k = j} d_n`. -/
def v : ℕ → ℝ := push (A M q s) pos (wt s d)

/-- `F(t) = −½ ∑ d_m d_n G(|t + log m − log n|)`. -/
def F (t : ℝ) : ℝ :=
  -(1 / 2) * ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M, d m * d n * G |t + (Real.log m - Real.log n)|

theorem card_I : (I q s).card = s := by unfold I; simp

theorem pos_mem {N : ℕ} (hq : 1 ≤ q) (hs : 1 ≤ s) (hN : M * (q + 1) * s ≤ N) :
    ∀ i ∈ A M q s, pos i ∈ Finset.Icc 1 N := by
  intro i hi
  simp only [A, I, Finset.mem_product, Finset.mem_Icc, Finset.mem_Ico] at hi
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hi
  simp only [pos, Finset.mem_Icc]
  constructor
  · exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by nlinarith))
  · calc i.1 * i.2 ≤ M * (q * s + s) := Nat.mul_le_mul h2 h4.le
      _ = M * (q + 1) * s := by ring
      _ ≤ N := hN

theorem sum_v {N : ℕ} (hq : 1 ≤ q) (hs : 1 ≤ s) (hN : M * (q + 1) * s ≤ N)
    (hd : ∑ n ∈ Finset.Icc 1 M, d n = 0) : ∑ j ∈ Finset.Icc 1 N, v M q s d j = 0 := by
  have h := sum_push (S := Finset.Icc 1 N) (wt s d) (pos_mem M q s hq hs hN) (fun _ => 1)
  simp only [mul_one] at h
  unfold v; rw [h]
  unfold A wt
  rw [Finset.sum_product]
  simp only [Finset.sum_const, card_I, nsmul_eq_mul]
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast (by omega : s ≠ 0)
  rw [show (∑ x ∈ Finset.Icc 1 M, (s : ℝ) * (d x / s)) = ∑ x ∈ Finset.Icc 1 M, d x from
    Finset.sum_congr rfl fun x _ => by field_simp, hd]

theorem reorder4 (X Y : Finset ℕ) (f : ℕ → ℕ → ℕ → ℕ → ℝ) :
    ∑ m ∈ X, ∑ k ∈ Y, ∑ n ∈ X, ∑ l ∈ Y, f m k n l = ∑ k ∈ Y, ∑ l ∈ Y, ∑ m ∈ X, ∑ n ∈ X, f m k n l := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_congr rfl fun m _ => Finset.sum_comm, Finset.sum_comm]

theorem E_v {N : ℕ} (hq : 1 ≤ q) (hs : 1 ≤ s) (hN : M * (q + 1) * s ≤ N) :
    E (Finset.Icc 1 N) (v M q s d)
      = (1 / (s : ℝ) ^ 2) * ∑ k ∈ I q s, ∑ l ∈ I q s, F M d (Real.log k - Real.log l) := by
  have hlog : ∀ n k : ℕ, 1 ≤ n → 1 ≤ k → Real.log ((n * k : ℕ) : ℝ) = Real.log n + Real.log k := by
    intro n k hn hk
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast (by omega : n ≠ 0)) (by exact_mod_cast (by omega : k ≠ 0))]
  have hkI : ∀ k ∈ I q s, 1 ≤ k := by
    intro k hk; simp only [I, Finset.mem_Ico] at hk; nlinarith
  unfold E v
  rw [double_push (wt s d) (pos_mem M q s hq hs hN) (fun j j' => G |Real.log j - Real.log j'|)]
  unfold A wt pos F
  rw [Finset.sum_product]
  simp_rw [Finset.sum_product]
  rw [reorder4]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun l hl =>
    Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun n hn => ?_
  simp only [Finset.mem_Icc] at hm hn
  rw [hlog m k hm.1 (hkI k hk), hlog n l hn.1 (hkI l hl)]
  rw [show Real.log m + Real.log k - (Real.log n + Real.log l)
      = Real.log k - Real.log l + (Real.log m - Real.log n) by ring]
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast (by omega : s ≠ 0)
  field_simp

theorem sum_v_sq {N : ℕ} (hq : 1 ≤ q) (hs : 1 ≤ s) (hN : M * (q + 1) * s ≤ N) :
    ∑ j ∈ Finset.Icc 1 N, v M q s d j ^ 2 ≤ M * (∑ n ∈ Finset.Icc 1 M, d n ^ 2) / s := by
  set e : ℕ → ℕ → ℝ := fun n j => ∑ k ∈ I q s, if n * k = j then d n / s else 0 with he
  have hv : ∀ j, v M q s d j = ∑ n ∈ Finset.Icc 1 M, e n j := by
    intro j; unfold v push A pos wt; rw [Finset.sum_product]
  have hcard : (Finset.Icc 1 M).card = M := by simp
  have h1 : ∀ j, v M q s d j ^ 2 ≤ M * ∑ n ∈ Finset.Icc 1 M, e n j ^ 2 := by
    intro j; rw [hv j]
    have := sq_sum_le_card_mul_sum_sq (s := Finset.Icc 1 M) (f := fun n => e n j)
    rw [hcard] at this; simpa using this
  have h2 : ∀ n ∈ Finset.Icc 1 M, ∀ j, e n j ^ 2 = ∑ k ∈ I q s, if n * k = j then (d n / s) ^ 2 else 0 := by
    intro n hn j
    simp only [Finset.mem_Icc] at hn
    rw [he, sq_sum_of_disjoint]
    · refine Finset.sum_congr rfl fun k _ => by split_ifs <;> ring
    · intro k _ l _ hkl
      by_cases h1 : n * k = j
      · by_cases h2 : n * l = j
        · exact absurd (Nat.eq_of_mul_eq_mul_left (by omega) (h1.trans h2.symm)) hkl
        · simp [h2]
      · simp [h1]
  have h3 : ∀ n ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 N, e n j ^ 2 = s * (d n / s) ^ 2 := by
    intro n hn
    rw [Finset.sum_congr rfl fun j _ => h2 n hn j, Finset.sum_comm]
    have hmem : ∀ k ∈ I q s, n * k ∈ Finset.Icc 1 N := fun k hk =>
      pos_mem M q s hq hs hN (n, k) (Finset.mem_product.2 ⟨hn, hk⟩)
    rw [Finset.sum_congr rfl fun k hk => by rw [Finset.sum_ite_eq, ite_eq_left (hmem k hk)]]
    rw [Finset.sum_const, card_I, nsmul_eq_mul]
  calc ∑ j ∈ Finset.Icc 1 N, v M q s d j ^ 2
      ≤ ∑ j ∈ Finset.Icc 1 N, M * ∑ n ∈ Finset.Icc 1 M, e n j ^ 2 := Finset.sum_le_sum fun j _ => h1 j
    _ = M * ∑ n ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 N, e n j ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ = M * ∑ n ∈ Finset.Icc 1 M, (s : ℝ) * (d n / s) ^ 2 := by
        rw [Finset.sum_congr rfl fun n hn => h3 n hn]
    _ = M * (∑ n ∈ Finset.Icc 1 M, d n ^ 2) / s := by
        have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast (by omega : s ≠ 0)
        simp only [Finset.mul_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun n _ => by field_simp

end avg

/-! ### Amplification and the criterion -/

theorem F_zero (M : ℕ) (d : ℕ → ℝ) : F M d 0 = E (Finset.Icc 1 M) d := by
  unfold F E; simp only [zero_add]

theorem continuousAt_F (M : ℕ) (d : ℕ → ℝ) : ContinuousAt (F M d) 0 := by
  unfold F
  refine ContinuousAt.mul continuousAt_const ?_
  have h : ∀ m n : ℕ, ContinuousAt
      (fun t : ℝ => d m * d n * G |t + (Real.log m - Real.log n)|) 0 := fun m n =>
    continuousAt_const.mul (continuousAt_G_abs _)
  have hs : Tendsto (fun t : ℝ => ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
      d m * d n * G |t + (Real.log m - Real.log n)|) (𝓝 0)
      (𝓝 (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
        d m * d n * G |(0:ℝ) + (Real.log m - Real.log n)|)) :=
    tendsto_finsetSum _ fun m _ => tendsto_finsetSum _ fun n _ => h m n
  exact hs

theorem qf_eq_E_v {M q s N : ℕ} (d : ℕ → ℝ) (hq : 1 ≤ q) (hs : 1 ≤ s) (hN : M * (q + 1) * s ≤ N)
    (hd : ∑ n ∈ Finset.Icc 1 M, d n = 0) : qf N (v M q s d) = E (Finset.Icc 1 N) (v M q s d) := by
  show QS (Finset.Icc 2 N) _ = _
  rw [← QS_Icc_one, QS_eq_E (sum_v M q s d hq hs hN hd)]

theorem log_close {q s k l : ℕ} (hq : 1 ≤ q) (hs : 1 ≤ s) (hk : k ∈ I q s) (hl : l ∈ I q s) :
    |Real.log k - Real.log l| ≤ 1 / q := by
  simp only [I, Finset.mem_Ico] at hk hl
  have hqs : (0:ℝ) < q * s := by positivity
  have hb : ∀ x : ℕ, q * s ≤ x → x < q * s + s →
      Real.log (q * s) ≤ Real.log x ∧ Real.log x ≤ Real.log (q * s + s) := by
    intro x h1 h2
    have h1' : ((q * s : ℕ) : ℝ) ≤ x := by exact_mod_cast h1
    have h2' : (x : ℝ) ≤ ((q * s + s : ℕ) : ℝ) := by exact_mod_cast h2.le
    push_cast at h1' h2'
    exact ⟨Real.log_le_log hqs h1', Real.log_le_log (by linarith) h2'⟩
  obtain ⟨k1, k2⟩ := hb k hk.1 hk.2
  obtain ⟨l1, l2⟩ := hb l hl.1 hl.2
  have hspan : Real.log ((q:ℝ) * s + s) - Real.log (q * s) ≤ 1 / q := by
    rw [← Real.log_div (by positivity) hqs.ne']
    have hx := Real.log_le_sub_one_of_pos (x := ((q:ℝ) * s + s) / (q * s)) (by positivity)
    have : ((q:ℝ) * s + s) / (q * s) - 1 = 1 / q := by field_simp; ring
    linarith
  rw [abs_le]; constructor <;> linarith

/-- **Dilation amplification**: one negative direction of the zero-sum form forces, for every large `N`, a box
test whose form is at most `−κN` times its squared coefficient norm. -/
theorem amplify (M : ℕ) (d : ℕ → ℝ) (hd : ∑ n ∈ Finset.Icc 1 M, d n = 0) (hneg : E (Finset.Icc 1 M) d < 0) :
    ∃ κ > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∃ w : ℕ → ℝ,
      qf N w < 0 ∧ qf N w ≤ -κ * N * ∑ j ∈ Finset.Icc 2 N, w j ^ 2 := by
  set a := -E (Finset.Icc 1 M) d with ha_def
  have ha : 0 < a := by linarith
  obtain ⟨η, hη, hball⟩ := Metric.continuousAt_iff.1 (continuousAt_F M d) (a / 2) (by linarith)
  have hFle : ∀ t : ℝ, |t| < η → F M d t ≤ -(a / 2) := by
    intro t ht
    have h := hball (by simpa [Real.dist_eq] using ht)
    rw [Real.dist_eq, F_zero, abs_lt] at h
    linarith [h.2]
  set q : ℕ := ⌈1 / η⌉₊ + 2 with hqdef
  have hq1 : 1 ≤ q := by omega
  have hqη : 1 / (q : ℝ) < η := by
    have hc : 1 / η ≤ (⌈1 / η⌉₊ : ℝ) := Nat.le_ceil _
    have hqr : (q : ℝ) = (⌈1 / η⌉₊ : ℝ) + 2 := by rw [hqdef]; push_cast; ring
    have hq0 : (0:ℝ) < q := by rw [hqr]; positivity
    rw [div_lt_iff₀ hq0]
    have : 1 < η * (1 / η + 2) := by
      rw [mul_add, mul_one_div_cancel hη.ne']; nlinarith
    calc (1:ℝ) < η * (1 / η + 2) := this
      _ ≤ η * q := by rw [hqr]; exact mul_le_mul_of_nonneg_left (by linarith) hη.le
  have hM : 1 ≤ M := by
    by_contra h
    have : Finset.Icc 1 M = ∅ := Finset.Icc_eq_empty (by omega)
    rw [this] at hneg; simp [E] at hneg
  set B := ∑ n ∈ Finset.Icc 1 M, d n ^ 2 with hB
  have hBpos : 0 < B := by
    rcases (Finset.sum_nonneg fun n _ => sq_nonneg (d n) : 0 ≤ B).lt_or_eq with h | h
    · exact h
    · exfalso
      have hz := (Finset.sum_eq_zero_iff_of_nonneg fun n _ => sq_nonneg (d n)).1 h.symm
      have : E (Finset.Icc 1 M) d = 0 := by
        unfold E
        rw [Finset.sum_eq_zero fun m hm => Finset.sum_eq_zero fun n _ => by
          rw [pow_eq_zero_iff two_ne_zero |>.1 (hz m hm)]; ring]
        ring
      linarith
  set κ : ℝ := a / (4 * (M * B) * (M * (q + 1))) with hκ
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  refine ⟨κ, by positivity, M * (q + 1), fun N hN => ?_⟩
  set s : ℕ := N / (M * (q + 1)) with hsdef
  have hk0 : 0 < M * (q + 1) := by positivity
  have hs : 1 ≤ s := (Nat.one_le_div_iff hk0).2 hN
  have hsN : M * (q + 1) * s ≤ N := by rw [mul_comm]; exact Nat.div_mul_le_self N _
  have hNs : N ≤ 2 * (M * (q + 1)) * s := by
    have h := Nat.lt_div_mul_add (a := N) hk0
    rw [← hsdef] at h
    nlinarith
  refine ⟨v M q s d, ?_⟩
  have hE : E (Finset.Icc 1 N) (v M q s d) ≤ -(a / 2) := by
    rw [E_v M q s d hq1 hs hsN]
    have hsum : ∑ k ∈ I q s, ∑ l ∈ I q s, F M d (Real.log k - Real.log l)
        ≤ ∑ k ∈ I q s, ∑ l ∈ I q s, -(a / 2) :=
      Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun l hl =>
        hFle _ (lt_of_le_of_lt (log_close hq1 hs hk hl) hqη)
    simp only [Finset.sum_const, card_I, nsmul_eq_mul] at hsum
    have hs' : (0:ℝ) < s := by exact_mod_cast hs
    calc 1 / (s:ℝ) ^ 2 * ∑ k ∈ I q s, ∑ l ∈ I q s, F M d (Real.log k - Real.log l)
        ≤ 1 / (s:ℝ) ^ 2 * ((s:ℝ) * ((s:ℝ) * -(a / 2))) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = -(a / 2) := by field_simp
  have hqf := qf_eq_E_v d hq1 hs hsN hd
  have hnorm : ∑ j ∈ Finset.Icc 2 N, v M q s d j ^ 2 ≤ M * B / s := by
    have h1 : ∑ j ∈ Finset.Icc 2 N, v M q s d j ^ 2 ≤ ∑ j ∈ Finset.Icc 1 N, v M q s d j ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc (by norm_num) le_rfl)
        fun j _ _ => sq_nonneg _
    exact h1.trans (sum_v_sq M q s d hq1 hs hsN)
  refine ⟨by rw [hqf]; linarith, ?_⟩
  rw [hqf]
  refine hE.trans ?_
  have hs' : (0:ℝ) < s := by exact_mod_cast hs
  have hNr : (N:ℝ) ≤ 2 * (M * (q + 1)) * s := by exact_mod_cast hNs
  have hS0 : 0 ≤ ∑ j ∈ Finset.Icc 2 N, v M q s d j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have key : κ * N * ∑ j ∈ Finset.Icc 2 N, v M q s d j ^ 2 ≤ a / 2 := by
    calc κ * N * ∑ j ∈ Finset.Icc 2 N, v M q s d j ^ 2 ≤ κ * N * (M * B / s) :=
          mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ ≤ κ * (2 * (M * (q + 1)) * s) * (M * B / s) := by
          gcongr
      _ = a / 2 := by rw [hκ]; field_simp; ring
  linarith

/-- The step's negative witness, in zero-sum coordinates (the zero box `n = 1` absorbs the sum). -/
theorem exists_negative_E_of_not_rh (h : ¬ RiemannHypothesis) :
    ∃ M : ℕ, ∃ d : ℕ → ℝ, ∑ n ∈ Finset.Icc 1 M, d n = 0 ∧ E (Finset.Icc 1 M) d < 0 := by
  have hs : ¬ ∀ N, 1 ≤ N → Cvs.Route.NestedBoxInduction.Step N := fun hs => h (Cvs.Route.NestedBoxInduction.rh_iff_forall_step.2 hs)
  push Not at hs
  obtain ⟨N, -, hstep⟩ := hs
  unfold Cvs.Route.NestedBoxInduction.Step at hstep
  push Not at hstep
  obtain ⟨c, -, hneg⟩ := hstep
  set M := N + 1
  set d : ℕ → ℝ := fun n => if n = 1 then -(∑ m ∈ Finset.Icc 2 M, c m) else c n with hd
  have hins : insert 1 (Finset.Icc 2 M) = Finset.Icc 1 M := by
    ext n; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
  have h1 : (1:ℕ) ∉ Finset.Icc 2 M := by simp
  have hagree : ∀ n ∈ Finset.Icc 2 M, d n = c n := by
    intro n hn; simp only [Finset.mem_Icc] at hn; simp only [hd]; rw [ite_eq_right (by omega)]
  refine ⟨M, d, ?_, ?_⟩
  · rw [← hins, Finset.sum_insert h1, Finset.sum_congr rfl hagree]
    simp [hd]
  · have hsum0 : ∑ n ∈ Finset.Icc 1 M, d n = 0 := by
      rw [← hins, Finset.sum_insert h1, Finset.sum_congr rfl hagree]; simp [hd]
    rw [← QS_eq_E hsum0, QS_Icc_one]
    have : QS (Finset.Icc 2 M) d = QS (Finset.Icc 2 M) c := by
      unfold QS
      refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun n hn => ?_
      rw [hagree m hm, hagree n hn]
    rw [this]; exact hneg

theorem pos_of_qf_neg {N : ℕ} {w : ℕ → ℝ} (h : qf N w < 0) : 0 < ∑ j ∈ Finset.Icc 2 N, w j ^ 2 := by
  rcases (Finset.sum_nonneg fun j _ => sq_nonneg (w j) :
      0 ≤ ∑ j ∈ Finset.Icc 2 N, w j ^ 2).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (w j)).1 heq.symm
    have : qf N w = 0 := by
      unfold qf
      refine Finset.sum_eq_zero fun m hm => Finset.sum_eq_zero fun n _ => ?_
      rw [pow_eq_zero_iff two_ne_zero |>.1 (hz m hm)]; ring
    linarith

/-- **RH from a sublinear lower bound** on the box form, holding frequently. -/
theorem rh_of_frequently_sublinear (r : ℕ → ℝ) (hr : Tendsto (fun N : ℕ => r N / N) atTop (𝓝 0))
    (h : ∃ᶠ N : ℕ in atTop, ∀ c : ℕ → ℝ, -(r N) * ∑ n ∈ Finset.Icc 2 N, c n ^ 2 ≤ qf N c) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨M, d, hd, hneg⟩ := exists_negative_E_of_not_rh hRH
  obtain ⟨κ, hκ, N₀, hamp⟩ := amplify M d hd hneg
  have hev : ∀ᶠ N : ℕ in atTop, r N / N < κ ∧ max N₀ 1 ≤ N :=
    (hr.eventually (gt_mem_nhds hκ)).and (eventually_ge_atTop _)
  obtain ⟨N, hN, hlt, hge⟩ := (h.and_eventually hev).exists
  obtain ⟨w, hw0, hw⟩ := hamp N (le_trans (le_max_left _ _) hge)
  have hS := pos_of_qf_neg hw0
  have hb := hN w
  have hNpos : (0:ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) hge))
  have : κ * N ≤ r N := by
    by_contra hc
    push Not at hc
    nlinarith
  rw [div_lt_iff₀ hNpos] at hlt
  linarith

/-- **RH iff some sublinear lower bound holds frequently** on the nested-box form. -/
theorem rh_iff_frequently_sublinear :
    RiemannHypothesis ↔ ∃ r : ℕ → ℝ, Tendsto (fun N : ℕ => r N / N) atTop (𝓝 0) ∧
      ∃ᶠ N : ℕ in atTop, ∀ c : ℕ → ℝ, -(r N) * ∑ n ∈ Finset.Icc 2 N, c n ^ 2 ≤ qf N c := by
  refine ⟨fun hRH => ⟨fun _ => 0, by simp, ?_⟩, fun ⟨r, hr, h⟩ => rh_of_frequently_sublinear r hr h⟩
  refine Eventually.frequently ?_
  filter_upwards [eventually_ge_atTop 2] with N hN c
  simp only [neg_zero, zero_mul]
  exact Cvs.Route.NestedBoxInduction.boxPSD_of_rh hRH hN c

end Cvs.Route.NestedBoxDilationAmplify
