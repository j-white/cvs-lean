import Mathlib
import Cvs.Approximant.SpineSubspace
import Cvs.Finite.WindowMatrixSymbolKernel
import Cvs.Route.OneCellBoxWindowForm
import Cvs.Route.OneCellCriterion
import Cvs.Route.OneCellLaplaceTransform
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.BilinearCrossRepresentatives
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.LevyDomainSpectral
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.TailBoundOnWindow
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowRepresentative
import Cvs.WeilForm.WindowSetNonempty
import Cvs.WeilForm.WindowWeilCriterion

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The dilation-lattice criterion: RH ⟺ the lattice Gram is positive semidefinite for every `N`

`e_n = 1_{(log n, log N)}` for `1 ≤ n < N` are classes of the form domain at `L = log N`; their Gram `latticeGram N`
under the window Weil form is `½[G(log N/m) + G(log N/n) − G(|log m/n|)]` in closed form (`latticeGram_eq`).  RH
gives positivity (Cvs.WeilForm.PositivityOfRH); conversely `e_m − e_n` has form `G(log n/m)`, the logs of rationals are dense, `G` is
continuous on `(0, ∞)`, and Cvs.Route.OneCellCriterion finishes (`rh_iff_latticeGram_posSemidef`).
-/

noncomputable section

open Real Set MeasureTheory Filter Topology Matrix
open scoped ArithmeticFunction.vonMangoldt

namespace Cvs.Route.DilationLatticeCriterion
open Cvs.ZeroCounting

open Cvs.Route.OneCellLaplaceTransform (G ladder primeSide)
open Cvs.Finite.WindowMatrixSymbolKernel (bk bk_pos)

/-! ### Continuity of `G` on `(0, ∞)` -/

theorem continuousOn_ladder : ContinuousOn ladder (Ioi 0) := by
  unfold ladder
  refine continuousOn_tsum (fun k => ?_) Cvs.Route.OneCellLaplaceTransform.summable_inv_bk_sq (fun k L hL => ?_)
  · exact (by fun_prop : Continuous fun L : ℝ => (1 - Real.exp (-(bk k * L))) / bk k ^ 2).continuousOn
  · have hL : 0 < L := hL
    have hb := bk_pos k
    have he : Real.exp (-(bk k * L)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have he0 := Real.exp_pos (-(bk k * L))
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0:ℝ) < bk k ^ 2),
      abs_of_nonneg (by linarith)]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)

theorem continuousOn_primeSide (L₀ : ℝ) : ContinuousOn primeSide (Iio L₀) := by
  unfold primeSide
  set u : ℕ → ℝ := fun n => Λ n / Real.sqrt n * max (L₀ - Real.log n) 0 with hu
  have hus : Summable u := by
    refine summable_of_ne_finset_zero (s := Finset.range (⌈Real.exp L₀⌉₊ + 1)) fun n hn => ?_
    rw [Finset.mem_range, not_lt] at hn
    have hn' : Real.exp L₀ < n := by
      have := Nat.le_ceil (Real.exp L₀)
      have h2 : (⌈Real.exp L₀⌉₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn
      linarith
    have hlog : L₀ < Real.log n := by
      rw [← Real.log_exp L₀]; exact Real.log_lt_log (Real.exp_pos _) hn'
    simp only [hu]; rw [max_eq_right (by linarith), mul_zero]
  refine continuousOn_tsum (fun n => ?_) hus (fun n L hL => ?_)
  · exact (by fun_prop : Continuous fun L : ℝ => Λ n / Real.sqrt n * max (L - Real.log n) 0).continuousOn
  · have hL : L < L₀ := hL
    have h0 : 0 ≤ Λ n / Real.sqrt n := by
      have := ArithmeticFunction.vonMangoldt_nonneg (n := n); positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simp only [hu]
    exact mul_le_mul_of_nonneg_left (max_le_max (by linarith) le_rfl) h0

theorem continuousAt_G {L : ℝ} (hL : 0 < L) : ContinuousAt G L := by
  have hl : ContinuousAt ladder L := continuousOn_ladder.continuousAt (Ioi_mem_nhds hL)
  have hp : ContinuousAt primeSide L :=
    (continuousOn_primeSide (L + 1)).continuousAt (Iio_mem_nhds (by linarith))
  have hs : ContinuousAt (fun L : ℝ => 16 * (Real.cosh (L / 2) - 1)
      + Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * L) L := by fun_prop
  unfold G
  exact (hs.add (continuousAt_const.mul hl)).sub (continuousAt_const.mul hp)

/-! ### The logs of rationals are dense in `(0, ∞)` -/

theorem exists_log_ratio_near {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) :
    ∃ m n : ℕ, 1 ≤ m ∧ m < n ∧ |Real.log ((n : ℝ) / m) - L| < ε := by
  obtain ⟨m₀, hm₀⟩ := exists_nat_gt (Real.exp (-L) / ε)
  set m : ℕ := m₀ + 1 with hm
  have hm1 : (1:ℝ) ≤ m := by rw [hm]; push_cast; linarith [(Nat.cast_nonneg m₀ : (0:ℝ) ≤ m₀)]
  have hmpos : (0:ℝ) < m := by linarith
  have hmε : Real.exp (-L) / ε < m := by rw [hm]; push_cast; linarith
  set y : ℝ := m * Real.exp L with hy
  have hy0 : 0 ≤ y := by positivity
  set n : ℕ := ⌊y⌋₊ + 1 with hn
  have hny : y < n := by rw [hn]; push_cast; exact Nat.lt_floor_add_one y
  have hyn : (n : ℝ) ≤ y + 1 := by rw [hn]; push_cast; linarith [Nat.floor_le hy0]
  have hn0 : (0:ℝ) < n := lt_of_le_of_lt hy0 hny
  refine ⟨m, n, by rw [hm]; omega, ?_, ?_⟩
  · -- m < n since m e^L > m ≥ 1 ... n > y = m e^L > m
    have : (m : ℝ) < n := by
      have : (m:ℝ) < y := by rw [hy]; have := Real.one_lt_exp_iff.2 hL; nlinarith
      linarith
    exact_mod_cast this
  · have hratio : Real.exp L < (n:ℝ) / m := by rw [lt_div_iff₀ hmpos]; linarith
    have hratio' : (n:ℝ) / m ≤ Real.exp L + 1 / m := by
      rw [div_le_iff₀ hmpos]; rw [hy] at hyn; linarith [show (1:ℝ) / m * m = 1 by field_simp]
    have hlog1 : L < Real.log ((n:ℝ) / m) := by
      rw [← Real.log_exp L]; exact Real.log_lt_log (Real.exp_pos _) hratio
    have hlog2 : Real.log ((n:ℝ) / m) - L ≤ 1 / (m * Real.exp L) := by
      have hpos : 0 < (n:ℝ) / m := by positivity
      have key : Real.log ((n:ℝ) / m) - L = Real.log (((n:ℝ) / m) / Real.exp L) := by
        rw [Real.log_div hpos.ne' (Real.exp_pos L).ne', Real.log_exp]
      rw [key]
      calc Real.log ((n:ℝ) / m / Real.exp L) ≤ (n:ℝ) / m / Real.exp L - 1 :=
            Real.log_le_sub_one_of_pos (by positivity)
        _ ≤ 1 / (m * Real.exp L) := by
            rw [div_div]
            have : (n:ℝ) / (m * Real.exp L) ≤ (Real.exp L + 1 / m) / Real.exp L := by
              rw [div_le_div_iff₀ (by positivity) (Real.exp_pos _)]
              have := hratio'; rw [div_le_iff₀ hmpos] at this
              nlinarith [Real.exp_pos L]
            have h2 : (Real.exp L + 1 / m) / Real.exp L = 1 + 1 / (m * Real.exp L) := by
              field_simp
            linarith
    have hsmall : 1 / (m * Real.exp L) < ε := by
      rw [div_lt_iff₀ (by positivity)]
      have := hmε; rw [div_lt_iff₀ hε] at this
      have h3 : Real.exp (-L) * Real.exp L = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos L, Real.exp_pos (-L)]
    rw [abs_lt]; constructor <;> linarith

theorem G_nonneg_of_log_ratio
    (h : ∀ m n : ℕ, 1 ≤ m → m < n → 0 ≤ G (Real.log ((n : ℝ) / m))) {L : ℝ} (hL : 0 < L) : 0 ≤ G L := by
  by_contra hneg
  rw [not_le] at hneg
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 (continuousAt_G hL) (-G L) (by linarith)
  obtain ⟨m, n, hm, hmn, hclose⟩ := exists_log_ratio_near hL hδ
  have h1 := hball (by rw [Real.dist_eq]; exact hclose)
  rw [Real.dist_eq, abs_lt] at h1
  have h2 := h m n hm hmn
  linarith

/-! ### The lattice classes -/

/-- The box `1_{(a, b]}`. -/
def box (a b : ℝ) : ℝ → ℝ := Set.indicator (Ioc a b) fun _ => (1:ℝ)

theorem box_eq_flat (a b : ℝ) : box a b = fun x => Cvs.WeilForm.WindowSetNonempty.flat (b - a) (x - a) := by
  funext x
  simp only [box, Cvs.WeilForm.WindowSetNonempty.flat, Set.indicator_apply, Set.mem_Ioc]
  have : (a < x ∧ x ≤ b) ↔ (0 < x - a ∧ x - a ≤ b - a) := by
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  simp only [this]

theorem memLp_box (a b : ℝ) : MemLp (box a b) 2 volume :=
  memLp_indicator_const 2 measurableSet_Ioc.nullMeasurableSet (1:ℝ) (Or.inr (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))

theorem box_supp {a b L : ℝ} (ha : 0 ≤ a) (hb : b ≤ L) :
    ∀ᵐ s ∂(volume : Measure ℝ), s ∉ Ioc (0:ℝ) L → box a b s = 0 := by
  refine ae_of_all _ fun s hs => ?_
  simp only [box, Set.indicator_apply]
  split_ifs with h
  · exact absurd ⟨by linarith [h.1], by linarith [h.2]⟩ hs
  · rfl

theorem levy_box {a b : ℝ} (hab : a < b) :
    IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (box a b)) (Ioi 0) volume := by
  have : box a b = fun x => Cvs.WeilForm.WindowSetNonempty.flat (b - a) (x + -a) := by
    rw [box_eq_flat]; funext x; simp only [sub_eq_add_neg]
  rw [this, Cvs.WeilForm.TailBoundOnWindow.levy_translate]
  exact Cvs.WeilForm.WindowSetNonempty.integrableOn_levy_flat (by linarith)

variable (N : ℕ)

/-- `log(i + 1)` for `i : Fin (N − 1)`: the left endpoint of the `i`-th lattice box. -/
def a (i : Fin (N - 1)) : ℝ := Real.log ((i : ℕ) + 1 : ℝ)

theorem a_nonneg (i : Fin (N - 1)) : 0 ≤ a N i :=
  Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le (i : ℕ)))

theorem a_lt (hN : 2 ≤ N) (i : Fin (N - 1)) : a N i < Real.log N := by
  unfold a
  apply Real.log_lt_log (by positivity)
  have := i.2; exact_mod_cast (by omega : (i : ℕ) + 1 < N)

/-- The lattice class `e_n = 1_{(log n, log N]}`, `n = i + 1`. -/
def e (hN : 2 ≤ N) (i : Fin (N - 1)) : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg N) :=
  Cvs.Approximant.SpineSubspace.ofFun _ (memLp_box (a N i) (Real.log N)) (box_supp (a_nonneg N i) le_rfl) (levy_box (a_lt N hN i))

theorem rep_e (hN : 2 ≤ N) (i : Fin (N - 1)) :
    Cvs.WeilForm.WindowRepresentative.rep ((e N hN i : Cvs.WeilForm.FormDomain.formDomain _) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log N)) =ᵐ[volume] box (a N i) (Real.log N) :=
  (Cvs.WeilForm.WindowRepresentative.ae_eq_rep _).symm.trans (Cvs.Approximant.SpineSubspace.coe_ofFun_ae _ _ _ _)

/-! ### The form on boxes is `G` of their length -/

/-- `crossW` of a box with itself is `G` of its length, for `0 ≤ a < b ≤ log N`. -/
theorem crossW_box (hN : 2 ≤ N) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ Real.log N) :
    Cvs.WeilForm.SymmetricBilinearForm.crossW N (Nat.clog 2 N) (box a b) (box a b) = G (b - a) := by
  obtain ⟨hL0, hexp, hR⟩ := Cvs.Approximant.SpineSubspace.sizes N hN
  -- translate to the box at the origin, i.e. `flat (b − a)`
  have ht : Cvs.WeilForm.SymmetricBilinearForm.crossW N (Nat.clog 2 N) (box a b) (box a b)
      = Cvs.WeilForm.SymmetricBilinearForm.crossW N (Nat.clog 2 N) (Cvs.WeilForm.WindowSetNonempty.flat (b - a)) (Cvs.WeilForm.WindowSetNonempty.flat (b - a)) := by
    rw [box_eq_flat]; exact Cvs.WeilForm.BilinearCrossRepresentatives.crossW_translate _ _ _ _ a
  rw [ht]
  -- `flat (b − a)` is the representative of a class whose form is `G (b − a)`
  have hsupp : ∀ᵐ s ∂(volume : Measure ℝ), s ∉ Ioc (0:ℝ) (Real.log N) → Cvs.WeilForm.WindowSetNonempty.flat (b - a) s = 0 := by
    have := box_supp (a := 0) (b := b - a) (L := Real.log N) le_rfl (by linarith)
    rwa [show box 0 (b - a) = Cvs.WeilForm.WindowSetNonempty.flat (b - a) by rw [box_eq_flat]; funext x; rw [sub_zero, sub_zero]] at this
  set ψ := Cvs.Approximant.SpineSubspace.ofFun (Real.log_natCast_nonneg N) (Cvs.WeilForm.WindowSetNonempty.memLp_flat (b - a)) hsupp
    (Cvs.WeilForm.WindowSetNonempty.integrableOn_levy_flat (by linarith)) with hψ
  have hrep : Cvs.WeilForm.WindowRepresentative.rep ((ψ : Cvs.WeilForm.FormDomain.formDomain _) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log N)) =ᵐ[volume] Cvs.WeilForm.WindowSetNonempty.flat (b - a) :=
    (Cvs.WeilForm.WindowRepresentative.ae_eq_rep _).symm.trans (Cvs.Approximant.SpineSubspace.coe_ofFun_ae _ _ _ _)
  rw [← Cvs.WeilForm.BilinearCrossRepresentatives.crossW_congr N (Nat.clog 2 N) hrep hrep, ← Cvs.WeilForm.BilinearCrossRepresentatives.QWbil_apply, Cvs.WeilForm.SymmetricBilinearForm.QWbil_self, hψ,
    Cvs.Approximant.SpineSubspace.Q_ofFun]
  exact Cvs.Route.OneCellBoxWindowForm.weilForm_flat_eq (by linarith) (by
      calc Real.exp (b - a) ≤ Real.exp (Real.log N) := Real.exp_le_exp.2 (by linarith)
        _ ≤ N := hexp) (by linarith)

theorem Q_e (hN : 2 ≤ N) (i : Fin (N - 1)) :
    Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg N) N (Nat.clog 2 N) (e N hN i) = G (Real.log N - a N i) := by
  rw [← Cvs.WeilForm.SymmetricBilinearForm.QWbil_self, Cvs.WeilForm.BilinearCrossRepresentatives.QWbil_apply, Cvs.WeilForm.BilinearCrossRepresentatives.crossW_congr N (Nat.clog 2 N) (rep_e N hN i) (rep_e N hN i)]
  exact crossW_box N hN (a_nonneg N i) (a_lt N hN i) le_rfl

/-- The difference of two lattice boxes is the box between their left endpoints. -/
theorem box_sub_box {a₁ a₂ b : ℝ} (h : a₁ ≤ a₂) (hb : a₂ ≤ b) :
    (fun x => box a₁ b x - box a₂ b x) = box a₁ a₂ := by
  funext x
  simp only [box, Set.indicator_apply, Set.mem_Ioc]
  by_cases h1 : a₁ < x
  · by_cases h2 : x ≤ a₂
    · have h4 : x ≤ b := le_trans h2 hb
      have h3 : ¬ a₂ < x := not_lt.2 h2
      simp [h1, h2, h3, h4]
    · have h2' : a₂ < x := not_le.1 h2
      by_cases h4 : x ≤ b
      · simp [h1, h2, h2', h4]
      · simp [h1, h2, h2', h4]
  · have h3 : ¬ a₂ < x := fun hc => h1 (lt_of_le_of_lt h hc)
    simp [h1, h3]

theorem Q_e_sub (hN : 2 ≤ N) {i j : Fin (N - 1)} (hij : a N i < a N j) :
    Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg N) N (Nat.clog 2 N) (e N hN i - e N hN j) = G (a N j - a N i) := by
  have hrep : Cvs.WeilForm.WindowRepresentative.rep (((e N hN i - e N hN j : Cvs.WeilForm.FormDomain.formDomain _)) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log N))
      =ᵐ[volume] box (a N i) (a N j) := by
    have hw : (((e N hN i - e N hN j : Cvs.WeilForm.FormDomain.formDomain _)) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log N))
        = (e N hN i : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log N)) + (-1 : ℝ) • (e N hN j : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log N)) := by
      rw [Submodule.coe_sub]
      exact (sub_eq_add_neg _ _).trans (congrArg _ (neg_one_smul ℝ _).symm)
    rw [hw]
    refine (Cvs.WeilForm.LevyDomainSpectral.rep_add_ae _ _).trans ?_
    have hj : Cvs.WeilForm.WindowRepresentative.rep ((-1 : ℝ) • (e N hN j : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log N)))
        =ᵐ[volume] fun x => -1 * box (a N j) (Real.log N) x :=
      (Cvs.WeilForm.LevyDomainSpectral.rep_smul_ae (-1) _).trans ((rep_e N hN j).mono fun x hx => by simp only [hx])
    refine ((rep_e N hN i).add hj).trans (ae_of_all _ fun x => ?_)
    show box (a N i) (Real.log N) x + -1 * box (a N j) (Real.log N) x = box (a N i) (a N j) x
    rw [← box_sub_box hij.le (a_lt N hN j).le]; ring
  rw [← Cvs.WeilForm.SymmetricBilinearForm.QWbil_self, Cvs.WeilForm.BilinearCrossRepresentatives.QWbil_apply, Cvs.WeilForm.BilinearCrossRepresentatives.crossW_congr N (Nat.clog 2 N) hrep hrep]
  exact crossW_box N hN (a_nonneg N i) hij (a_lt N hN j).le

/-! ### The lattice Gram and its closed form -/

/-- The lattice Gram `QWbil(e_i, e_j)`. -/
def latticeGram (hN : 2 ≤ N) : Matrix (Fin (N - 1)) (Fin (N - 1)) ℝ :=
  fun i j => Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg N) N (Nat.clog 2 N) (e N hN i) (e N hN j)

theorem G_zero : G 0 = 0 := by
  unfold G ladder primeSide
  simp [Real.log_natCast_nonneg]

/-- **The closed form**: `½[G(log N/m) + G(log N/n) − G(|log m/n|)]`. -/
theorem latticeGram_eq (hN : 2 ≤ N) (i j : Fin (N - 1)) :
    latticeGram N hN i j
      = (G (Real.log N - a N i) + G (Real.log N - a N j) - G (|a N i - a N j|)) / 2 := by
  have hsymm := Cvs.WeilForm.SymmetricBilinearForm.QWbil_isSymm (Real.log_natCast_nonneg N) N (Nat.clog 2 N)
  set B := Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg N) N (Nat.clog 2 N) with hB
  have hpol : B (e N hN i) (e N hN j)
      = (B (e N hN i) (e N hN i) + B (e N hN j) (e N hN j) - B (e N hN i - e N hN j) (e N hN i - e N hN j)) / 2 := by
    have hs : B (e N hN j) (e N hN i) = B (e N hN i) (e N hN j) := by simpa using hsymm.eq (e N hN j) (e N hN i)
    have h1 : B (e N hN i - e N hN j) = B (e N hN i) - B (e N hN j) := map_sub B _ _
    have h2 : B (e N hN i) (e N hN i - e N hN j) = B (e N hN i) (e N hN i) - B (e N hN i) (e N hN j) :=
      map_sub (B (e N hN i)) _ _
    have h3 : B (e N hN j) (e N hN i - e N hN j) = B (e N hN j) (e N hN i) - B (e N hN j) (e N hN j) :=
      map_sub (B (e N hN j)) _ _
    rw [h1, LinearMap.sub_apply, h2, h3]
    linarith
  show B (e N hN i) (e N hN j) = _
  rw [hpol, Cvs.WeilForm.SymmetricBilinearForm.QWbil_self, Cvs.WeilForm.SymmetricBilinearForm.QWbil_self, Cvs.WeilForm.SymmetricBilinearForm.QWbil_self, Q_e, Q_e]
  rcases lt_trichotomy (a N i) (a N j) with h | h | h
  · rw [Q_e_sub N hN h, abs_of_neg (by linarith), neg_sub]
  · have hij : i = j := by
      have : ((i : ℕ) + 1 : ℝ) = ((j : ℕ) + 1 : ℝ) :=
        Real.log_injOn_pos (by simp; positivity) (by simp; positivity) h
      ext; exact_mod_cast (by linarith : ((i : ℕ) : ℝ) = j)
    subst hij
    have h0 : e N hN i - e N hN i = 0 := sub_self (e N hN i)
    rw [h0, Cvs.WeilForm.SymmetricBilinearForm.Q_zero, sub_self, abs_zero, G_zero]
  · have hsw : B (e N hN i - e N hN j) (e N hN i - e N hN j) = B (e N hN j - e N hN i) (e N hN j - e N hN i) := by
      have h1 : B (e N hN i - e N hN j) = B (e N hN i) - B (e N hN j) := map_sub B _ _
      have h1' : B (e N hN j - e N hN i) = B (e N hN j) - B (e N hN i) := map_sub B _ _
      have h2 : ∀ x y z, B x (y - z) = B x y - B x z := fun x y z => map_sub (B x) _ _
      rw [h1, h1', LinearMap.sub_apply, LinearMap.sub_apply, h2, h2, h2, h2]
      have := hsymm.eq (e N hN i) (e N hN j)
      linarith
    rw [← Cvs.WeilForm.SymmetricBilinearForm.QWbil_self, ← hB, hsw, hB, Cvs.WeilForm.SymmetricBilinearForm.QWbil_self, Q_e_sub N hN h, abs_of_pos (by linarith)]

/-! ### The criterion -/

theorem dotProduct_latticeGram (hN : 2 ≤ N) (x : Fin (N - 1) → ℝ) :
    x ⬝ᵥ (latticeGram N hN *ᵥ x)
      = Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg N) N (Nat.clog 2 N) (∑ i, x i • e N hN i) := by
  rw [← Cvs.WeilForm.SymmetricBilinearForm.QWbil_self]
  simp only [dotProduct, mulVec, latticeGram, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem latticeGram_posSemidef_of_rh (hRH : RiemannHypothesis) (hN : 2 ≤ N) :
    (latticeGram N hN).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext i j
    simp only [conjTranspose_apply, star_trivial, latticeGram]
    simpa using (Cvs.WeilForm.SymmetricBilinearForm.QWbil_isSymm _ _ _).eq (e N hN j) (e N hN i)
  · rw [star_trivial, dotProduct_latticeGram]
    exact (Cvs.WeilForm.WindowWeilCriterion.rh_iff_windowPos 2 le_rfl).1 hRH N hN _

theorem rh_of_latticeGram_posSemidef (h : ∀ N : ℕ, ∀ hN : 2 ≤ N, (latticeGram N hN).PosSemidef) :
    RiemannHypothesis := by
  refine Cvs.Route.OneCellCriterion.riemannHypothesis_of_G_nonneg fun L hL => ?_
  refine G_nonneg_of_log_ratio (fun m n hm hmn => ?_) hL
  -- the lattice at level `N = n + 1`, the vector `e_m − e_n`
  set N := n + 1 with hNdef
  have hN : 2 ≤ N := by omega
  have hi : m - 1 < N - 1 := by omega
  have hj : n - 1 < N - 1 := by omega
  set i : Fin (N - 1) := ⟨m - 1, hi⟩
  set j : Fin (N - 1) := ⟨n - 1, hj⟩
  have hai : a N i = Real.log m := by
    simp only [a, i]; congr 1; push_cast [Nat.cast_sub hm]; ring
  have haj : a N j = Real.log n := by
    simp only [a, j]; congr 1; push_cast [Nat.cast_sub (by omega : 1 ≤ n)]; ring
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; simp only [i, j] at this; omega
  obtain ⟨-, hpos⟩ := posSemidef_iff_dotProduct_mulVec.1 (h N hN)
  have := hpos (Pi.single i 1 - Pi.single j 1)
  rw [star_trivial] at this
  have hval : (Pi.single i (1:ℝ) - Pi.single j 1) ⬝ᵥ (latticeGram N hN *ᵥ (Pi.single i 1 - Pi.single j 1))
      = G (Real.log ((n : ℝ) / m)) := by
    have hsym : latticeGram N hN j i = latticeGram N hN i j := by
      simpa [latticeGram] using (Cvs.WeilForm.SymmetricBilinearForm.QWbil_isSymm _ _ _).eq (e N hN j) (e N hN i)
    have hmv : ∀ k, (latticeGram N hN *ᵥ (Pi.single i (1:ℝ) - Pi.single j 1)) k
        = latticeGram N hN k i - latticeGram N hN k j := by
      intro k
      simp only [mulVec, dotProduct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, Pi.single_apply,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [dotProduct, hmv, Pi.sub_apply, Pi.single_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have hlt : Real.log (m : ℝ) < Real.log n := Real.log_lt_log (by positivity) (by exact_mod_cast hmn)
    have h1 : |Real.log (m:ℝ) - Real.log n| = Real.log n - Real.log m := by
      rw [abs_of_neg (by linarith)]; ring
    have h2 : |Real.log (n:ℝ) - Real.log m| = Real.log n - Real.log m := abs_of_pos (by linarith)
    simp only [latticeGram_eq, hai, haj, sub_self, abs_zero, G_zero, h1, h2]
    rw [Real.log_div (Nat.cast_ne_zero.2 (by omega)) (Nat.cast_ne_zero.2 (by omega))]
    ring
  rw [hval] at this
  exact this

/-- **The dilation-lattice criterion.** -/
theorem rh_iff_latticeGram_posSemidef :
    RiemannHypothesis ↔ ∀ N : ℕ, ∀ hN : 2 ≤ N, (latticeGram N hN).PosSemidef :=
  ⟨fun h N hN => latticeGram_posSemidef_of_rh N h hN, rh_of_latticeGram_posSemidef⟩

end Cvs.Route.DilationLatticeCriterion
