import Mathlib
import Cvs.Finite.CoefficientDilation
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.UniversalFunctionPairing
import Cvs.Finite.VanishingMomentsDamping
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroSideMoments

/-!
# Nesting, exactly: the dilated minimiser at the next scale
On `Idx N` an even vector is a pair vector `y` (`y_0 = xi_0`, `y_k = 2xi_k`) on the distinct nodes
`q_k = (2πk)²`, and `Cvs.Finite.UniversalFunctionPairing`'s rational factor is `Cvs.Finite.CoefficientDilation`'s `Rq` on those nodes. Dilating `y` by
`t = (L'/L)²` gives an even vector `dilE` whose universal function at `L'z` is the original's at
`Lz` times an explicit factor (`F_dilE_mul`), so the CvS form of `dilE` at scale `L'` is the old
zero sum reweighted zero by zero (`quadForm_dilE`): "`x_n` restricts `x_{n+1}`" as an identity.
-/

noncomputable section

open Real Filter Topology Matrix Polynomial Cvs.WeilForm.SelfConvolutionTransform

namespace Cvs.Finite.NestedMinimiser
open Cvs.ZeroCounting

/-- The pair index: the absolute mode `0, 1, …, N`. -/
abbrev PIdx (N : ℕ) := Option (Fin N)

/-- The absolute mode of a pair. -/
def amode (N : ℕ) : PIdx N → ℕ
  | none => 0
  | some k => (k : ℕ) + 1

theorem amode_injective (N : ℕ) : Function.Injective (amode N) := by
  rintro (_ | k) (_ | k') h <;> simp [amode] at h ⊢
  exact Fin.ext h

/-- The real nodes `(2π·amode)²`. -/
def qr (N : ℕ) (m : PIdx N) : ℝ := (2 * π * (amode N m : ℝ)) ^ 2

theorem qr_injective (N : ℕ) : Function.Injective (qr N) := by
  intro m m' h
  unfold qr at h
  have hπ : 0 < π := Real.pi_pos
  have h1 : 0 ≤ 2 * π * (amode N m : ℝ) := by positivity
  have h2 : 0 ≤ 2 * π * (amode N m' : ℝ) := by positivity
  have h3 := (pow_left_inj₀ h1 h2 two_ne_zero).mp h
  have h4 : (amode N m : ℝ) = amode N m' :=
    mul_left_cancel₀ (by positivity : (2 * π : ℝ) ≠ 0) h3
  exact amode_injective N (by exact_mod_cast h4)

/-- The pair coefficients of an even vector. -/
def toY (N : ℕ) (xi : Cvs.Finite.SymmetricModeSet.Idx N → ℝ) : PIdx N → ℝ
  | none => xi none
  | some k => 2 * xi (some (k, true))

/-- The even vector of a pair vector. -/
def ofY (N : ℕ) (y : PIdx N → ℝ) : Cvs.Finite.SymmetricModeSet.Idx N → ℝ
  | none => y none
  | some (k, _) => y (some k) / 2

theorem ofY_even (N : ℕ) (y : PIdx N → ℝ) (i : Cvs.Finite.SymmetricModeSet.Idx N) :
    ofY N y (Cvs.Finite.SymmetricModeSet.negI N i) = ofY N y i := by
  rcases i with _ | ⟨k, b⟩ <;> simp [ofY, Cvs.Finite.SymmetricModeSet.negI]

theorem toY_ofY (N : ℕ) (y : PIdx N → ℝ) : toY N (ofY N y) = y := by
  funext m
  rcases m with _ | k
  · simp [toY, ofY]
  · simp only [toY, ofY]; ring

/-- The squared frequency of an index is the node of its pair. -/
theorem q_mode_eq (N : ℕ) (i : Cvs.Finite.SymmetricModeSet.Idx N) :
    ((2 * π * (Cvs.Finite.SymmetricModeSet.mode N i : ℤ) / 1 : ℝ) : ℂ) ^ 2 = ((qr N (i.map Prod.fst) : ℝ) : ℂ) := by
  rcases i with _ | ⟨k, b⟩
  · simp [qr, amode, Cvs.Finite.SymmetricModeSet.mode]
  · cases b <;> simp [qr, amode, Cvs.Finite.SymmetricModeSet.mode] <;> push_cast <;> ring

/-- **The rational factor of an even vector is `Rq` of its pair vector**, on the nodes `q_k`
(at scale `L` the frequencies are `2πk/L`, so the nodes are `(2πk)²` in the dilated variable). -/
theorem R_eq_Rq (N : ℕ) {xi : Cvs.Finite.SymmetricModeSet.Idx N → ℝ}
    (hxieven : ∀ i, xi (Cvs.Finite.SymmetricModeSet.negI N i) = xi i) (u : ℂ) :
    Cvs.Finite.UniversalFunctionPairing.R (Cvs.Finite.SymmetricModeSet.mode N) xi u
      = Cvs.Finite.CoefficientDilation.Rq (fun m => ((qr N m : ℝ) : ℂ)) (fun m => ((toY N xi m : ℝ) : ℂ)) u := by
  unfold Cvs.Finite.UniversalFunctionPairing.R Cvs.Finite.CoefficientDilation.Rq
  rw [Fintype.sum_option, Fintype.sum_option, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  congr 1
  · simp [toY, qr, amode, Cvs.Finite.SymmetricModeSet.mode]
  · refine Finset.sum_congr rfl fun k _ => ?_
    have he := hxieven (some (k, true))
    simp only [Cvs.Finite.SymmetricModeSet.negI, Bool.not_true] at he
    simp only [toY, qr, amode, Cvs.Finite.SymmetricModeSet.mode, Bool.false_eq_true, ↓reduceIte, he]
    push_cast
    ring

/-! ### The dilated even vector -/

/-- **The dilated even vector**: the pair vector dilated by `t`, re-expanded. -/
def dilE (N : ℕ) (t : ℝ) (xi : Cvs.Finite.SymmetricModeSet.Idx N → ℝ) : Cvs.Finite.SymmetricModeSet.Idx N → ℝ :=
  ofY N (Cvs.Finite.CoefficientDilation.dil (qr N) t (toY N xi))

theorem dilE_even (N : ℕ) (t : ℝ) (xi : Cvs.Finite.SymmetricModeSet.Idx N → ℝ) (i) :
    dilE N t xi (Cvs.Finite.SymmetricModeSet.negI N i) = dilE N t xi i := ofY_even N _ i

/-- The secular polynomial commutes with complexification. -/
theorem Psec_map {κ : Type*} [Fintype κ] [DecidableEq κ] (q y : κ → ℝ) :
    (Cvs.Finite.CoefficientDilation.Psec q y).map Complex.ofRealHom
      = Cvs.Finite.CoefficientDilation.Psec (fun k => ((q k : ℝ) : ℂ)) (fun k => ((y k : ℝ) : ℂ)) := by
  unfold Cvs.Finite.CoefficientDilation.Psec
  simp [Polynomial.map_sum, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_mul]

/-- The dilation commutes with complexification. -/
theorem dil_map {κ : Type*} [Fintype κ] [DecidableEq κ] (q y : κ → ℝ) (t : ℝ) (k : κ) :
    ((Cvs.Finite.CoefficientDilation.dil q t y k : ℝ) : ℂ)
      = Cvs.Finite.CoefficientDilation.dil (fun k => ((q k : ℝ) : ℂ)) (t : ℂ) (fun k => ((y k : ℝ) : ℂ)) k := by
  unfold Cvs.Finite.CoefficientDilation.dil
  have h1 : (Cvs.Finite.CoefficientDilation.Psec (fun k => ((q k : ℝ) : ℂ)) (fun k => ((y k : ℝ) : ℂ))).eval
      (((q k : ℝ) : ℂ) / (t : ℂ))
      = (((Cvs.Finite.CoefficientDilation.Psec q y).eval (q k / t) : ℝ) : ℂ) := by
    rw [← Psec_map, Polynomial.eval_map,
      show ((q k : ℝ) : ℂ) / (t : ℂ) = Complex.ofRealHom (q k / t) by
        rw [Complex.ofRealHom_eq_coe]; push_cast; rfl,
      Polynomial.eval₂_at_apply, Complex.ofRealHom_eq_coe]
  rw [h1]
  push_cast
  rfl

/-- **The rational factor of the dilated vector**, through the complex dilation. -/
theorem R_dilE (N : ℕ) (t : ℝ) {xi : Cvs.Finite.SymmetricModeSet.Idx N → ℝ} (u : ℂ) :
    Cvs.Finite.UniversalFunctionPairing.R (Cvs.Finite.SymmetricModeSet.mode N) (dilE N t xi) u
      = Cvs.Finite.CoefficientDilation.Rq (fun m => ((qr N m : ℝ) : ℂ))
          (Cvs.Finite.CoefficientDilation.dil (fun m => ((qr N m : ℝ) : ℂ)) (t : ℂ)
            (fun m => ((toY N xi m : ℝ) : ℂ))) u := by
  rw [R_eq_Rq N (dilE_even N t xi)]
  unfold dilE
  rw [toY_ofY]
  unfold Cvs.Finite.CoefficientDilation.Rq
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [dil_map]

theorem qr_injective_C (N : ℕ) : Function.Injective (fun m => ((qr N m : ℝ) : ℂ)) := by
  intro m m' h
  have h' : ((qr N m : ℝ) : ℂ) = qr N m' := h
  exact qr_injective N (by exact_mod_cast h')

/-- **The transfer identity for the universal function**, division-free: with `t = s²`,
`F_{dilE}(s·u)·L-side factors = F_xi(u)·L'-side factors`. -/
theorem F_dilE_mul (N : ℕ) {s : ℝ} (hs : s ≠ 0) {xi : Cvs.Finite.SymmetricModeSet.Idx N → ℝ}
    (hxieven : ∀ i, xi (Cvs.Finite.SymmetricModeSet.negI N i) = xi i) {u : ℂ}
    (hu : ∀ m, ((qr N m : ℝ) : ℂ) - u ^ 2 ≠ 0) (hu' : ∀ m, ((qr N m : ℝ) : ℂ) - ((s : ℂ) * u) ^ 2 ≠ 0) :
    Cvs.Finite.UniversalFunctionPairing.F (Cvs.Finite.SymmetricModeSet.mode N) (dilE N (s ^ 2) xi) ((s : ℂ) * u)
        * (∏ m, (((qr N m : ℝ) : ℂ) - ((s : ℂ) * u) ^ 2)) ^ 2 * Complex.sin (u / 2) ^ 2
      = Cvs.Finite.UniversalFunctionPairing.F (Cvs.Finite.SymmetricModeSet.mode N) xi u
        * (∏ m, (((qr N m : ℝ) : ℂ) - u ^ 2)) ^ 2 * (s : ℂ) ^ 2 * Complex.sin ((s : ℂ) * u / 2) ^ 2 := by
  unfold Cvs.Finite.UniversalFunctionPairing.F
  rw [R_dilE, R_eq_Rq N hxieven]
  have htr := Cvs.Finite.CoefficientDilation.Rq_dil_transfer (qr_injective_C N) (s := (s : ℂ))
    (by exact_mod_cast hs) (fun m => ((toY N xi m : ℝ) : ℂ)) hu hu'
  rw [show ((s : ℂ)) ^ 2 = (((s ^ 2 : ℝ)) : ℂ) by push_cast; ring] at htr
  rw [htr, div_pow]
  have hne : ∏ m, (((qr N m : ℝ) : ℂ) - ((s : ℂ) * u) ^ 2) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun m _ => hu' m
  have hne2 : (∏ m, (((qr N m : ℝ) : ℂ) - ((s : ℂ) * u) ^ 2)) ^ 2 ≠ 0 := pow_ne_zero 2 hne
  have key : (Cvs.Finite.CoefficientDilation.Rq (fun m => ((qr N m : ℝ) : ℂ))
        (fun m => ((toY N xi m : ℝ) : ℂ)) u * ∏ l, (((qr N l : ℝ) : ℂ) - u ^ 2)) ^ 2
        / (∏ m, (((qr N m : ℝ) : ℂ) - ((s : ℂ) * u) ^ 2)) ^ 2
      * (∏ m, (((qr N m : ℝ) : ℂ) - ((s : ℂ) * u) ^ 2)) ^ 2
      = (Cvs.Finite.CoefficientDilation.Rq (fun m => ((qr N m : ℝ) : ℂ))
        (fun m => ((toY N xi m : ℝ) : ℂ)) u * ∏ l, (((qr N l : ℝ) : ℂ) - u ^ 2)) ^ 2 :=
    div_mul_cancel₀ _ hne2
  linear_combination (4 * ((s : ℂ) * u) ^ 2 * Complex.sin ((s : ℂ) * u / 2) ^ 2
    * Complex.sin (u / 2) ^ 2) * key

/-- The pair node is the squared frequency of a representative index. -/
theorem qr_eq_q (N : ℕ) (m : PIdx N) :
    ((qr N m : ℝ) : ℂ) = Cvs.Finite.VanishingMomentsDamping.q (Cvs.Finite.SymmetricModeSet.mode N)
      (m.map fun k => (k, true)) := by
  rcases m with _ | k <;> simp [qr, amode, Cvs.Finite.VanishingMomentsDamping.q, Cvs.Finite.SymmetricModeSet.mode]

/-- Genericity at a scale, on the pair nodes. -/
theorem qr_sub_ne {L : ℝ} (hL : 0 < L) (N : ℕ) {z : ℂ}
    (hgen : ∀ k, ((2 * π * Cvs.Finite.SymmetricModeSet.mode N k / L : ℝ) : ℂ) ^ 2 - z ^ 2 ≠ 0) (m : PIdx N) :
    ((qr N m : ℝ) : ℂ) - ((L : ℂ) * z) ^ 2 ≠ 0 := by
  rw [qr_eq_q]
  exact Cvs.Finite.VanishingMomentsDamping.q_sub_ne hL _ hgen _

/-- **Nesting as an identity**: the CvS form at scale `L'` of the dilated vector is the zero sum
of the original's universal function at scale `L`, reweighted zero by zero. -/
theorem quadForm_dilE {L L' : ℝ} (hL : 0 < L) (hL' : 0 < L') (N : ℕ)
    {xi : Cvs.Finite.SymmetricModeSet.Idx N → ℝ}
    (hxieven : ∀ i, xi (Cvs.Finite.SymmetricModeSet.negI N i) = xi i)
    (hgen : ∀ rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet, ∀ k,
      ((2 * π * Cvs.Finite.SymmetricModeSet.mode N k / L : ℝ) : ℂ) ^ 2 - (Cvs.ZeroCounting.zPoint rho) ^ 2 ≠ 0)
    (hgen' : ∀ rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet, ∀ k,
      ((2 * π * Cvs.Finite.SymmetricModeSet.mode N k / L' : ℝ) : ℂ) ^ 2 - (Cvs.ZeroCounting.zPoint rho) ^ 2 ≠ 0)
    (hsin : ∀ rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet,
      Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ≠ 0) :
    dilE N ((L' / L) ^ 2) xi ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M ⌈Real.exp L'⌉₊ ⌈L' / Real.log 2⌉₊ L'
        (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ dilE N ((L' / L) ^ 2) xi)
      = L' * ∑' rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet,
          (Cvs.Criterion.divisorWeight rho : ℝ)
            * (Cvs.Finite.UniversalFunctionPairing.F (Cvs.Finite.SymmetricModeSet.mode N) xi
                ((L : ℂ) * Cvs.ZeroCounting.zPoint rho)
              * ((((L' / L : ℝ)) : ℂ) ^ 2
                * Complex.sin ((L' : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2
                * (∏ m, (((qr N m : ℝ) : ℂ) - ((L : ℂ) * Cvs.ZeroCounting.zPoint rho) ^ 2)) ^ 2)
              / (Complex.sin ((L : ℂ) * Cvs.ZeroCounting.zPoint rho / 2) ^ 2
                * (∏ m, (((qr N m : ℝ) : ℂ) - ((L' : ℂ) * Cvs.ZeroCounting.zPoint rho) ^ 2)) ^ 2)).re := by
  classical
  rw [Cvs.Finite.UniversalFunctionPairing.quadForm_eq_universal hL' (Cvs.Finite.SymmetricModeSet.mode_injective N)
    (Cvs.Finite.SymmetricModeSet.negI_involutive N) (Cvs.Finite.SymmetricModeSet.mode_negI N)
    (dilE_even N _ xi) hgen']
  refine congrArg (L' * ·) ?_
  refine tsum_congr fun rho => ?_
  refine congrArg (fun w : ℂ => (Cvs.Criterion.divisorWeight rho : ℝ) * w.re) ?_
  set z := Cvs.ZeroCounting.zPoint rho with hz
  set s : ℝ := L' / L with hs
  have hs0 : s ≠ 0 := by rw [hs]; exact div_ne_zero hL'.ne' hL.ne'
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hsu : (L' : ℂ) * z = (s : ℂ) * ((L : ℂ) * z) := by
    rw [hs]; push_cast; field_simp
  have hu := fun m => qr_sub_ne hL N (hgen rho) m
  have hu' : ∀ m, ((qr N m : ℝ) : ℂ) - ((s : ℂ) * ((L : ℂ) * z)) ^ 2 ≠ 0 := by
    intro m; rw [← hsu]; exact qr_sub_ne hL' N (hgen' rho) m
  have hmul := F_dilE_mul N hs0 hxieven (u := (L : ℂ) * z) hu hu'
  rw [← hsu] at hmul
  have hne : (∏ m, (((qr N m : ℝ) : ℂ) - ((L' : ℂ) * z) ^ 2)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (Finset.prod_ne_zero_iff.mpr fun m _ => by rw [hsu]; exact hu' m)
  have hsin2 : Complex.sin ((L : ℂ) * z / 2) ^ 2 ≠ 0 := pow_ne_zero 2 (hsin rho)
  rw [eq_div_iff (mul_ne_zero hsin2 hne)]
  linear_combination hmul

end Cvs.Finite.NestedMinimiser
