import Mathlib
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroSideMoments

/-!
# The moments converge
-/

set_option maxHeartbeats 1000000

noncomputable section

open Complex MeasureTheory Finset

namespace Cvs.ZeroCounting

/-- The zero-side point has the ordinate as its real part. -/
theorem zPoint_re (rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet) :
    (zPoint rho).re = (rho : ℂ).im := by
  unfold zPoint; simp

/-- Its imaginary part is minus the distance off the line. -/
theorem zPoint_im (rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet) :
    (zPoint rho).im = -((rho : ℂ).re - 1 / 2) := by
  unfold zPoint; simp

/-- The strip bounds the imaginary part of the zero-side point. -/
theorem sq_zPoint_im_le (rho : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet) :
    (zPoint rho).im ^ 2 ≤ 1 / 4 := by
  have hd := abs_le.mp (Cvs.Zeta.GaussKernel.AdmissibleKernel.abs_re_sub_half_le rho)
  rw [zPoint_im]
  nlinarith [hd.1, hd.2]

end Cvs.ZeroCounting
