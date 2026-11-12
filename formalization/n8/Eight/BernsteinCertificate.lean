import Eight.BernsteinDense

namespace MordellEight
open Checks

theorem DenseKernel.affine_checked_real (p U V T : DenseKernel) (lu du lv dv lt dt : ℚ)
    (hU : denseCheck ((p.shiftU lu).rescaleU du) U = true)
    (hV : denseCheck ((U.shiftV lv).rescaleV dv) V = true)
    (hT : denseCheck ((V.shiftT lt).rescaleT dt) T = true) (u v t : ℝ) :
    T.real u v t = p.real ((du : ℝ)*u+lu) ((dv : ℝ)*v+lv) ((dt : ℝ)*t+lt) := by
  rw [←denseCheck_sound hT,DenseKernel.rescaleT_real,DenseKernel.shiftT_real,
      ←denseCheck_sound hV,DenseKernel.rescaleV_real,DenseKernel.shiftV_real,
      ←denseCheck_sound hU,DenseKernel.rescaleU_real,DenseKernel.shiftU_real]

theorem DenseKernel.bernstein_checked_nonneg (p U V T : DenseKernel)
    (hU : denseCheck p.bernU U = true) (hV : denseCheck U.bernV V = true)
    (hT : denseCheck V.bernT T = true) (hc : T.nonnegCheck = true)
    (u v t : ℝ) (hu : 0 ≤ u ∧ u ≤ 1) (hv : 0 ≤ v ∧ v ≤ 1) (ht : 0 ≤ t ∧ t ≤ 1) :
    0 ≤ p.real u v t := by
  apply DenseKernel.bernstein_sound p u v t hu hv ht
  rw [denseCheck_sound hU,denseCheck_sound hV,denseCheck_sound hT]
  exact hc

end MordellEight
