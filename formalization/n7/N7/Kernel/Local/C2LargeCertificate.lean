import N7.Kernel.Local.C2T00
import N7.Kernel.Local.C2T01
import N7.Kernel.Local.C2T02
import N7.Kernel.Local.C2T11
import N7.Kernel.Local.C2T12
import N7.Kernel.Local.C2T22
set_option autoImplicit false
set_option maxRecDepth 64000
set_option maxHeartbeats 0
namespace N7.Kernel.Local.C2
open LocalCongruence LocalGeometry GapAnalytic Checks Matrix
def transformed : Fin 3 → Fin 3 → DenseKernel := ![![C2T00.polynomial,C2T01.polynomial,C2T02.polynomial],![C2T01.polynomial,C2T11.polynomial,C2T12.polynomial],![C2T02.polynomial,C2T12.polynomial,C2T22.polynomial]]
theorem transformed_checked (i j : Fin 3) : densePadCheck (conjugateDense T polys i j) (transformed i j)=true := by
  fin_cases i <;> fin_cases j
  · exact C2T00.checked
  · exact C2T01.checked
  · exact C2T02.checked
  · exact C2T01.checked_reverse
  · exact C2T11.checked
  · exact C2T12.checked
  · exact C2T02.checked_reverse
  · exact C2T12.checked_reverse
  · exact C2T22.checked
theorem transformed_real (i j : Fin 3) (x : Fin 3 → ℝ) : (transformed i j).real (x 0-center 0) (x 1-center 1) (x 2-center 2)=∑ a,∑ b,(T a i:ℝ)*(T b j:ℝ)*eval3 (partialPoly (partialPoly exactMajorant (indices a)) (indices b)) x := by
  have h := densePadCheck_sound _ _ (transformed_checked i j) (x 0-center 0) (x 1-center 1) (x 2-center 2)
  rw [conjugateDense_real] at h
  simp_rw [polys_real] at h
  exact h.symm
def largeBounds := conjugateBounds center largeRadius indices T transformed
theorem large_checked : LocalSchur.check largeBounds=true := by decide +kernel
theorem large_hessian_psd {x : Fin 3 → ℝ} (hn : Near center largeRadius x) : ((hessian exactMajorant x).submatrix indices indices).PosSemidef := by
  apply psd_of_congruence_inverse _ (realMatrix T) (realMatrix S) inverse_real
  apply LocalSchur.check_sound largeBounds large_checked
  · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.isHermitian_conjTranspose_mul_mul (realMatrix T) ((hessian_isHermitian exactMajorant x).submatrix indices)
  · exact conjugateBounds_sound exactMajorant center largeRadius indices T transformed transformed_real large_distance_pos hn
#print axioms large_hessian_psd
end N7.Kernel.Local.C2
