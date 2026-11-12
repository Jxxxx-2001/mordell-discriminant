import N7.Kernel.Local.C0T00
import N7.Kernel.Local.C0T01
import N7.Kernel.Local.C0T11
set_option autoImplicit false
set_option maxRecDepth 64000
set_option maxHeartbeats 0
namespace N7.Kernel.Local.C0
open LocalCongruence LocalGeometry GapAnalytic Checks Matrix
def transformed : Fin 2 → Fin 2 → DenseKernel := ![![C0T00.polynomial,C0T01.polynomial],![C0T01.polynomial,C0T11.polynomial]]
theorem transformed_checked (i j : Fin 2) : densePadCheck (conjugateDense T polys i j) (transformed i j)=true := by
  fin_cases i <;> fin_cases j
  · exact C0T00.checked
  · exact C0T01.checked
  · exact C0T01.checked_reverse
  · exact C0T11.checked
theorem transformed_real (i j : Fin 2) (x : Fin 3 → ℝ) : (transformed i j).real (x 0-center 0) (x 1-center 1) (x 2-center 2)=∑ a,∑ b,(T a i:ℝ)*(T b j:ℝ)*eval3 (partialPoly (partialPoly exactMajorant (indices a)) (indices b)) x := by
  have h := densePadCheck_sound _ _ (transformed_checked i j) (x 0-center 0) (x 1-center 1) (x 2-center 2)
  rw [conjugateDense_real] at h
  simp_rw [polys_real] at h
  exact h.symm
def largeBounds := conjugateBounds center largeRadius indices T transformed
def largeC : Matrix (Fin 2) (Fin 2) ℚ := ![![(1759594327/8000000000:ℚ),(-16674207/1000000000000:ℚ)],![(-16674207/1000000000000:ℚ),(180106270711/1000000000000:ℚ)]]
def largeU : Matrix (Fin 2) (Fin 2) ℚ := ![![1,(-16674207/182209679603:ℚ)],![0,1]]
def largeR : Matrix (Fin 2) (Fin 2) ℚ := ![![1,(16674207/182209679603:ℚ)],![0,1]]
def largeD : Fin 2 → ℚ := ![(182209679603/1000000000000:ℚ),(6485145781125106660967/45552419900750000000000:ℚ)]
def largeError : ℚ := (4717451409/250000000000:ℚ)
theorem large_checked : intervalMatrixCheck largeBounds largeC largeU largeR largeD largeError=true := by decide +kernel
theorem large_hessian_psd {x : Fin 3 → ℝ} (hn : Near center largeRadius x) : ((hessian exactMajorant x).submatrix indices indices).PosSemidef := by
  apply psd_of_congruence_inverse _ (realMatrix T) (realMatrix S) inverse_real
  apply (intervalMatrixCheck_sound largeBounds largeC largeU largeR largeD largeError large_checked _ _ _).posSemidef
  · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.isHermitian_conjTranspose_mul_mul (realMatrix T) ((hessian_isHermitian exactMajorant x).submatrix indices)
  · exact conjugateBounds_sound exactMajorant center largeRadius indices T transformed transformed_real large_distance_pos hn
#print axioms large_hessian_psd
end N7.Kernel.Local.C0
