import Eight.KernelPieces.K0
import Eight.KernelPieces.K1
import Eight.KernelPieces.K2
import Eight.KernelPieces.K3
import Eight.KernelPieces.K4
import Eight.KernelPieces.K5
import Eight.KernelPieces.K6
import Eight.ExactDefinition

namespace MordellEight
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def certifiedPieces : Fin 7 → DenseKernel :=
  ![KernelPiece0.polynomial,KernelPiece1.polynomial,KernelPiece2.polynomial,KernelPiece3.polynomial,KernelPiece4.polynomial,KernelPiece5.polynomial,KernelPiece6.polynomial]

theorem certifiedPieces_real (k : Fin 7) (u v t : ℝ) :
    (certifiedPieces k).real u v t=kernelPiece k u v t := by
  fin_cases k
  · exact KernelPiece0.polynomial_real u v t
  · exact KernelPiece1.polynomial_real u v t
  · exact KernelPiece2.polynomial_real u v t
  · exact KernelPiece3.polynomial_real u v t
  · exact KernelPiece4.polynomial_real u v t
  · exact KernelPiece5.polynomial_real u v t
  · exact KernelPiece6.polynomial_real u v t

theorem matrix_majorant_certificate :
    densePadCheck (majorantDense certifiedPieces) exactMajorant.dense=true := by
  decide +kernel

theorem exact_majorant_eq_kernel (u v t : ℝ) :
    exactMajorant.real u v t=majorantFromMatrices u v t := by
  have h := densePadCheck_sound _ _ matrix_majorant_certificate u v t
  rw [majorantDense_real certifiedPieces certifiedPieces_real,ExactKernel.dense_real] at h
  exact h.symm

end MordellEight
