import N7.Kernel.PolynomialPiece0
import N7.Kernel.PolynomialPiece1
import N7.Kernel.PolynomialPiece2
import N7.Kernel.PolynomialPiece3
import N7.Kernel.PolynomialPiece4
import N7.Kernel.PolynomialPiece5
import N7.Kernel.PolynomialData
set_option autoImplicit false
set_option maxRecDepth 64000
set_option maxHeartbeats 6000000
namespace N7.Kernel
theorem log_six : Real.log 6 = Real.log 2 + Real.log 3 := by
  have h := Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)
  norm_num at h
  exact h

theorem kernel_sum_polynomials (a b c : ℝ) :
    kernelFromMatrices matrix a b c = piecePolynomial0.real a b c + (piecePolynomial1.real a b c + (piecePolynomial2.real a b c + (piecePolynomial3.real a b c + (piecePolynomial4.real a b c + (piecePolynomial5.real a b c + (0)))))) := by
  simp [kernelFromMatrices, Fin.sum_univ_succ, ←piecePolynomial0_real, ←piecePolynomial1_real, ←piecePolynomial2_real, ←piecePolynomial3_real, ←piecePolynomial4_real, ←piecePolynomial5_real]

theorem exact_majorant_eq_kernel (u v t : ℝ) :
    exactMajorant.real u v t = majorantFromMatrices matrix u v t := by
  rw [majorantFromMatrices, kernel_sum_polynomials, kernel_sum_polynomials, kernel_sum_polynomials]
  norm_num [exactMajorant, piecePolynomial0, piecePolynomial1, piecePolynomial2, piecePolynomial3, piecePolynomial4, piecePolynomial5, ExactKernel.real, KernelTerm.real, KernelCoeff.real, log_six]
  <;> ring

#print axioms exact_majorant_eq_kernel
end N7.Kernel
