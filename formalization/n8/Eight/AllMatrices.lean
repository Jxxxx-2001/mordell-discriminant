import Eight.MatrixCertificates.Q0
import Eight.MatrixCertificates.Q1
import Eight.MatrixCertificates.Q2
import Eight.MatrixCertificates.Q3
import Eight.MatrixCertificates.Q4
import Eight.MatrixCertificates.Q5

namespace MordellEight

noncomputable def kernelQ (k : Fin 7) : Matrix (Fin 4) (Fin 4) ℝ :=
  kernelMatrixReal (allMatrixCoefficients k)

theorem kernelQ_six : kernelQ 6=Q6 := by
  ext i j
  exact (Q6_coefficient_semantics i j).symm

theorem all_kernel_posDef (k : Fin 7) : (kernelQ k).PosDef := by
  fin_cases k
  · exact MatrixCertificate0.posDef
  · exact MatrixCertificate1.posDef
  · exact MatrixCertificate2.posDef
  · exact MatrixCertificate3.posDef
  · exact MatrixCertificate4.posDef
  · exact MatrixCertificate5.posDef
  · change (kernelQ 6).PosDef
    rw [kernelQ_six]
    exact Q6_posDef

end MordellEight
