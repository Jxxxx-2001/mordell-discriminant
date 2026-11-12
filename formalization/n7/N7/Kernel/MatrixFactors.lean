import N7.Kernel.MatrixQ0
set_option autoImplicit false
set_option maxRecDepth 64000
set_option maxHeartbeats 0
namespace N7.Kernel
open Checks

theorem matrix1_factor_checked :
    factorCheck (matrixLower 1) (matrixU 1) (matrixR 1) (matrixD 1) = true := by
  decide +kernel

theorem matrix2_factor_checked :
    factorCheck (matrixLower 2) (matrixU 2) (matrixR 2) (matrixD 2) = true := by
  decide +kernel

theorem matrix3_factor_checked :
    factorCheck (matrixLower 3) (matrixU 3) (matrixR 3) (matrixD 3) = true := by
  decide +kernel

theorem matrix4_factor_checked :
    factorCheck (matrixLower 4) (matrixU 4) (matrixR 4) (matrixD 4) = true := by
  decide +kernel

theorem matrix5_factor_checked :
    factorCheck (matrixLower 5) (matrixU 5) (matrixR 5) (matrixD 5) = true := by
  decide +kernel

theorem matrix_factor_checked (k : Fin 6) :
    factorCheck (matrixLower k) (matrixU k) (matrixR k) (matrixD k) = true := by
  fin_cases k <;> first
  | exact matrix0_factor_checked
  | exact matrix1_factor_checked
  | exact matrix2_factor_checked
  | exact matrix3_factor_checked
  | exact matrix4_factor_checked
  | exact matrix5_factor_checked

#print axioms matrix_factor_checked
end N7.Kernel
