import N7.Kernel.MatrixCheckData
set_option autoImplicit false
set_option maxRecDepth 64000
set_option maxHeartbeats 0
namespace N7.Kernel
open Checks
theorem matrix0_factor_checked :
    factorCheck (matrixLower 0) (matrixU 0) (matrixR 0) (matrixD 0) = true := by
  decide +kernel
#print axioms matrix0_factor_checked
end N7.Kernel
