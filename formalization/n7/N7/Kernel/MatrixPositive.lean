import N7.Kernel.MatrixFactors
import N7.Kernel.MatrixBounds
set_option autoImplicit false
namespace N7.Kernel
open Checks

theorem matrix_lower_posDef (k : Fin 6) : (realMatrix (matrixLower k)).PosDef :=
  factorCheck_sound _ _ _ _ (matrix_factor_checked k)

/-- All six exact log-valued matrices are positive definite. -/
theorem matrix_posDef (k : Fin 6) : (matrix k).PosDef := by
  apply uniform_perturbation_posDef (matrix k) (realMatrix (matrixCenter k))
    (matrixError : ℝ)
  · norm_num [matrixError]
  · exact matrix_isHermitian k
  · exact matrix_entry_error_bound k
  · have h := matrix_lower_posDef k
    simpa only [matrixLower, realMatrix_sub, realMatrix_diagonal,
      Rat.cast_mul, Rat.cast_ofNat] using h

#print axioms matrix_posDef
end N7.Kernel
