import N7.Kernel.Cover.Verified
import N7.Kernel.MatrixPositive
import N7.Kernel.EqualityReduction

set_option autoImplicit false
namespace N7

/-- The sharp seven-point bound, under only the original energy constraint. -/
theorem mordell_seven_norm_bound {z : Configuration} (hz : energy z = 7) :
    delta z ≤ sharpConstant :=
  Kernel.upper_of_domainMajorant Kernel.matrix Kernel.matrix_posDef
    Kernel.Cover.domain_majorant hz

/-- All equality cases are rotations and relabellings of the explicit hexagon witness. -/
theorem mordell_seven_norm_equality_iff {z : Configuration} (hz : energy z = 7) :
    delta z = sharpConstant ↔ IsCenteredHexagon z :=
  Kernel.equality_iff_of_majorant Kernel.matrix Kernel.matrix_posDef
    (Kernel.maximum_majorant_of_domainMajorant Kernel.matrix
      Kernel.Cover.domain_majorant) hz

#print mordell_seven_norm_bound
#print mordell_seven_sharp_witness
#print mordell_seven_norm_equality_iff
#print axioms mordell_seven_norm_bound
#print axioms mordell_seven_sharp_witness
#print axioms mordell_seven_norm_equality_iff
end N7
