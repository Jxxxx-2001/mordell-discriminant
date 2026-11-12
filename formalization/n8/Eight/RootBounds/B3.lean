import Eight.CubicBoxes.B3.G01
import Eight.RootPartition
import Eight.RootGeometry.Narrow
namespace MordellEight.CubicBoxes.B3
open FixedTensor IntegerCube RationalCube Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000

end MordellEight.CubicBoxes.B3
namespace MordellEight.RootBounds.B3
open FixedTensor IntegerCube RationalCube Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem box_eq : MordellEight.CubicBoxes.B3.G0.box=RootGeometry.narrowBox RootPartition.B3 := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem majorant : BoxMajorant RootPartition.B3 := by
  apply RootGeometry.majorant_of_narrow RootPartition.B3
  rw [←box_eq]
  exact MordellEight.CubicBoxes.B3.G0.bound
#print axioms majorant
end MordellEight.RootBounds.B3
