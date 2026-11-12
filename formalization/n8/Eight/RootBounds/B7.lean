import Eight.CubicBoxes.B7.G01
import Eight.RootPartition
namespace MordellEight.CubicBoxes.B7
open FixedTensor IntegerCube RationalCube Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000

end MordellEight.CubicBoxes.B7
namespace MordellEight.RootBounds.B7
open FixedTensor IntegerCube RationalCube Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem box_eq : MordellEight.CubicBoxes.B7.G0.box=RootPartition.B7 := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem majorant : BoxMajorant RootPartition.B7 := by
  rw [←box_eq]
  exact MordellEight.CubicBoxes.B7.G0.bound
#print axioms majorant
end MordellEight.RootBounds.B7
