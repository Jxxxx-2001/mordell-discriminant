import Eight.CubicBoxes.B6.G01
import Eight.RootPartition
namespace MordellEight.CubicBoxes.B6
open FixedTensor IntegerCube RationalCube Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000

end MordellEight.CubicBoxes.B6
namespace MordellEight.RootBounds.B6
open FixedTensor IntegerCube RationalCube Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem box_eq : MordellEight.CubicBoxes.B6.G0.box=RootPartition.B6 := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem majorant : BoxMajorant RootPartition.B6 := by
  rw [←box_eq]
  exact MordellEight.CubicBoxes.B6.G0.bound
#print axioms majorant
end MordellEight.RootBounds.B6
