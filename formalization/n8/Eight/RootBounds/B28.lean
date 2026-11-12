import Eight.CubicBoxes.B28.G03
import Eight.RootPartition
namespace MordellEight.CubicBoxes.B28
open FixedTensor IntegerCube RationalCube Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000

end MordellEight.CubicBoxes.B28
namespace MordellEight.RootBounds.B28
open FixedTensor IntegerCube RationalCube Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem box_eq : MordellEight.CubicBoxes.B28.G0.box=RootPartition.B28 := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem majorant : BoxMajorant RootPartition.B28 := by
  rw [←box_eq]
  exact MordellEight.CubicBoxes.B28.G0.bound
#print axioms majorant
end MordellEight.RootBounds.B28
