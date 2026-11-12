import Eight.CubicBoxes.B2.G01
import Eight.RootPartition
namespace MordellEight.CubicBoxes.B2
open FixedTensor IntegerCube RationalCube Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000

end MordellEight.CubicBoxes.B2
namespace MordellEight.RootBounds.B2
open FixedTensor IntegerCube RationalCube Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem box_eq : MordellEight.CubicBoxes.B2.G0.box=RootPartition.B2 := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem majorant : BoxMajorant RootPartition.B2 := by
  rw [←box_eq]
  exact MordellEight.CubicBoxes.B2.G0.bound
#print axioms majorant
end MordellEight.RootBounds.B2
