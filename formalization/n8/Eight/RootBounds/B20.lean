import Eight.CubicBoxes.B20.G03
import Eight.RootPartition
namespace MordellEight.CubicBoxes.B20
open FixedTensor IntegerCube RationalCube Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000

end MordellEight.CubicBoxes.B20
namespace MordellEight.RootBounds.B20
open FixedTensor IntegerCube RationalCube Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem box_eq : MordellEight.CubicBoxes.B20.G0.box=RootPartition.B20 := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem majorant : BoxMajorant RootPartition.B20 := by
  rw [←box_eq]
  exact MordellEight.CubicBoxes.B20.G0.bound
#print axioms majorant
end MordellEight.RootBounds.B20
