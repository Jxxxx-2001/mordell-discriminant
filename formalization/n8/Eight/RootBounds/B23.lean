import Eight.CubicBoxes.B23.C06
import Eight.RootPartition
namespace MordellEight.CubicBoxes.B23
open FixedTensor IntegerCube RationalCube Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace G1
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/1048576),(965267/1048576)],![(965267/1048576),(2895801/2097152),(965267/524288)]⟩
theorem bound : BoxMajorant box := Leaf0.bound
end G1

namespace G4
def box : ClosedBox 3 := ⟨![(965267/2097152),(2895801/2097152),(965267/1048576)],![(2895801/4194304),(965267/524288),(2895801/2097152)]⟩
theorem bound : BoxMajorant box := Leaf1.bound
end G4

namespace G6
def box : ClosedBox 3 := ⟨![(2895801/4194304),(2895801/2097152),(965267/1048576)],![(965267/1048576),(6756869/4194304),(2895801/2097152)]⟩
theorem bound : BoxMajorant box := Leaf2.bound
end G6

namespace G8
def box : ClosedBox 3 := ⟨![(2895801/4194304),(6756869/4194304),(965267/1048576)],![(965267/1048576),(965267/524288),(4826335/4194304)]⟩
theorem bound : BoxMajorant box := Leaf3.bound
end G8

namespace G9
def box : ClosedBox 3 := ⟨![(2895801/4194304),(6756869/4194304),(4826335/4194304)],![(965267/1048576),(965267/524288),(2895801/2097152)]⟩
theorem bound : BoxMajorant box := Leaf4.bound
end G9

namespace G7
def box : ClosedBox 3 := ⟨![(2895801/4194304),(6756869/4194304),(965267/1048576)],![(965267/1048576),(965267/524288),(2895801/2097152)]⟩
theorem eq_false : box.half 2 false=G8.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G9.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G8.bound) (by rw [eq_true]; exact G9.bound)
end G7

namespace G5
def box : ClosedBox 3 := ⟨![(2895801/4194304),(2895801/2097152),(965267/1048576)],![(965267/1048576),(965267/524288),(2895801/2097152)]⟩
theorem eq_false : box.half 1 false=G6.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G7.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G6.bound) (by rw [eq_true]; exact G7.bound)
end G5

namespace G3
def box : ClosedBox 3 := ⟨![(965267/2097152),(2895801/2097152),(965267/1048576)],![(965267/1048576),(965267/524288),(2895801/2097152)]⟩
theorem eq_false : box.half 0 false=G4.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G5.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G4.bound) (by rw [eq_true]; exact G5.bound)
end G3

namespace G10
def box : ClosedBox 3 := ⟨![(965267/2097152),(2895801/2097152),(2895801/2097152)],![(965267/1048576),(965267/524288),(965267/524288)]⟩
theorem checked : outsideCheck box=true := by decide +kernel
theorem bound : BoxMajorant box := by
  intro x hx hd
  exact (outsideCheck_sound box checked hx hd.1 hd.2).elim
end G10

namespace G2
def box : ClosedBox 3 := ⟨![(965267/2097152),(2895801/2097152),(965267/1048576)],![(965267/1048576),(965267/524288),(965267/524288)]⟩
theorem eq_false : box.half 2 false=G3.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G10.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G3.bound) (by rw [eq_true]; exact G10.bound)
end G2

namespace G0
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/1048576),(965267/1048576)],![(965267/1048576),(965267/524288),(965267/524288)]⟩
theorem eq_false : box.half 1 false=G1.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G2.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G1.bound) (by rw [eq_true]; exact G2.bound)
end G0

end MordellEight.CubicBoxes.B23
namespace MordellEight.RootBounds.B23
open FixedTensor IntegerCube RationalCube Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem box_eq : MordellEight.CubicBoxes.B23.G0.box=RootPartition.B23 := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem majorant : BoxMajorant RootPartition.B23 := by
  rw [←box_eq]
  exact MordellEight.CubicBoxes.B23.G0.bound
#print axioms majorant
end MordellEight.RootBounds.B23
