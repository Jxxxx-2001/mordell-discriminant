import Eight.CubicBoxes.B16.C00
import Eight.CubicBoxes.B16.C01
import Eight.CubicBoxes.B16.C02
import Eight.RootPartition
namespace MordellEight.CubicBoxes.B16
open FixedTensor IntegerCube RationalCube Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace G3
def box : ClosedBox 3 := ⟨![0,0,0],![(965267/2097152),(965267/2097152),(965267/4194304)]⟩
theorem bound : BoxMajorant box := Leaf0.bound
end G3

namespace G4
def box : ClosedBox 3 := ⟨![0,0,(965267/4194304)],![(965267/2097152),(965267/2097152),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf1.bound
end G4

namespace G2
def box : ClosedBox 3 := ⟨![0,0,0],![(965267/2097152),(965267/2097152),(965267/2097152)]⟩
theorem eq_false : box.half 2 false=G3.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G4.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G3.bound) (by rw [eq_true]; exact G4.bound)
end G2

namespace G5
def box : ClosedBox 3 := ⟨![0,0,(965267/2097152)],![(965267/2097152),(965267/2097152),(965267/1048576)]⟩
theorem checked : outsideCheck box=true := by decide +kernel
theorem bound : BoxMajorant box := by
  intro x hx hd
  exact (outsideCheck_sound box checked hx hd.1 hd.2).elim
end G5

namespace G1
def box : ClosedBox 3 := ⟨![0,0,0],![(965267/2097152),(965267/2097152),(965267/1048576)]⟩
theorem eq_false : box.half 2 false=G2.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G5.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G2.bound) (by rw [eq_true]; exact G5.bound)
end G1

namespace G8
def box : ClosedBox 3 := ⟨![0,(965267/2097152),0],![(965267/4194304),(965267/1048576),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf2.bound
end G8

namespace G11
def box : ClosedBox 3 := ⟨![(965267/4194304),(965267/2097152),0],![(965267/2097152),(2895801/4194304),(965267/4194304)]⟩
theorem bound : BoxMajorant box := Leaf3.bound
end G11

namespace G12
def box : ClosedBox 3 := ⟨![(965267/4194304),(965267/2097152),(965267/4194304)],![(965267/2097152),(2895801/4194304),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf4.bound
end G12

namespace G10
def box : ClosedBox 3 := ⟨![(965267/4194304),(965267/2097152),0],![(965267/2097152),(2895801/4194304),(965267/2097152)]⟩
theorem eq_false : box.half 2 false=G11.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G12.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G11.bound) (by rw [eq_true]; exact G12.bound)
end G10

namespace G14
def box : ClosedBox 3 := ⟨![(965267/4194304),(2895801/4194304),0],![(965267/2097152),(965267/1048576),(965267/4194304)]⟩
theorem bound : BoxMajorant box := Leaf5.bound
end G14

namespace G15
def box : ClosedBox 3 := ⟨![(965267/4194304),(2895801/4194304),(965267/4194304)],![(965267/2097152),(965267/1048576),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf6.bound
end G15

namespace G13
def box : ClosedBox 3 := ⟨![(965267/4194304),(2895801/4194304),0],![(965267/2097152),(965267/1048576),(965267/2097152)]⟩
theorem eq_false : box.half 2 false=G14.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G15.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G14.bound) (by rw [eq_true]; exact G15.bound)
end G13

namespace G9
def box : ClosedBox 3 := ⟨![(965267/4194304),(965267/2097152),0],![(965267/2097152),(965267/1048576),(965267/2097152)]⟩
theorem eq_false : box.half 1 false=G10.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G13.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G10.bound) (by rw [eq_true]; exact G13.bound)
end G9

namespace G7
def box : ClosedBox 3 := ⟨![0,(965267/2097152),0],![(965267/2097152),(965267/1048576),(965267/2097152)]⟩
theorem eq_false : box.half 0 false=G8.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G9.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G8.bound) (by rw [eq_true]; exact G9.bound)
end G7

namespace G16
def box : ClosedBox 3 := ⟨![0,(965267/2097152),(965267/2097152)],![(965267/2097152),(965267/1048576),(965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf7.bound
end G16

namespace G6
def box : ClosedBox 3 := ⟨![0,(965267/2097152),0],![(965267/2097152),(965267/1048576),(965267/1048576)]⟩
theorem eq_false : box.half 2 false=G7.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G16.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G7.bound) (by rw [eq_true]; exact G16.bound)
end G6

namespace G0
def box : ClosedBox 3 := ⟨![0,0,0],![(965267/2097152),(965267/1048576),(965267/1048576)]⟩
theorem eq_false : box.half 1 false=G1.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G6.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G1.bound) (by rw [eq_true]; exact G6.bound)
end G0

end MordellEight.CubicBoxes.B16
namespace MordellEight.RootBounds.B16
open FixedTensor IntegerCube RationalCube Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem box_eq : MordellEight.CubicBoxes.B16.G0.box=RootPartition.B16 := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem majorant : BoxMajorant RootPartition.B16 := by
  rw [←box_eq]
  exact MordellEight.CubicBoxes.B16.G0.bound
#print axioms majorant
end MordellEight.RootBounds.B16
