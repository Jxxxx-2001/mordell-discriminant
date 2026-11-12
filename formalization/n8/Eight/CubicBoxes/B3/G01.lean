import Eight.CubicBoxes.B3.C16
import Eight.CubicBoxes.B3.C17
import Eight.CubicBoxes.B3.G00
import Eight.RootPartition
import Eight.LocalLeaf
namespace MordellEight.CubicBoxes.B3
open FixedTensor IntegerCube RationalCube Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace G78
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/2097152),(-965267/4194304)],![(2895801/4194304),(2895801/4194304),0]⟩
theorem eq_false : box.half 0 false=G79.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G84.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G79.bound) (by rw [eq_true]; exact G84.bound)
end G78

namespace G76
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/2097152),(-965267/2097152)],![(2895801/4194304),(2895801/4194304),0]⟩
theorem eq_false : box.half 2 false=G77.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G78.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G77.bound) (by rw [eq_true]; exact G78.bound)
end G76

namespace G86
def box : ClosedBox 3 := ⟨![(965267/2097152),(2895801/4194304),(-965267/2097152)],![(2895801/4194304),(965267/1048576),(-965267/4194304)]⟩
theorem bound : BoxMajorant box := Leaf41.bound
end G86

namespace G87
def box : ClosedBox 3 := ⟨![(965267/2097152),(2895801/4194304),(-965267/4194304)],![(2895801/4194304),(965267/1048576),0]⟩
theorem bound : BoxMajorant box := Leaf42.bound
end G87

namespace G85
def box : ClosedBox 3 := ⟨![(965267/2097152),(2895801/4194304),(-965267/2097152)],![(2895801/4194304),(965267/1048576),0]⟩
theorem eq_false : box.half 2 false=G86.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G87.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G86.bound) (by rw [eq_true]; exact G87.bound)
end G85

namespace G75
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/2097152),(-965267/2097152)],![(2895801/4194304),(965267/1048576),0]⟩
theorem eq_false : box.half 1 false=G76.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G85.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G76.bound) (by rw [eq_true]; exact G85.bound)
end G75

namespace G89
def box : ClosedBox 3 := ⟨![(2895801/4194304),(965267/2097152),(-965267/2097152)],![(965267/1048576),(2895801/4194304),0]⟩
theorem bound : BoxMajorant box := Leaf43.bound
end G89

namespace G91
def box : ClosedBox 3 := ⟨![(2895801/4194304),(2895801/4194304),(-965267/2097152)],![(965267/1048576),(965267/1048576),(-965267/4194304)]⟩
theorem bound : BoxMajorant box := Leaf44.bound
end G91

namespace G92
def box : ClosedBox 3 := ⟨![(2895801/4194304),(2895801/4194304),(-965267/4194304)],![(965267/1048576),(965267/1048576),0]⟩
theorem bound : BoxMajorant box := Leaf45.bound
end G92

namespace G90
def box : ClosedBox 3 := ⟨![(2895801/4194304),(2895801/4194304),(-965267/2097152)],![(965267/1048576),(965267/1048576),0]⟩
theorem eq_false : box.half 2 false=G91.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G92.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G91.bound) (by rw [eq_true]; exact G92.bound)
end G90

namespace G88
def box : ClosedBox 3 := ⟨![(2895801/4194304),(965267/2097152),(-965267/2097152)],![(965267/1048576),(965267/1048576),0]⟩
theorem eq_false : box.half 1 false=G89.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G90.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G89.bound) (by rw [eq_true]; exact G90.bound)
end G88

namespace G74
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/2097152),(-965267/2097152)],![(965267/1048576),(965267/1048576),0]⟩
theorem eq_false : box.half 0 false=G75.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G88.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G75.bound) (by rw [eq_true]; exact G88.bound)
end G74

namespace G0
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/2097152),(-965267/1048576)],![(965267/1048576),(965267/1048576),0]⟩
theorem eq_false : box.half 2 false=G1.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G74.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G1.bound) (by rw [eq_true]; exact G74.bound)
end G0

end MordellEight.CubicBoxes.B3
