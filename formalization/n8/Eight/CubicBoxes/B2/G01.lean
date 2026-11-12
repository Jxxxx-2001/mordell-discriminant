import Eight.CubicBoxes.B2.C16
import Eight.CubicBoxes.B2.C17
import Eight.CubicBoxes.B2.G00
import Eight.RootPartition
import Eight.LocalLeaf
namespace MordellEight.CubicBoxes.B2
open FixedTensor IntegerCube RationalCube Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace G85
def box : ClosedBox 3 := ⟨![(965267/4194304),(2895801/4194304),(-965267/2097152)],![(965267/2097152),(965267/1048576),(-965267/4194304)]⟩
theorem bound : BoxMajorant box := Leaf40.bound
end G85

namespace G88
def box : ClosedBox 3 := ⟨![(965267/4194304),(2895801/4194304),(-965267/4194304)],![(2895801/8388608),(6756869/8388608),0]⟩
theorem bound : BoxMajorant box := Leaf41.bound
end G88

namespace G89
def box : ClosedBox 3 := ⟨![(965267/4194304),(6756869/8388608),(-965267/4194304)],![(2895801/8388608),(965267/1048576),0]⟩
theorem bound : BoxMajorant box := Leaf42.bound
end G89

namespace G87
def box : ClosedBox 3 := ⟨![(965267/4194304),(2895801/4194304),(-965267/4194304)],![(2895801/8388608),(965267/1048576),0]⟩
theorem eq_false : box.half 1 false=G88.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G89.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G88.bound) (by rw [eq_true]; exact G89.bound)
end G87

namespace G90
def box : ClosedBox 3 := ⟨![(2895801/8388608),(2895801/4194304),(-965267/4194304)],![(965267/2097152),(965267/1048576),0]⟩
theorem bound : BoxMajorant box := Leaf43.bound
end G90

namespace G86
def box : ClosedBox 3 := ⟨![(965267/4194304),(2895801/4194304),(-965267/4194304)],![(965267/2097152),(965267/1048576),0]⟩
theorem eq_false : box.half 0 false=G87.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G90.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G87.bound) (by rw [eq_true]; exact G90.bound)
end G86

namespace G84
def box : ClosedBox 3 := ⟨![(965267/4194304),(2895801/4194304),(-965267/2097152)],![(965267/2097152),(965267/1048576),0]⟩
theorem eq_false : box.half 2 false=G85.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G86.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G85.bound) (by rw [eq_true]; exact G86.bound)
end G84

namespace G72
def box : ClosedBox 3 := ⟨![(965267/4194304),(965267/2097152),(-965267/2097152)],![(965267/2097152),(965267/1048576),0]⟩
theorem eq_false : box.half 1 false=G73.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G84.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G73.bound) (by rw [eq_true]; exact G84.bound)
end G72

namespace G64
def box : ClosedBox 3 := ⟨![0,(965267/2097152),(-965267/2097152)],![(965267/2097152),(965267/1048576),0]⟩
theorem eq_false : box.half 0 false=G65.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G72.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G65.bound) (by rw [eq_true]; exact G72.bound)
end G64

namespace G50
def box : ClosedBox 3 := ⟨![0,(965267/2097152),(-965267/1048576)],![(965267/2097152),(965267/1048576),0]⟩
theorem eq_false : box.half 2 false=G51.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G64.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G51.bound) (by rw [eq_true]; exact G64.bound)
end G50

namespace G0
def box : ClosedBox 3 := ⟨![0,0,(-965267/1048576)],![(965267/2097152),(965267/1048576),0]⟩
theorem eq_false : box.half 1 false=G1.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G50.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G1.bound) (by rw [eq_true]; exact G50.bound)
end G0

end MordellEight.CubicBoxes.B2
