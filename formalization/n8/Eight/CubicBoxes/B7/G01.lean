import Eight.CubicBoxes.B7.C16
import Eight.CubicBoxes.B7.G00
import Eight.RootPartition
import Eight.LocalLeaf
namespace MordellEight.CubicBoxes.B7
open FixedTensor IntegerCube RationalCube Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace G81
def box : ClosedBox 3 := ⟨![(2895801/4194304),(2895801/2097152),(-965267/1048576)],![(965267/1048576),(965267/524288),(-965267/2097152)]⟩
theorem eq_false : box.half 1 false=G82.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G83.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G82.bound) (by rw [eq_true]; exact G83.bound)
end G81

namespace G79
def box : ClosedBox 3 := ⟨![(965267/2097152),(2895801/2097152),(-965267/1048576)],![(965267/1048576),(965267/524288),(-965267/2097152)]⟩
theorem eq_false : box.half 0 false=G80.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G81.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G80.bound) (by rw [eq_true]; exact G81.bound)
end G79

namespace G84
def box : ClosedBox 3 := ⟨![(965267/2097152),(2895801/2097152),(-965267/2097152)],![(965267/1048576),(965267/524288),0]⟩
theorem bound : BoxMajorant box := Leaf41.bound
end G84

namespace G78
def box : ClosedBox 3 := ⟨![(965267/2097152),(2895801/2097152),(-965267/1048576)],![(965267/1048576),(965267/524288),0]⟩
theorem eq_false : box.half 2 false=G79.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G84.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G79.bound) (by rw [eq_true]; exact G84.bound)
end G78

namespace G0
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/1048576),(-965267/1048576)],![(965267/1048576),(965267/524288),0]⟩
theorem eq_false : box.half 1 false=G1.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G78.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G1.bound) (by rw [eq_true]; exact G78.bound)
end G0

end MordellEight.CubicBoxes.B7
