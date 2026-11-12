import Eight.CubicBoxes.B20.C44
import Eight.CubicBoxes.B20.C45
import Eight.CubicBoxes.B20.C46
import Eight.CubicBoxes.B20.G01
import Eight.CubicBoxes.B20.G02
import Eight.RootPartition
import Eight.LocalLeaf
namespace MordellEight.CubicBoxes.B20
open FixedTensor IntegerCube RationalCube Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace G245
def box : ClosedBox 3 := ⟨![0,(6756869/4194304),(2895801/4194304)],![(965267/4194304),(965267/524288),(965267/1048576)]⟩
theorem checked : outsideCheck box=true := by decide +kernel
theorem bound : BoxMajorant box := by
  intro x hx hd
  exact (outsideCheck_sound box checked hx hd.1 hd.2).elim
end G245

namespace G213
def box : ClosedBox 3 := ⟨![0,(6756869/4194304),(965267/2097152)],![(965267/4194304),(965267/524288),(965267/1048576)]⟩
theorem eq_false : box.half 2 false=G214.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G245.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G214.bound) (by rw [eq_true]; exact G245.bound)
end G213

namespace G195
def box : ClosedBox 3 := ⟨![0,(2895801/2097152),(965267/2097152)],![(965267/4194304),(965267/524288),(965267/1048576)]⟩
theorem eq_false : box.half 1 false=G196.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G213.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G196.bound) (by rw [eq_true]; exact G213.bound)
end G195

namespace G248
def box : ClosedBox 3 := ⟨![(965267/4194304),(2895801/2097152),(965267/2097152)],![(965267/2097152),(6756869/4194304),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf114.bound
end G248

namespace G249
def box : ClosedBox 3 := ⟨![(965267/4194304),(2895801/2097152),(2895801/4194304)],![(965267/2097152),(6756869/4194304),(965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf115.bound
end G249

namespace G247
def box : ClosedBox 3 := ⟨![(965267/4194304),(2895801/2097152),(965267/2097152)],![(965267/2097152),(6756869/4194304),(965267/1048576)]⟩
theorem eq_false : box.half 2 false=G248.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G249.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G248.bound) (by rw [eq_true]; exact G249.bound)
end G247

namespace G252
def box : ClosedBox 3 := ⟨![(965267/4194304),(6756869/4194304),(965267/2097152)],![(965267/2097152),(965267/524288),(4826335/8388608)]⟩
theorem bound : BoxMajorant box := Leaf116.bound
end G252

namespace G253
def box : ClosedBox 3 := ⟨![(965267/4194304),(6756869/4194304),(4826335/8388608)],![(965267/2097152),(965267/524288),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf117.bound
end G253

namespace G251
def box : ClosedBox 3 := ⟨![(965267/4194304),(6756869/4194304),(965267/2097152)],![(965267/2097152),(965267/524288),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G252.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G253.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G252.bound) (by rw [eq_true]; exact G253.bound)
end G251

namespace G254
def box : ClosedBox 3 := ⟨![(965267/4194304),(6756869/4194304),(2895801/4194304)],![(965267/2097152),(965267/524288),(965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf118.bound
end G254

namespace G250
def box : ClosedBox 3 := ⟨![(965267/4194304),(6756869/4194304),(965267/2097152)],![(965267/2097152),(965267/524288),(965267/1048576)]⟩
theorem eq_false : box.half 2 false=G251.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G254.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G251.bound) (by rw [eq_true]; exact G254.bound)
end G250

namespace G246
def box : ClosedBox 3 := ⟨![(965267/4194304),(2895801/2097152),(965267/2097152)],![(965267/2097152),(965267/524288),(965267/1048576)]⟩
theorem eq_false : box.half 1 false=G247.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G250.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G247.bound) (by rw [eq_true]; exact G250.bound)
end G246

namespace G194
def box : ClosedBox 3 := ⟨![0,(2895801/2097152),(965267/2097152)],![(965267/2097152),(965267/524288),(965267/1048576)]⟩
theorem eq_false : box.half 0 false=G195.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G246.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G195.bound) (by rw [eq_true]; exact G246.bound)
end G194

namespace G126
def box : ClosedBox 3 := ⟨![0,(2895801/2097152),0],![(965267/2097152),(965267/524288),(965267/1048576)]⟩
theorem eq_false : box.half 2 false=G127.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G194.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G127.bound) (by rw [eq_true]; exact G194.bound)
end G126

namespace G0
def box : ClosedBox 3 := ⟨![0,(965267/1048576),0],![(965267/2097152),(965267/524288),(965267/1048576)]⟩
theorem eq_false : box.half 1 false=G1.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G126.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G1.bound) (by rw [eq_true]; exact G126.bound)
end G0

end MordellEight.CubicBoxes.B20
