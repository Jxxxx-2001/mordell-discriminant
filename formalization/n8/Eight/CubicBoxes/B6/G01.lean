import Eight.CubicBoxes.B6.C16
import Eight.CubicBoxes.B6.C17
import Eight.CubicBoxes.B6.C18
import Eight.CubicBoxes.B6.G00
import Eight.RootPartition
import Eight.LocalLeaf
namespace MordellEight.CubicBoxes.B6
open FixedTensor IntegerCube RationalCube Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace G85
def box : ClosedBox 3 := ⟨![0,(6756869/4194304),(-965267/1048576)],![(965267/4194304),(965267/524288),(-2895801/4194304)]⟩
theorem checked : outsideCheck box=true := by decide +kernel
theorem bound : BoxMajorant box := by
  intro x hx hd
  exact (outsideCheck_sound box checked hx hd.1 hd.2).elim
end G85

namespace G87
def box : ClosedBox 3 := ⟨![0,(6756869/4194304),(-2895801/4194304)],![(965267/8388608),(965267/524288),(-965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf39.bound
end G87

namespace G88
def box : ClosedBox 3 := ⟨![(965267/8388608),(6756869/4194304),(-2895801/4194304)],![(965267/4194304),(965267/524288),(-965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf40.bound
end G88

namespace G86
def box : ClosedBox 3 := ⟨![0,(6756869/4194304),(-2895801/4194304)],![(965267/4194304),(965267/524288),(-965267/2097152)]⟩
theorem eq_false : box.half 0 false=G87.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G88.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G87.bound) (by rw [eq_true]; exact G88.bound)
end G86

namespace G84
def box : ClosedBox 3 := ⟨![0,(6756869/4194304),(-965267/1048576)],![(965267/4194304),(965267/524288),(-965267/2097152)]⟩
theorem eq_false : box.half 2 false=G85.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G86.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G85.bound) (by rw [eq_true]; exact G86.bound)
end G84

namespace G82
def box : ClosedBox 3 := ⟨![0,(2895801/2097152),(-965267/1048576)],![(965267/4194304),(965267/524288),(-965267/2097152)]⟩
theorem eq_false : box.half 1 false=G83.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G84.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G83.bound) (by rw [eq_true]; exact G84.bound)
end G82

namespace G90
def box : ClosedBox 3 := ⟨![(965267/4194304),(2895801/2097152),(-965267/1048576)],![(965267/2097152),(6756869/4194304),(-965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf41.bound
end G90

namespace G94
def box : ClosedBox 3 := ⟨![(965267/4194304),(6756869/4194304),(-965267/1048576)],![(2895801/8388608),(965267/524288),(-6756869/8388608)]⟩
theorem checked : outsideCheck box=true := by decide +kernel
theorem bound : BoxMajorant box := by
  intro x hx hd
  exact (outsideCheck_sound box checked hx hd.1 hd.2).elim
end G94

namespace G95
def box : ClosedBox 3 := ⟨![(965267/4194304),(6756869/4194304),(-6756869/8388608)],![(2895801/8388608),(965267/524288),(-2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf42.bound
end G95

namespace G93
def box : ClosedBox 3 := ⟨![(965267/4194304),(6756869/4194304),(-965267/1048576)],![(2895801/8388608),(965267/524288),(-2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G94.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G95.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G94.bound) (by rw [eq_true]; exact G95.bound)
end G93

namespace G96
def box : ClosedBox 3 := ⟨![(2895801/8388608),(6756869/4194304),(-965267/1048576)],![(965267/2097152),(965267/524288),(-2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf43.bound
end G96

namespace G92
def box : ClosedBox 3 := ⟨![(965267/4194304),(6756869/4194304),(-965267/1048576)],![(965267/2097152),(965267/524288),(-2895801/4194304)]⟩
theorem eq_false : box.half 0 false=G93.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G96.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G93.bound) (by rw [eq_true]; exact G96.bound)
end G92

namespace G97
def box : ClosedBox 3 := ⟨![(965267/4194304),(6756869/4194304),(-2895801/4194304)],![(965267/2097152),(965267/524288),(-965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf44.bound
end G97

namespace G91
def box : ClosedBox 3 := ⟨![(965267/4194304),(6756869/4194304),(-965267/1048576)],![(965267/2097152),(965267/524288),(-965267/2097152)]⟩
theorem eq_false : box.half 2 false=G92.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G97.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G92.bound) (by rw [eq_true]; exact G97.bound)
end G91

namespace G89
def box : ClosedBox 3 := ⟨![(965267/4194304),(2895801/2097152),(-965267/1048576)],![(965267/2097152),(965267/524288),(-965267/2097152)]⟩
theorem eq_false : box.half 1 false=G90.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G91.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G90.bound) (by rw [eq_true]; exact G91.bound)
end G89

namespace G81
def box : ClosedBox 3 := ⟨![0,(2895801/2097152),(-965267/1048576)],![(965267/2097152),(965267/524288),(-965267/2097152)]⟩
theorem eq_false : box.half 0 false=G82.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G89.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G82.bound) (by rw [eq_true]; exact G89.bound)
end G81

namespace G98
def box : ClosedBox 3 := ⟨![0,(2895801/2097152),(-965267/2097152)],![(965267/2097152),(965267/524288),0]⟩
theorem bound : BoxMajorant box := Leaf45.bound
end G98

namespace G80
def box : ClosedBox 3 := ⟨![0,(2895801/2097152),(-965267/1048576)],![(965267/2097152),(965267/524288),0]⟩
theorem eq_false : box.half 2 false=G81.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G98.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G81.bound) (by rw [eq_true]; exact G98.bound)
end G80

namespace G0
def box : ClosedBox 3 := ⟨![0,(965267/1048576),(-965267/1048576)],![(965267/2097152),(965267/524288),0]⟩
theorem eq_false : box.half 1 false=G1.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G80.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G1.bound) (by rw [eq_true]; exact G80.bound)
end G0

end MordellEight.CubicBoxes.B6
