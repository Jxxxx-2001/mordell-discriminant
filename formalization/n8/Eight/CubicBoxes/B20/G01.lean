import Eight.CubicBoxes.B20.C17
import Eight.CubicBoxes.B20.C18
import Eight.CubicBoxes.B20.C19
import Eight.CubicBoxes.B20.C20
import Eight.CubicBoxes.B20.C21
import Eight.CubicBoxes.B20.C22
import Eight.CubicBoxes.B20.C23
import Eight.CubicBoxes.B20.C24
import Eight.CubicBoxes.B20.C25
import Eight.CubicBoxes.B20.C26
import Eight.CubicBoxes.B20.C27
import Eight.CubicBoxes.B20.C28
import Eight.CubicBoxes.B20.C29
import Eight.CubicBoxes.B20.C30
import Eight.CubicBoxes.B20.G00
import Eight.RootPartition
import Eight.LocalLeaf
namespace MordellEight.CubicBoxes.B20
open FixedTensor IntegerCube RationalCube Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace G85
def box : ClosedBox 3 := ⟨![(965267/16777216),(10617937/8388608),(965267/4194304)],![(965267/8388608),(2895801/2097152),(2895801/8388608)]⟩
theorem eq_false : box.half 1 false=G86.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G89.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G86.bound) (by rw [eq_true]; exact G89.bound)
end G85

namespace G83
def box : ClosedBox 3 := ⟨![0,(10617937/8388608),(965267/4194304)],![(965267/8388608),(2895801/2097152),(2895801/8388608)]⟩
theorem eq_false : box.half 0 false=G84.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G85.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G84.bound) (by rw [eq_true]; exact G85.bound)
end G83

namespace G90
def box : ClosedBox 3 := ⟨![0,(10617937/8388608),(2895801/8388608)],![(965267/8388608),(2895801/2097152),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf42.bound
end G90

namespace G82
def box : ClosedBox 3 := ⟨![0,(10617937/8388608),(965267/4194304)],![(965267/8388608),(2895801/2097152),(965267/2097152)]⟩
theorem eq_false : box.half 2 false=G83.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G90.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G83.bound) (by rw [eq_true]; exact G90.bound)
end G82

namespace G76
def box : ClosedBox 3 := ⟨![0,(4826335/4194304),(965267/4194304)],![(965267/8388608),(2895801/2097152),(965267/2097152)]⟩
theorem eq_false : box.half 1 false=G77.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G82.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G77.bound) (by rw [eq_true]; exact G82.bound)
end G76

namespace G93
def box : ClosedBox 3 := ⟨![(965267/8388608),(4826335/4194304),(965267/4194304)],![(965267/4194304),(10617937/8388608),(2895801/8388608)]⟩
theorem bound : BoxMajorant box := Leaf43.bound
end G93

namespace G94
def box : ClosedBox 3 := ⟨![(965267/8388608),(4826335/4194304),(2895801/8388608)],![(965267/4194304),(10617937/8388608),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf44.bound
end G94

namespace G92
def box : ClosedBox 3 := ⟨![(965267/8388608),(4826335/4194304),(965267/4194304)],![(965267/4194304),(10617937/8388608),(965267/2097152)]⟩
theorem eq_false : box.half 2 false=G93.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G94.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G93.bound) (by rw [eq_true]; exact G94.bound)
end G92

namespace G97
def box : ClosedBox 3 := ⟨![(965267/8388608),(10617937/8388608),(965267/4194304)],![(965267/4194304),(2895801/2097152),(4826335/16777216)]⟩
theorem bound : BoxMajorant box := Leaf45.bound
end G97

namespace G98
def box : ClosedBox 3 := ⟨![(965267/8388608),(10617937/8388608),(4826335/16777216)],![(965267/4194304),(2895801/2097152),(2895801/8388608)]⟩
theorem bound : BoxMajorant box := Leaf46.bound
end G98

namespace G96
def box : ClosedBox 3 := ⟨![(965267/8388608),(10617937/8388608),(965267/4194304)],![(965267/4194304),(2895801/2097152),(2895801/8388608)]⟩
theorem eq_false : box.half 2 false=G97.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G98.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G97.bound) (by rw [eq_true]; exact G98.bound)
end G96

namespace G99
def box : ClosedBox 3 := ⟨![(965267/8388608),(10617937/8388608),(2895801/8388608)],![(965267/4194304),(2895801/2097152),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf47.bound
end G99

namespace G95
def box : ClosedBox 3 := ⟨![(965267/8388608),(10617937/8388608),(965267/4194304)],![(965267/4194304),(2895801/2097152),(965267/2097152)]⟩
theorem eq_false : box.half 2 false=G96.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G99.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G96.bound) (by rw [eq_true]; exact G99.bound)
end G95

namespace G91
def box : ClosedBox 3 := ⟨![(965267/8388608),(4826335/4194304),(965267/4194304)],![(965267/4194304),(2895801/2097152),(965267/2097152)]⟩
theorem eq_false : box.half 1 false=G92.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G95.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G92.bound) (by rw [eq_true]; exact G95.bound)
end G91

namespace G75
def box : ClosedBox 3 := ⟨![0,(4826335/4194304),(965267/4194304)],![(965267/4194304),(2895801/2097152),(965267/2097152)]⟩
theorem eq_false : box.half 0 false=G76.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G91.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G76.bound) (by rw [eq_true]; exact G91.bound)
end G75

namespace G69
def box : ClosedBox 3 := ⟨![0,(4826335/4194304),0],![(965267/4194304),(2895801/2097152),(965267/2097152)]⟩
theorem eq_false : box.half 2 false=G70.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G75.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G70.bound) (by rw [eq_true]; exact G75.bound)
end G69

namespace G3
def box : ClosedBox 3 := ⟨![0,(965267/1048576),0],![(965267/4194304),(2895801/2097152),(965267/2097152)]⟩
theorem eq_false : box.half 1 false=G4.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G69.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G4.bound) (by rw [eq_true]; exact G69.bound)
end G3

namespace G102
def box : ClosedBox 3 := ⟨![(965267/4194304),(965267/1048576),0],![(965267/2097152),(4826335/4194304),(965267/4194304)]⟩
theorem bound : BoxMajorant box := Leaf48.bound
end G102

namespace G103
def box : ClosedBox 3 := ⟨![(965267/4194304),(965267/1048576),(965267/4194304)],![(965267/2097152),(4826335/4194304),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf49.bound
end G103

namespace G101
def box : ClosedBox 3 := ⟨![(965267/4194304),(965267/1048576),0],![(965267/2097152),(4826335/4194304),(965267/2097152)]⟩
theorem eq_false : box.half 2 false=G102.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G103.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G102.bound) (by rw [eq_true]; exact G103.bound)
end G101

namespace G105
def box : ClosedBox 3 := ⟨![(965267/4194304),(4826335/4194304),0],![(965267/2097152),(2895801/2097152),(965267/4194304)]⟩
theorem bound : BoxMajorant box := Leaf50.bound
end G105

namespace G109
def box : ClosedBox 3 := ⟨![(965267/4194304),(4826335/4194304),(965267/4194304)],![(2895801/8388608),(10617937/8388608),(2895801/8388608)]⟩
theorem bound : BoxMajorant box := Leaf51.bound
end G109

namespace G110
def box : ClosedBox 3 := ⟨![(965267/4194304),(4826335/4194304),(2895801/8388608)],![(2895801/8388608),(10617937/8388608),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf52.bound
end G110

namespace G108
def box : ClosedBox 3 := ⟨![(965267/4194304),(4826335/4194304),(965267/4194304)],![(2895801/8388608),(10617937/8388608),(965267/2097152)]⟩
theorem eq_false : box.half 2 false=G109.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G110.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G109.bound) (by rw [eq_true]; exact G110.bound)
end G108

namespace G112
def box : ClosedBox 3 := ⟨![(965267/4194304),(10617937/8388608),(965267/4194304)],![(2895801/8388608),(2895801/2097152),(2895801/8388608)]⟩
theorem bound : BoxMajorant box := Leaf53.bound
end G112

namespace G113
def box : ClosedBox 3 := ⟨![(965267/4194304),(10617937/8388608),(2895801/8388608)],![(2895801/8388608),(2895801/2097152),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf54.bound
end G113

namespace G111
def box : ClosedBox 3 := ⟨![(965267/4194304),(10617937/8388608),(965267/4194304)],![(2895801/8388608),(2895801/2097152),(965267/2097152)]⟩
theorem eq_false : box.half 2 false=G112.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G113.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G112.bound) (by rw [eq_true]; exact G113.bound)
end G111

namespace G107
def box : ClosedBox 3 := ⟨![(965267/4194304),(4826335/4194304),(965267/4194304)],![(2895801/8388608),(2895801/2097152),(965267/2097152)]⟩
theorem eq_false : box.half 1 false=G108.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G111.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G108.bound) (by rw [eq_true]; exact G111.bound)
end G107

namespace G115
def box : ClosedBox 3 := ⟨![(2895801/8388608),(4826335/4194304),(965267/4194304)],![(965267/2097152),(2895801/2097152),(2895801/8388608)]⟩
theorem bound : BoxMajorant box := Leaf55.bound
end G115

namespace G116
def box : ClosedBox 3 := ⟨![(2895801/8388608),(4826335/4194304),(2895801/8388608)],![(965267/2097152),(2895801/2097152),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf56.bound
end G116

namespace G114
def box : ClosedBox 3 := ⟨![(2895801/8388608),(4826335/4194304),(965267/4194304)],![(965267/2097152),(2895801/2097152),(965267/2097152)]⟩
theorem eq_false : box.half 2 false=G115.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G116.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G115.bound) (by rw [eq_true]; exact G116.bound)
end G114

namespace G106
def box : ClosedBox 3 := ⟨![(965267/4194304),(4826335/4194304),(965267/4194304)],![(965267/2097152),(2895801/2097152),(965267/2097152)]⟩
theorem eq_false : box.half 0 false=G107.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G114.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G107.bound) (by rw [eq_true]; exact G114.bound)
end G106

namespace G104
def box : ClosedBox 3 := ⟨![(965267/4194304),(4826335/4194304),0],![(965267/2097152),(2895801/2097152),(965267/2097152)]⟩
theorem eq_false : box.half 2 false=G105.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G106.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G105.bound) (by rw [eq_true]; exact G106.bound)
end G104

namespace G100
def box : ClosedBox 3 := ⟨![(965267/4194304),(965267/1048576),0],![(965267/2097152),(2895801/2097152),(965267/2097152)]⟩
theorem eq_false : box.half 1 false=G101.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G104.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G101.bound) (by rw [eq_true]; exact G104.bound)
end G100

namespace G2
def box : ClosedBox 3 := ⟨![0,(965267/1048576),0],![(965267/2097152),(2895801/2097152),(965267/2097152)]⟩
theorem eq_false : box.half 0 false=G3.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G100.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G3.bound) (by rw [eq_true]; exact G100.bound)
end G2

namespace G118
def box : ClosedBox 3 := ⟨![0,(965267/1048576),(965267/2097152)],![(965267/4194304),(2895801/2097152),(965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf57.bound
end G118

namespace G120
def box : ClosedBox 3 := ⟨![(965267/4194304),(965267/1048576),(965267/2097152)],![(965267/2097152),(4826335/4194304),(965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf58.bound
end G120

namespace G123
def box : ClosedBox 3 := ⟨![(965267/4194304),(4826335/4194304),(965267/2097152)],![(965267/2097152),(2895801/2097152),(4826335/8388608)]⟩
theorem bound : BoxMajorant box := Leaf59.bound
end G123

namespace G124
def box : ClosedBox 3 := ⟨![(965267/4194304),(4826335/4194304),(4826335/8388608)],![(965267/2097152),(2895801/2097152),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf60.bound
end G124

namespace G122
def box : ClosedBox 3 := ⟨![(965267/4194304),(4826335/4194304),(965267/2097152)],![(965267/2097152),(2895801/2097152),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G123.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G124.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G123.bound) (by rw [eq_true]; exact G124.bound)
end G122

namespace G125
def box : ClosedBox 3 := ⟨![(965267/4194304),(4826335/4194304),(2895801/4194304)],![(965267/2097152),(2895801/2097152),(965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf61.bound
end G125

namespace G121
def box : ClosedBox 3 := ⟨![(965267/4194304),(4826335/4194304),(965267/2097152)],![(965267/2097152),(2895801/2097152),(965267/1048576)]⟩
theorem eq_false : box.half 2 false=G122.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G125.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G122.bound) (by rw [eq_true]; exact G125.bound)
end G121

namespace G119
def box : ClosedBox 3 := ⟨![(965267/4194304),(965267/1048576),(965267/2097152)],![(965267/2097152),(2895801/2097152),(965267/1048576)]⟩
theorem eq_false : box.half 1 false=G120.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G121.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G120.bound) (by rw [eq_true]; exact G121.bound)
end G119

namespace G117
def box : ClosedBox 3 := ⟨![0,(965267/1048576),(965267/2097152)],![(965267/2097152),(2895801/2097152),(965267/1048576)]⟩
theorem eq_false : box.half 0 false=G118.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G119.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G118.bound) (by rw [eq_true]; exact G119.bound)
end G117

namespace G1
def box : ClosedBox 3 := ⟨![0,(965267/1048576),0],![(965267/2097152),(2895801/2097152),(965267/1048576)]⟩
theorem eq_false : box.half 2 false=G2.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G117.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G2.bound) (by rw [eq_true]; exact G117.bound)
end G1

namespace G130
def box : ClosedBox 3 := ⟨![0,(2895801/2097152),0],![(965267/4194304),(6756869/4194304),(965267/4194304)]⟩
theorem bound : BoxMajorant box := Leaf62.bound
end G130

namespace G135
def box : ClosedBox 3 := ⟨![0,(2895801/2097152),(965267/4194304)],![(965267/16777216),(12548471/8388608),(2895801/8388608)]⟩
theorem bound : BoxMajorant box := Leaf63.bound
end G135

namespace G136
def box : ClosedBox 3 := ⟨![(965267/16777216),(2895801/2097152),(965267/4194304)],![(965267/8388608),(12548471/8388608),(2895801/8388608)]⟩
theorem bound : BoxMajorant box := Leaf64.bound
end G136

namespace G134
def box : ClosedBox 3 := ⟨![0,(2895801/2097152),(965267/4194304)],![(965267/8388608),(12548471/8388608),(2895801/8388608)]⟩
theorem eq_false : box.half 0 false=G135.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G136.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G135.bound) (by rw [eq_true]; exact G136.bound)
end G134

namespace G138
def box : ClosedBox 3 := ⟨![0,(2895801/2097152),(2895801/8388608)],![(965267/16777216),(12548471/8388608),(965267/2097152)]⟩
theorem checked : outsideCheck box=true := by decide +kernel
theorem bound : BoxMajorant box := by
  intro x hx hd
  exact (outsideCheck_sound box checked hx hd.1 hd.2).elim
end G138

namespace G142
def box : ClosedBox 3 := ⟨![(965267/16777216),(2895801/2097152),(2895801/8388608)],![(2895801/33554432),(24131675/16777216),(6756869/16777216)]⟩
theorem bound : BoxMajorant box := Leaf65.bound
end G142

namespace G143
def box : ClosedBox 3 := ⟨![(2895801/33554432),(2895801/2097152),(2895801/8388608)],![(965267/8388608),(24131675/16777216),(6756869/16777216)]⟩
theorem bound : BoxMajorant box := Leaf66.bound
end G143

namespace G141
def box : ClosedBox 3 := ⟨![(965267/16777216),(2895801/2097152),(2895801/8388608)],![(965267/8388608),(24131675/16777216),(6756869/16777216)]⟩
theorem eq_false : box.half 0 false=G142.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G143.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G142.bound) (by rw [eq_true]; exact G143.bound)
end G141

namespace G144
def box : ClosedBox 3 := ⟨![(965267/16777216),(2895801/2097152),(6756869/16777216)],![(965267/8388608),(24131675/16777216),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf67.bound
end G144

namespace G140
def box : ClosedBox 3 := ⟨![(965267/16777216),(2895801/2097152),(2895801/8388608)],![(965267/8388608),(24131675/16777216),(965267/2097152)]⟩
theorem eq_false : box.half 2 false=G141.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G144.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G141.bound) (by rw [eq_true]; exact G144.bound)
end G140

namespace G145
def box : ClosedBox 3 := ⟨![(965267/16777216),(24131675/16777216),(2895801/8388608)],![(965267/8388608),(12548471/8388608),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf68.bound
end G145

namespace G139
def box : ClosedBox 3 := ⟨![(965267/16777216),(2895801/2097152),(2895801/8388608)],![(965267/8388608),(12548471/8388608),(965267/2097152)]⟩
theorem eq_false : box.half 1 false=G140.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G145.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G140.bound) (by rw [eq_true]; exact G145.bound)
end G139

namespace G137
def box : ClosedBox 3 := ⟨![0,(2895801/2097152),(2895801/8388608)],![(965267/8388608),(12548471/8388608),(965267/2097152)]⟩
theorem eq_false : box.half 0 false=G138.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G139.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G138.bound) (by rw [eq_true]; exact G139.bound)
end G137

namespace G133
def box : ClosedBox 3 := ⟨![0,(2895801/2097152),(965267/4194304)],![(965267/8388608),(12548471/8388608),(965267/2097152)]⟩
theorem eq_false : box.half 2 false=G134.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G137.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G134.bound) (by rw [eq_true]; exact G137.bound)
end G133

namespace G147
def box : ClosedBox 3 := ⟨![0,(12548471/8388608),(965267/4194304)],![(965267/8388608),(6756869/4194304),(2895801/8388608)]⟩
theorem bound : BoxMajorant box := Leaf69.bound
end G147

namespace G149
def box : ClosedBox 3 := ⟨![0,(12548471/8388608),(2895801/8388608)],![(965267/16777216),(6756869/4194304),(965267/2097152)]⟩
theorem checked : outsideCheck box=true := by decide +kernel
theorem bound : BoxMajorant box := by
  intro x hx hd
  exact (outsideCheck_sound box checked hx hd.1 hd.2).elim
end G149

namespace G150
def box : ClosedBox 3 := ⟨![(965267/16777216),(12548471/8388608),(2895801/8388608)],![(965267/8388608),(6756869/4194304),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf70.bound
end G150

namespace G148
def box : ClosedBox 3 := ⟨![0,(12548471/8388608),(2895801/8388608)],![(965267/8388608),(6756869/4194304),(965267/2097152)]⟩
theorem eq_false : box.half 0 false=G149.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G150.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G149.bound) (by rw [eq_true]; exact G150.bound)
end G148

namespace G146
def box : ClosedBox 3 := ⟨![0,(12548471/8388608),(965267/4194304)],![(965267/8388608),(6756869/4194304),(965267/2097152)]⟩
theorem eq_false : box.half 2 false=G147.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G148.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G147.bound) (by rw [eq_true]; exact G148.bound)
end G146

namespace G132
def box : ClosedBox 3 := ⟨![0,(2895801/2097152),(965267/4194304)],![(965267/8388608),(6756869/4194304),(965267/2097152)]⟩
theorem eq_false : box.half 1 false=G133.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G146.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G133.bound) (by rw [eq_true]; exact G146.bound)
end G132

namespace G153
def box : ClosedBox 3 := ⟨![(965267/8388608),(2895801/2097152),(965267/4194304)],![(965267/4194304),(12548471/8388608),(2895801/8388608)]⟩
theorem bound : BoxMajorant box := Leaf71.bound
end G153

namespace G156
def box : ClosedBox 3 := ⟨![(965267/8388608),(2895801/2097152),(2895801/8388608)],![(2895801/16777216),(24131675/16777216),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf72.bound
end G156

namespace G157
def box : ClosedBox 3 := ⟨![(965267/8388608),(24131675/16777216),(2895801/8388608)],![(2895801/16777216),(12548471/8388608),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf73.bound
end G157

namespace G155
def box : ClosedBox 3 := ⟨![(965267/8388608),(2895801/2097152),(2895801/8388608)],![(2895801/16777216),(12548471/8388608),(965267/2097152)]⟩
theorem eq_false : box.half 1 false=G156.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G157.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G156.bound) (by rw [eq_true]; exact G157.bound)
end G155

namespace G158
def box : ClosedBox 3 := ⟨![(2895801/16777216),(2895801/2097152),(2895801/8388608)],![(965267/4194304),(12548471/8388608),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf74.bound
end G158

namespace G154
def box : ClosedBox 3 := ⟨![(965267/8388608),(2895801/2097152),(2895801/8388608)],![(965267/4194304),(12548471/8388608),(965267/2097152)]⟩
theorem eq_false : box.half 0 false=G155.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G158.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G155.bound) (by rw [eq_true]; exact G158.bound)
end G154

namespace G152
def box : ClosedBox 3 := ⟨![(965267/8388608),(2895801/2097152),(965267/4194304)],![(965267/4194304),(12548471/8388608),(965267/2097152)]⟩
theorem eq_false : box.half 2 false=G153.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G154.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G153.bound) (by rw [eq_true]; exact G154.bound)
end G152

namespace G160
def box : ClosedBox 3 := ⟨![(965267/8388608),(12548471/8388608),(965267/4194304)],![(965267/4194304),(6756869/4194304),(2895801/8388608)]⟩
theorem bound : BoxMajorant box := Leaf75.bound
end G160

namespace G162
def box : ClosedBox 3 := ⟨![(965267/8388608),(12548471/8388608),(2895801/8388608)],![(2895801/16777216),(6756869/4194304),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf76.bound
end G162

namespace G163
def box : ClosedBox 3 := ⟨![(2895801/16777216),(12548471/8388608),(2895801/8388608)],![(965267/4194304),(6756869/4194304),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf77.bound
end G163

namespace G161
def box : ClosedBox 3 := ⟨![(965267/8388608),(12548471/8388608),(2895801/8388608)],![(965267/4194304),(6756869/4194304),(965267/2097152)]⟩
theorem eq_false : box.half 0 false=G162.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G163.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G162.bound) (by rw [eq_true]; exact G163.bound)
end G161

namespace G159
def box : ClosedBox 3 := ⟨![(965267/8388608),(12548471/8388608),(965267/4194304)],![(965267/4194304),(6756869/4194304),(965267/2097152)]⟩
theorem eq_false : box.half 2 false=G160.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G161.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G160.bound) (by rw [eq_true]; exact G161.bound)
end G159

namespace G151
def box : ClosedBox 3 := ⟨![(965267/8388608),(2895801/2097152),(965267/4194304)],![(965267/4194304),(6756869/4194304),(965267/2097152)]⟩
theorem eq_false : box.half 1 false=G152.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G159.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G152.bound) (by rw [eq_true]; exact G159.bound)
end G151

namespace G131
def box : ClosedBox 3 := ⟨![0,(2895801/2097152),(965267/4194304)],![(965267/4194304),(6756869/4194304),(965267/2097152)]⟩
theorem eq_false : box.half 0 false=G132.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G151.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G132.bound) (by rw [eq_true]; exact G151.bound)
end G131

namespace G129
def box : ClosedBox 3 := ⟨![0,(2895801/2097152),0],![(965267/4194304),(6756869/4194304),(965267/2097152)]⟩
theorem eq_false : box.half 2 false=G130.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G131.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G130.bound) (by rw [eq_true]; exact G131.bound)
end G129

end MordellEight.CubicBoxes.B20
