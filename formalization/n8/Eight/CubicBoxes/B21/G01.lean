import Eight.CubicBoxes.B21.C14
import Eight.CubicBoxes.B21.C15
import Eight.CubicBoxes.B21.C16
import Eight.CubicBoxes.B21.C17
import Eight.CubicBoxes.B21.C18
import Eight.CubicBoxes.B21.C19
import Eight.CubicBoxes.B21.C20
import Eight.CubicBoxes.B21.C21
import Eight.CubicBoxes.B21.C22
import Eight.CubicBoxes.B21.C23
import Eight.CubicBoxes.B21.G00
import Eight.RootPartition
import Eight.LocalLeaf
namespace MordellEight.CubicBoxes.B21
open FixedTensor IntegerCube RationalCube Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace G82
def box : ClosedBox 3 := ⟨![(14479005/16777216),(8687403/8388608),(4826335/8388608)],![(965267/1048576),(18340073/16777216),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G83.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G90.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G83.bound) (by rw [eq_true]; exact G90.bound)
end G82

namespace G93
def box : ClosedBox 3 := ⟨![(14479005/16777216),(18340073/16777216),(4826335/8388608)],![(965267/1048576),(4826335/4194304),(20270607/33554432)]⟩
theorem bound : BoxMajorant box := Leaf44.bound
end G93

namespace G94
def box : ClosedBox 3 := ⟨![(14479005/16777216),(18340073/16777216),(20270607/33554432)],![(965267/1048576),(4826335/4194304),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf45.bound
end G94

namespace G92
def box : ClosedBox 3 := ⟨![(14479005/16777216),(18340073/16777216),(4826335/8388608)],![(965267/1048576),(4826335/4194304),(10617937/16777216)]⟩
theorem eq_false : box.half 2 false=G93.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G94.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G93.bound) (by rw [eq_true]; exact G94.bound)
end G92

namespace G95
def box : ClosedBox 3 := ⟨![(14479005/16777216),(18340073/16777216),(10617937/16777216)],![(965267/1048576),(4826335/4194304),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf46.bound
end G95

namespace G91
def box : ClosedBox 3 := ⟨![(14479005/16777216),(18340073/16777216),(4826335/8388608)],![(965267/1048576),(4826335/4194304),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G92.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G95.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G92.bound) (by rw [eq_true]; exact G95.bound)
end G91

namespace G81
def box : ClosedBox 3 := ⟨![(14479005/16777216),(8687403/8388608),(4826335/8388608)],![(965267/1048576),(4826335/4194304),(2895801/4194304)]⟩
theorem eq_false : box.half 1 false=G82.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G91.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G82.bound) (by rw [eq_true]; exact G91.bound)
end G81

namespace G73
def box : ClosedBox 3 := ⟨![(6756869/8388608),(8687403/8388608),(4826335/8388608)],![(965267/1048576),(4826335/4194304),(2895801/4194304)]⟩
theorem eq_false : box.half 0 false=G74.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G81.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G74.bound) (by rw [eq_true]; exact G81.bound)
end G73

namespace G71
def box : ClosedBox 3 := ⟨![(6756869/8388608),(8687403/8388608),(965267/2097152)],![(965267/1048576),(4826335/4194304),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G72.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G73.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G72.bound) (by rw [eq_true]; exact G73.bound)
end G71

namespace G61
def box : ClosedBox 3 := ⟨![(6756869/8388608),(965267/1048576),(965267/2097152)],![(965267/1048576),(4826335/4194304),(2895801/4194304)]⟩
theorem eq_false : box.half 1 false=G62.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G71.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G62.bound) (by rw [eq_true]; exact G71.bound)
end G61

namespace G47
def box : ClosedBox 3 := ⟨![(2895801/4194304),(965267/1048576),(965267/2097152)],![(965267/1048576),(4826335/4194304),(2895801/4194304)]⟩
theorem eq_false : box.half 0 false=G48.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G61.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G48.bound) (by rw [eq_true]; exact G61.bound)
end G47

namespace G96
def box : ClosedBox 3 := ⟨![(2895801/4194304),(965267/1048576),(2895801/4194304)],![(965267/1048576),(4826335/4194304),(965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf47.bound
end G96

namespace G46
def box : ClosedBox 3 := ⟨![(2895801/4194304),(965267/1048576),(965267/2097152)],![(965267/1048576),(4826335/4194304),(965267/1048576)]⟩
theorem eq_false : box.half 2 false=G47.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G96.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G47.bound) (by rw [eq_true]; exact G96.bound)
end G46

namespace G101
def box : ClosedBox 3 := ⟨![(2895801/4194304),(4826335/4194304),(965267/2097152)],![(6756869/8388608),(10617937/8388608),(4826335/8388608)]⟩
theorem bound : BoxMajorant box := Leaf48.bound
end G101

namespace G105
def box : ClosedBox 3 := ⟨![(2895801/4194304),(4826335/4194304),(4826335/8388608)],![(12548471/16777216),(20270607/16777216),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf49.bound
end G105

namespace G106
def box : ClosedBox 3 := ⟨![(2895801/4194304),(4826335/4194304),(10617937/16777216)],![(12548471/16777216),(20270607/16777216),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf50.bound
end G106

namespace G104
def box : ClosedBox 3 := ⟨![(2895801/4194304),(4826335/4194304),(4826335/8388608)],![(12548471/16777216),(20270607/16777216),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G105.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G106.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G105.bound) (by rw [eq_true]; exact G106.bound)
end G104

namespace G107
def box : ClosedBox 3 := ⟨![(2895801/4194304),(20270607/16777216),(4826335/8388608)],![(12548471/16777216),(10617937/8388608),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf51.bound
end G107

namespace G103
def box : ClosedBox 3 := ⟨![(2895801/4194304),(4826335/4194304),(4826335/8388608)],![(12548471/16777216),(10617937/8388608),(2895801/4194304)]⟩
theorem eq_false : box.half 1 false=G104.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G107.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G104.bound) (by rw [eq_true]; exact G107.bound)
end G103

namespace G110
def box : ClosedBox 3 := ⟨![(12548471/16777216),(4826335/4194304),(4826335/8388608)],![(6756869/8388608),(20270607/16777216),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf52.bound
end G110

namespace G111
def box : ClosedBox 3 := ⟨![(12548471/16777216),(4826335/4194304),(10617937/16777216)],![(6756869/8388608),(20270607/16777216),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf53.bound
end G111

namespace G109
def box : ClosedBox 3 := ⟨![(12548471/16777216),(4826335/4194304),(4826335/8388608)],![(6756869/8388608),(20270607/16777216),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G110.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G111.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G110.bound) (by rw [eq_true]; exact G111.bound)
end G109

namespace G112
def box : ClosedBox 3 := ⟨![(12548471/16777216),(20270607/16777216),(4826335/8388608)],![(6756869/8388608),(10617937/8388608),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf54.bound
end G112

namespace G108
def box : ClosedBox 3 := ⟨![(12548471/16777216),(4826335/4194304),(4826335/8388608)],![(6756869/8388608),(10617937/8388608),(2895801/4194304)]⟩
theorem eq_false : box.half 1 false=G109.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G112.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G109.bound) (by rw [eq_true]; exact G112.bound)
end G108

namespace G102
def box : ClosedBox 3 := ⟨![(2895801/4194304),(4826335/4194304),(4826335/8388608)],![(6756869/8388608),(10617937/8388608),(2895801/4194304)]⟩
theorem eq_false : box.half 0 false=G103.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G108.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G103.bound) (by rw [eq_true]; exact G108.bound)
end G102

namespace G100
def box : ClosedBox 3 := ⟨![(2895801/4194304),(4826335/4194304),(965267/2097152)],![(6756869/8388608),(10617937/8388608),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G101.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G102.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G101.bound) (by rw [eq_true]; exact G102.bound)
end G100

namespace G114
def box : ClosedBox 3 := ⟨![(2895801/4194304),(10617937/8388608),(965267/2097152)],![(6756869/8388608),(2895801/2097152),(4826335/8388608)]⟩
theorem bound : BoxMajorant box := Leaf55.bound
end G114

namespace G115
def box : ClosedBox 3 := ⟨![(2895801/4194304),(10617937/8388608),(4826335/8388608)],![(6756869/8388608),(2895801/2097152),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf56.bound
end G115

namespace G113
def box : ClosedBox 3 := ⟨![(2895801/4194304),(10617937/8388608),(965267/2097152)],![(6756869/8388608),(2895801/2097152),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G114.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G115.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G114.bound) (by rw [eq_true]; exact G115.bound)
end G113

namespace G99
def box : ClosedBox 3 := ⟨![(2895801/4194304),(4826335/4194304),(965267/2097152)],![(6756869/8388608),(2895801/2097152),(2895801/4194304)]⟩
theorem eq_false : box.half 1 false=G100.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G113.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G100.bound) (by rw [eq_true]; exact G113.bound)
end G99

namespace G118
def box : ClosedBox 3 := ⟨![(6756869/8388608),(4826335/4194304),(965267/2097152)],![(965267/1048576),(10617937/8388608),(4826335/8388608)]⟩
theorem bound : BoxMajorant box := Leaf57.bound
end G118

namespace G122
def box : ClosedBox 3 := ⟨![(6756869/8388608),(4826335/4194304),(4826335/8388608)],![(14479005/16777216),(20270607/16777216),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf58.bound
end G122

namespace G123
def box : ClosedBox 3 := ⟨![(6756869/8388608),(4826335/4194304),(10617937/16777216)],![(14479005/16777216),(20270607/16777216),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf59.bound
end G123

namespace G121
def box : ClosedBox 3 := ⟨![(6756869/8388608),(4826335/4194304),(4826335/8388608)],![(14479005/16777216),(20270607/16777216),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G122.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G123.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G122.bound) (by rw [eq_true]; exact G123.bound)
end G121

namespace G124
def box : ClosedBox 3 := ⟨![(6756869/8388608),(20270607/16777216),(4826335/8388608)],![(14479005/16777216),(10617937/8388608),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf60.bound
end G124

namespace G120
def box : ClosedBox 3 := ⟨![(6756869/8388608),(4826335/4194304),(4826335/8388608)],![(14479005/16777216),(10617937/8388608),(2895801/4194304)]⟩
theorem eq_false : box.half 1 false=G121.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G124.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G121.bound) (by rw [eq_true]; exact G124.bound)
end G120

namespace G126
def box : ClosedBox 3 := ⟨![(14479005/16777216),(4826335/4194304),(4826335/8388608)],![(965267/1048576),(10617937/8388608),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf61.bound
end G126

namespace G127
def box : ClosedBox 3 := ⟨![(14479005/16777216),(4826335/4194304),(10617937/16777216)],![(965267/1048576),(10617937/8388608),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf62.bound
end G127

namespace G125
def box : ClosedBox 3 := ⟨![(14479005/16777216),(4826335/4194304),(4826335/8388608)],![(965267/1048576),(10617937/8388608),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G126.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G127.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G126.bound) (by rw [eq_true]; exact G127.bound)
end G125

namespace G119
def box : ClosedBox 3 := ⟨![(6756869/8388608),(4826335/4194304),(4826335/8388608)],![(965267/1048576),(10617937/8388608),(2895801/4194304)]⟩
theorem eq_false : box.half 0 false=G120.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G125.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G120.bound) (by rw [eq_true]; exact G125.bound)
end G119

namespace G117
def box : ClosedBox 3 := ⟨![(6756869/8388608),(4826335/4194304),(965267/2097152)],![(965267/1048576),(10617937/8388608),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G118.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G119.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G118.bound) (by rw [eq_true]; exact G119.bound)
end G117

namespace G128
def box : ClosedBox 3 := ⟨![(6756869/8388608),(10617937/8388608),(965267/2097152)],![(965267/1048576),(2895801/2097152),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf63.bound
end G128

namespace G116
def box : ClosedBox 3 := ⟨![(6756869/8388608),(4826335/4194304),(965267/2097152)],![(965267/1048576),(2895801/2097152),(2895801/4194304)]⟩
theorem eq_false : box.half 1 false=G117.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G128.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G117.bound) (by rw [eq_true]; exact G128.bound)
end G116

namespace G98
def box : ClosedBox 3 := ⟨![(2895801/4194304),(4826335/4194304),(965267/2097152)],![(965267/1048576),(2895801/2097152),(2895801/4194304)]⟩
theorem eq_false : box.half 0 false=G99.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G116.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G99.bound) (by rw [eq_true]; exact G116.bound)
end G98

namespace G129
def box : ClosedBox 3 := ⟨![(2895801/4194304),(4826335/4194304),(2895801/4194304)],![(965267/1048576),(2895801/2097152),(965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf64.bound
end G129

namespace G97
def box : ClosedBox 3 := ⟨![(2895801/4194304),(4826335/4194304),(965267/2097152)],![(965267/1048576),(2895801/2097152),(965267/1048576)]⟩
theorem eq_false : box.half 2 false=G98.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G129.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G98.bound) (by rw [eq_true]; exact G129.bound)
end G97

namespace G45
def box : ClosedBox 3 := ⟨![(2895801/4194304),(965267/1048576),(965267/2097152)],![(965267/1048576),(2895801/2097152),(965267/1048576)]⟩
theorem eq_false : box.half 1 false=G46.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G97.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G46.bound) (by rw [eq_true]; exact G97.bound)
end G45

namespace G21
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/1048576),(965267/2097152)],![(965267/1048576),(2895801/2097152),(965267/1048576)]⟩
theorem eq_false : box.half 0 false=G22.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G45.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G22.bound) (by rw [eq_true]; exact G45.bound)
end G21

namespace G1
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/1048576),0],![(965267/1048576),(2895801/2097152),(965267/1048576)]⟩
theorem eq_false : box.half 2 false=G2.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G21.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G2.bound) (by rw [eq_true]; exact G21.bound)
end G1

namespace G134
def box : ClosedBox 3 := ⟨![(965267/2097152),(2895801/2097152),0],![(2895801/4194304),(6756869/4194304),(965267/4194304)]⟩
theorem bound : BoxMajorant box := Leaf65.bound
end G134

namespace G135
def box : ClosedBox 3 := ⟨![(965267/2097152),(2895801/2097152),(965267/4194304)],![(2895801/4194304),(6756869/4194304),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf66.bound
end G135

namespace G133
def box : ClosedBox 3 := ⟨![(965267/2097152),(2895801/2097152),0],![(2895801/4194304),(6756869/4194304),(965267/2097152)]⟩
theorem eq_false : box.half 2 false=G134.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G135.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G134.bound) (by rw [eq_true]; exact G135.bound)
end G133

namespace G136
def box : ClosedBox 3 := ⟨![(965267/2097152),(6756869/4194304),0],![(2895801/4194304),(965267/524288),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf67.bound
end G136

namespace G132
def box : ClosedBox 3 := ⟨![(965267/2097152),(2895801/2097152),0],![(2895801/4194304),(965267/524288),(965267/2097152)]⟩
theorem eq_false : box.half 1 false=G133.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G136.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G133.bound) (by rw [eq_true]; exact G136.bound)
end G132

namespace G137
def box : ClosedBox 3 := ⟨![(2895801/4194304),(2895801/2097152),0],![(965267/1048576),(965267/524288),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf68.bound
end G137

namespace G131
def box : ClosedBox 3 := ⟨![(965267/2097152),(2895801/2097152),0],![(965267/1048576),(965267/524288),(965267/2097152)]⟩
theorem eq_false : box.half 0 false=G132.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G137.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G132.bound) (by rw [eq_true]; exact G137.bound)
end G131

namespace G142
def box : ClosedBox 3 := ⟨![(965267/2097152),(2895801/2097152),(965267/2097152)],![(2895801/4194304),(6756869/4194304),(4826335/8388608)]⟩
theorem bound : BoxMajorant box := Leaf69.bound
end G142

namespace G143
def box : ClosedBox 3 := ⟨![(965267/2097152),(2895801/2097152),(4826335/8388608)],![(2895801/4194304),(6756869/4194304),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf70.bound
end G143

namespace G141
def box : ClosedBox 3 := ⟨![(965267/2097152),(2895801/2097152),(965267/2097152)],![(2895801/4194304),(6756869/4194304),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G142.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G143.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G142.bound) (by rw [eq_true]; exact G143.bound)
end G141

namespace G144
def box : ClosedBox 3 := ⟨![(965267/2097152),(2895801/2097152),(2895801/4194304)],![(2895801/4194304),(6756869/4194304),(965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf71.bound
end G144

namespace G140
def box : ClosedBox 3 := ⟨![(965267/2097152),(2895801/2097152),(965267/2097152)],![(2895801/4194304),(6756869/4194304),(965267/1048576)]⟩
theorem eq_false : box.half 2 false=G141.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G144.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G141.bound) (by rw [eq_true]; exact G144.bound)
end G140

namespace G145
def box : ClosedBox 3 := ⟨![(965267/2097152),(6756869/4194304),(965267/2097152)],![(2895801/4194304),(965267/524288),(965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf72.bound
end G145

namespace G139
def box : ClosedBox 3 := ⟨![(965267/2097152),(2895801/2097152),(965267/2097152)],![(2895801/4194304),(965267/524288),(965267/1048576)]⟩
theorem eq_false : box.half 1 false=G140.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G145.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G140.bound) (by rw [eq_true]; exact G145.bound)
end G139

namespace G148
def box : ClosedBox 3 := ⟨![(2895801/4194304),(2895801/2097152),(965267/2097152)],![(965267/1048576),(6756869/4194304),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf73.bound
end G148

namespace G149
def box : ClosedBox 3 := ⟨![(2895801/4194304),(2895801/2097152),(2895801/4194304)],![(965267/1048576),(6756869/4194304),(965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf74.bound
end G149

namespace G147
def box : ClosedBox 3 := ⟨![(2895801/4194304),(2895801/2097152),(965267/2097152)],![(965267/1048576),(6756869/4194304),(965267/1048576)]⟩
theorem eq_false : box.half 2 false=G148.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G149.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G148.bound) (by rw [eq_true]; exact G149.bound)
end G147

namespace G150
def box : ClosedBox 3 := ⟨![(2895801/4194304),(6756869/4194304),(965267/2097152)],![(965267/1048576),(965267/524288),(965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf75.bound
end G150

namespace G146
def box : ClosedBox 3 := ⟨![(2895801/4194304),(2895801/2097152),(965267/2097152)],![(965267/1048576),(965267/524288),(965267/1048576)]⟩
theorem eq_false : box.half 1 false=G147.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G150.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G147.bound) (by rw [eq_true]; exact G150.bound)
end G146

namespace G138
def box : ClosedBox 3 := ⟨![(965267/2097152),(2895801/2097152),(965267/2097152)],![(965267/1048576),(965267/524288),(965267/1048576)]⟩
theorem eq_false : box.half 0 false=G139.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G146.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G139.bound) (by rw [eq_true]; exact G146.bound)
end G138

namespace G130
def box : ClosedBox 3 := ⟨![(965267/2097152),(2895801/2097152),0],![(965267/1048576),(965267/524288),(965267/1048576)]⟩
theorem eq_false : box.half 2 false=G131.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G138.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G131.bound) (by rw [eq_true]; exact G138.bound)
end G130

namespace G0
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/1048576),0],![(965267/1048576),(965267/524288),(965267/1048576)]⟩
theorem eq_false : box.half 1 false=G1.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G130.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G1.bound) (by rw [eq_true]; exact G130.bound)
end G0

end MordellEight.CubicBoxes.B21
