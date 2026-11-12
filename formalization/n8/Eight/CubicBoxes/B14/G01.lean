import Eight.CubicBoxes.B14.C18
import Eight.CubicBoxes.B14.C19
import Eight.CubicBoxes.B14.C21
import Eight.CubicBoxes.B14.C22
import Eight.CubicBoxes.B14.C23
import Eight.CubicBoxes.B14.C24
import Eight.CubicBoxes.B14.C25
import Eight.CubicBoxes.B14.C26
import Eight.CubicBoxes.B14.C27
import Eight.CubicBoxes.B14.C28
import Eight.CubicBoxes.B14.C29
import Eight.CubicBoxes.B14.G00
import Eight.RootPartition
import Eight.LocalLeaf
namespace MordellEight.CubicBoxes.B14
open FixedTensor IntegerCube RationalCube Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace G99
def box : ClosedBox 3 := ⟨![(66603423/67108864),(66603423/67108864),(-965267/4194304)],![(134172113/134217728),(134172113/134217728),(-14479005/67108864)]⟩
theorem bound : BoxMajorant box := Leaf42.bound
end G99

namespace G101
def box : ClosedBox 3 := ⟨![(66603423/67108864),(134172113/134217728),(-965267/4194304)],![(134172113/134217728),(33784345/33554432),(-29923277/134217728)]⟩
theorem bound : BoxMajorant box := Leaf43.bound
end G101

namespace G102
def box : ClosedBox 3 := ⟨![(66603423/67108864),(134172113/134217728),(-29923277/134217728)],![(134172113/134217728),(33784345/33554432),(-14479005/67108864)]⟩
theorem bound : BoxMajorant box := Leaf44.bound
end G102

namespace G100
def box : ClosedBox 3 := ⟨![(66603423/67108864),(134172113/134217728),(-965267/4194304)],![(134172113/134217728),(33784345/33554432),(-14479005/67108864)]⟩
theorem eq_false : box.half 2 false=G101.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G102.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G101.bound) (by rw [eq_true]; exact G102.bound)
end G100

namespace G98
def box : ClosedBox 3 := ⟨![(66603423/67108864),(66603423/67108864),(-965267/4194304)],![(134172113/134217728),(33784345/33554432),(-14479005/67108864)]⟩
theorem eq_false : box.half 1 false=G99.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G100.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G99.bound) (by rw [eq_true]; exact G100.bound)
end G98

namespace G105
def box : ClosedBox 3 := ⟨![(134172113/134217728),(66603423/67108864),(-965267/4194304)],![(33784345/33554432),(134172113/134217728),(-29923277/134217728)]⟩
theorem bound : BoxMajorant box := Leaf45.bound
end G105

namespace G106
def box : ClosedBox 3 := ⟨![(134172113/134217728),(66603423/67108864),(-29923277/134217728)],![(33784345/33554432),(134172113/134217728),(-14479005/67108864)]⟩
theorem bound : BoxMajorant box := Leaf46.bound
end G106

namespace G104
def box : ClosedBox 3 := ⟨![(134172113/134217728),(66603423/67108864),(-965267/4194304)],![(33784345/33554432),(134172113/134217728),(-14479005/67108864)]⟩
theorem eq_false : box.half 2 false=G105.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G106.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G105.bound) (by rw [eq_true]; exact G106.bound)
end G104

namespace G108
def box : ClosedBox 3 := ⟨![(134172113/134217728),(134172113/134217728),(-965267/4194304)],![(33784345/33554432),(33784345/33554432),(-29923277/134217728)]⟩
theorem bound : BoxMajorant box := Leaf47.bound
end G108

namespace G120
def box : ClosedBox 3 := ⟨![(134172113/134217728),(134172113/134217728),(-29923277/134217728)],![(2147719075/2147483648),(2147719075/2147483648),(-238420949/1073741824)]⟩
theorem checked : localLeafCheck box 3=true := by decide +kernel
theorem bound : BoxMajorant box := by
  intro x hx hd
  exact localLeafCheck_sound box 3 checked hx hd.1
end G120

namespace G121
def box : ClosedBox 3 := ⟨![(134172113/134217728),(2147719075/2147483648),(-29923277/134217728)],![(2147719075/2147483648),(1074342171/1073741824),(-238420949/1073741824)]⟩
theorem bound : BoxMajorant box := Leaf48.bound
end G121

namespace G119
def box : ClosedBox 3 := ⟨![(134172113/134217728),(134172113/134217728),(-29923277/134217728)],![(2147719075/2147483648),(1074342171/1073741824),(-238420949/1073741824)]⟩
theorem eq_false : box.half 1 false=G120.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G121.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G120.bound) (by rw [eq_true]; exact G121.bound)
end G119

namespace G122
def box : ClosedBox 3 := ⟨![(2147719075/2147483648),(134172113/134217728),(-29923277/134217728)],![(1074342171/1073741824),(1074342171/1073741824),(-238420949/1073741824)]⟩
theorem bound : BoxMajorant box := Leaf49.bound
end G122

namespace G118
def box : ClosedBox 3 := ⟨![(134172113/134217728),(134172113/134217728),(-29923277/134217728)],![(1074342171/1073741824),(1074342171/1073741824),(-238420949/1073741824)]⟩
theorem eq_false : box.half 0 false=G119.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G122.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G119.bound) (by rw [eq_true]; exact G122.bound)
end G118

namespace G123
def box : ClosedBox 3 := ⟨![(134172113/134217728),(134172113/134217728),(-238420949/1073741824)],![(1074342171/1073741824),(1074342171/1073741824),(-118727841/536870912)]⟩
theorem bound : BoxMajorant box := Leaf50.bound
end G123

namespace G117
def box : ClosedBox 3 := ⟨![(134172113/134217728),(134172113/134217728),(-29923277/134217728)],![(1074342171/1073741824),(1074342171/1073741824),(-118727841/536870912)]⟩
theorem eq_false : box.half 2 false=G118.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G123.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G118.bound) (by rw [eq_true]; exact G123.bound)
end G117

namespace G124
def box : ClosedBox 3 := ⟨![(134172113/134217728),(1074342171/1073741824),(-29923277/134217728)],![(1074342171/1073741824),(537653719/536870912),(-118727841/536870912)]⟩
theorem bound : BoxMajorant box := Leaf51.bound
end G124

namespace G116
def box : ClosedBox 3 := ⟨![(134172113/134217728),(134172113/134217728),(-29923277/134217728)],![(1074342171/1073741824),(537653719/536870912),(-118727841/536870912)]⟩
theorem eq_false : box.half 1 false=G117.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G124.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G117.bound) (by rw [eq_true]; exact G124.bound)
end G116

namespace G125
def box : ClosedBox 3 := ⟨![(1074342171/1073741824),(134172113/134217728),(-29923277/134217728)],![(537653719/536870912),(537653719/536870912),(-118727841/536870912)]⟩
theorem bound : BoxMajorant box := Leaf52.bound
end G125

namespace G115
def box : ClosedBox 3 := ⟨![(134172113/134217728),(134172113/134217728),(-29923277/134217728)],![(537653719/536870912),(537653719/536870912),(-118727841/536870912)]⟩
theorem eq_false : box.half 0 false=G116.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G125.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G116.bound) (by rw [eq_true]; exact G125.bound)
end G115

namespace G126
def box : ClosedBox 3 := ⟨![(134172113/134217728),(134172113/134217728),(-118727841/536870912)],![(537653719/536870912),(537653719/536870912),(-58881287/268435456)]⟩
theorem bound : BoxMajorant box := Leaf53.bound
end G126

namespace G114
def box : ClosedBox 3 := ⟨![(134172113/134217728),(134172113/134217728),(-29923277/134217728)],![(537653719/536870912),(537653719/536870912),(-58881287/268435456)]⟩
theorem eq_false : box.half 2 false=G115.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G126.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G115.bound) (by rw [eq_true]; exact G126.bound)
end G114

namespace G127
def box : ClosedBox 3 := ⟨![(134172113/134217728),(537653719/536870912),(-29923277/134217728)],![(537653719/536870912),(269309493/268435456),(-58881287/268435456)]⟩
theorem bound : BoxMajorant box := Leaf54.bound
end G127

namespace G113
def box : ClosedBox 3 := ⟨![(134172113/134217728),(134172113/134217728),(-29923277/134217728)],![(537653719/536870912),(269309493/268435456),(-58881287/268435456)]⟩
theorem eq_false : box.half 1 false=G114.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G127.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G114.bound) (by rw [eq_true]; exact G127.bound)
end G113

namespace G128
def box : ClosedBox 3 := ⟨![(537653719/536870912),(134172113/134217728),(-29923277/134217728)],![(269309493/268435456),(269309493/268435456),(-58881287/268435456)]⟩
theorem bound : BoxMajorant box := Leaf55.bound
end G128

namespace G112
def box : ClosedBox 3 := ⟨![(134172113/134217728),(134172113/134217728),(-29923277/134217728)],![(269309493/268435456),(269309493/268435456),(-58881287/268435456)]⟩
theorem eq_false : box.half 0 false=G113.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G128.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G113.bound) (by rw [eq_true]; exact G128.bound)
end G112

namespace G129
def box : ClosedBox 3 := ⟨![(134172113/134217728),(134172113/134217728),(-58881287/268435456)],![(269309493/268435456),(269309493/268435456),(-14479005/67108864)]⟩
theorem bound : BoxMajorant box := Leaf56.bound
end G129

namespace G111
def box : ClosedBox 3 := ⟨![(134172113/134217728),(134172113/134217728),(-29923277/134217728)],![(269309493/268435456),(269309493/268435456),(-14479005/67108864)]⟩
theorem eq_false : box.half 2 false=G112.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G129.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G112.bound) (by rw [eq_true]; exact G129.bound)
end G111

namespace G130
def box : ClosedBox 3 := ⟨![(134172113/134217728),(269309493/268435456),(-29923277/134217728)],![(269309493/268435456),(33784345/33554432),(-14479005/67108864)]⟩
theorem bound : BoxMajorant box := Leaf57.bound
end G130

namespace G110
def box : ClosedBox 3 := ⟨![(134172113/134217728),(134172113/134217728),(-29923277/134217728)],![(269309493/268435456),(33784345/33554432),(-14479005/67108864)]⟩
theorem eq_false : box.half 1 false=G111.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G130.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G111.bound) (by rw [eq_true]; exact G130.bound)
end G110

namespace G131
def box : ClosedBox 3 := ⟨![(269309493/268435456),(134172113/134217728),(-29923277/134217728)],![(33784345/33554432),(33784345/33554432),(-14479005/67108864)]⟩
theorem bound : BoxMajorant box := Leaf58.bound
end G131

namespace G109
def box : ClosedBox 3 := ⟨![(134172113/134217728),(134172113/134217728),(-29923277/134217728)],![(33784345/33554432),(33784345/33554432),(-14479005/67108864)]⟩
theorem eq_false : box.half 0 false=G110.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G131.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G110.bound) (by rw [eq_true]; exact G131.bound)
end G109

namespace G107
def box : ClosedBox 3 := ⟨![(134172113/134217728),(134172113/134217728),(-965267/4194304)],![(33784345/33554432),(33784345/33554432),(-14479005/67108864)]⟩
theorem eq_false : box.half 2 false=G108.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G109.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G108.bound) (by rw [eq_true]; exact G109.bound)
end G107

namespace G103
def box : ClosedBox 3 := ⟨![(134172113/134217728),(66603423/67108864),(-965267/4194304)],![(33784345/33554432),(33784345/33554432),(-14479005/67108864)]⟩
theorem eq_false : box.half 1 false=G104.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G107.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G104.bound) (by rw [eq_true]; exact G107.bound)
end G103

namespace G97
def box : ClosedBox 3 := ⟨![(66603423/67108864),(66603423/67108864),(-965267/4194304)],![(33784345/33554432),(33784345/33554432),(-14479005/67108864)]⟩
theorem eq_false : box.half 0 false=G98.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G103.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G98.bound) (by rw [eq_true]; exact G103.bound)
end G97

namespace G132
def box : ClosedBox 3 := ⟨![(66603423/67108864),(66603423/67108864),(-14479005/67108864)],![(33784345/33554432),(33784345/33554432),(-6756869/33554432)]⟩
theorem bound : BoxMajorant box := Leaf59.bound
end G132

namespace G96
def box : ClosedBox 3 := ⟨![(66603423/67108864),(66603423/67108864),(-965267/4194304)],![(33784345/33554432),(33784345/33554432),(-6756869/33554432)]⟩
theorem eq_false : box.half 2 false=G97.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G132.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G97.bound) (by rw [eq_true]; exact G132.bound)
end G96

namespace G94
def box : ClosedBox 3 := ⟨![(66603423/67108864),(16409539/16777216),(-965267/4194304)],![(33784345/33554432),(33784345/33554432),(-6756869/33554432)]⟩
theorem eq_false : box.half 1 false=G95.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G96.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G95.bound) (by rw [eq_true]; exact G96.bound)
end G94

namespace G92
def box : ClosedBox 3 := ⟨![(16409539/16777216),(16409539/16777216),(-965267/4194304)],![(33784345/33554432),(33784345/33554432),(-6756869/33554432)]⟩
theorem eq_false : box.half 0 false=G93.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G94.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G93.bound) (by rw [eq_true]; exact G94.bound)
end G92

namespace G133
def box : ClosedBox 3 := ⟨![(16409539/16777216),(16409539/16777216),(-6756869/33554432)],![(33784345/33554432),(33784345/33554432),(-2895801/16777216)]⟩
theorem bound : BoxMajorant box := Leaf60.bound
end G133

namespace G91
def box : ClosedBox 3 := ⟨![(16409539/16777216),(16409539/16777216),(-965267/4194304)],![(33784345/33554432),(33784345/33554432),(-2895801/16777216)]⟩
theorem eq_false : box.half 2 false=G92.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G133.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G92.bound) (by rw [eq_true]; exact G133.bound)
end G91

namespace G134
def box : ClosedBox 3 := ⟨![(16409539/16777216),(33784345/33554432),(-965267/4194304)],![(33784345/33554432),(8687403/8388608),(-2895801/16777216)]⟩
theorem bound : BoxMajorant box := Leaf61.bound
end G134

namespace G90
def box : ClosedBox 3 := ⟨![(16409539/16777216),(16409539/16777216),(-965267/4194304)],![(33784345/33554432),(8687403/8388608),(-2895801/16777216)]⟩
theorem eq_false : box.half 1 false=G91.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G134.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G91.bound) (by rw [eq_true]; exact G134.bound)
end G90

namespace G135
def box : ClosedBox 3 := ⟨![(33784345/33554432),(16409539/16777216),(-965267/4194304)],![(8687403/8388608),(8687403/8388608),(-2895801/16777216)]⟩
theorem bound : BoxMajorant box := Leaf62.bound
end G135

namespace G89
def box : ClosedBox 3 := ⟨![(16409539/16777216),(16409539/16777216),(-965267/4194304)],![(8687403/8388608),(8687403/8388608),(-2895801/16777216)]⟩
theorem eq_false : box.half 0 false=G90.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G135.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G90.bound) (by rw [eq_true]; exact G135.bound)
end G89

namespace G136
def box : ClosedBox 3 := ⟨![(16409539/16777216),(16409539/16777216),(-2895801/16777216)],![(8687403/8388608),(8687403/8388608),(-965267/8388608)]⟩
theorem bound : BoxMajorant box := Leaf63.bound
end G136

namespace G88
def box : ClosedBox 3 := ⟨![(16409539/16777216),(16409539/16777216),(-965267/4194304)],![(8687403/8388608),(8687403/8388608),(-965267/8388608)]⟩
theorem eq_false : box.half 2 false=G89.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G136.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G89.bound) (by rw [eq_true]; exact G136.bound)
end G88

namespace G86
def box : ClosedBox 3 := ⟨![(16409539/16777216),(965267/1048576),(-965267/4194304)],![(8687403/8388608),(8687403/8388608),(-965267/8388608)]⟩
theorem eq_false : box.half 1 false=G87.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G88.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G87.bound) (by rw [eq_true]; exact G88.bound)
end G86

namespace G82
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(-965267/4194304)],![(8687403/8388608),(8687403/8388608),(-965267/8388608)]⟩
theorem eq_false : box.half 0 false=G83.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G86.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G83.bound) (by rw [eq_true]; exact G86.bound)
end G82

namespace G137
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(-965267/8388608)],![(8687403/8388608),(8687403/8388608),0]⟩
theorem bound : BoxMajorant box := Leaf64.bound
end G137

namespace G81
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(-965267/4194304)],![(8687403/8388608),(8687403/8388608),0]⟩
theorem eq_false : box.half 2 false=G82.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G137.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G82.bound) (by rw [eq_true]; exact G137.bound)
end G81

namespace G139
def box : ClosedBox 3 := ⟨![(965267/1048576),(8687403/8388608),(-965267/4194304)],![(8687403/8388608),(4826335/4194304),(-965267/8388608)]⟩
theorem bound : BoxMajorant box := Leaf65.bound
end G139

namespace G140
def box : ClosedBox 3 := ⟨![(965267/1048576),(8687403/8388608),(-965267/8388608)],![(8687403/8388608),(4826335/4194304),0]⟩
theorem bound : BoxMajorant box := Leaf66.bound
end G140

namespace G138
def box : ClosedBox 3 := ⟨![(965267/1048576),(8687403/8388608),(-965267/4194304)],![(8687403/8388608),(4826335/4194304),0]⟩
theorem eq_false : box.half 2 false=G139.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G140.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G139.bound) (by rw [eq_true]; exact G140.bound)
end G138

namespace G80
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(-965267/4194304)],![(8687403/8388608),(4826335/4194304),0]⟩
theorem eq_false : box.half 1 false=G81.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G138.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G81.bound) (by rw [eq_true]; exact G138.bound)
end G80

namespace G141
def box : ClosedBox 3 := ⟨![(8687403/8388608),(965267/1048576),(-965267/4194304)],![(4826335/4194304),(4826335/4194304),0]⟩
theorem bound : BoxMajorant box := Leaf67.bound
end G141

namespace G79
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(-965267/4194304)],![(4826335/4194304),(4826335/4194304),0]⟩
theorem eq_false : box.half 0 false=G80.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G141.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G80.bound) (by rw [eq_true]; exact G141.bound)
end G79

namespace G67
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(-965267/2097152)],![(4826335/4194304),(4826335/4194304),0]⟩
theorem eq_false : box.half 2 false=G68.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G79.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G68.bound) (by rw [eq_true]; exact G79.bound)
end G67

namespace G143
def box : ClosedBox 3 := ⟨![(965267/1048576),(4826335/4194304),(-965267/2097152)],![(4826335/4194304),(2895801/2097152),(-965267/4194304)]⟩
theorem bound : BoxMajorant box := Leaf68.bound
end G143

namespace G144
def box : ClosedBox 3 := ⟨![(965267/1048576),(4826335/4194304),(-965267/4194304)],![(4826335/4194304),(2895801/2097152),0]⟩
theorem bound : BoxMajorant box := Leaf69.bound
end G144

namespace G142
def box : ClosedBox 3 := ⟨![(965267/1048576),(4826335/4194304),(-965267/2097152)],![(4826335/4194304),(2895801/2097152),0]⟩
theorem eq_false : box.half 2 false=G143.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G144.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G143.bound) (by rw [eq_true]; exact G144.bound)
end G142

namespace G66
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(-965267/2097152)],![(4826335/4194304),(2895801/2097152),0]⟩
theorem eq_false : box.half 1 false=G67.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G142.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G67.bound) (by rw [eq_true]; exact G142.bound)
end G66

namespace G145
def box : ClosedBox 3 := ⟨![(4826335/4194304),(965267/1048576),(-965267/2097152)],![(2895801/2097152),(2895801/2097152),0]⟩
theorem bound : BoxMajorant box := Leaf70.bound
end G145

namespace G65
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(-965267/2097152)],![(2895801/2097152),(2895801/2097152),0]⟩
theorem eq_false : box.half 0 false=G66.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G145.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G66.bound) (by rw [eq_true]; exact G145.bound)
end G65

namespace G1
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(-965267/1048576)],![(2895801/2097152),(2895801/2097152),0]⟩
theorem eq_false : box.half 2 false=G2.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G65.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G2.bound) (by rw [eq_true]; exact G65.bound)
end G1

namespace G150
def box : ClosedBox 3 := ⟨![(965267/1048576),(2895801/2097152),(-965267/1048576)],![(4826335/4194304),(6756869/4194304),(-2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf71.bound
end G150

namespace G151
def box : ClosedBox 3 := ⟨![(965267/1048576),(2895801/2097152),(-2895801/4194304)],![(4826335/4194304),(6756869/4194304),(-965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf72.bound
end G151

namespace G149
def box : ClosedBox 3 := ⟨![(965267/1048576),(2895801/2097152),(-965267/1048576)],![(4826335/4194304),(6756869/4194304),(-965267/2097152)]⟩
theorem eq_false : box.half 2 false=G150.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G151.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G150.bound) (by rw [eq_true]; exact G151.bound)
end G149

namespace G153
def box : ClosedBox 3 := ⟨![(965267/1048576),(6756869/4194304),(-965267/1048576)],![(4826335/4194304),(965267/524288),(-2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf73.bound
end G153

namespace G154
def box : ClosedBox 3 := ⟨![(965267/1048576),(6756869/4194304),(-2895801/4194304)],![(4826335/4194304),(965267/524288),(-965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf74.bound
end G154

namespace G152
def box : ClosedBox 3 := ⟨![(965267/1048576),(6756869/4194304),(-965267/1048576)],![(4826335/4194304),(965267/524288),(-965267/2097152)]⟩
theorem eq_false : box.half 2 false=G153.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G154.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G153.bound) (by rw [eq_true]; exact G154.bound)
end G152

namespace G148
def box : ClosedBox 3 := ⟨![(965267/1048576),(2895801/2097152),(-965267/1048576)],![(4826335/4194304),(965267/524288),(-965267/2097152)]⟩
theorem eq_false : box.half 1 false=G149.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G152.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G149.bound) (by rw [eq_true]; exact G152.bound)
end G148

namespace G155
def box : ClosedBox 3 := ⟨![(4826335/4194304),(2895801/2097152),(-965267/1048576)],![(2895801/2097152),(965267/524288),(-965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf75.bound
end G155

namespace G147
def box : ClosedBox 3 := ⟨![(965267/1048576),(2895801/2097152),(-965267/1048576)],![(2895801/2097152),(965267/524288),(-965267/2097152)]⟩
theorem eq_false : box.half 0 false=G148.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G155.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G148.bound) (by rw [eq_true]; exact G155.bound)
end G147

namespace G156
def box : ClosedBox 3 := ⟨![(965267/1048576),(2895801/2097152),(-965267/2097152)],![(2895801/2097152),(965267/524288),0]⟩
theorem bound : BoxMajorant box := Leaf76.bound
end G156

namespace G146
def box : ClosedBox 3 := ⟨![(965267/1048576),(2895801/2097152),(-965267/1048576)],![(2895801/2097152),(965267/524288),0]⟩
theorem eq_false : box.half 2 false=G147.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G156.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G147.bound) (by rw [eq_true]; exact G156.bound)
end G146

namespace G0
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(-965267/1048576)],![(2895801/2097152),(965267/524288),0]⟩
theorem eq_false : box.half 1 false=G1.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G146.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G1.bound) (by rw [eq_true]; exact G146.bound)
end G0

end MordellEight.CubicBoxes.B14
