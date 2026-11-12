import Eight.CubicBoxes.B28.C32
import Eight.CubicBoxes.B28.C33
import Eight.CubicBoxes.B28.C34
import Eight.CubicBoxes.B28.C35
import Eight.CubicBoxes.B28.C36
import Eight.CubicBoxes.B28.C37
import Eight.CubicBoxes.B28.C38
import Eight.CubicBoxes.B28.C39
import Eight.CubicBoxes.B28.C40
import Eight.CubicBoxes.B28.C41
import Eight.CubicBoxes.B28.C42
import Eight.CubicBoxes.B28.C43
import Eight.CubicBoxes.B28.G00
import Eight.CubicBoxes.B28.G01
import Eight.RootPartition
import Eight.LocalLeaf
namespace MordellEight.CubicBoxes.B28
open FixedTensor IntegerCube RationalCube Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace G192
def box : ClosedBox 3 := ⟨![(134172113/134217728),(2147719075/2147483648),(1338825329/2147483648)],![(2147719075/2147483648),(1074342171/1073741824),(334947649/536870912)]⟩
theorem bound : BoxMajorant box := Leaf76.bound
end G192

namespace G190
def box : ClosedBox 3 := ⟨![(134172113/134217728),(2147719075/2147483648),(668930031/1073741824)],![(2147719075/2147483648),(1074342171/1073741824),(334947649/536870912)]⟩
theorem eq_false : box.half 2 false=G191.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G192.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G191.bound) (by rw [eq_true]; exact G192.bound)
end G190

namespace G138
def box : ClosedBox 3 := ⟨![(134172113/134217728),(134172113/134217728),(668930031/1073741824)],![(2147719075/2147483648),(1074342171/1073741824),(334947649/536870912)]⟩
theorem eq_false : box.half 1 false=G139.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G190.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G139.bound) (by rw [eq_true]; exact G190.bound)
end G138

namespace G195
def box : ClosedBox 3 := ⟨![(2147719075/2147483648),(134172113/134217728),(668930031/1073741824)],![(1074342171/1073741824),(2147719075/2147483648),(1338825329/2147483648)]⟩
theorem bound : BoxMajorant box := Leaf77.bound
end G195

namespace G196
def box : ClosedBox 3 := ⟨![(2147719075/2147483648),(134172113/134217728),(1338825329/2147483648)],![(1074342171/1073741824),(2147719075/2147483648),(334947649/536870912)]⟩
theorem bound : BoxMajorant box := Leaf78.bound
end G196

namespace G194
def box : ClosedBox 3 := ⟨![(2147719075/2147483648),(134172113/134217728),(668930031/1073741824)],![(1074342171/1073741824),(2147719075/2147483648),(334947649/536870912)]⟩
theorem eq_false : box.half 2 false=G195.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G196.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G195.bound) (by rw [eq_true]; exact G196.bound)
end G194

namespace G197
def box : ClosedBox 3 := ⟨![(2147719075/2147483648),(2147719075/2147483648),(668930031/1073741824)],![(1074342171/1073741824),(1074342171/1073741824),(334947649/536870912)]⟩
theorem bound : BoxMajorant box := Leaf79.bound
end G197

namespace G193
def box : ClosedBox 3 := ⟨![(2147719075/2147483648),(134172113/134217728),(668930031/1073741824)],![(1074342171/1073741824),(1074342171/1073741824),(334947649/536870912)]⟩
theorem eq_false : box.half 1 false=G194.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G197.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G194.bound) (by rw [eq_true]; exact G197.bound)
end G193

namespace G137
def box : ClosedBox 3 := ⟨![(134172113/134217728),(134172113/134217728),(668930031/1073741824)],![(1074342171/1073741824),(1074342171/1073741824),(334947649/536870912)]⟩
theorem eq_false : box.half 0 false=G138.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G193.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G138.bound) (by rw [eq_true]; exact G193.bound)
end G137

namespace G135
def box : ClosedBox 3 := ⟨![(134172113/134217728),(134172113/134217728),(166991191/268435456)],![(1074342171/1073741824),(1074342171/1073741824),(334947649/536870912)]⟩
theorem eq_false : box.half 2 false=G136.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G137.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G136.bound) (by rw [eq_true]; exact G137.bound)
end G135

namespace G198
def box : ClosedBox 3 := ⟨![(134172113/134217728),(1074342171/1073741824),(166991191/268435456)],![(1074342171/1073741824),(537653719/536870912),(334947649/536870912)]⟩
theorem bound : BoxMajorant box := Leaf80.bound
end G198

namespace G134
def box : ClosedBox 3 := ⟨![(134172113/134217728),(134172113/134217728),(166991191/268435456)],![(1074342171/1073741824),(537653719/536870912),(334947649/536870912)]⟩
theorem eq_false : box.half 1 false=G135.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G198.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G135.bound) (by rw [eq_true]; exact G198.bound)
end G134

namespace G199
def box : ClosedBox 3 := ⟨![(1074342171/1073741824),(134172113/134217728),(166991191/268435456)],![(537653719/536870912),(537653719/536870912),(334947649/536870912)]⟩
theorem bound : BoxMajorant box := Leaf81.bound
end G199

namespace G133
def box : ClosedBox 3 := ⟨![(134172113/134217728),(134172113/134217728),(166991191/268435456)],![(537653719/536870912),(537653719/536870912),(334947649/536870912)]⟩
theorem eq_false : box.half 0 false=G134.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G199.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G134.bound) (by rw [eq_true]; exact G199.bound)
end G133

namespace G200
def box : ClosedBox 3 := ⟨![(134172113/134217728),(134172113/134217728),(334947649/536870912)],![(537653719/536870912),(537653719/536870912),(83978229/134217728)]⟩
theorem bound : BoxMajorant box := Leaf82.bound
end G200

namespace G132
def box : ClosedBox 3 := ⟨![(134172113/134217728),(134172113/134217728),(166991191/268435456)],![(537653719/536870912),(537653719/536870912),(83978229/134217728)]⟩
theorem eq_false : box.half 2 false=G133.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G200.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G133.bound) (by rw [eq_true]; exact G200.bound)
end G132

namespace G201
def box : ClosedBox 3 := ⟨![(134172113/134217728),(537653719/536870912),(166991191/268435456)],![(537653719/536870912),(269309493/268435456),(83978229/134217728)]⟩
theorem bound : BoxMajorant box := Leaf83.bound
end G201

namespace G131
def box : ClosedBox 3 := ⟨![(134172113/134217728),(134172113/134217728),(166991191/268435456)],![(537653719/536870912),(269309493/268435456),(83978229/134217728)]⟩
theorem eq_false : box.half 1 false=G132.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G201.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G132.bound) (by rw [eq_true]; exact G201.bound)
end G131

namespace G202
def box : ClosedBox 3 := ⟨![(537653719/536870912),(134172113/134217728),(166991191/268435456)],![(269309493/268435456),(269309493/268435456),(83978229/134217728)]⟩
theorem bound : BoxMajorant box := Leaf84.bound
end G202

namespace G130
def box : ClosedBox 3 := ⟨![(134172113/134217728),(134172113/134217728),(166991191/268435456)],![(269309493/268435456),(269309493/268435456),(83978229/134217728)]⟩
theorem eq_false : box.half 0 false=G131.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G202.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G131.bound) (by rw [eq_true]; exact G202.bound)
end G130

namespace G128
def box : ClosedBox 3 := ⟨![(134172113/134217728),(134172113/134217728),(41506481/67108864)],![(269309493/268435456),(269309493/268435456),(83978229/134217728)]⟩
theorem eq_false : box.half 2 false=G129.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G130.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G129.bound) (by rw [eq_true]; exact G130.bound)
end G128

namespace G203
def box : ClosedBox 3 := ⟨![(134172113/134217728),(269309493/268435456),(41506481/67108864)],![(269309493/268435456),(33784345/33554432),(83978229/134217728)]⟩
theorem bound : BoxMajorant box := Leaf85.bound
end G203

namespace G127
def box : ClosedBox 3 := ⟨![(134172113/134217728),(134172113/134217728),(41506481/67108864)],![(269309493/268435456),(33784345/33554432),(83978229/134217728)]⟩
theorem eq_false : box.half 1 false=G128.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G203.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G128.bound) (by rw [eq_true]; exact G203.bound)
end G127

namespace G204
def box : ClosedBox 3 := ⟨![(269309493/268435456),(134172113/134217728),(41506481/67108864)],![(33784345/33554432),(33784345/33554432),(83978229/134217728)]⟩
theorem bound : BoxMajorant box := Leaf86.bound
end G204

namespace G126
def box : ClosedBox 3 := ⟨![(134172113/134217728),(134172113/134217728),(41506481/67108864)],![(33784345/33554432),(33784345/33554432),(83978229/134217728)]⟩
theorem eq_false : box.half 0 false=G127.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G204.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G127.bound) (by rw [eq_true]; exact G204.bound)
end G126

namespace G205
def box : ClosedBox 3 := ⟨![(134172113/134217728),(134172113/134217728),(83978229/134217728)],![(33784345/33554432),(33784345/33554432),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf87.bound
end G205

namespace G125
def box : ClosedBox 3 := ⟨![(134172113/134217728),(134172113/134217728),(41506481/67108864)],![(33784345/33554432),(33784345/33554432),(10617937/16777216)]⟩
theorem eq_false : box.half 2 false=G126.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G205.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G126.bound) (by rw [eq_true]; exact G205.bound)
end G125

namespace G103
def box : ClosedBox 3 := ⟨![(134172113/134217728),(66603423/67108864),(41506481/67108864)],![(33784345/33554432),(33784345/33554432),(10617937/16777216)]⟩
theorem eq_false : box.half 1 false=G104.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G125.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G104.bound) (by rw [eq_true]; exact G125.bound)
end G103

namespace G71
def box : ClosedBox 3 := ⟨![(66603423/67108864),(66603423/67108864),(41506481/67108864)],![(33784345/33554432),(33784345/33554432),(10617937/16777216)]⟩
theorem eq_false : box.half 0 false=G72.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G103.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G72.bound) (by rw [eq_true]; exact G103.bound)
end G71

namespace G69
def box : ClosedBox 3 := ⟨![(66603423/67108864),(66603423/67108864),(20270607/33554432)],![(33784345/33554432),(33784345/33554432),(10617937/16777216)]⟩
theorem eq_false : box.half 2 false=G70.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G71.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G70.bound) (by rw [eq_true]; exact G71.bound)
end G69

namespace G65
def box : ClosedBox 3 := ⟨![(66603423/67108864),(16409539/16777216),(20270607/33554432)],![(33784345/33554432),(33784345/33554432),(10617937/16777216)]⟩
theorem eq_false : box.half 1 false=G66.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G69.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G66.bound) (by rw [eq_true]; exact G69.bound)
end G65

namespace G59
def box : ClosedBox 3 := ⟨![(16409539/16777216),(16409539/16777216),(20270607/33554432)],![(33784345/33554432),(33784345/33554432),(10617937/16777216)]⟩
theorem eq_false : box.half 0 false=G60.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G65.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G60.bound) (by rw [eq_true]; exact G65.bound)
end G59

namespace G57
def box : ClosedBox 3 := ⟨![(16409539/16777216),(16409539/16777216),(4826335/8388608)],![(33784345/33554432),(33784345/33554432),(10617937/16777216)]⟩
theorem eq_false : box.half 2 false=G58.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G59.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G58.bound) (by rw [eq_true]; exact G59.bound)
end G57

namespace G207
def box : ClosedBox 3 := ⟨![(16409539/16777216),(33784345/33554432),(4826335/8388608)],![(33784345/33554432),(8687403/8388608),(20270607/33554432)]⟩
theorem bound : BoxMajorant box := Leaf88.bound
end G207

namespace G211
def box : ClosedBox 3 := ⟨![(16409539/16777216),(33784345/33554432),(20270607/33554432)],![(66603423/67108864),(68533957/67108864),(41506481/67108864)]⟩
theorem bound : BoxMajorant box := Leaf89.bound
end G211

namespace G212
def box : ClosedBox 3 := ⟨![(16409539/16777216),(33784345/33554432),(41506481/67108864)],![(66603423/67108864),(68533957/67108864),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf90.bound
end G212

namespace G210
def box : ClosedBox 3 := ⟨![(16409539/16777216),(33784345/33554432),(20270607/33554432)],![(66603423/67108864),(68533957/67108864),(10617937/16777216)]⟩
theorem eq_false : box.half 2 false=G211.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G212.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G211.bound) (by rw [eq_true]; exact G212.bound)
end G210

namespace G214
def box : ClosedBox 3 := ⟨![(16409539/16777216),(68533957/67108864),(20270607/33554432)],![(66603423/67108864),(8687403/8388608),(41506481/67108864)]⟩
theorem bound : BoxMajorant box := Leaf91.bound
end G214

namespace G215
def box : ClosedBox 3 := ⟨![(16409539/16777216),(68533957/67108864),(41506481/67108864)],![(66603423/67108864),(8687403/8388608),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf92.bound
end G215

namespace G213
def box : ClosedBox 3 := ⟨![(16409539/16777216),(68533957/67108864),(20270607/33554432)],![(66603423/67108864),(8687403/8388608),(10617937/16777216)]⟩
theorem eq_false : box.half 2 false=G214.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G215.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G214.bound) (by rw [eq_true]; exact G215.bound)
end G213

namespace G209
def box : ClosedBox 3 := ⟨![(16409539/16777216),(33784345/33554432),(20270607/33554432)],![(66603423/67108864),(8687403/8388608),(10617937/16777216)]⟩
theorem eq_false : box.half 1 false=G210.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G213.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G210.bound) (by rw [eq_true]; exact G213.bound)
end G209

namespace G218
def box : ClosedBox 3 := ⟨![(66603423/67108864),(33784345/33554432),(20270607/33554432)],![(33784345/33554432),(68533957/67108864),(41506481/67108864)]⟩
theorem bound : BoxMajorant box := Leaf93.bound
end G218

namespace G221
def box : ClosedBox 3 := ⟨![(66603423/67108864),(33784345/33554432),(41506481/67108864)],![(134172113/134217728),(136102647/134217728),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf94.bound
end G221

namespace G222
def box : ClosedBox 3 := ⟨![(66603423/67108864),(136102647/134217728),(41506481/67108864)],![(134172113/134217728),(68533957/67108864),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf95.bound
end G222

namespace G220
def box : ClosedBox 3 := ⟨![(66603423/67108864),(33784345/33554432),(41506481/67108864)],![(134172113/134217728),(68533957/67108864),(10617937/16777216)]⟩
theorem eq_false : box.half 1 false=G221.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G222.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G221.bound) (by rw [eq_true]; exact G222.bound)
end G220

namespace G223
def box : ClosedBox 3 := ⟨![(134172113/134217728),(33784345/33554432),(41506481/67108864)],![(33784345/33554432),(68533957/67108864),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf96.bound
end G223

namespace G219
def box : ClosedBox 3 := ⟨![(66603423/67108864),(33784345/33554432),(41506481/67108864)],![(33784345/33554432),(68533957/67108864),(10617937/16777216)]⟩
theorem eq_false : box.half 0 false=G220.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G223.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G220.bound) (by rw [eq_true]; exact G223.bound)
end G219

namespace G217
def box : ClosedBox 3 := ⟨![(66603423/67108864),(33784345/33554432),(20270607/33554432)],![(33784345/33554432),(68533957/67108864),(10617937/16777216)]⟩
theorem eq_false : box.half 2 false=G218.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G219.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G218.bound) (by rw [eq_true]; exact G219.bound)
end G217

namespace G224
def box : ClosedBox 3 := ⟨![(66603423/67108864),(68533957/67108864),(20270607/33554432)],![(33784345/33554432),(8687403/8388608),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf97.bound
end G224

namespace G216
def box : ClosedBox 3 := ⟨![(66603423/67108864),(33784345/33554432),(20270607/33554432)],![(33784345/33554432),(8687403/8388608),(10617937/16777216)]⟩
theorem eq_false : box.half 1 false=G217.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G224.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G217.bound) (by rw [eq_true]; exact G224.bound)
end G216

namespace G208
def box : ClosedBox 3 := ⟨![(16409539/16777216),(33784345/33554432),(20270607/33554432)],![(33784345/33554432),(8687403/8388608),(10617937/16777216)]⟩
theorem eq_false : box.half 0 false=G209.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G216.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G209.bound) (by rw [eq_true]; exact G216.bound)
end G208

namespace G206
def box : ClosedBox 3 := ⟨![(16409539/16777216),(33784345/33554432),(4826335/8388608)],![(33784345/33554432),(8687403/8388608),(10617937/16777216)]⟩
theorem eq_false : box.half 2 false=G207.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G208.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G207.bound) (by rw [eq_true]; exact G208.bound)
end G206

namespace G56
def box : ClosedBox 3 := ⟨![(16409539/16777216),(16409539/16777216),(4826335/8388608)],![(33784345/33554432),(8687403/8388608),(10617937/16777216)]⟩
theorem eq_false : box.half 1 false=G57.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G206.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G57.bound) (by rw [eq_true]; exact G206.bound)
end G56

namespace G227
def box : ClosedBox 3 := ⟨![(33784345/33554432),(16409539/16777216),(4826335/8388608)],![(8687403/8388608),(33784345/33554432),(20270607/33554432)]⟩
theorem bound : BoxMajorant box := Leaf98.bound
end G227

namespace G230
def box : ClosedBox 3 := ⟨![(33784345/33554432),(16409539/16777216),(20270607/33554432)],![(68533957/67108864),(66603423/67108864),(10617937/16777216)]⟩
theorem checked : outsideCheck box=true := by decide +kernel
theorem bound : BoxMajorant box := by
  intro x hx hd
  exact (outsideCheck_sound box checked hx hd.1 hd.2).elim
end G230

namespace G232
def box : ClosedBox 3 := ⟨![(33784345/33554432),(66603423/67108864),(20270607/33554432)],![(68533957/67108864),(33784345/33554432),(41506481/67108864)]⟩
theorem bound : BoxMajorant box := Leaf99.bound
end G232

namespace G235
def box : ClosedBox 3 := ⟨![(33784345/33554432),(66603423/67108864),(41506481/67108864)],![(136102647/134217728),(134172113/134217728),(10617937/16777216)]⟩
theorem checked : outsideCheck box=true := by decide +kernel
theorem bound : BoxMajorant box := by
  intro x hx hd
  exact (outsideCheck_sound box checked hx hd.1 hd.2).elim
end G235

namespace G236
def box : ClosedBox 3 := ⟨![(33784345/33554432),(134172113/134217728),(41506481/67108864)],![(136102647/134217728),(33784345/33554432),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf100.bound
end G236

namespace G234
def box : ClosedBox 3 := ⟨![(33784345/33554432),(66603423/67108864),(41506481/67108864)],![(136102647/134217728),(33784345/33554432),(10617937/16777216)]⟩
theorem eq_false : box.half 1 false=G235.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G236.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G235.bound) (by rw [eq_true]; exact G236.bound)
end G234

namespace G237
def box : ClosedBox 3 := ⟨![(136102647/134217728),(66603423/67108864),(41506481/67108864)],![(68533957/67108864),(33784345/33554432),(10617937/16777216)]⟩
theorem checked : outsideCheck box=true := by decide +kernel
theorem bound : BoxMajorant box := by
  intro x hx hd
  exact (outsideCheck_sound box checked hx hd.1 hd.2).elim
end G237

namespace G233
def box : ClosedBox 3 := ⟨![(33784345/33554432),(66603423/67108864),(41506481/67108864)],![(68533957/67108864),(33784345/33554432),(10617937/16777216)]⟩
theorem eq_false : box.half 0 false=G234.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G237.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G234.bound) (by rw [eq_true]; exact G237.bound)
end G233

namespace G231
def box : ClosedBox 3 := ⟨![(33784345/33554432),(66603423/67108864),(20270607/33554432)],![(68533957/67108864),(33784345/33554432),(10617937/16777216)]⟩
theorem eq_false : box.half 2 false=G232.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G233.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G232.bound) (by rw [eq_true]; exact G233.bound)
end G231

namespace G229
def box : ClosedBox 3 := ⟨![(33784345/33554432),(16409539/16777216),(20270607/33554432)],![(68533957/67108864),(33784345/33554432),(10617937/16777216)]⟩
theorem eq_false : box.half 1 false=G230.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G231.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G230.bound) (by rw [eq_true]; exact G231.bound)
end G229

namespace G238
def box : ClosedBox 3 := ⟨![(68533957/67108864),(16409539/16777216),(20270607/33554432)],![(8687403/8388608),(33784345/33554432),(10617937/16777216)]⟩
theorem checked : outsideCheck box=true := by decide +kernel
theorem bound : BoxMajorant box := by
  intro x hx hd
  exact (outsideCheck_sound box checked hx hd.1 hd.2).elim
end G238

namespace G228
def box : ClosedBox 3 := ⟨![(33784345/33554432),(16409539/16777216),(20270607/33554432)],![(8687403/8388608),(33784345/33554432),(10617937/16777216)]⟩
theorem eq_false : box.half 0 false=G229.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G238.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G229.bound) (by rw [eq_true]; exact G238.bound)
end G228

namespace G226
def box : ClosedBox 3 := ⟨![(33784345/33554432),(16409539/16777216),(4826335/8388608)],![(8687403/8388608),(33784345/33554432),(10617937/16777216)]⟩
theorem eq_false : box.half 2 false=G227.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G228.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G227.bound) (by rw [eq_true]; exact G228.bound)
end G226

namespace G240
def box : ClosedBox 3 := ⟨![(33784345/33554432),(33784345/33554432),(4826335/8388608)],![(8687403/8388608),(8687403/8388608),(20270607/33554432)]⟩
theorem bound : BoxMajorant box := Leaf101.bound
end G240

namespace G241
def box : ClosedBox 3 := ⟨![(33784345/33554432),(33784345/33554432),(20270607/33554432)],![(8687403/8388608),(8687403/8388608),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf102.bound
end G241

namespace G239
def box : ClosedBox 3 := ⟨![(33784345/33554432),(33784345/33554432),(4826335/8388608)],![(8687403/8388608),(8687403/8388608),(10617937/16777216)]⟩
theorem eq_false : box.half 2 false=G240.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G241.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G240.bound) (by rw [eq_true]; exact G241.bound)
end G239

namespace G225
def box : ClosedBox 3 := ⟨![(33784345/33554432),(16409539/16777216),(4826335/8388608)],![(8687403/8388608),(8687403/8388608),(10617937/16777216)]⟩
theorem eq_false : box.half 1 false=G226.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G239.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G226.bound) (by rw [eq_true]; exact G239.bound)
end G225

namespace G55
def box : ClosedBox 3 := ⟨![(16409539/16777216),(16409539/16777216),(4826335/8388608)],![(8687403/8388608),(8687403/8388608),(10617937/16777216)]⟩
theorem eq_false : box.half 0 false=G56.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G225.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G56.bound) (by rw [eq_true]; exact G225.bound)
end G55

namespace G242
def box : ClosedBox 3 := ⟨![(16409539/16777216),(16409539/16777216),(10617937/16777216)],![(8687403/8388608),(8687403/8388608),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf103.bound
end G242

namespace G54
def box : ClosedBox 3 := ⟨![(16409539/16777216),(16409539/16777216),(4826335/8388608)],![(8687403/8388608),(8687403/8388608),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G55.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G242.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G55.bound) (by rw [eq_true]; exact G242.bound)
end G54

namespace G44
def box : ClosedBox 3 := ⟨![(16409539/16777216),(965267/1048576),(4826335/8388608)],![(8687403/8388608),(8687403/8388608),(2895801/4194304)]⟩
theorem eq_false : box.half 1 false=G45.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G54.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G45.bound) (by rw [eq_true]; exact G54.bound)
end G44

namespace G16
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(4826335/8388608)],![(8687403/8388608),(8687403/8388608),(2895801/4194304)]⟩
theorem eq_false : box.half 0 false=G17.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G44.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G17.bound) (by rw [eq_true]; exact G44.bound)
end G16

namespace G14
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(965267/2097152)],![(8687403/8388608),(8687403/8388608),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G15.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G16.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G15.bound) (by rw [eq_true]; exact G16.bound)
end G14

namespace G244
def box : ClosedBox 3 := ⟨![(965267/1048576),(8687403/8388608),(965267/2097152)],![(8687403/8388608),(4826335/4194304),(4826335/8388608)]⟩
theorem bound : BoxMajorant box := Leaf104.bound
end G244

namespace G251
def box : ClosedBox 3 := ⟨![(965267/1048576),(8687403/8388608),(4826335/8388608)],![(31853811/33554432),(35714879/33554432),(20270607/33554432)]⟩
theorem bound : BoxMajorant box := Leaf105.bound
end G251

namespace G252
def box : ClosedBox 3 := ⟨![(965267/1048576),(8687403/8388608),(20270607/33554432)],![(31853811/33554432),(35714879/33554432),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf106.bound
end G252

namespace G250
def box : ClosedBox 3 := ⟨![(965267/1048576),(8687403/8388608),(4826335/8388608)],![(31853811/33554432),(35714879/33554432),(10617937/16777216)]⟩
theorem eq_false : box.half 2 false=G251.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G252.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G251.bound) (by rw [eq_true]; exact G252.bound)
end G250

end MordellEight.CubicBoxes.B28
