import Eight.CubicBoxes.B28.C18
import Eight.CubicBoxes.B28.C19
import Eight.CubicBoxes.B28.C20
import Eight.CubicBoxes.B28.C21
import Eight.CubicBoxes.B28.C22
import Eight.CubicBoxes.B28.C23
import Eight.CubicBoxes.B28.C24
import Eight.CubicBoxes.B28.C25
import Eight.CubicBoxes.B28.C26
import Eight.CubicBoxes.B28.C27
import Eight.CubicBoxes.B28.C28
import Eight.CubicBoxes.B28.C29
import Eight.CubicBoxes.B28.C30
import Eight.CubicBoxes.B28.C31
import Eight.CubicBoxes.B28.C32
import Eight.CubicBoxes.B28.G00
import Eight.RootPartition
import Eight.LocalLeaf
namespace MordellEight.CubicBoxes.B28
open FixedTensor IntegerCube RationalCube Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace G85
def box : ClosedBox 3 := ⟨![(267378959/268435456),(134172113/134217728),(41506481/67108864)],![(134172113/134217728),(33784345/33554432),(83978229/134217728)]⟩
theorem eq_false : box.half 1 false=G86.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G101.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G86.bound) (by rw [eq_true]; exact G101.bound)
end G85

namespace G83
def box : ClosedBox 3 := ⟨![(66603423/67108864),(134172113/134217728),(41506481/67108864)],![(134172113/134217728),(33784345/33554432),(83978229/134217728)]⟩
theorem eq_false : box.half 0 false=G84.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G85.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G84.bound) (by rw [eq_true]; exact G85.bound)
end G83

namespace G102
def box : ClosedBox 3 := ⟨![(66603423/67108864),(134172113/134217728),(83978229/134217728)],![(134172113/134217728),(33784345/33554432),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf44.bound
end G102

namespace G82
def box : ClosedBox 3 := ⟨![(66603423/67108864),(134172113/134217728),(41506481/67108864)],![(134172113/134217728),(33784345/33554432),(10617937/16777216)]⟩
theorem eq_false : box.half 2 false=G83.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G102.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G83.bound) (by rw [eq_true]; exact G102.bound)
end G82

namespace G72
def box : ClosedBox 3 := ⟨![(66603423/67108864),(66603423/67108864),(41506481/67108864)],![(134172113/134217728),(33784345/33554432),(10617937/16777216)]⟩
theorem eq_false : box.half 1 false=G73.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G82.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G73.bound) (by rw [eq_true]; exact G82.bound)
end G72

namespace G107
def box : ClosedBox 3 := ⟨![(134172113/134217728),(66603423/67108864),(41506481/67108864)],![(269309493/268435456),(267378959/268435456),(83978229/134217728)]⟩
theorem checked : outsideCheck box=true := by decide +kernel
theorem bound : BoxMajorant box := by
  intro x hx hd
  exact (outsideCheck_sound box checked hx hd.1 hd.2).elim
end G107

namespace G109
def box : ClosedBox 3 := ⟨![(134172113/134217728),(267378959/268435456),(41506481/67108864)],![(269309493/268435456),(134172113/134217728),(166991191/268435456)]⟩
theorem bound : BoxMajorant box := Leaf45.bound
end G109

namespace G112
def box : ClosedBox 3 := ⟨![(134172113/134217728),(267378959/268435456),(166991191/268435456)],![(537653719/536870912),(535723185/536870912),(83978229/134217728)]⟩
theorem checked : outsideCheck box=true := by decide +kernel
theorem bound : BoxMajorant box := by
  intro x hx hd
  exact (outsideCheck_sound box checked hx hd.1 hd.2).elim
end G112

namespace G116
def box : ClosedBox 3 := ⟨![(134172113/134217728),(535723185/536870912),(166991191/268435456)],![(1074342171/1073741824),(1072411637/1073741824),(334947649/536870912)]⟩
theorem checked : outsideCheck box=true := by decide +kernel
theorem bound : BoxMajorant box := by
  intro x hx hd
  exact (outsideCheck_sound box checked hx hd.1 hd.2).elim
end G116

namespace G118
def box : ClosedBox 3 := ⟨![(134172113/134217728),(1072411637/1073741824),(166991191/268435456)],![(1074342171/1073741824),(134172113/134217728),(668930031/1073741824)]⟩
theorem bound : BoxMajorant box := Leaf46.bound
end G118

namespace G119
def box : ClosedBox 3 := ⟨![(134172113/134217728),(1072411637/1073741824),(668930031/1073741824)],![(1074342171/1073741824),(134172113/134217728),(334947649/536870912)]⟩
theorem bound : BoxMajorant box := Leaf47.bound
end G119

namespace G117
def box : ClosedBox 3 := ⟨![(134172113/134217728),(1072411637/1073741824),(166991191/268435456)],![(1074342171/1073741824),(134172113/134217728),(334947649/536870912)]⟩
theorem eq_false : box.half 2 false=G118.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G119.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G118.bound) (by rw [eq_true]; exact G119.bound)
end G117

namespace G115
def box : ClosedBox 3 := ⟨![(134172113/134217728),(535723185/536870912),(166991191/268435456)],![(1074342171/1073741824),(134172113/134217728),(334947649/536870912)]⟩
theorem eq_false : box.half 1 false=G116.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G117.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G116.bound) (by rw [eq_true]; exact G117.bound)
end G115

namespace G120
def box : ClosedBox 3 := ⟨![(1074342171/1073741824),(535723185/536870912),(166991191/268435456)],![(537653719/536870912),(134172113/134217728),(334947649/536870912)]⟩
theorem checked : outsideCheck box=true := by decide +kernel
theorem bound : BoxMajorant box := by
  intro x hx hd
  exact (outsideCheck_sound box checked hx hd.1 hd.2).elim
end G120

namespace G114
def box : ClosedBox 3 := ⟨![(134172113/134217728),(535723185/536870912),(166991191/268435456)],![(537653719/536870912),(134172113/134217728),(334947649/536870912)]⟩
theorem eq_false : box.half 0 false=G115.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G120.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G115.bound) (by rw [eq_true]; exact G120.bound)
end G114

namespace G121
def box : ClosedBox 3 := ⟨![(134172113/134217728),(535723185/536870912),(334947649/536870912)],![(537653719/536870912),(134172113/134217728),(83978229/134217728)]⟩
theorem bound : BoxMajorant box := Leaf48.bound
end G121

namespace G113
def box : ClosedBox 3 := ⟨![(134172113/134217728),(535723185/536870912),(166991191/268435456)],![(537653719/536870912),(134172113/134217728),(83978229/134217728)]⟩
theorem eq_false : box.half 2 false=G114.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G121.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G114.bound) (by rw [eq_true]; exact G121.bound)
end G113

namespace G111
def box : ClosedBox 3 := ⟨![(134172113/134217728),(267378959/268435456),(166991191/268435456)],![(537653719/536870912),(134172113/134217728),(83978229/134217728)]⟩
theorem eq_false : box.half 1 false=G112.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G113.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G112.bound) (by rw [eq_true]; exact G113.bound)
end G111

namespace G122
def box : ClosedBox 3 := ⟨![(537653719/536870912),(267378959/268435456),(166991191/268435456)],![(269309493/268435456),(134172113/134217728),(83978229/134217728)]⟩
theorem checked : outsideCheck box=true := by decide +kernel
theorem bound : BoxMajorant box := by
  intro x hx hd
  exact (outsideCheck_sound box checked hx hd.1 hd.2).elim
end G122

namespace G110
def box : ClosedBox 3 := ⟨![(134172113/134217728),(267378959/268435456),(166991191/268435456)],![(269309493/268435456),(134172113/134217728),(83978229/134217728)]⟩
theorem eq_false : box.half 0 false=G111.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G122.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G111.bound) (by rw [eq_true]; exact G122.bound)
end G110

namespace G108
def box : ClosedBox 3 := ⟨![(134172113/134217728),(267378959/268435456),(41506481/67108864)],![(269309493/268435456),(134172113/134217728),(83978229/134217728)]⟩
theorem eq_false : box.half 2 false=G109.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G110.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G109.bound) (by rw [eq_true]; exact G110.bound)
end G108

namespace G106
def box : ClosedBox 3 := ⟨![(134172113/134217728),(66603423/67108864),(41506481/67108864)],![(269309493/268435456),(134172113/134217728),(83978229/134217728)]⟩
theorem eq_false : box.half 1 false=G107.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G108.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G107.bound) (by rw [eq_true]; exact G108.bound)
end G106

namespace G123
def box : ClosedBox 3 := ⟨![(269309493/268435456),(66603423/67108864),(41506481/67108864)],![(33784345/33554432),(134172113/134217728),(83978229/134217728)]⟩
theorem checked : outsideCheck box=true := by decide +kernel
theorem bound : BoxMajorant box := by
  intro x hx hd
  exact (outsideCheck_sound box checked hx hd.1 hd.2).elim
end G123

namespace G105
def box : ClosedBox 3 := ⟨![(134172113/134217728),(66603423/67108864),(41506481/67108864)],![(33784345/33554432),(134172113/134217728),(83978229/134217728)]⟩
theorem eq_false : box.half 0 false=G106.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G123.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G106.bound) (by rw [eq_true]; exact G123.bound)
end G105

namespace G124
def box : ClosedBox 3 := ⟨![(134172113/134217728),(66603423/67108864),(83978229/134217728)],![(33784345/33554432),(134172113/134217728),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf49.bound
end G124

namespace G104
def box : ClosedBox 3 := ⟨![(134172113/134217728),(66603423/67108864),(41506481/67108864)],![(33784345/33554432),(134172113/134217728),(10617937/16777216)]⟩
theorem eq_false : box.half 2 false=G105.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G124.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G105.bound) (by rw [eq_true]; exact G124.bound)
end G104

namespace G129
def box : ClosedBox 3 := ⟨![(134172113/134217728),(134172113/134217728),(41506481/67108864)],![(269309493/268435456),(269309493/268435456),(166991191/268435456)]⟩
theorem bound : BoxMajorant box := Leaf50.bound
end G129

namespace G136
def box : ClosedBox 3 := ⟨![(134172113/134217728),(134172113/134217728),(166991191/268435456)],![(1074342171/1073741824),(1074342171/1073741824),(668930031/1073741824)]⟩
theorem bound : BoxMajorant box := Leaf51.bound
end G136

namespace G140
def box : ClosedBox 3 := ⟨![(134172113/134217728),(134172113/134217728),(668930031/1073741824)],![(2147719075/2147483648),(2147719075/2147483648),(1338825329/2147483648)]⟩
theorem bound : BoxMajorant box := Leaf52.bound
end G140

namespace G142
def box : ClosedBox 3 := ⟨![(134172113/134217728),(134172113/134217728),(1338825329/2147483648)],![(4294472883/4294967296),(2147719075/2147483648),(334947649/536870912)]⟩
theorem bound : BoxMajorant box := Leaf53.bound
end G142

namespace G144
def box : ClosedBox 3 := ⟨![(4294472883/4294967296),(134172113/134217728),(1338825329/2147483648)],![(2147719075/2147483648),(4294472883/4294967296),(334947649/536870912)]⟩
theorem bound : BoxMajorant box := Leaf54.bound
end G144

namespace G148
def box : ClosedBox 3 := ⟨![(4294472883/4294967296),(4294472883/4294967296),(1338825329/2147483648)],![(8589911033/8589934592),(8589911033/8589934592),(2678615925/4294967296)]⟩
theorem bound : BoxMajorant box := Leaf55.bound
end G148

namespace G151
def box : ClosedBox 3 := ⟨![(4294472883/4294967296),(8589911033/8589934592),(1338825329/2147483648)],![(17178856799/17179869184),(2147719075/2147483648),(5356266583/8589934592)]⟩
theorem bound : BoxMajorant box := Leaf56.bound
end G151

namespace G154
def box : ClosedBox 3 := ⟨![(17178856799/17179869184),(8589911033/8589934592),(1338825329/2147483648)],![(8589911033/8589934592),(17180787333/17179869184),(10711567899/17179869184)]⟩
theorem bound : BoxMajorant box := Leaf57.bound
end G154

namespace G155
def box : ClosedBox 3 := ⟨![(17178856799/17179869184),(8589911033/8589934592),(10711567899/17179869184)],![(8589911033/8589934592),(17180787333/17179869184),(5356266583/8589934592)]⟩
theorem bound : BoxMajorant box := Leaf58.bound
end G155

namespace G153
def box : ClosedBox 3 := ⟨![(17178856799/17179869184),(8589911033/8589934592),(1338825329/2147483648)],![(8589911033/8589934592),(17180787333/17179869184),(5356266583/8589934592)]⟩
theorem eq_false : box.half 2 false=G154.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G155.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G154.bound) (by rw [eq_true]; exact G155.bound)
end G153

namespace G156
def box : ClosedBox 3 := ⟨![(17178856799/17179869184),(17180787333/17179869184),(1338825329/2147483648)],![(8589911033/8589934592),(2147719075/2147483648),(5356266583/8589934592)]⟩
theorem bound : BoxMajorant box := Leaf59.bound
end G156

namespace G152
def box : ClosedBox 3 := ⟨![(17178856799/17179869184),(8589911033/8589934592),(1338825329/2147483648)],![(8589911033/8589934592),(2147719075/2147483648),(5356266583/8589934592)]⟩
theorem eq_false : box.half 1 false=G153.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G156.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G153.bound) (by rw [eq_true]; exact G156.bound)
end G152

namespace G150
def box : ClosedBox 3 := ⟨![(4294472883/4294967296),(8589911033/8589934592),(1338825329/2147483648)],![(8589911033/8589934592),(2147719075/2147483648),(5356266583/8589934592)]⟩
theorem eq_false : box.half 0 false=G151.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G152.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G151.bound) (by rw [eq_true]; exact G152.bound)
end G150

namespace G157
def box : ClosedBox 3 := ⟨![(4294472883/4294967296),(8589911033/8589934592),(5356266583/8589934592)],![(8589911033/8589934592),(2147719075/2147483648),(2678615925/4294967296)]⟩
theorem bound : BoxMajorant box := Leaf60.bound
end G157

namespace G149
def box : ClosedBox 3 := ⟨![(4294472883/4294967296),(8589911033/8589934592),(1338825329/2147483648)],![(8589911033/8589934592),(2147719075/2147483648),(2678615925/4294967296)]⟩
theorem eq_false : box.half 2 false=G150.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G157.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G150.bound) (by rw [eq_true]; exact G157.bound)
end G149

namespace G147
def box : ClosedBox 3 := ⟨![(4294472883/4294967296),(4294472883/4294967296),(1338825329/2147483648)],![(8589911033/8589934592),(2147719075/2147483648),(2678615925/4294967296)]⟩
theorem eq_false : box.half 1 false=G148.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G149.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G148.bound) (by rw [eq_true]; exact G149.bound)
end G147

namespace G162
def box : ClosedBox 3 := ⟨![(8589911033/8589934592),(4294472883/4294967296),(1338825329/2147483648)],![(17180787333/17179869184),(17178856799/17179869184),(5356266583/8589934592)]⟩
theorem checked : outsideCheck box=true := by decide +kernel
theorem bound : BoxMajorant box := by
  intro x hx hd
  exact (outsideCheck_sound box checked hx hd.1 hd.2).elim
end G162

namespace G164
def box : ClosedBox 3 := ⟨![(8589911033/8589934592),(17178856799/17179869184),(1338825329/2147483648)],![(17180787333/17179869184),(8589911033/8589934592),(10711567899/17179869184)]⟩
theorem bound : BoxMajorant box := Leaf61.bound
end G164

namespace G165
def box : ClosedBox 3 := ⟨![(8589911033/8589934592),(17178856799/17179869184),(10711567899/17179869184)],![(17180787333/17179869184),(8589911033/8589934592),(5356266583/8589934592)]⟩
theorem bound : BoxMajorant box := Leaf62.bound
end G165

namespace G163
def box : ClosedBox 3 := ⟨![(8589911033/8589934592),(17178856799/17179869184),(1338825329/2147483648)],![(17180787333/17179869184),(8589911033/8589934592),(5356266583/8589934592)]⟩
theorem eq_false : box.half 2 false=G164.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G165.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G164.bound) (by rw [eq_true]; exact G165.bound)
end G163

namespace G161
def box : ClosedBox 3 := ⟨![(8589911033/8589934592),(4294472883/4294967296),(1338825329/2147483648)],![(17180787333/17179869184),(8589911033/8589934592),(5356266583/8589934592)]⟩
theorem eq_false : box.half 1 false=G162.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G163.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G162.bound) (by rw [eq_true]; exact G163.bound)
end G161

namespace G166
def box : ClosedBox 3 := ⟨![(17180787333/17179869184),(4294472883/4294967296),(1338825329/2147483648)],![(2147719075/2147483648),(8589911033/8589934592),(5356266583/8589934592)]⟩
theorem checked : outsideCheck box=true := by decide +kernel
theorem bound : BoxMajorant box := by
  intro x hx hd
  exact (outsideCheck_sound box checked hx hd.1 hd.2).elim
end G166

namespace G160
def box : ClosedBox 3 := ⟨![(8589911033/8589934592),(4294472883/4294967296),(1338825329/2147483648)],![(2147719075/2147483648),(8589911033/8589934592),(5356266583/8589934592)]⟩
theorem eq_false : box.half 0 false=G161.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G166.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G161.bound) (by rw [eq_true]; exact G166.bound)
end G160

namespace G167
def box : ClosedBox 3 := ⟨![(8589911033/8589934592),(4294472883/4294967296),(5356266583/8589934592)],![(2147719075/2147483648),(8589911033/8589934592),(2678615925/4294967296)]⟩
theorem bound : BoxMajorant box := Leaf63.bound
end G167

namespace G159
def box : ClosedBox 3 := ⟨![(8589911033/8589934592),(4294472883/4294967296),(1338825329/2147483648)],![(2147719075/2147483648),(8589911033/8589934592),(2678615925/4294967296)]⟩
theorem eq_false : box.half 2 false=G160.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G167.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G160.bound) (by rw [eq_true]; exact G167.bound)
end G159

namespace G175
def box : ClosedBox 3 := ⟨![(8589911033/8589934592),(8589911033/8589934592),(1338825329/2147483648)],![(34360609399/34359738368),(34360609399/34359738368),(21422170531/34359738368)]⟩
theorem bound : BoxMajorant box := Leaf64.bound
end G175

namespace G179
def box : ClosedBox 3 := ⟨![(8589911033/8589934592),(8589911033/8589934592),(21422170531/34359738368)],![(68720253531/68719476736),(68720253531/68719476736),(42845306329/68719476736)]⟩
theorem bound : BoxMajorant box := Leaf65.bound
end G179

namespace G180
def box : ClosedBox 3 := ⟨![(8589911033/8589934592),(8589911033/8589934592),(42845306329/68719476736)],![(68720253531/68719476736),(68720253531/68719476736),(10711567899/17179869184)]⟩
theorem checked : localLeafCheck box 2=true := by decide +kernel
theorem bound : BoxMajorant box := by
  intro x hx hd
  exact localLeafCheck_sound box 2 checked hx hd.1
end G180

namespace G178
def box : ClosedBox 3 := ⟨![(8589911033/8589934592),(8589911033/8589934592),(21422170531/34359738368)],![(68720253531/68719476736),(68720253531/68719476736),(10711567899/17179869184)]⟩
theorem eq_false : box.half 2 false=G179.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G180.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G179.bound) (by rw [eq_true]; exact G180.bound)
end G178

namespace G181
def box : ClosedBox 3 := ⟨![(8589911033/8589934592),(68720253531/68719476736),(21422170531/34359738368)],![(68720253531/68719476736),(34360609399/34359738368),(10711567899/17179869184)]⟩
theorem bound : BoxMajorant box := Leaf66.bound
end G181

namespace G177
def box : ClosedBox 3 := ⟨![(8589911033/8589934592),(8589911033/8589934592),(21422170531/34359738368)],![(68720253531/68719476736),(34360609399/34359738368),(10711567899/17179869184)]⟩
theorem eq_false : box.half 1 false=G178.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G181.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G178.bound) (by rw [eq_true]; exact G181.bound)
end G177

namespace G182
def box : ClosedBox 3 := ⟨![(68720253531/68719476736),(8589911033/8589934592),(21422170531/34359738368)],![(34360609399/34359738368),(34360609399/34359738368),(10711567899/17179869184)]⟩
theorem bound : BoxMajorant box := Leaf67.bound
end G182

namespace G176
def box : ClosedBox 3 := ⟨![(8589911033/8589934592),(8589911033/8589934592),(21422170531/34359738368)],![(34360609399/34359738368),(34360609399/34359738368),(10711567899/17179869184)]⟩
theorem eq_false : box.half 0 false=G177.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G182.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G177.bound) (by rw [eq_true]; exact G182.bound)
end G176

namespace G174
def box : ClosedBox 3 := ⟨![(8589911033/8589934592),(8589911033/8589934592),(1338825329/2147483648)],![(34360609399/34359738368),(34360609399/34359738368),(10711567899/17179869184)]⟩
theorem eq_false : box.half 2 false=G175.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G176.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G175.bound) (by rw [eq_true]; exact G176.bound)
end G174

namespace G183
def box : ClosedBox 3 := ⟨![(8589911033/8589934592),(34360609399/34359738368),(1338825329/2147483648)],![(34360609399/34359738368),(17180787333/17179869184),(10711567899/17179869184)]⟩
theorem bound : BoxMajorant box := Leaf68.bound
end G183

namespace G173
def box : ClosedBox 3 := ⟨![(8589911033/8589934592),(8589911033/8589934592),(1338825329/2147483648)],![(34360609399/34359738368),(17180787333/17179869184),(10711567899/17179869184)]⟩
theorem eq_false : box.half 1 false=G174.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G183.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G174.bound) (by rw [eq_true]; exact G183.bound)
end G173

namespace G184
def box : ClosedBox 3 := ⟨![(34360609399/34359738368),(8589911033/8589934592),(1338825329/2147483648)],![(17180787333/17179869184),(17180787333/17179869184),(10711567899/17179869184)]⟩
theorem bound : BoxMajorant box := Leaf69.bound
end G184

namespace G172
def box : ClosedBox 3 := ⟨![(8589911033/8589934592),(8589911033/8589934592),(1338825329/2147483648)],![(17180787333/17179869184),(17180787333/17179869184),(10711567899/17179869184)]⟩
theorem eq_false : box.half 0 false=G173.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G184.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G173.bound) (by rw [eq_true]; exact G184.bound)
end G172

namespace G185
def box : ClosedBox 3 := ⟨![(8589911033/8589934592),(8589911033/8589934592),(10711567899/17179869184)],![(17180787333/17179869184),(17180787333/17179869184),(5356266583/8589934592)]⟩
theorem bound : BoxMajorant box := Leaf70.bound
end G185

namespace G171
def box : ClosedBox 3 := ⟨![(8589911033/8589934592),(8589911033/8589934592),(1338825329/2147483648)],![(17180787333/17179869184),(17180787333/17179869184),(5356266583/8589934592)]⟩
theorem eq_false : box.half 2 false=G172.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G185.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G172.bound) (by rw [eq_true]; exact G185.bound)
end G171

namespace G186
def box : ClosedBox 3 := ⟨![(8589911033/8589934592),(17180787333/17179869184),(1338825329/2147483648)],![(17180787333/17179869184),(2147719075/2147483648),(5356266583/8589934592)]⟩
theorem bound : BoxMajorant box := Leaf71.bound
end G186

namespace G170
def box : ClosedBox 3 := ⟨![(8589911033/8589934592),(8589911033/8589934592),(1338825329/2147483648)],![(17180787333/17179869184),(2147719075/2147483648),(5356266583/8589934592)]⟩
theorem eq_false : box.half 1 false=G171.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G186.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G171.bound) (by rw [eq_true]; exact G186.bound)
end G170

namespace G187
def box : ClosedBox 3 := ⟨![(17180787333/17179869184),(8589911033/8589934592),(1338825329/2147483648)],![(2147719075/2147483648),(2147719075/2147483648),(5356266583/8589934592)]⟩
theorem bound : BoxMajorant box := Leaf72.bound
end G187

namespace G169
def box : ClosedBox 3 := ⟨![(8589911033/8589934592),(8589911033/8589934592),(1338825329/2147483648)],![(2147719075/2147483648),(2147719075/2147483648),(5356266583/8589934592)]⟩
theorem eq_false : box.half 0 false=G170.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G187.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G170.bound) (by rw [eq_true]; exact G187.bound)
end G169

namespace G188
def box : ClosedBox 3 := ⟨![(8589911033/8589934592),(8589911033/8589934592),(5356266583/8589934592)],![(2147719075/2147483648),(2147719075/2147483648),(2678615925/4294967296)]⟩
theorem bound : BoxMajorant box := Leaf73.bound
end G188

namespace G168
def box : ClosedBox 3 := ⟨![(8589911033/8589934592),(8589911033/8589934592),(1338825329/2147483648)],![(2147719075/2147483648),(2147719075/2147483648),(2678615925/4294967296)]⟩
theorem eq_false : box.half 2 false=G169.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G188.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G169.bound) (by rw [eq_true]; exact G188.bound)
end G168

namespace G158
def box : ClosedBox 3 := ⟨![(8589911033/8589934592),(4294472883/4294967296),(1338825329/2147483648)],![(2147719075/2147483648),(2147719075/2147483648),(2678615925/4294967296)]⟩
theorem eq_false : box.half 1 false=G159.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G168.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G159.bound) (by rw [eq_true]; exact G168.bound)
end G158

namespace G146
def box : ClosedBox 3 := ⟨![(4294472883/4294967296),(4294472883/4294967296),(1338825329/2147483648)],![(2147719075/2147483648),(2147719075/2147483648),(2678615925/4294967296)]⟩
theorem eq_false : box.half 0 false=G147.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G158.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G147.bound) (by rw [eq_true]; exact G158.bound)
end G146

namespace G189
def box : ClosedBox 3 := ⟨![(4294472883/4294967296),(4294472883/4294967296),(2678615925/4294967296)],![(2147719075/2147483648),(2147719075/2147483648),(334947649/536870912)]⟩
theorem bound : BoxMajorant box := Leaf74.bound
end G189

namespace G145
def box : ClosedBox 3 := ⟨![(4294472883/4294967296),(4294472883/4294967296),(1338825329/2147483648)],![(2147719075/2147483648),(2147719075/2147483648),(334947649/536870912)]⟩
theorem eq_false : box.half 2 false=G146.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G189.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G146.bound) (by rw [eq_true]; exact G189.bound)
end G145

namespace G143
def box : ClosedBox 3 := ⟨![(4294472883/4294967296),(134172113/134217728),(1338825329/2147483648)],![(2147719075/2147483648),(2147719075/2147483648),(334947649/536870912)]⟩
theorem eq_false : box.half 1 false=G144.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G145.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G144.bound) (by rw [eq_true]; exact G145.bound)
end G143

namespace G141
def box : ClosedBox 3 := ⟨![(134172113/134217728),(134172113/134217728),(1338825329/2147483648)],![(2147719075/2147483648),(2147719075/2147483648),(334947649/536870912)]⟩
theorem eq_false : box.half 0 false=G142.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G143.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G142.bound) (by rw [eq_true]; exact G143.bound)
end G141

namespace G139
def box : ClosedBox 3 := ⟨![(134172113/134217728),(134172113/134217728),(668930031/1073741824)],![(2147719075/2147483648),(2147719075/2147483648),(334947649/536870912)]⟩
theorem eq_false : box.half 2 false=G140.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G141.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G140.bound) (by rw [eq_true]; exact G141.bound)
end G139

namespace G191
def box : ClosedBox 3 := ⟨![(134172113/134217728),(2147719075/2147483648),(668930031/1073741824)],![(2147719075/2147483648),(1074342171/1073741824),(1338825329/2147483648)]⟩
theorem bound : BoxMajorant box := Leaf75.bound
end G191

end MordellEight.CubicBoxes.B28
