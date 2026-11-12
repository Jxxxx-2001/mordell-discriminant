import Eight.CubicBoxes.B6.C01
import Eight.CubicBoxes.B6.C02
import Eight.CubicBoxes.B6.C03
import Eight.CubicBoxes.B6.C04
import Eight.CubicBoxes.B6.C05
import Eight.CubicBoxes.B6.C06
import Eight.CubicBoxes.B6.C07
import Eight.CubicBoxes.B6.C08
import Eight.CubicBoxes.B6.C09
import Eight.CubicBoxes.B6.C10
import Eight.CubicBoxes.B6.C11
import Eight.CubicBoxes.B6.C12
import Eight.CubicBoxes.B6.C13
import Eight.CubicBoxes.B6.C14
import Eight.CubicBoxes.B6.C15
import Eight.RootPartition
import Eight.LocalLeaf
namespace MordellEight.CubicBoxes.B6
open FixedTensor IntegerCube RationalCube Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace G4
def box : ClosedBox 3 := ⟨![0,(965267/1048576),(-965267/1048576)],![(965267/4194304),(2895801/2097152),(-2895801/4194304)]⟩
theorem checked : outsideCheck box=true := by decide +kernel
theorem bound : BoxMajorant box := by
  intro x hx hd
  exact (outsideCheck_sound box checked hx hd.1 hd.2).elim
end G4

namespace G5
def box : ClosedBox 3 := ⟨![0,(965267/1048576),(-2895801/4194304)],![(965267/4194304),(2895801/2097152),(-965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf0.bound
end G5

namespace G3
def box : ClosedBox 3 := ⟨![0,(965267/1048576),(-965267/1048576)],![(965267/4194304),(2895801/2097152),(-965267/2097152)]⟩
theorem eq_false : box.half 2 false=G4.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G5.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G4.bound) (by rw [eq_true]; exact G5.bound)
end G3

namespace G8
def box : ClosedBox 3 := ⟨![(965267/4194304),(965267/1048576),(-965267/1048576)],![(965267/2097152),(4826335/4194304),(-2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf1.bound
end G8

namespace G9
def box : ClosedBox 3 := ⟨![(965267/4194304),(965267/1048576),(-2895801/4194304)],![(965267/2097152),(4826335/4194304),(-965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf2.bound
end G9

namespace G7
def box : ClosedBox 3 := ⟨![(965267/4194304),(965267/1048576),(-965267/1048576)],![(965267/2097152),(4826335/4194304),(-965267/2097152)]⟩
theorem eq_false : box.half 2 false=G8.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G9.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G8.bound) (by rw [eq_true]; exact G9.bound)
end G7

namespace G10
def box : ClosedBox 3 := ⟨![(965267/4194304),(4826335/4194304),(-965267/1048576)],![(965267/2097152),(2895801/2097152),(-965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf3.bound
end G10

namespace G6
def box : ClosedBox 3 := ⟨![(965267/4194304),(965267/1048576),(-965267/1048576)],![(965267/2097152),(2895801/2097152),(-965267/2097152)]⟩
theorem eq_false : box.half 1 false=G7.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G10.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G7.bound) (by rw [eq_true]; exact G10.bound)
end G6

namespace G2
def box : ClosedBox 3 := ⟨![0,(965267/1048576),(-965267/1048576)],![(965267/2097152),(2895801/2097152),(-965267/2097152)]⟩
theorem eq_false : box.half 0 false=G3.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G6.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G3.bound) (by rw [eq_true]; exact G6.bound)
end G2

namespace G14
def box : ClosedBox 3 := ⟨![0,(965267/1048576),(-965267/2097152)],![(965267/4194304),(4826335/4194304),(-965267/4194304)]⟩
theorem bound : BoxMajorant box := Leaf4.bound
end G14

namespace G18
def box : ClosedBox 3 := ⟨![0,(965267/1048576),(-965267/4194304)],![(965267/8388608),(8687403/8388608),(-965267/8388608)]⟩
theorem bound : BoxMajorant box := Leaf5.bound
end G18

namespace G21
def box : ClosedBox 3 := ⟨![0,(965267/1048576),(-965267/8388608)],![(965267/16777216),(16409539/16777216),0]⟩
theorem bound : BoxMajorant box := Leaf6.bound
end G21

namespace G23
def box : ClosedBox 3 := ⟨![0,(16409539/16777216),(-965267/8388608)],![(965267/16777216),(8687403/8388608),(-965267/16777216)]⟩
theorem bound : BoxMajorant box := Leaf7.bound
end G23

namespace G27
def box : ClosedBox 3 := ⟨![0,(16409539/16777216),(-965267/16777216)],![(965267/33554432),(33784345/33554432),(-965267/33554432)]⟩
theorem bound : BoxMajorant box := Leaf8.bound
end G27

namespace G30
def box : ClosedBox 3 := ⟨![0,(16409539/16777216),(-965267/33554432)],![(965267/67108864),(66603423/67108864),0]⟩
theorem bound : BoxMajorant box := Leaf9.bound
end G30

namespace G32
def box : ClosedBox 3 := ⟨![0,(66603423/67108864),(-965267/33554432)],![(965267/67108864),(33784345/33554432),(-965267/67108864)]⟩
theorem bound : BoxMajorant box := Leaf10.bound
end G32

namespace G35
def box : ClosedBox 3 := ⟨![0,(66603423/67108864),(-965267/67108864)],![(965267/134217728),(134172113/134217728),0]⟩
theorem bound : BoxMajorant box := Leaf11.bound
end G35

namespace G37
def box : ClosedBox 3 := ⟨![0,(134172113/134217728),(-965267/67108864)],![(965267/134217728),(33784345/33554432),(-965267/134217728)]⟩
theorem bound : BoxMajorant box := Leaf12.bound
end G37

namespace G41
def box : ClosedBox 3 := ⟨![0,(134172113/134217728),(-965267/134217728)],![(965267/268435456),(269309493/268435456),(-965267/268435456)]⟩
theorem bound : BoxMajorant box := Leaf13.bound
end G41

namespace G45
def box : ClosedBox 3 := ⟨![0,(134172113/134217728),(-965267/268435456)],![(965267/536870912),(537653719/536870912),(-965267/536870912)]⟩
theorem bound : BoxMajorant box := Leaf14.bound
end G45

namespace G49
def box : ClosedBox 3 := ⟨![0,(134172113/134217728),(-965267/536870912)],![(965267/1073741824),(1074342171/1073741824),(-965267/1073741824)]⟩
theorem bound : BoxMajorant box := Leaf15.bound
end G49

namespace G53
def box : ClosedBox 3 := ⟨![0,(134172113/134217728),(-965267/1073741824)],![(965267/2147483648),(2147719075/2147483648),(-965267/2147483648)]⟩
theorem bound : BoxMajorant box := Leaf16.bound
end G53

namespace G56
def box : ClosedBox 3 := ⟨![0,(134172113/134217728),(-965267/2147483648)],![(965267/4294967296),(4294472883/4294967296),0]⟩
theorem bound : BoxMajorant box := Leaf17.bound
end G56

namespace G58
def box : ClosedBox 3 := ⟨![0,(4294472883/4294967296),(-965267/2147483648)],![(965267/4294967296),(2147719075/2147483648),(-965267/4294967296)]⟩
theorem bound : BoxMajorant box := Leaf18.bound
end G58

namespace G59
def box : ClosedBox 3 := ⟨![0,(4294472883/4294967296),(-965267/4294967296)],![(965267/4294967296),(2147719075/2147483648),0]⟩
theorem checked : localLeafCheck box 0=true := by decide +kernel
theorem bound : BoxMajorant box := by
  intro x hx hd
  exact localLeafCheck_sound box 0 checked hx hd.1
end G59

namespace G57
def box : ClosedBox 3 := ⟨![0,(4294472883/4294967296),(-965267/2147483648)],![(965267/4294967296),(2147719075/2147483648),0]⟩
theorem eq_false : box.half 2 false=G58.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G59.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G58.bound) (by rw [eq_true]; exact G59.bound)
end G57

namespace G55
def box : ClosedBox 3 := ⟨![0,(134172113/134217728),(-965267/2147483648)],![(965267/4294967296),(2147719075/2147483648),0]⟩
theorem eq_false : box.half 1 false=G56.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G57.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G56.bound) (by rw [eq_true]; exact G57.bound)
end G55

namespace G60
def box : ClosedBox 3 := ⟨![(965267/4294967296),(134172113/134217728),(-965267/2147483648)],![(965267/2147483648),(2147719075/2147483648),0]⟩
theorem bound : BoxMajorant box := Leaf19.bound
end G60

namespace G54
def box : ClosedBox 3 := ⟨![0,(134172113/134217728),(-965267/2147483648)],![(965267/2147483648),(2147719075/2147483648),0]⟩
theorem eq_false : box.half 0 false=G55.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G60.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G55.bound) (by rw [eq_true]; exact G60.bound)
end G54

namespace G52
def box : ClosedBox 3 := ⟨![0,(134172113/134217728),(-965267/1073741824)],![(965267/2147483648),(2147719075/2147483648),0]⟩
theorem eq_false : box.half 2 false=G53.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G54.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G53.bound) (by rw [eq_true]; exact G54.bound)
end G52

namespace G61
def box : ClosedBox 3 := ⟨![0,(2147719075/2147483648),(-965267/1073741824)],![(965267/2147483648),(1074342171/1073741824),0]⟩
theorem bound : BoxMajorant box := Leaf20.bound
end G61

namespace G51
def box : ClosedBox 3 := ⟨![0,(134172113/134217728),(-965267/1073741824)],![(965267/2147483648),(1074342171/1073741824),0]⟩
theorem eq_false : box.half 1 false=G52.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G61.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G52.bound) (by rw [eq_true]; exact G61.bound)
end G51

namespace G62
def box : ClosedBox 3 := ⟨![(965267/2147483648),(134172113/134217728),(-965267/1073741824)],![(965267/1073741824),(1074342171/1073741824),0]⟩
theorem bound : BoxMajorant box := Leaf21.bound
end G62

namespace G50
def box : ClosedBox 3 := ⟨![0,(134172113/134217728),(-965267/1073741824)],![(965267/1073741824),(1074342171/1073741824),0]⟩
theorem eq_false : box.half 0 false=G51.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G62.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G51.bound) (by rw [eq_true]; exact G62.bound)
end G50

namespace G48
def box : ClosedBox 3 := ⟨![0,(134172113/134217728),(-965267/536870912)],![(965267/1073741824),(1074342171/1073741824),0]⟩
theorem eq_false : box.half 2 false=G49.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G50.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G49.bound) (by rw [eq_true]; exact G50.bound)
end G48

namespace G63
def box : ClosedBox 3 := ⟨![0,(1074342171/1073741824),(-965267/536870912)],![(965267/1073741824),(537653719/536870912),0]⟩
theorem bound : BoxMajorant box := Leaf22.bound
end G63

namespace G47
def box : ClosedBox 3 := ⟨![0,(134172113/134217728),(-965267/536870912)],![(965267/1073741824),(537653719/536870912),0]⟩
theorem eq_false : box.half 1 false=G48.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G63.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G48.bound) (by rw [eq_true]; exact G63.bound)
end G47

namespace G64
def box : ClosedBox 3 := ⟨![(965267/1073741824),(134172113/134217728),(-965267/536870912)],![(965267/536870912),(537653719/536870912),0]⟩
theorem bound : BoxMajorant box := Leaf23.bound
end G64

namespace G46
def box : ClosedBox 3 := ⟨![0,(134172113/134217728),(-965267/536870912)],![(965267/536870912),(537653719/536870912),0]⟩
theorem eq_false : box.half 0 false=G47.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G64.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G47.bound) (by rw [eq_true]; exact G64.bound)
end G46

namespace G44
def box : ClosedBox 3 := ⟨![0,(134172113/134217728),(-965267/268435456)],![(965267/536870912),(537653719/536870912),0]⟩
theorem eq_false : box.half 2 false=G45.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G46.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G45.bound) (by rw [eq_true]; exact G46.bound)
end G44

namespace G65
def box : ClosedBox 3 := ⟨![0,(537653719/536870912),(-965267/268435456)],![(965267/536870912),(269309493/268435456),0]⟩
theorem bound : BoxMajorant box := Leaf24.bound
end G65

namespace G43
def box : ClosedBox 3 := ⟨![0,(134172113/134217728),(-965267/268435456)],![(965267/536870912),(269309493/268435456),0]⟩
theorem eq_false : box.half 1 false=G44.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G65.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G44.bound) (by rw [eq_true]; exact G65.bound)
end G43

namespace G66
def box : ClosedBox 3 := ⟨![(965267/536870912),(134172113/134217728),(-965267/268435456)],![(965267/268435456),(269309493/268435456),0]⟩
theorem bound : BoxMajorant box := Leaf25.bound
end G66

namespace G42
def box : ClosedBox 3 := ⟨![0,(134172113/134217728),(-965267/268435456)],![(965267/268435456),(269309493/268435456),0]⟩
theorem eq_false : box.half 0 false=G43.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G66.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G43.bound) (by rw [eq_true]; exact G66.bound)
end G42

namespace G40
def box : ClosedBox 3 := ⟨![0,(134172113/134217728),(-965267/134217728)],![(965267/268435456),(269309493/268435456),0]⟩
theorem eq_false : box.half 2 false=G41.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G42.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G41.bound) (by rw [eq_true]; exact G42.bound)
end G40

namespace G67
def box : ClosedBox 3 := ⟨![0,(269309493/268435456),(-965267/134217728)],![(965267/268435456),(33784345/33554432),0]⟩
theorem bound : BoxMajorant box := Leaf26.bound
end G67

namespace G39
def box : ClosedBox 3 := ⟨![0,(134172113/134217728),(-965267/134217728)],![(965267/268435456),(33784345/33554432),0]⟩
theorem eq_false : box.half 1 false=G40.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G67.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G40.bound) (by rw [eq_true]; exact G67.bound)
end G39

namespace G68
def box : ClosedBox 3 := ⟨![(965267/268435456),(134172113/134217728),(-965267/134217728)],![(965267/134217728),(33784345/33554432),0]⟩
theorem bound : BoxMajorant box := Leaf27.bound
end G68

namespace G38
def box : ClosedBox 3 := ⟨![0,(134172113/134217728),(-965267/134217728)],![(965267/134217728),(33784345/33554432),0]⟩
theorem eq_false : box.half 0 false=G39.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G68.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G39.bound) (by rw [eq_true]; exact G68.bound)
end G38

namespace G36
def box : ClosedBox 3 := ⟨![0,(134172113/134217728),(-965267/67108864)],![(965267/134217728),(33784345/33554432),0]⟩
theorem eq_false : box.half 2 false=G37.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G38.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G37.bound) (by rw [eq_true]; exact G38.bound)
end G36

namespace G34
def box : ClosedBox 3 := ⟨![0,(66603423/67108864),(-965267/67108864)],![(965267/134217728),(33784345/33554432),0]⟩
theorem eq_false : box.half 1 false=G35.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G36.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G35.bound) (by rw [eq_true]; exact G36.bound)
end G34

namespace G69
def box : ClosedBox 3 := ⟨![(965267/134217728),(66603423/67108864),(-965267/67108864)],![(965267/67108864),(33784345/33554432),0]⟩
theorem bound : BoxMajorant box := Leaf28.bound
end G69

namespace G33
def box : ClosedBox 3 := ⟨![0,(66603423/67108864),(-965267/67108864)],![(965267/67108864),(33784345/33554432),0]⟩
theorem eq_false : box.half 0 false=G34.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G69.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G34.bound) (by rw [eq_true]; exact G69.bound)
end G33

namespace G31
def box : ClosedBox 3 := ⟨![0,(66603423/67108864),(-965267/33554432)],![(965267/67108864),(33784345/33554432),0]⟩
theorem eq_false : box.half 2 false=G32.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G33.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G32.bound) (by rw [eq_true]; exact G33.bound)
end G31

namespace G29
def box : ClosedBox 3 := ⟨![0,(16409539/16777216),(-965267/33554432)],![(965267/67108864),(33784345/33554432),0]⟩
theorem eq_false : box.half 1 false=G30.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G31.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G30.bound) (by rw [eq_true]; exact G31.bound)
end G29

namespace G70
def box : ClosedBox 3 := ⟨![(965267/67108864),(16409539/16777216),(-965267/33554432)],![(965267/33554432),(33784345/33554432),0]⟩
theorem bound : BoxMajorant box := Leaf29.bound
end G70

namespace G28
def box : ClosedBox 3 := ⟨![0,(16409539/16777216),(-965267/33554432)],![(965267/33554432),(33784345/33554432),0]⟩
theorem eq_false : box.half 0 false=G29.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G70.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G29.bound) (by rw [eq_true]; exact G70.bound)
end G28

namespace G26
def box : ClosedBox 3 := ⟨![0,(16409539/16777216),(-965267/16777216)],![(965267/33554432),(33784345/33554432),0]⟩
theorem eq_false : box.half 2 false=G27.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G28.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G27.bound) (by rw [eq_true]; exact G28.bound)
end G26

namespace G71
def box : ClosedBox 3 := ⟨![0,(33784345/33554432),(-965267/16777216)],![(965267/33554432),(8687403/8388608),0]⟩
theorem bound : BoxMajorant box := Leaf30.bound
end G71

namespace G25
def box : ClosedBox 3 := ⟨![0,(16409539/16777216),(-965267/16777216)],![(965267/33554432),(8687403/8388608),0]⟩
theorem eq_false : box.half 1 false=G26.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G71.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G26.bound) (by rw [eq_true]; exact G71.bound)
end G25

namespace G72
def box : ClosedBox 3 := ⟨![(965267/33554432),(16409539/16777216),(-965267/16777216)],![(965267/16777216),(8687403/8388608),0]⟩
theorem bound : BoxMajorant box := Leaf31.bound
end G72

namespace G24
def box : ClosedBox 3 := ⟨![0,(16409539/16777216),(-965267/16777216)],![(965267/16777216),(8687403/8388608),0]⟩
theorem eq_false : box.half 0 false=G25.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G72.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G25.bound) (by rw [eq_true]; exact G72.bound)
end G24

namespace G22
def box : ClosedBox 3 := ⟨![0,(16409539/16777216),(-965267/8388608)],![(965267/16777216),(8687403/8388608),0]⟩
theorem eq_false : box.half 2 false=G23.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G24.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G23.bound) (by rw [eq_true]; exact G24.bound)
end G22

namespace G20
def box : ClosedBox 3 := ⟨![0,(965267/1048576),(-965267/8388608)],![(965267/16777216),(8687403/8388608),0]⟩
theorem eq_false : box.half 1 false=G21.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G22.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G21.bound) (by rw [eq_true]; exact G22.bound)
end G20

namespace G73
def box : ClosedBox 3 := ⟨![(965267/16777216),(965267/1048576),(-965267/8388608)],![(965267/8388608),(8687403/8388608),0]⟩
theorem bound : BoxMajorant box := Leaf32.bound
end G73

namespace G19
def box : ClosedBox 3 := ⟨![0,(965267/1048576),(-965267/8388608)],![(965267/8388608),(8687403/8388608),0]⟩
theorem eq_false : box.half 0 false=G20.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G73.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G20.bound) (by rw [eq_true]; exact G73.bound)
end G19

namespace G17
def box : ClosedBox 3 := ⟨![0,(965267/1048576),(-965267/4194304)],![(965267/8388608),(8687403/8388608),0]⟩
theorem eq_false : box.half 2 false=G18.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G19.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G18.bound) (by rw [eq_true]; exact G19.bound)
end G17

namespace G74
def box : ClosedBox 3 := ⟨![0,(8687403/8388608),(-965267/4194304)],![(965267/8388608),(4826335/4194304),0]⟩
theorem bound : BoxMajorant box := Leaf33.bound
end G74

namespace G16
def box : ClosedBox 3 := ⟨![0,(965267/1048576),(-965267/4194304)],![(965267/8388608),(4826335/4194304),0]⟩
theorem eq_false : box.half 1 false=G17.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G74.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G17.bound) (by rw [eq_true]; exact G74.bound)
end G16

namespace G75
def box : ClosedBox 3 := ⟨![(965267/8388608),(965267/1048576),(-965267/4194304)],![(965267/4194304),(4826335/4194304),0]⟩
theorem bound : BoxMajorant box := Leaf34.bound
end G75

namespace G15
def box : ClosedBox 3 := ⟨![0,(965267/1048576),(-965267/4194304)],![(965267/4194304),(4826335/4194304),0]⟩
theorem eq_false : box.half 0 false=G16.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G75.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G16.bound) (by rw [eq_true]; exact G75.bound)
end G15

namespace G13
def box : ClosedBox 3 := ⟨![0,(965267/1048576),(-965267/2097152)],![(965267/4194304),(4826335/4194304),0]⟩
theorem eq_false : box.half 2 false=G14.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G15.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G14.bound) (by rw [eq_true]; exact G15.bound)
end G13

namespace G76
def box : ClosedBox 3 := ⟨![0,(4826335/4194304),(-965267/2097152)],![(965267/4194304),(2895801/2097152),0]⟩
theorem bound : BoxMajorant box := Leaf35.bound
end G76

namespace G12
def box : ClosedBox 3 := ⟨![0,(965267/1048576),(-965267/2097152)],![(965267/4194304),(2895801/2097152),0]⟩
theorem eq_false : box.half 1 false=G13.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G76.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G13.bound) (by rw [eq_true]; exact G76.bound)
end G12

namespace G78
def box : ClosedBox 3 := ⟨![(965267/4194304),(965267/1048576),(-965267/2097152)],![(965267/2097152),(2895801/2097152),(-965267/4194304)]⟩
theorem bound : BoxMajorant box := Leaf36.bound
end G78

namespace G79
def box : ClosedBox 3 := ⟨![(965267/4194304),(965267/1048576),(-965267/4194304)],![(965267/2097152),(2895801/2097152),0]⟩
theorem bound : BoxMajorant box := Leaf37.bound
end G79

namespace G77
def box : ClosedBox 3 := ⟨![(965267/4194304),(965267/1048576),(-965267/2097152)],![(965267/2097152),(2895801/2097152),0]⟩
theorem eq_false : box.half 2 false=G78.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G79.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G78.bound) (by rw [eq_true]; exact G79.bound)
end G77

namespace G11
def box : ClosedBox 3 := ⟨![0,(965267/1048576),(-965267/2097152)],![(965267/2097152),(2895801/2097152),0]⟩
theorem eq_false : box.half 0 false=G12.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G77.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G12.bound) (by rw [eq_true]; exact G77.bound)
end G11

namespace G1
def box : ClosedBox 3 := ⟨![0,(965267/1048576),(-965267/1048576)],![(965267/2097152),(2895801/2097152),0]⟩
theorem eq_false : box.half 2 false=G2.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G11.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G2.bound) (by rw [eq_true]; exact G11.bound)
end G1

namespace G83
def box : ClosedBox 3 := ⟨![0,(2895801/2097152),(-965267/1048576)],![(965267/4194304),(6756869/4194304),(-965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf38.bound
end G83

end MordellEight.CubicBoxes.B6
