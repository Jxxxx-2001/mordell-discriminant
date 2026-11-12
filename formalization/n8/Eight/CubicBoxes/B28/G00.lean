import Eight.CubicBoxes.B28.C01
import Eight.CubicBoxes.B28.C02
import Eight.CubicBoxes.B28.C03
import Eight.CubicBoxes.B28.C04
import Eight.CubicBoxes.B28.C05
import Eight.CubicBoxes.B28.C06
import Eight.CubicBoxes.B28.C07
import Eight.CubicBoxes.B28.C08
import Eight.CubicBoxes.B28.C09
import Eight.CubicBoxes.B28.C10
import Eight.CubicBoxes.B28.C11
import Eight.CubicBoxes.B28.C12
import Eight.CubicBoxes.B28.C13
import Eight.CubicBoxes.B28.C14
import Eight.CubicBoxes.B28.C15
import Eight.CubicBoxes.B28.C16
import Eight.CubicBoxes.B28.C17
import Eight.CubicBoxes.B28.C18
import Eight.RootPartition
import Eight.LocalLeaf
namespace MordellEight.CubicBoxes.B28
open FixedTensor IntegerCube RationalCube Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace G5
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),0],![(4826335/4194304),(4826335/4194304),(965267/4194304)]⟩
theorem bound : BoxMajorant box := Leaf0.bound
end G5

namespace G6
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(965267/4194304)],![(4826335/4194304),(4826335/4194304),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf1.bound
end G6

namespace G4
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),0],![(4826335/4194304),(4826335/4194304),(965267/2097152)]⟩
theorem eq_false : box.half 2 false=G5.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G6.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G5.bound) (by rw [eq_true]; exact G6.bound)
end G4

namespace G7
def box : ClosedBox 3 := ⟨![(965267/1048576),(4826335/4194304),0],![(4826335/4194304),(2895801/2097152),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf2.bound
end G7

namespace G3
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),0],![(4826335/4194304),(2895801/2097152),(965267/2097152)]⟩
theorem eq_false : box.half 1 false=G4.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G7.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G4.bound) (by rw [eq_true]; exact G7.bound)
end G3

namespace G8
def box : ClosedBox 3 := ⟨![(4826335/4194304),(965267/1048576),0],![(2895801/2097152),(2895801/2097152),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf3.bound
end G8

namespace G2
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),0],![(2895801/2097152),(2895801/2097152),(965267/2097152)]⟩
theorem eq_false : box.half 0 false=G3.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G8.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G3.bound) (by rw [eq_true]; exact G8.bound)
end G2

namespace G15
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(965267/2097152)],![(8687403/8388608),(8687403/8388608),(4826335/8388608)]⟩
theorem bound : BoxMajorant box := Leaf4.bound
end G15

namespace G19
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(4826335/8388608)],![(16409539/16777216),(16409539/16777216),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf5.bound
end G19

namespace G20
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(10617937/16777216)],![(16409539/16777216),(16409539/16777216),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf6.bound
end G20

namespace G18
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(4826335/8388608)],![(16409539/16777216),(16409539/16777216),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G19.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G20.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G19.bound) (by rw [eq_true]; exact G20.bound)
end G18

namespace G24
def box : ClosedBox 3 := ⟨![(965267/1048576),(16409539/16777216),(4826335/8388608)],![(31853811/33554432),(33784345/33554432),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf7.bound
end G24

namespace G26
def box : ClosedBox 3 := ⟨![(965267/1048576),(33784345/33554432),(4826335/8388608)],![(31853811/33554432),(8687403/8388608),(20270607/33554432)]⟩
theorem bound : BoxMajorant box := Leaf8.bound
end G26

namespace G27
def box : ClosedBox 3 := ⟨![(965267/1048576),(33784345/33554432),(20270607/33554432)],![(31853811/33554432),(8687403/8388608),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf9.bound
end G27

namespace G25
def box : ClosedBox 3 := ⟨![(965267/1048576),(33784345/33554432),(4826335/8388608)],![(31853811/33554432),(8687403/8388608),(10617937/16777216)]⟩
theorem eq_false : box.half 2 false=G26.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G27.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G26.bound) (by rw [eq_true]; exact G27.bound)
end G25

namespace G23
def box : ClosedBox 3 := ⟨![(965267/1048576),(16409539/16777216),(4826335/8388608)],![(31853811/33554432),(8687403/8388608),(10617937/16777216)]⟩
theorem eq_false : box.half 1 false=G24.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G25.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G24.bound) (by rw [eq_true]; exact G25.bound)
end G23

namespace G30
def box : ClosedBox 3 := ⟨![(31853811/33554432),(16409539/16777216),(4826335/8388608)],![(16409539/16777216),(33784345/33554432),(20270607/33554432)]⟩
theorem bound : BoxMajorant box := Leaf10.bound
end G30

namespace G31
def box : ClosedBox 3 := ⟨![(31853811/33554432),(16409539/16777216),(20270607/33554432)],![(16409539/16777216),(33784345/33554432),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf11.bound
end G31

namespace G29
def box : ClosedBox 3 := ⟨![(31853811/33554432),(16409539/16777216),(4826335/8388608)],![(16409539/16777216),(33784345/33554432),(10617937/16777216)]⟩
theorem eq_false : box.half 2 false=G30.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G31.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G30.bound) (by rw [eq_true]; exact G31.bound)
end G29

namespace G33
def box : ClosedBox 3 := ⟨![(31853811/33554432),(33784345/33554432),(4826335/8388608)],![(16409539/16777216),(8687403/8388608),(20270607/33554432)]⟩
theorem bound : BoxMajorant box := Leaf12.bound
end G33

namespace G35
def box : ClosedBox 3 := ⟨![(31853811/33554432),(33784345/33554432),(20270607/33554432)],![(64672889/67108864),(8687403/8388608),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf13.bound
end G35

namespace G38
def box : ClosedBox 3 := ⟨![(64672889/67108864),(33784345/33554432),(20270607/33554432)],![(16409539/16777216),(68533957/67108864),(41506481/67108864)]⟩
theorem bound : BoxMajorant box := Leaf14.bound
end G38

namespace G39
def box : ClosedBox 3 := ⟨![(64672889/67108864),(33784345/33554432),(41506481/67108864)],![(16409539/16777216),(68533957/67108864),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf15.bound
end G39

namespace G37
def box : ClosedBox 3 := ⟨![(64672889/67108864),(33784345/33554432),(20270607/33554432)],![(16409539/16777216),(68533957/67108864),(10617937/16777216)]⟩
theorem eq_false : box.half 2 false=G38.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G39.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G38.bound) (by rw [eq_true]; exact G39.bound)
end G37

namespace G41
def box : ClosedBox 3 := ⟨![(64672889/67108864),(68533957/67108864),(20270607/33554432)],![(16409539/16777216),(8687403/8388608),(41506481/67108864)]⟩
theorem bound : BoxMajorant box := Leaf16.bound
end G41

namespace G42
def box : ClosedBox 3 := ⟨![(64672889/67108864),(68533957/67108864),(41506481/67108864)],![(16409539/16777216),(8687403/8388608),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf17.bound
end G42

namespace G40
def box : ClosedBox 3 := ⟨![(64672889/67108864),(68533957/67108864),(20270607/33554432)],![(16409539/16777216),(8687403/8388608),(10617937/16777216)]⟩
theorem eq_false : box.half 2 false=G41.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G42.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G41.bound) (by rw [eq_true]; exact G42.bound)
end G40

namespace G36
def box : ClosedBox 3 := ⟨![(64672889/67108864),(33784345/33554432),(20270607/33554432)],![(16409539/16777216),(8687403/8388608),(10617937/16777216)]⟩
theorem eq_false : box.half 1 false=G37.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G40.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G37.bound) (by rw [eq_true]; exact G40.bound)
end G36

namespace G34
def box : ClosedBox 3 := ⟨![(31853811/33554432),(33784345/33554432),(20270607/33554432)],![(16409539/16777216),(8687403/8388608),(10617937/16777216)]⟩
theorem eq_false : box.half 0 false=G35.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G36.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G35.bound) (by rw [eq_true]; exact G36.bound)
end G34

namespace G32
def box : ClosedBox 3 := ⟨![(31853811/33554432),(33784345/33554432),(4826335/8388608)],![(16409539/16777216),(8687403/8388608),(10617937/16777216)]⟩
theorem eq_false : box.half 2 false=G33.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G34.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G33.bound) (by rw [eq_true]; exact G34.bound)
end G32

namespace G28
def box : ClosedBox 3 := ⟨![(31853811/33554432),(16409539/16777216),(4826335/8388608)],![(16409539/16777216),(8687403/8388608),(10617937/16777216)]⟩
theorem eq_false : box.half 1 false=G29.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G32.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G29.bound) (by rw [eq_true]; exact G32.bound)
end G28

namespace G22
def box : ClosedBox 3 := ⟨![(965267/1048576),(16409539/16777216),(4826335/8388608)],![(16409539/16777216),(8687403/8388608),(10617937/16777216)]⟩
theorem eq_false : box.half 0 false=G23.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G28.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G23.bound) (by rw [eq_true]; exact G28.bound)
end G22

namespace G43
def box : ClosedBox 3 := ⟨![(965267/1048576),(16409539/16777216),(10617937/16777216)],![(16409539/16777216),(8687403/8388608),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf18.bound
end G43

namespace G21
def box : ClosedBox 3 := ⟨![(965267/1048576),(16409539/16777216),(4826335/8388608)],![(16409539/16777216),(8687403/8388608),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G22.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G43.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G22.bound) (by rw [eq_true]; exact G43.bound)
end G21

namespace G17
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(4826335/8388608)],![(16409539/16777216),(8687403/8388608),(2895801/4194304)]⟩
theorem eq_false : box.half 1 false=G18.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G21.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G18.bound) (by rw [eq_true]; exact G21.bound)
end G17

namespace G48
def box : ClosedBox 3 := ⟨![(16409539/16777216),(965267/1048576),(4826335/8388608)],![(33784345/33554432),(31853811/33554432),(10617937/16777216)]⟩
theorem checked : outsideCheck box=true := by decide +kernel
theorem bound : BoxMajorant box := by
  intro x hx hd
  exact (outsideCheck_sound box checked hx hd.1 hd.2).elim
end G48

namespace G50
def box : ClosedBox 3 := ⟨![(16409539/16777216),(31853811/33554432),(4826335/8388608)],![(33784345/33554432),(16409539/16777216),(20270607/33554432)]⟩
theorem bound : BoxMajorant box := Leaf19.bound
end G50

namespace G51
def box : ClosedBox 3 := ⟨![(16409539/16777216),(31853811/33554432),(20270607/33554432)],![(33784345/33554432),(16409539/16777216),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf20.bound
end G51

namespace G49
def box : ClosedBox 3 := ⟨![(16409539/16777216),(31853811/33554432),(4826335/8388608)],![(33784345/33554432),(16409539/16777216),(10617937/16777216)]⟩
theorem eq_false : box.half 2 false=G50.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G51.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G50.bound) (by rw [eq_true]; exact G51.bound)
end G49

namespace G47
def box : ClosedBox 3 := ⟨![(16409539/16777216),(965267/1048576),(4826335/8388608)],![(33784345/33554432),(16409539/16777216),(10617937/16777216)]⟩
theorem eq_false : box.half 1 false=G48.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G49.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G48.bound) (by rw [eq_true]; exact G49.bound)
end G47

namespace G52
def box : ClosedBox 3 := ⟨![(33784345/33554432),(965267/1048576),(4826335/8388608)],![(8687403/8388608),(16409539/16777216),(10617937/16777216)]⟩
theorem checked : outsideCheck box=true := by decide +kernel
theorem bound : BoxMajorant box := by
  intro x hx hd
  exact (outsideCheck_sound box checked hx hd.1 hd.2).elim
end G52

namespace G46
def box : ClosedBox 3 := ⟨![(16409539/16777216),(965267/1048576),(4826335/8388608)],![(8687403/8388608),(16409539/16777216),(10617937/16777216)]⟩
theorem eq_false : box.half 0 false=G47.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G52.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G47.bound) (by rw [eq_true]; exact G52.bound)
end G46

namespace G53
def box : ClosedBox 3 := ⟨![(16409539/16777216),(965267/1048576),(10617937/16777216)],![(8687403/8388608),(16409539/16777216),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf21.bound
end G53

namespace G45
def box : ClosedBox 3 := ⟨![(16409539/16777216),(965267/1048576),(4826335/8388608)],![(8687403/8388608),(16409539/16777216),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G46.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G53.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G46.bound) (by rw [eq_true]; exact G53.bound)
end G45

namespace G58
def box : ClosedBox 3 := ⟨![(16409539/16777216),(16409539/16777216),(4826335/8388608)],![(33784345/33554432),(33784345/33554432),(20270607/33554432)]⟩
theorem bound : BoxMajorant box := Leaf22.bound
end G58

namespace G61
def box : ClosedBox 3 := ⟨![(16409539/16777216),(16409539/16777216),(20270607/33554432)],![(66603423/67108864),(66603423/67108864),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf23.bound
end G61

namespace G63
def box : ClosedBox 3 := ⟨![(16409539/16777216),(66603423/67108864),(20270607/33554432)],![(66603423/67108864),(33784345/33554432),(41506481/67108864)]⟩
theorem bound : BoxMajorant box := Leaf24.bound
end G63

namespace G64
def box : ClosedBox 3 := ⟨![(16409539/16777216),(66603423/67108864),(41506481/67108864)],![(66603423/67108864),(33784345/33554432),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf25.bound
end G64

namespace G62
def box : ClosedBox 3 := ⟨![(16409539/16777216),(66603423/67108864),(20270607/33554432)],![(66603423/67108864),(33784345/33554432),(10617937/16777216)]⟩
theorem eq_false : box.half 2 false=G63.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G64.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G63.bound) (by rw [eq_true]; exact G64.bound)
end G62

namespace G60
def box : ClosedBox 3 := ⟨![(16409539/16777216),(16409539/16777216),(20270607/33554432)],![(66603423/67108864),(33784345/33554432),(10617937/16777216)]⟩
theorem eq_false : box.half 1 false=G61.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G62.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G61.bound) (by rw [eq_true]; exact G62.bound)
end G60

namespace G67
def box : ClosedBox 3 := ⟨![(66603423/67108864),(16409539/16777216),(20270607/33554432)],![(33784345/33554432),(66603423/67108864),(41506481/67108864)]⟩
theorem bound : BoxMajorant box := Leaf26.bound
end G67

namespace G68
def box : ClosedBox 3 := ⟨![(66603423/67108864),(16409539/16777216),(41506481/67108864)],![(33784345/33554432),(66603423/67108864),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf27.bound
end G68

namespace G66
def box : ClosedBox 3 := ⟨![(66603423/67108864),(16409539/16777216),(20270607/33554432)],![(33784345/33554432),(66603423/67108864),(10617937/16777216)]⟩
theorem eq_false : box.half 2 false=G67.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G68.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G67.bound) (by rw [eq_true]; exact G68.bound)
end G66

namespace G70
def box : ClosedBox 3 := ⟨![(66603423/67108864),(66603423/67108864),(20270607/33554432)],![(33784345/33554432),(33784345/33554432),(41506481/67108864)]⟩
theorem bound : BoxMajorant box := Leaf28.bound
end G70

namespace G75
def box : ClosedBox 3 := ⟨![(66603423/67108864),(66603423/67108864),(41506481/67108864)],![(267378959/268435456),(134172113/134217728),(83978229/134217728)]⟩
theorem bound : BoxMajorant box := Leaf29.bound
end G75

namespace G77
def box : ClosedBox 3 := ⟨![(267378959/268435456),(66603423/67108864),(41506481/67108864)],![(134172113/134217728),(267378959/268435456),(83978229/134217728)]⟩
theorem bound : BoxMajorant box := Leaf30.bound
end G77

namespace G79
def box : ClosedBox 3 := ⟨![(267378959/268435456),(267378959/268435456),(41506481/67108864)],![(134172113/134217728),(134172113/134217728),(166991191/268435456)]⟩
theorem bound : BoxMajorant box := Leaf31.bound
end G79

namespace G80
def box : ClosedBox 3 := ⟨![(267378959/268435456),(267378959/268435456),(166991191/268435456)],![(134172113/134217728),(134172113/134217728),(83978229/134217728)]⟩
theorem bound : BoxMajorant box := Leaf32.bound
end G80

namespace G78
def box : ClosedBox 3 := ⟨![(267378959/268435456),(267378959/268435456),(41506481/67108864)],![(134172113/134217728),(134172113/134217728),(83978229/134217728)]⟩
theorem eq_false : box.half 2 false=G79.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G80.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G79.bound) (by rw [eq_true]; exact G80.bound)
end G78

namespace G76
def box : ClosedBox 3 := ⟨![(267378959/268435456),(66603423/67108864),(41506481/67108864)],![(134172113/134217728),(134172113/134217728),(83978229/134217728)]⟩
theorem eq_false : box.half 1 false=G77.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G78.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G77.bound) (by rw [eq_true]; exact G78.bound)
end G76

namespace G74
def box : ClosedBox 3 := ⟨![(66603423/67108864),(66603423/67108864),(41506481/67108864)],![(134172113/134217728),(134172113/134217728),(83978229/134217728)]⟩
theorem eq_false : box.half 0 false=G75.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G76.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G75.bound) (by rw [eq_true]; exact G76.bound)
end G74

namespace G81
def box : ClosedBox 3 := ⟨![(66603423/67108864),(66603423/67108864),(83978229/134217728)],![(134172113/134217728),(134172113/134217728),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf33.bound
end G81

namespace G73
def box : ClosedBox 3 := ⟨![(66603423/67108864),(66603423/67108864),(41506481/67108864)],![(134172113/134217728),(134172113/134217728),(10617937/16777216)]⟩
theorem eq_false : box.half 2 false=G74.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G81.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G74.bound) (by rw [eq_true]; exact G81.bound)
end G73

namespace G84
def box : ClosedBox 3 := ⟨![(66603423/67108864),(134172113/134217728),(41506481/67108864)],![(267378959/268435456),(33784345/33554432),(83978229/134217728)]⟩
theorem bound : BoxMajorant box := Leaf34.bound
end G84

namespace G87
def box : ClosedBox 3 := ⟨![(267378959/268435456),(134172113/134217728),(41506481/67108864)],![(134172113/134217728),(269309493/268435456),(166991191/268435456)]⟩
theorem bound : BoxMajorant box := Leaf35.bound
end G87

namespace G89
def box : ClosedBox 3 := ⟨![(267378959/268435456),(134172113/134217728),(166991191/268435456)],![(535723185/536870912),(269309493/268435456),(83978229/134217728)]⟩
theorem bound : BoxMajorant box := Leaf36.bound
end G89

namespace G93
def box : ClosedBox 3 := ⟨![(535723185/536870912),(134172113/134217728),(166991191/268435456)],![(1072411637/1073741824),(537653719/536870912),(334947649/536870912)]⟩
theorem bound : BoxMajorant box := Leaf37.bound
end G93

namespace G96
def box : ClosedBox 3 := ⟨![(1072411637/1073741824),(134172113/134217728),(166991191/268435456)],![(134172113/134217728),(1074342171/1073741824),(668930031/1073741824)]⟩
theorem bound : BoxMajorant box := Leaf38.bound
end G96

namespace G97
def box : ClosedBox 3 := ⟨![(1072411637/1073741824),(134172113/134217728),(668930031/1073741824)],![(134172113/134217728),(1074342171/1073741824),(334947649/536870912)]⟩
theorem bound : BoxMajorant box := Leaf39.bound
end G97

namespace G95
def box : ClosedBox 3 := ⟨![(1072411637/1073741824),(134172113/134217728),(166991191/268435456)],![(134172113/134217728),(1074342171/1073741824),(334947649/536870912)]⟩
theorem eq_false : box.half 2 false=G96.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G97.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G96.bound) (by rw [eq_true]; exact G97.bound)
end G95

namespace G98
def box : ClosedBox 3 := ⟨![(1072411637/1073741824),(1074342171/1073741824),(166991191/268435456)],![(134172113/134217728),(537653719/536870912),(334947649/536870912)]⟩
theorem bound : BoxMajorant box := Leaf40.bound
end G98

namespace G94
def box : ClosedBox 3 := ⟨![(1072411637/1073741824),(134172113/134217728),(166991191/268435456)],![(134172113/134217728),(537653719/536870912),(334947649/536870912)]⟩
theorem eq_false : box.half 1 false=G95.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G98.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G95.bound) (by rw [eq_true]; exact G98.bound)
end G94

namespace G92
def box : ClosedBox 3 := ⟨![(535723185/536870912),(134172113/134217728),(166991191/268435456)],![(134172113/134217728),(537653719/536870912),(334947649/536870912)]⟩
theorem eq_false : box.half 0 false=G93.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G94.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G93.bound) (by rw [eq_true]; exact G94.bound)
end G92

namespace G99
def box : ClosedBox 3 := ⟨![(535723185/536870912),(134172113/134217728),(334947649/536870912)],![(134172113/134217728),(537653719/536870912),(83978229/134217728)]⟩
theorem bound : BoxMajorant box := Leaf41.bound
end G99

namespace G91
def box : ClosedBox 3 := ⟨![(535723185/536870912),(134172113/134217728),(166991191/268435456)],![(134172113/134217728),(537653719/536870912),(83978229/134217728)]⟩
theorem eq_false : box.half 2 false=G92.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G99.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G92.bound) (by rw [eq_true]; exact G99.bound)
end G91

namespace G100
def box : ClosedBox 3 := ⟨![(535723185/536870912),(537653719/536870912),(166991191/268435456)],![(134172113/134217728),(269309493/268435456),(83978229/134217728)]⟩
theorem bound : BoxMajorant box := Leaf42.bound
end G100

namespace G90
def box : ClosedBox 3 := ⟨![(535723185/536870912),(134172113/134217728),(166991191/268435456)],![(134172113/134217728),(269309493/268435456),(83978229/134217728)]⟩
theorem eq_false : box.half 1 false=G91.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G100.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G91.bound) (by rw [eq_true]; exact G100.bound)
end G90

namespace G88
def box : ClosedBox 3 := ⟨![(267378959/268435456),(134172113/134217728),(166991191/268435456)],![(134172113/134217728),(269309493/268435456),(83978229/134217728)]⟩
theorem eq_false : box.half 0 false=G89.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G90.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G89.bound) (by rw [eq_true]; exact G90.bound)
end G88

namespace G86
def box : ClosedBox 3 := ⟨![(267378959/268435456),(134172113/134217728),(41506481/67108864)],![(134172113/134217728),(269309493/268435456),(83978229/134217728)]⟩
theorem eq_false : box.half 2 false=G87.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G88.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G87.bound) (by rw [eq_true]; exact G88.bound)
end G86

namespace G101
def box : ClosedBox 3 := ⟨![(267378959/268435456),(269309493/268435456),(41506481/67108864)],![(134172113/134217728),(33784345/33554432),(83978229/134217728)]⟩
theorem bound : BoxMajorant box := Leaf43.bound
end G101

end MordellEight.CubicBoxes.B28
