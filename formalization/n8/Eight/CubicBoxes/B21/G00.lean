import Eight.CubicBoxes.B21.C01
import Eight.CubicBoxes.B21.C02
import Eight.CubicBoxes.B21.C03
import Eight.CubicBoxes.B21.C04
import Eight.CubicBoxes.B21.C05
import Eight.CubicBoxes.B21.C06
import Eight.CubicBoxes.B21.C07
import Eight.CubicBoxes.B21.C08
import Eight.CubicBoxes.B21.C09
import Eight.CubicBoxes.B21.C10
import Eight.CubicBoxes.B21.C11
import Eight.CubicBoxes.B21.C12
import Eight.CubicBoxes.B21.C13
import Eight.RootPartition
import Eight.LocalLeaf
namespace MordellEight.CubicBoxes.B21
open FixedTensor IntegerCube RationalCube Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace G5
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/1048576),0],![(2895801/4194304),(4826335/4194304),(965267/4194304)]⟩
theorem bound : BoxMajorant box := Leaf0.bound
end G5

namespace G6
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/1048576),(965267/4194304)],![(2895801/4194304),(4826335/4194304),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf1.bound
end G6

namespace G4
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/1048576),0],![(2895801/4194304),(4826335/4194304),(965267/2097152)]⟩
theorem eq_false : box.half 2 false=G5.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G6.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G5.bound) (by rw [eq_true]; exact G6.bound)
end G4

namespace G8
def box : ClosedBox 3 := ⟨![(965267/2097152),(4826335/4194304),0],![(2895801/4194304),(2895801/2097152),(965267/4194304)]⟩
theorem bound : BoxMajorant box := Leaf2.bound
end G8

namespace G10
def box : ClosedBox 3 := ⟨![(965267/2097152),(4826335/4194304),(965267/4194304)],![(2895801/4194304),(2895801/2097152),(2895801/8388608)]⟩
theorem bound : BoxMajorant box := Leaf3.bound
end G10

namespace G11
def box : ClosedBox 3 := ⟨![(965267/2097152),(4826335/4194304),(2895801/8388608)],![(2895801/4194304),(2895801/2097152),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf4.bound
end G11

namespace G9
def box : ClosedBox 3 := ⟨![(965267/2097152),(4826335/4194304),(965267/4194304)],![(2895801/4194304),(2895801/2097152),(965267/2097152)]⟩
theorem eq_false : box.half 2 false=G10.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G11.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G10.bound) (by rw [eq_true]; exact G11.bound)
end G9

namespace G7
def box : ClosedBox 3 := ⟨![(965267/2097152),(4826335/4194304),0],![(2895801/4194304),(2895801/2097152),(965267/2097152)]⟩
theorem eq_false : box.half 2 false=G8.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G9.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G8.bound) (by rw [eq_true]; exact G9.bound)
end G7

namespace G3
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/1048576),0],![(2895801/4194304),(2895801/2097152),(965267/2097152)]⟩
theorem eq_false : box.half 1 false=G4.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G7.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G4.bound) (by rw [eq_true]; exact G7.bound)
end G3

namespace G14
def box : ClosedBox 3 := ⟨![(2895801/4194304),(965267/1048576),0],![(965267/1048576),(4826335/4194304),(965267/4194304)]⟩
theorem bound : BoxMajorant box := Leaf5.bound
end G14

namespace G16
def box : ClosedBox 3 := ⟨![(2895801/4194304),(965267/1048576),(965267/4194304)],![(965267/1048576),(4826335/4194304),(2895801/8388608)]⟩
theorem bound : BoxMajorant box := Leaf6.bound
end G16

namespace G17
def box : ClosedBox 3 := ⟨![(2895801/4194304),(965267/1048576),(2895801/8388608)],![(965267/1048576),(4826335/4194304),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf7.bound
end G17

namespace G15
def box : ClosedBox 3 := ⟨![(2895801/4194304),(965267/1048576),(965267/4194304)],![(965267/1048576),(4826335/4194304),(965267/2097152)]⟩
theorem eq_false : box.half 2 false=G16.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G17.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G16.bound) (by rw [eq_true]; exact G17.bound)
end G15

namespace G13
def box : ClosedBox 3 := ⟨![(2895801/4194304),(965267/1048576),0],![(965267/1048576),(4826335/4194304),(965267/2097152)]⟩
theorem eq_false : box.half 2 false=G14.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G15.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G14.bound) (by rw [eq_true]; exact G15.bound)
end G13

namespace G19
def box : ClosedBox 3 := ⟨![(2895801/4194304),(4826335/4194304),0],![(965267/1048576),(2895801/2097152),(965267/4194304)]⟩
theorem bound : BoxMajorant box := Leaf8.bound
end G19

namespace G20
def box : ClosedBox 3 := ⟨![(2895801/4194304),(4826335/4194304),(965267/4194304)],![(965267/1048576),(2895801/2097152),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf9.bound
end G20

namespace G18
def box : ClosedBox 3 := ⟨![(2895801/4194304),(4826335/4194304),0],![(965267/1048576),(2895801/2097152),(965267/2097152)]⟩
theorem eq_false : box.half 2 false=G19.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G20.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G19.bound) (by rw [eq_true]; exact G20.bound)
end G18

namespace G12
def box : ClosedBox 3 := ⟨![(2895801/4194304),(965267/1048576),0],![(965267/1048576),(2895801/2097152),(965267/2097152)]⟩
theorem eq_false : box.half 1 false=G13.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G18.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G13.bound) (by rw [eq_true]; exact G18.bound)
end G12

namespace G2
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/1048576),0],![(965267/1048576),(2895801/2097152),(965267/2097152)]⟩
theorem eq_false : box.half 0 false=G3.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G12.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G3.bound) (by rw [eq_true]; exact G12.bound)
end G2

namespace G25
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/1048576),(965267/2097152)],![(2895801/4194304),(4826335/4194304),(4826335/8388608)]⟩
theorem bound : BoxMajorant box := Leaf10.bound
end G25

namespace G26
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/1048576),(4826335/8388608)],![(2895801/4194304),(4826335/4194304),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf11.bound
end G26

namespace G24
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/1048576),(965267/2097152)],![(2895801/4194304),(4826335/4194304),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G25.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G26.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G25.bound) (by rw [eq_true]; exact G26.bound)
end G24

namespace G27
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/1048576),(2895801/4194304)],![(2895801/4194304),(4826335/4194304),(965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf12.bound
end G27

namespace G23
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/1048576),(965267/2097152)],![(2895801/4194304),(4826335/4194304),(965267/1048576)]⟩
theorem eq_false : box.half 2 false=G24.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G27.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G24.bound) (by rw [eq_true]; exact G27.bound)
end G23

namespace G32
def box : ClosedBox 3 := ⟨![(965267/2097152),(4826335/4194304),(965267/2097152)],![(4826335/8388608),(10617937/8388608),(4826335/8388608)]⟩
theorem bound : BoxMajorant box := Leaf13.bound
end G32

namespace G33
def box : ClosedBox 3 := ⟨![(965267/2097152),(4826335/4194304),(4826335/8388608)],![(4826335/8388608),(10617937/8388608),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf14.bound
end G33

namespace G31
def box : ClosedBox 3 := ⟨![(965267/2097152),(4826335/4194304),(965267/2097152)],![(4826335/8388608),(10617937/8388608),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G32.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G33.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G32.bound) (by rw [eq_true]; exact G33.bound)
end G31

namespace G35
def box : ClosedBox 3 := ⟨![(965267/2097152),(10617937/8388608),(965267/2097152)],![(4826335/8388608),(2895801/2097152),(4826335/8388608)]⟩
theorem bound : BoxMajorant box := Leaf15.bound
end G35

namespace G36
def box : ClosedBox 3 := ⟨![(965267/2097152),(10617937/8388608),(4826335/8388608)],![(4826335/8388608),(2895801/2097152),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf16.bound
end G36

namespace G34
def box : ClosedBox 3 := ⟨![(965267/2097152),(10617937/8388608),(965267/2097152)],![(4826335/8388608),(2895801/2097152),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G35.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G36.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G35.bound) (by rw [eq_true]; exact G36.bound)
end G34

namespace G30
def box : ClosedBox 3 := ⟨![(965267/2097152),(4826335/4194304),(965267/2097152)],![(4826335/8388608),(2895801/2097152),(2895801/4194304)]⟩
theorem eq_false : box.half 1 false=G31.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G34.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G31.bound) (by rw [eq_true]; exact G34.bound)
end G30

namespace G39
def box : ClosedBox 3 := ⟨![(4826335/8388608),(4826335/4194304),(965267/2097152)],![(2895801/4194304),(10617937/8388608),(4826335/8388608)]⟩
theorem bound : BoxMajorant box := Leaf17.bound
end G39

namespace G40
def box : ClosedBox 3 := ⟨![(4826335/8388608),(4826335/4194304),(4826335/8388608)],![(2895801/4194304),(10617937/8388608),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf18.bound
end G40

namespace G38
def box : ClosedBox 3 := ⟨![(4826335/8388608),(4826335/4194304),(965267/2097152)],![(2895801/4194304),(10617937/8388608),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G39.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G40.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G39.bound) (by rw [eq_true]; exact G40.bound)
end G38

namespace G42
def box : ClosedBox 3 := ⟨![(4826335/8388608),(10617937/8388608),(965267/2097152)],![(2895801/4194304),(2895801/2097152),(4826335/8388608)]⟩
theorem bound : BoxMajorant box := Leaf19.bound
end G42

namespace G43
def box : ClosedBox 3 := ⟨![(4826335/8388608),(10617937/8388608),(4826335/8388608)],![(2895801/4194304),(2895801/2097152),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf20.bound
end G43

namespace G41
def box : ClosedBox 3 := ⟨![(4826335/8388608),(10617937/8388608),(965267/2097152)],![(2895801/4194304),(2895801/2097152),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G42.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G43.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G42.bound) (by rw [eq_true]; exact G43.bound)
end G41

namespace G37
def box : ClosedBox 3 := ⟨![(4826335/8388608),(4826335/4194304),(965267/2097152)],![(2895801/4194304),(2895801/2097152),(2895801/4194304)]⟩
theorem eq_false : box.half 1 false=G38.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G41.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G38.bound) (by rw [eq_true]; exact G41.bound)
end G37

namespace G29
def box : ClosedBox 3 := ⟨![(965267/2097152),(4826335/4194304),(965267/2097152)],![(2895801/4194304),(2895801/2097152),(2895801/4194304)]⟩
theorem eq_false : box.half 0 false=G30.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G37.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G30.bound) (by rw [eq_true]; exact G37.bound)
end G29

namespace G44
def box : ClosedBox 3 := ⟨![(965267/2097152),(4826335/4194304),(2895801/4194304)],![(2895801/4194304),(2895801/2097152),(965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf21.bound
end G44

namespace G28
def box : ClosedBox 3 := ⟨![(965267/2097152),(4826335/4194304),(965267/2097152)],![(2895801/4194304),(2895801/2097152),(965267/1048576)]⟩
theorem eq_false : box.half 2 false=G29.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G44.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G29.bound) (by rw [eq_true]; exact G44.bound)
end G28

namespace G22
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/1048576),(965267/2097152)],![(2895801/4194304),(2895801/2097152),(965267/1048576)]⟩
theorem eq_false : box.half 1 false=G23.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G28.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G23.bound) (by rw [eq_true]; exact G28.bound)
end G22

namespace G50
def box : ClosedBox 3 := ⟨![(2895801/4194304),(965267/1048576),(965267/2097152)],![(6756869/8388608),(8687403/8388608),(4826335/8388608)]⟩
theorem bound : BoxMajorant box := Leaf22.bound
end G50

namespace G51
def box : ClosedBox 3 := ⟨![(2895801/4194304),(965267/1048576),(4826335/8388608)],![(6756869/8388608),(8687403/8388608),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf23.bound
end G51

namespace G49
def box : ClosedBox 3 := ⟨![(2895801/4194304),(965267/1048576),(965267/2097152)],![(6756869/8388608),(8687403/8388608),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G50.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G51.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G50.bound) (by rw [eq_true]; exact G51.bound)
end G49

namespace G53
def box : ClosedBox 3 := ⟨![(2895801/4194304),(8687403/8388608),(965267/2097152)],![(6756869/8388608),(4826335/4194304),(4826335/8388608)]⟩
theorem bound : BoxMajorant box := Leaf24.bound
end G53

namespace G55
def box : ClosedBox 3 := ⟨![(2895801/4194304),(8687403/8388608),(4826335/8388608)],![(12548471/16777216),(4826335/4194304),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf25.bound
end G55

namespace G57
def box : ClosedBox 3 := ⟨![(12548471/16777216),(8687403/8388608),(4826335/8388608)],![(6756869/8388608),(18340073/16777216),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf26.bound
end G57

namespace G59
def box : ClosedBox 3 := ⟨![(12548471/16777216),(18340073/16777216),(4826335/8388608)],![(6756869/8388608),(4826335/4194304),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf27.bound
end G59

namespace G60
def box : ClosedBox 3 := ⟨![(12548471/16777216),(18340073/16777216),(10617937/16777216)],![(6756869/8388608),(4826335/4194304),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf28.bound
end G60

namespace G58
def box : ClosedBox 3 := ⟨![(12548471/16777216),(18340073/16777216),(4826335/8388608)],![(6756869/8388608),(4826335/4194304),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G59.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G60.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G59.bound) (by rw [eq_true]; exact G60.bound)
end G58

namespace G56
def box : ClosedBox 3 := ⟨![(12548471/16777216),(8687403/8388608),(4826335/8388608)],![(6756869/8388608),(4826335/4194304),(2895801/4194304)]⟩
theorem eq_false : box.half 1 false=G57.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G58.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G57.bound) (by rw [eq_true]; exact G58.bound)
end G56

namespace G54
def box : ClosedBox 3 := ⟨![(2895801/4194304),(8687403/8388608),(4826335/8388608)],![(6756869/8388608),(4826335/4194304),(2895801/4194304)]⟩
theorem eq_false : box.half 0 false=G55.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G56.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G55.bound) (by rw [eq_true]; exact G56.bound)
end G54

namespace G52
def box : ClosedBox 3 := ⟨![(2895801/4194304),(8687403/8388608),(965267/2097152)],![(6756869/8388608),(4826335/4194304),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G53.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G54.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G53.bound) (by rw [eq_true]; exact G54.bound)
end G52

namespace G48
def box : ClosedBox 3 := ⟨![(2895801/4194304),(965267/1048576),(965267/2097152)],![(6756869/8388608),(4826335/4194304),(2895801/4194304)]⟩
theorem eq_false : box.half 1 false=G49.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G52.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G49.bound) (by rw [eq_true]; exact G52.bound)
end G48

namespace G63
def box : ClosedBox 3 := ⟨![(6756869/8388608),(965267/1048576),(965267/2097152)],![(965267/1048576),(8687403/8388608),(4826335/8388608)]⟩
theorem bound : BoxMajorant box := Leaf29.bound
end G63

namespace G65
def box : ClosedBox 3 := ⟨![(6756869/8388608),(965267/1048576),(4826335/8388608)],![(14479005/16777216),(8687403/8388608),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf30.bound
end G65

namespace G67
def box : ClosedBox 3 := ⟨![(14479005/16777216),(965267/1048576),(4826335/8388608)],![(965267/1048576),(16409539/16777216),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf31.bound
end G67

namespace G69
def box : ClosedBox 3 := ⟨![(14479005/16777216),(16409539/16777216),(4826335/8388608)],![(965267/1048576),(8687403/8388608),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf32.bound
end G69

namespace G70
def box : ClosedBox 3 := ⟨![(14479005/16777216),(16409539/16777216),(10617937/16777216)],![(965267/1048576),(8687403/8388608),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf33.bound
end G70

namespace G68
def box : ClosedBox 3 := ⟨![(14479005/16777216),(16409539/16777216),(4826335/8388608)],![(965267/1048576),(8687403/8388608),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G69.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G70.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G69.bound) (by rw [eq_true]; exact G70.bound)
end G68

namespace G66
def box : ClosedBox 3 := ⟨![(14479005/16777216),(965267/1048576),(4826335/8388608)],![(965267/1048576),(8687403/8388608),(2895801/4194304)]⟩
theorem eq_false : box.half 1 false=G67.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G68.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G67.bound) (by rw [eq_true]; exact G68.bound)
end G66

namespace G64
def box : ClosedBox 3 := ⟨![(6756869/8388608),(965267/1048576),(4826335/8388608)],![(965267/1048576),(8687403/8388608),(2895801/4194304)]⟩
theorem eq_false : box.half 0 false=G65.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G66.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G65.bound) (by rw [eq_true]; exact G66.bound)
end G64

namespace G62
def box : ClosedBox 3 := ⟨![(6756869/8388608),(965267/1048576),(965267/2097152)],![(965267/1048576),(8687403/8388608),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G63.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G64.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G63.bound) (by rw [eq_true]; exact G64.bound)
end G62

namespace G72
def box : ClosedBox 3 := ⟨![(6756869/8388608),(8687403/8388608),(965267/2097152)],![(965267/1048576),(4826335/4194304),(4826335/8388608)]⟩
theorem bound : BoxMajorant box := Leaf34.bound
end G72

namespace G76
def box : ClosedBox 3 := ⟨![(6756869/8388608),(8687403/8388608),(4826335/8388608)],![(14479005/16777216),(18340073/16777216),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf35.bound
end G76

namespace G77
def box : ClosedBox 3 := ⟨![(6756869/8388608),(8687403/8388608),(10617937/16777216)],![(14479005/16777216),(18340073/16777216),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf36.bound
end G77

namespace G75
def box : ClosedBox 3 := ⟨![(6756869/8388608),(8687403/8388608),(4826335/8388608)],![(14479005/16777216),(18340073/16777216),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G76.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G77.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G76.bound) (by rw [eq_true]; exact G77.bound)
end G75

namespace G79
def box : ClosedBox 3 := ⟨![(6756869/8388608),(18340073/16777216),(4826335/8388608)],![(14479005/16777216),(4826335/4194304),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf37.bound
end G79

namespace G80
def box : ClosedBox 3 := ⟨![(6756869/8388608),(18340073/16777216),(10617937/16777216)],![(14479005/16777216),(4826335/4194304),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf38.bound
end G80

namespace G78
def box : ClosedBox 3 := ⟨![(6756869/8388608),(18340073/16777216),(4826335/8388608)],![(14479005/16777216),(4826335/4194304),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G79.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G80.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G79.bound) (by rw [eq_true]; exact G80.bound)
end G78

namespace G74
def box : ClosedBox 3 := ⟨![(6756869/8388608),(8687403/8388608),(4826335/8388608)],![(14479005/16777216),(4826335/4194304),(2895801/4194304)]⟩
theorem eq_false : box.half 1 false=G75.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G78.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G75.bound) (by rw [eq_true]; exact G78.bound)
end G74

namespace G84
def box : ClosedBox 3 := ⟨![(14479005/16777216),(8687403/8388608),(4826335/8388608)],![(29923277/33554432),(18340073/16777216),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf39.bound
end G84

namespace G86
def box : ClosedBox 3 := ⟨![(29923277/33554432),(8687403/8388608),(4826335/8388608)],![(965267/1048576),(35714879/33554432),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf40.bound
end G86

namespace G88
def box : ClosedBox 3 := ⟨![(29923277/33554432),(35714879/33554432),(4826335/8388608)],![(965267/1048576),(18340073/16777216),(20270607/33554432)]⟩
theorem bound : BoxMajorant box := Leaf41.bound
end G88

namespace G89
def box : ClosedBox 3 := ⟨![(29923277/33554432),(35714879/33554432),(20270607/33554432)],![(965267/1048576),(18340073/16777216),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf42.bound
end G89

namespace G87
def box : ClosedBox 3 := ⟨![(29923277/33554432),(35714879/33554432),(4826335/8388608)],![(965267/1048576),(18340073/16777216),(10617937/16777216)]⟩
theorem eq_false : box.half 2 false=G88.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G89.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G88.bound) (by rw [eq_true]; exact G89.bound)
end G87

namespace G85
def box : ClosedBox 3 := ⟨![(29923277/33554432),(8687403/8388608),(4826335/8388608)],![(965267/1048576),(18340073/16777216),(10617937/16777216)]⟩
theorem eq_false : box.half 1 false=G86.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G87.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G86.bound) (by rw [eq_true]; exact G87.bound)
end G85

namespace G83
def box : ClosedBox 3 := ⟨![(14479005/16777216),(8687403/8388608),(4826335/8388608)],![(965267/1048576),(18340073/16777216),(10617937/16777216)]⟩
theorem eq_false : box.half 0 false=G84.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G85.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G84.bound) (by rw [eq_true]; exact G85.bound)
end G83

namespace G90
def box : ClosedBox 3 := ⟨![(14479005/16777216),(8687403/8388608),(10617937/16777216)],![(965267/1048576),(18340073/16777216),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf43.bound
end G90

end MordellEight.CubicBoxes.B21
