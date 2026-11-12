import Eight.CubicBoxes.B12.C00
import Eight.CubicBoxes.B12.C01
import Eight.CubicBoxes.B12.C02
import Eight.CubicBoxes.B12.C03
import Eight.CubicBoxes.B12.C04
import Eight.CubicBoxes.B12.C05
import Eight.CubicBoxes.B12.C06
import Eight.CubicBoxes.B12.C07
import Eight.CubicBoxes.B12.C08
import Eight.CubicBoxes.B12.C09
import Eight.CubicBoxes.B12.C10
import Eight.CubicBoxes.B12.C11
import Eight.RootPartition
namespace MordellEight.CubicBoxes.B12
open FixedTensor IntegerCube RationalCube Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace G2
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(-965267/524288)],![(2895801/2097152),(2895801/2097152),(-2895801/2097152)]⟩
theorem bound : BoxMajorant box := Leaf0.bound
end G2

namespace G6
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(-2895801/2097152)],![(4826335/4194304),(4826335/4194304),(-4826335/4194304)]⟩
theorem bound : BoxMajorant box := Leaf1.bound
end G6

namespace G10
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(-4826335/4194304)],![(8687403/8388608),(8687403/8388608),(-8687403/8388608)]⟩
theorem bound : BoxMajorant box := Leaf2.bound
end G10

namespace G12
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(-8687403/8388608)],![(16409539/16777216),(8687403/8388608),(-965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf3.bound
end G12

namespace G13
def box : ClosedBox 3 := ⟨![(16409539/16777216),(965267/1048576),(-8687403/8388608)],![(8687403/8388608),(8687403/8388608),(-965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf4.bound
end G13

namespace G11
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(-8687403/8388608)],![(8687403/8388608),(8687403/8388608),(-965267/1048576)]⟩
theorem eq_false : box.half 0 false=G12.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G13.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G12.bound) (by rw [eq_true]; exact G13.bound)
end G11

namespace G9
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(-4826335/4194304)],![(8687403/8388608),(8687403/8388608),(-965267/1048576)]⟩
theorem eq_false : box.half 2 false=G10.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G11.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G10.bound) (by rw [eq_true]; exact G11.bound)
end G9

namespace G14
def box : ClosedBox 3 := ⟨![(965267/1048576),(8687403/8388608),(-4826335/4194304)],![(8687403/8388608),(4826335/4194304),(-965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf5.bound
end G14

namespace G8
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(-4826335/4194304)],![(8687403/8388608),(4826335/4194304),(-965267/1048576)]⟩
theorem eq_false : box.half 1 false=G9.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G14.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G9.bound) (by rw [eq_true]; exact G14.bound)
end G8

namespace G16
def box : ClosedBox 3 := ⟨![(8687403/8388608),(965267/1048576),(-4826335/4194304)],![(4826335/4194304),(8687403/8388608),(-965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf6.bound
end G16

namespace G17
def box : ClosedBox 3 := ⟨![(8687403/8388608),(8687403/8388608),(-4826335/4194304)],![(4826335/4194304),(4826335/4194304),(-965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf7.bound
end G17

namespace G15
def box : ClosedBox 3 := ⟨![(8687403/8388608),(965267/1048576),(-4826335/4194304)],![(4826335/4194304),(4826335/4194304),(-965267/1048576)]⟩
theorem eq_false : box.half 1 false=G16.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G17.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G16.bound) (by rw [eq_true]; exact G17.bound)
end G15

namespace G7
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(-4826335/4194304)],![(4826335/4194304),(4826335/4194304),(-965267/1048576)]⟩
theorem eq_false : box.half 0 false=G8.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G15.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G8.bound) (by rw [eq_true]; exact G15.bound)
end G7

namespace G5
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(-2895801/2097152)],![(4826335/4194304),(4826335/4194304),(-965267/1048576)]⟩
theorem eq_false : box.half 2 false=G6.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G7.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G6.bound) (by rw [eq_true]; exact G7.bound)
end G5

namespace G19
def box : ClosedBox 3 := ⟨![(965267/1048576),(4826335/4194304),(-2895801/2097152)],![(4826335/4194304),(2895801/2097152),(-4826335/4194304)]⟩
theorem bound : BoxMajorant box := Leaf8.bound
end G19

namespace G20
def box : ClosedBox 3 := ⟨![(965267/1048576),(4826335/4194304),(-4826335/4194304)],![(4826335/4194304),(2895801/2097152),(-965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf9.bound
end G20

namespace G18
def box : ClosedBox 3 := ⟨![(965267/1048576),(4826335/4194304),(-2895801/2097152)],![(4826335/4194304),(2895801/2097152),(-965267/1048576)]⟩
theorem eq_false : box.half 2 false=G19.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G20.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G19.bound) (by rw [eq_true]; exact G20.bound)
end G18

namespace G4
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(-2895801/2097152)],![(4826335/4194304),(2895801/2097152),(-965267/1048576)]⟩
theorem eq_false : box.half 1 false=G5.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G18.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G5.bound) (by rw [eq_true]; exact G18.bound)
end G4

namespace G23
def box : ClosedBox 3 := ⟨![(4826335/4194304),(965267/1048576),(-2895801/2097152)],![(2895801/2097152),(4826335/4194304),(-4826335/4194304)]⟩
theorem bound : BoxMajorant box := Leaf10.bound
end G23

namespace G24
def box : ClosedBox 3 := ⟨![(4826335/4194304),(965267/1048576),(-4826335/4194304)],![(2895801/2097152),(4826335/4194304),(-965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf11.bound
end G24

namespace G22
def box : ClosedBox 3 := ⟨![(4826335/4194304),(965267/1048576),(-2895801/2097152)],![(2895801/2097152),(4826335/4194304),(-965267/1048576)]⟩
theorem eq_false : box.half 2 false=G23.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G24.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G23.bound) (by rw [eq_true]; exact G24.bound)
end G22

namespace G29
def box : ClosedBox 3 := ⟨![(4826335/4194304),(4826335/4194304),(-2895801/2097152)],![(10617937/8388608),(10617937/8388608),(-10617937/8388608)]⟩
theorem bound : BoxMajorant box := Leaf12.bound
end G29

namespace G30
def box : ClosedBox 3 := ⟨![(4826335/4194304),(4826335/4194304),(-10617937/8388608)],![(10617937/8388608),(10617937/8388608),(-4826335/4194304)]⟩
theorem bound : BoxMajorant box := Leaf13.bound
end G30

namespace G28
def box : ClosedBox 3 := ⟨![(4826335/4194304),(4826335/4194304),(-2895801/2097152)],![(10617937/8388608),(10617937/8388608),(-4826335/4194304)]⟩
theorem eq_false : box.half 2 false=G29.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G30.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G29.bound) (by rw [eq_true]; exact G30.bound)
end G28

namespace G32
def box : ClosedBox 3 := ⟨![(4826335/4194304),(10617937/8388608),(-2895801/2097152)],![(10617937/8388608),(2895801/2097152),(-10617937/8388608)]⟩
theorem bound : BoxMajorant box := Leaf14.bound
end G32

namespace G33
def box : ClosedBox 3 := ⟨![(4826335/4194304),(10617937/8388608),(-10617937/8388608)],![(10617937/8388608),(2895801/2097152),(-4826335/4194304)]⟩
theorem bound : BoxMajorant box := Leaf15.bound
end G33

namespace G31
def box : ClosedBox 3 := ⟨![(4826335/4194304),(10617937/8388608),(-2895801/2097152)],![(10617937/8388608),(2895801/2097152),(-4826335/4194304)]⟩
theorem eq_false : box.half 2 false=G32.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G33.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G32.bound) (by rw [eq_true]; exact G33.bound)
end G31

namespace G27
def box : ClosedBox 3 := ⟨![(4826335/4194304),(4826335/4194304),(-2895801/2097152)],![(10617937/8388608),(2895801/2097152),(-4826335/4194304)]⟩
theorem eq_false : box.half 1 false=G28.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G31.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G28.bound) (by rw [eq_true]; exact G31.bound)
end G27

namespace G35
def box : ClosedBox 3 := ⟨![(10617937/8388608),(4826335/4194304),(-2895801/2097152)],![(2895801/2097152),(10617937/8388608),(-4826335/4194304)]⟩
theorem bound : BoxMajorant box := Leaf16.bound
end G35

namespace G36
def box : ClosedBox 3 := ⟨![(10617937/8388608),(10617937/8388608),(-2895801/2097152)],![(2895801/2097152),(2895801/2097152),(-4826335/4194304)]⟩
theorem bound : BoxMajorant box := Leaf17.bound
end G36

namespace G34
def box : ClosedBox 3 := ⟨![(10617937/8388608),(4826335/4194304),(-2895801/2097152)],![(2895801/2097152),(2895801/2097152),(-4826335/4194304)]⟩
theorem eq_false : box.half 1 false=G35.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G36.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G35.bound) (by rw [eq_true]; exact G36.bound)
end G34

namespace G26
def box : ClosedBox 3 := ⟨![(4826335/4194304),(4826335/4194304),(-2895801/2097152)],![(2895801/2097152),(2895801/2097152),(-4826335/4194304)]⟩
theorem eq_false : box.half 0 false=G27.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G34.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G27.bound) (by rw [eq_true]; exact G34.bound)
end G26

namespace G37
def box : ClosedBox 3 := ⟨![(4826335/4194304),(4826335/4194304),(-4826335/4194304)],![(2895801/2097152),(2895801/2097152),(-965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf18.bound
end G37

namespace G25
def box : ClosedBox 3 := ⟨![(4826335/4194304),(4826335/4194304),(-2895801/2097152)],![(2895801/2097152),(2895801/2097152),(-965267/1048576)]⟩
theorem eq_false : box.half 2 false=G26.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G37.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G26.bound) (by rw [eq_true]; exact G37.bound)
end G25

namespace G21
def box : ClosedBox 3 := ⟨![(4826335/4194304),(965267/1048576),(-2895801/2097152)],![(2895801/2097152),(2895801/2097152),(-965267/1048576)]⟩
theorem eq_false : box.half 1 false=G22.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G25.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G22.bound) (by rw [eq_true]; exact G25.bound)
end G21

namespace G3
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(-2895801/2097152)],![(2895801/2097152),(2895801/2097152),(-965267/1048576)]⟩
theorem eq_false : box.half 0 false=G4.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G21.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G4.bound) (by rw [eq_true]; exact G21.bound)
end G3

namespace G1
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(-965267/524288)],![(2895801/2097152),(2895801/2097152),(-965267/1048576)]⟩
theorem eq_false : box.half 2 false=G2.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G3.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G2.bound) (by rw [eq_true]; exact G3.bound)
end G1

namespace G40
def box : ClosedBox 3 := ⟨![(965267/1048576),(2895801/2097152),(-965267/524288)],![(4826335/4194304),(965267/524288),(-2895801/2097152)]⟩
theorem bound : BoxMajorant box := Leaf19.bound
end G40

namespace G43
def box : ClosedBox 3 := ⟨![(4826335/4194304),(2895801/2097152),(-965267/524288)],![(2895801/2097152),(6756869/4194304),(-6756869/4194304)]⟩
theorem checked : outsideCheck box=true := by decide +kernel
theorem bound : BoxMajorant box := by
  intro x hx hd
  exact (outsideCheck_sound box checked hx hd.1 hd.2).elim
end G43

namespace G44
def box : ClosedBox 3 := ⟨![(4826335/4194304),(2895801/2097152),(-6756869/4194304)],![(2895801/2097152),(6756869/4194304),(-2895801/2097152)]⟩
theorem bound : BoxMajorant box := Leaf20.bound
end G44

namespace G42
def box : ClosedBox 3 := ⟨![(4826335/4194304),(2895801/2097152),(-965267/524288)],![(2895801/2097152),(6756869/4194304),(-2895801/2097152)]⟩
theorem eq_false : box.half 2 false=G43.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G44.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G43.bound) (by rw [eq_true]; exact G44.bound)
end G42

namespace G46
def box : ClosedBox 3 := ⟨![(4826335/4194304),(6756869/4194304),(-965267/524288)],![(2895801/2097152),(965267/524288),(-6756869/4194304)]⟩
theorem checked : outsideCheck box=true := by decide +kernel
theorem bound : BoxMajorant box := by
  intro x hx hd
  exact (outsideCheck_sound box checked hx hd.1 hd.2).elim
end G46

namespace G47
def box : ClosedBox 3 := ⟨![(4826335/4194304),(6756869/4194304),(-6756869/4194304)],![(2895801/2097152),(965267/524288),(-2895801/2097152)]⟩
theorem bound : BoxMajorant box := Leaf21.bound
end G47

namespace G45
def box : ClosedBox 3 := ⟨![(4826335/4194304),(6756869/4194304),(-965267/524288)],![(2895801/2097152),(965267/524288),(-2895801/2097152)]⟩
theorem eq_false : box.half 2 false=G46.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G47.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G46.bound) (by rw [eq_true]; exact G47.bound)
end G45

namespace G41
def box : ClosedBox 3 := ⟨![(4826335/4194304),(2895801/2097152),(-965267/524288)],![(2895801/2097152),(965267/524288),(-2895801/2097152)]⟩
theorem eq_false : box.half 1 false=G42.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G45.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G42.bound) (by rw [eq_true]; exact G45.bound)
end G41

namespace G39
def box : ClosedBox 3 := ⟨![(965267/1048576),(2895801/2097152),(-965267/524288)],![(2895801/2097152),(965267/524288),(-2895801/2097152)]⟩
theorem eq_false : box.half 0 false=G40.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G41.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G40.bound) (by rw [eq_true]; exact G41.bound)
end G39

namespace G51
def box : ClosedBox 3 := ⟨![(965267/1048576),(2895801/2097152),(-2895801/2097152)],![(4826335/4194304),(6756869/4194304),(-4826335/4194304)]⟩
theorem bound : BoxMajorant box := Leaf22.bound
end G51

namespace G52
def box : ClosedBox 3 := ⟨![(965267/1048576),(2895801/2097152),(-4826335/4194304)],![(4826335/4194304),(6756869/4194304),(-965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf23.bound
end G52

namespace G50
def box : ClosedBox 3 := ⟨![(965267/1048576),(2895801/2097152),(-2895801/2097152)],![(4826335/4194304),(6756869/4194304),(-965267/1048576)]⟩
theorem eq_false : box.half 2 false=G51.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G52.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G51.bound) (by rw [eq_true]; exact G52.bound)
end G50

namespace G54
def box : ClosedBox 3 := ⟨![(965267/1048576),(6756869/4194304),(-2895801/2097152)],![(4826335/4194304),(965267/524288),(-4826335/4194304)]⟩
theorem bound : BoxMajorant box := Leaf24.bound
end G54

namespace G55
def box : ClosedBox 3 := ⟨![(965267/1048576),(6756869/4194304),(-4826335/4194304)],![(4826335/4194304),(965267/524288),(-965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf25.bound
end G55

namespace G53
def box : ClosedBox 3 := ⟨![(965267/1048576),(6756869/4194304),(-2895801/2097152)],![(4826335/4194304),(965267/524288),(-965267/1048576)]⟩
theorem eq_false : box.half 2 false=G54.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G55.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G54.bound) (by rw [eq_true]; exact G55.bound)
end G53

namespace G49
def box : ClosedBox 3 := ⟨![(965267/1048576),(2895801/2097152),(-2895801/2097152)],![(4826335/4194304),(965267/524288),(-965267/1048576)]⟩
theorem eq_false : box.half 1 false=G50.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G53.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G50.bound) (by rw [eq_true]; exact G53.bound)
end G49

namespace G58
def box : ClosedBox 3 := ⟨![(4826335/4194304),(2895801/2097152),(-2895801/2097152)],![(2895801/2097152),(6756869/4194304),(-4826335/4194304)]⟩
theorem bound : BoxMajorant box := Leaf26.bound
end G58

namespace G59
def box : ClosedBox 3 := ⟨![(4826335/4194304),(2895801/2097152),(-4826335/4194304)],![(2895801/2097152),(6756869/4194304),(-965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf27.bound
end G59

namespace G57
def box : ClosedBox 3 := ⟨![(4826335/4194304),(2895801/2097152),(-2895801/2097152)],![(2895801/2097152),(6756869/4194304),(-965267/1048576)]⟩
theorem eq_false : box.half 2 false=G58.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G59.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G58.bound) (by rw [eq_true]; exact G59.bound)
end G57

namespace G60
def box : ClosedBox 3 := ⟨![(4826335/4194304),(6756869/4194304),(-2895801/2097152)],![(2895801/2097152),(965267/524288),(-965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf28.bound
end G60

namespace G56
def box : ClosedBox 3 := ⟨![(4826335/4194304),(2895801/2097152),(-2895801/2097152)],![(2895801/2097152),(965267/524288),(-965267/1048576)]⟩
theorem eq_false : box.half 1 false=G57.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G60.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G57.bound) (by rw [eq_true]; exact G60.bound)
end G56

namespace G48
def box : ClosedBox 3 := ⟨![(965267/1048576),(2895801/2097152),(-2895801/2097152)],![(2895801/2097152),(965267/524288),(-965267/1048576)]⟩
theorem eq_false : box.half 0 false=G49.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G56.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G49.bound) (by rw [eq_true]; exact G56.bound)
end G48

namespace G38
def box : ClosedBox 3 := ⟨![(965267/1048576),(2895801/2097152),(-965267/524288)],![(2895801/2097152),(965267/524288),(-965267/1048576)]⟩
theorem eq_false : box.half 2 false=G39.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G48.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G39.bound) (by rw [eq_true]; exact G48.bound)
end G38

namespace G0
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(-965267/524288)],![(2895801/2097152),(965267/524288),(-965267/1048576)]⟩
theorem eq_false : box.half 1 false=G1.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G38.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G1.bound) (by rw [eq_true]; exact G38.bound)
end G0

end MordellEight.CubicBoxes.B12
namespace MordellEight.RootBounds.B12
open FixedTensor IntegerCube RationalCube Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem box_eq : MordellEight.CubicBoxes.B12.G0.box=RootPartition.B12 := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem majorant : BoxMajorant RootPartition.B12 := by
  rw [←box_eq]
  exact MordellEight.CubicBoxes.B12.G0.bound
#print axioms majorant
end MordellEight.RootBounds.B12
