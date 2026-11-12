import Eight.CubicBoxes.B17.C01
import Eight.CubicBoxes.B17.C02
import Eight.CubicBoxes.B17.C03
import Eight.CubicBoxes.B17.C04
import Eight.CubicBoxes.B17.C05
import Eight.CubicBoxes.B17.C06
import Eight.CubicBoxes.B17.C07
import Eight.CubicBoxes.B17.C08
import Eight.CubicBoxes.B17.C09
import Eight.RootPartition
import Eight.RootGeometry.Narrow
namespace MordellEight.CubicBoxes.B17
open FixedTensor IntegerCube RationalCube Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace G7
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/2097152),0],![(4826335/8388608),(4826335/8388608),(965267/8388608)]⟩
theorem bound : BoxMajorant box := Leaf0.bound
end G7

namespace G8
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/2097152),(965267/8388608)],![(4826335/8388608),(4826335/8388608),(965267/4194304)]⟩
theorem bound : BoxMajorant box := Leaf1.bound
end G8

namespace G6
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/2097152),0],![(4826335/8388608),(4826335/8388608),(965267/4194304)]⟩
theorem eq_false : box.half 2 false=G7.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G8.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G7.bound) (by rw [eq_true]; exact G8.bound)
end G6

namespace G9
def box : ClosedBox 3 := ⟨![(965267/2097152),(4826335/8388608),0],![(4826335/8388608),(2895801/4194304),(965267/4194304)]⟩
theorem bound : BoxMajorant box := Leaf2.bound
end G9

namespace G5
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/2097152),0],![(4826335/8388608),(2895801/4194304),(965267/4194304)]⟩
theorem eq_false : box.half 1 false=G6.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G9.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G6.bound) (by rw [eq_true]; exact G9.bound)
end G5

namespace G10
def box : ClosedBox 3 := ⟨![(4826335/8388608),(965267/2097152),0],![(2895801/4194304),(2895801/4194304),(965267/4194304)]⟩
theorem bound : BoxMajorant box := Leaf3.bound
end G10

namespace G4
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/2097152),0],![(2895801/4194304),(2895801/4194304),(965267/4194304)]⟩
theorem eq_false : box.half 0 false=G5.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G10.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G5.bound) (by rw [eq_true]; exact G10.bound)
end G4

namespace G11
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/2097152),(965267/4194304)],![(2895801/4194304),(2895801/4194304),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf4.bound
end G11

namespace G3
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/2097152),0],![(2895801/4194304),(2895801/4194304),(965267/2097152)]⟩
theorem eq_false : box.half 2 false=G4.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G11.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G4.bound) (by rw [eq_true]; exact G11.bound)
end G3

namespace G14
def box : ClosedBox 3 := ⟨![(965267/2097152),(2895801/4194304),0],![(4826335/8388608),(965267/1048576),(965267/4194304)]⟩
theorem bound : BoxMajorant box := Leaf5.bound
end G14

namespace G16
def box : ClosedBox 3 := ⟨![(4826335/8388608),(2895801/4194304),0],![(2895801/4194304),(6756869/8388608),(965267/4194304)]⟩
theorem bound : BoxMajorant box := Leaf6.bound
end G16

namespace G17
def box : ClosedBox 3 := ⟨![(4826335/8388608),(6756869/8388608),0],![(2895801/4194304),(965267/1048576),(965267/4194304)]⟩
theorem bound : BoxMajorant box := Leaf7.bound
end G17

namespace G15
def box : ClosedBox 3 := ⟨![(4826335/8388608),(2895801/4194304),0],![(2895801/4194304),(965267/1048576),(965267/4194304)]⟩
theorem eq_false : box.half 1 false=G16.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G17.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G16.bound) (by rw [eq_true]; exact G17.bound)
end G15

namespace G13
def box : ClosedBox 3 := ⟨![(965267/2097152),(2895801/4194304),0],![(2895801/4194304),(965267/1048576),(965267/4194304)]⟩
theorem eq_false : box.half 0 false=G14.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G15.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G14.bound) (by rw [eq_true]; exact G15.bound)
end G13

namespace G18
def box : ClosedBox 3 := ⟨![(965267/2097152),(2895801/4194304),(965267/4194304)],![(2895801/4194304),(965267/1048576),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf8.bound
end G18

namespace G12
def box : ClosedBox 3 := ⟨![(965267/2097152),(2895801/4194304),0],![(2895801/4194304),(965267/1048576),(965267/2097152)]⟩
theorem eq_false : box.half 2 false=G13.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G18.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G13.bound) (by rw [eq_true]; exact G18.bound)
end G12

namespace G2
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/2097152),0],![(2895801/4194304),(965267/1048576),(965267/2097152)]⟩
theorem eq_false : box.half 1 false=G3.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G12.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G3.bound) (by rw [eq_true]; exact G12.bound)
end G2

namespace G21
def box : ClosedBox 3 := ⟨![(2895801/4194304),(965267/2097152),0],![(965267/1048576),(2895801/4194304),(965267/4194304)]⟩
theorem bound : BoxMajorant box := Leaf9.bound
end G21

namespace G22
def box : ClosedBox 3 := ⟨![(2895801/4194304),(965267/2097152),(965267/4194304)],![(965267/1048576),(2895801/4194304),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf10.bound
end G22

namespace G20
def box : ClosedBox 3 := ⟨![(2895801/4194304),(965267/2097152),0],![(965267/1048576),(2895801/4194304),(965267/2097152)]⟩
theorem eq_false : box.half 2 false=G21.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G22.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G21.bound) (by rw [eq_true]; exact G22.bound)
end G20

namespace G25
def box : ClosedBox 3 := ⟨![(2895801/4194304),(2895801/4194304),0],![(6756869/8388608),(965267/1048576),(965267/4194304)]⟩
theorem bound : BoxMajorant box := Leaf11.bound
end G25

namespace G26
def box : ClosedBox 3 := ⟨![(6756869/8388608),(2895801/4194304),0],![(965267/1048576),(965267/1048576),(965267/4194304)]⟩
theorem bound : BoxMajorant box := Leaf12.bound
end G26

namespace G24
def box : ClosedBox 3 := ⟨![(2895801/4194304),(2895801/4194304),0],![(965267/1048576),(965267/1048576),(965267/4194304)]⟩
theorem eq_false : box.half 0 false=G25.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G26.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G25.bound) (by rw [eq_true]; exact G26.bound)
end G24

namespace G28
def box : ClosedBox 3 := ⟨![(2895801/4194304),(2895801/4194304),(965267/4194304)],![(6756869/8388608),(965267/1048576),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf13.bound
end G28

namespace G29
def box : ClosedBox 3 := ⟨![(6756869/8388608),(2895801/4194304),(965267/4194304)],![(965267/1048576),(965267/1048576),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf14.bound
end G29

namespace G27
def box : ClosedBox 3 := ⟨![(2895801/4194304),(2895801/4194304),(965267/4194304)],![(965267/1048576),(965267/1048576),(965267/2097152)]⟩
theorem eq_false : box.half 0 false=G28.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G29.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G28.bound) (by rw [eq_true]; exact G29.bound)
end G27

namespace G23
def box : ClosedBox 3 := ⟨![(2895801/4194304),(2895801/4194304),0],![(965267/1048576),(965267/1048576),(965267/2097152)]⟩
theorem eq_false : box.half 2 false=G24.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G27.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G24.bound) (by rw [eq_true]; exact G27.bound)
end G23

namespace G19
def box : ClosedBox 3 := ⟨![(2895801/4194304),(965267/2097152),0],![(965267/1048576),(965267/1048576),(965267/2097152)]⟩
theorem eq_false : box.half 1 false=G20.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G23.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G20.bound) (by rw [eq_true]; exact G23.bound)
end G19

namespace G1
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/2097152),0],![(965267/1048576),(965267/1048576),(965267/2097152)]⟩
theorem eq_false : box.half 0 false=G2.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G19.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G2.bound) (by rw [eq_true]; exact G19.bound)
end G1

namespace G32
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/2097152),(965267/2097152)],![(2895801/4194304),(2895801/4194304),(965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf15.bound
end G32

namespace G35
def box : ClosedBox 3 := ⟨![(965267/2097152),(2895801/4194304),(965267/2097152)],![(4826335/8388608),(965267/1048576),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf16.bound
end G35

namespace G36
def box : ClosedBox 3 := ⟨![(4826335/8388608),(2895801/4194304),(965267/2097152)],![(2895801/4194304),(965267/1048576),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf17.bound
end G36

namespace G34
def box : ClosedBox 3 := ⟨![(965267/2097152),(2895801/4194304),(965267/2097152)],![(2895801/4194304),(965267/1048576),(2895801/4194304)]⟩
theorem eq_false : box.half 0 false=G35.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G36.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G35.bound) (by rw [eq_true]; exact G36.bound)
end G34

namespace G37
def box : ClosedBox 3 := ⟨![(965267/2097152),(2895801/4194304),(2895801/4194304)],![(2895801/4194304),(965267/1048576),(965267/1048576)]⟩
theorem checked : outsideCheck box=true := by decide +kernel
theorem bound : BoxMajorant box := by
  intro x hx hd
  exact (outsideCheck_sound box checked hx hd.1 hd.2).elim
end G37

namespace G33
def box : ClosedBox 3 := ⟨![(965267/2097152),(2895801/4194304),(965267/2097152)],![(2895801/4194304),(965267/1048576),(965267/1048576)]⟩
theorem eq_false : box.half 2 false=G34.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G37.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G34.bound) (by rw [eq_true]; exact G37.bound)
end G33

namespace G31
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/2097152),(965267/2097152)],![(2895801/4194304),(965267/1048576),(965267/1048576)]⟩
theorem eq_false : box.half 1 false=G32.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G33.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G32.bound) (by rw [eq_true]; exact G33.bound)
end G31

namespace G39
def box : ClosedBox 3 := ⟨![(2895801/4194304),(965267/2097152),(965267/2097152)],![(965267/1048576),(2895801/4194304),(965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf18.bound
end G39

namespace G42
def box : ClosedBox 3 := ⟨![(2895801/4194304),(2895801/4194304),(965267/2097152)],![(6756869/8388608),(965267/1048576),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf19.bound
end G42

namespace G44
def box : ClosedBox 3 := ⟨![(6756869/8388608),(2895801/4194304),(965267/2097152)],![(965267/1048576),(6756869/8388608),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf20.bound
end G44

namespace G46
def box : ClosedBox 3 := ⟨![(6756869/8388608),(6756869/8388608),(965267/2097152)],![(965267/1048576),(965267/1048576),(4826335/8388608)]⟩
theorem bound : BoxMajorant box := Leaf21.bound
end G46

namespace G47
def box : ClosedBox 3 := ⟨![(6756869/8388608),(6756869/8388608),(4826335/8388608)],![(965267/1048576),(965267/1048576),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf22.bound
end G47

namespace G45
def box : ClosedBox 3 := ⟨![(6756869/8388608),(6756869/8388608),(965267/2097152)],![(965267/1048576),(965267/1048576),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G46.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G47.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G46.bound) (by rw [eq_true]; exact G47.bound)
end G45

namespace G43
def box : ClosedBox 3 := ⟨![(6756869/8388608),(2895801/4194304),(965267/2097152)],![(965267/1048576),(965267/1048576),(2895801/4194304)]⟩
theorem eq_false : box.half 1 false=G44.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G45.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G44.bound) (by rw [eq_true]; exact G45.bound)
end G43

namespace G41
def box : ClosedBox 3 := ⟨![(2895801/4194304),(2895801/4194304),(965267/2097152)],![(965267/1048576),(965267/1048576),(2895801/4194304)]⟩
theorem eq_false : box.half 0 false=G42.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G43.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G42.bound) (by rw [eq_true]; exact G43.bound)
end G41

namespace G48
def box : ClosedBox 3 := ⟨![(2895801/4194304),(2895801/4194304),(2895801/4194304)],![(965267/1048576),(965267/1048576),(965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf23.bound
end G48

namespace G40
def box : ClosedBox 3 := ⟨![(2895801/4194304),(2895801/4194304),(965267/2097152)],![(965267/1048576),(965267/1048576),(965267/1048576)]⟩
theorem eq_false : box.half 2 false=G41.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G48.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G41.bound) (by rw [eq_true]; exact G48.bound)
end G40

namespace G38
def box : ClosedBox 3 := ⟨![(2895801/4194304),(965267/2097152),(965267/2097152)],![(965267/1048576),(965267/1048576),(965267/1048576)]⟩
theorem eq_false : box.half 1 false=G39.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G40.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G39.bound) (by rw [eq_true]; exact G40.bound)
end G38

namespace G30
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/2097152),(965267/2097152)],![(965267/1048576),(965267/1048576),(965267/1048576)]⟩
theorem eq_false : box.half 0 false=G31.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G38.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G31.bound) (by rw [eq_true]; exact G38.bound)
end G30

namespace G0
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/2097152),0],![(965267/1048576),(965267/1048576),(965267/1048576)]⟩
theorem eq_false : box.half 2 false=G1.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G30.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G1.bound) (by rw [eq_true]; exact G30.bound)
end G0

end MordellEight.CubicBoxes.B17
namespace MordellEight.RootBounds.B17
open FixedTensor IntegerCube RationalCube Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem box_eq : MordellEight.CubicBoxes.B17.G0.box=RootGeometry.narrowBox RootPartition.B17 := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem majorant : BoxMajorant RootPartition.B17 := by
  apply RootGeometry.majorant_of_narrow RootPartition.B17
  rw [←box_eq]
  exact MordellEight.CubicBoxes.B17.G0.bound
#print axioms majorant
end MordellEight.RootBounds.B17
