import Eight.CubicBoxes.B5.C01
import Eight.CubicBoxes.B5.C02
import Eight.CubicBoxes.B5.C03
import Eight.CubicBoxes.B5.C04
import Eight.RootPartition
namespace MordellEight.CubicBoxes.B5
open FixedTensor IntegerCube RationalCube Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace G2
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/1048576),(-965267/524288)],![(965267/1048576),(2895801/2097152),(-2895801/2097152)]⟩
theorem checked : outsideCheck box=true := by decide +kernel
theorem bound : BoxMajorant box := by
  intro x hx hd
  exact (outsideCheck_sound box checked hx hd.1 hd.2).elim
end G2

namespace G4
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/1048576),(-2895801/2097152)],![(2895801/4194304),(2895801/2097152),(-965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf0.bound
end G4

namespace G7
def box : ClosedBox 3 := ⟨![(2895801/4194304),(965267/1048576),(-2895801/2097152)],![(965267/1048576),(4826335/4194304),(-4826335/4194304)]⟩
theorem checked : outsideCheck box=true := by decide +kernel
theorem bound : BoxMajorant box := by
  intro x hx hd
  exact (outsideCheck_sound box checked hx hd.1 hd.2).elim
end G7

namespace G9
def box : ClosedBox 3 := ⟨![(2895801/4194304),(965267/1048576),(-4826335/4194304)],![(6756869/8388608),(4826335/4194304),(-965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf1.bound
end G9

namespace G10
def box : ClosedBox 3 := ⟨![(6756869/8388608),(965267/1048576),(-4826335/4194304)],![(965267/1048576),(4826335/4194304),(-965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf2.bound
end G10

namespace G8
def box : ClosedBox 3 := ⟨![(2895801/4194304),(965267/1048576),(-4826335/4194304)],![(965267/1048576),(4826335/4194304),(-965267/1048576)]⟩
theorem eq_false : box.half 0 false=G9.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G10.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G9.bound) (by rw [eq_true]; exact G10.bound)
end G8

namespace G6
def box : ClosedBox 3 := ⟨![(2895801/4194304),(965267/1048576),(-2895801/2097152)],![(965267/1048576),(4826335/4194304),(-965267/1048576)]⟩
theorem eq_false : box.half 2 false=G7.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G8.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G7.bound) (by rw [eq_true]; exact G8.bound)
end G6

namespace G11
def box : ClosedBox 3 := ⟨![(2895801/4194304),(4826335/4194304),(-2895801/2097152)],![(965267/1048576),(2895801/2097152),(-965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf3.bound
end G11

namespace G5
def box : ClosedBox 3 := ⟨![(2895801/4194304),(965267/1048576),(-2895801/2097152)],![(965267/1048576),(2895801/2097152),(-965267/1048576)]⟩
theorem eq_false : box.half 1 false=G6.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G11.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G6.bound) (by rw [eq_true]; exact G11.bound)
end G5

namespace G3
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/1048576),(-2895801/2097152)],![(965267/1048576),(2895801/2097152),(-965267/1048576)]⟩
theorem eq_false : box.half 0 false=G4.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G5.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G4.bound) (by rw [eq_true]; exact G5.bound)
end G3

namespace G1
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/1048576),(-965267/524288)],![(965267/1048576),(2895801/2097152),(-965267/1048576)]⟩
theorem eq_false : box.half 2 false=G2.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G3.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G2.bound) (by rw [eq_true]; exact G3.bound)
end G1

namespace G13
def box : ClosedBox 3 := ⟨![(965267/2097152),(2895801/2097152),(-965267/524288)],![(965267/1048576),(965267/524288),(-2895801/2097152)]⟩
theorem checked : outsideCheck box=true := by decide +kernel
theorem bound : BoxMajorant box := by
  intro x hx hd
  exact (outsideCheck_sound box checked hx hd.1 hd.2).elim
end G13

namespace G16
def box : ClosedBox 3 := ⟨![(965267/2097152),(2895801/2097152),(-2895801/2097152)],![(2895801/4194304),(6756869/4194304),(-965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf4.bound
end G16

namespace G18
def box : ClosedBox 3 := ⟨![(965267/2097152),(6756869/4194304),(-2895801/2097152)],![(2895801/4194304),(965267/524288),(-4826335/4194304)]⟩
theorem checked : outsideCheck box=true := by decide +kernel
theorem bound : BoxMajorant box := by
  intro x hx hd
  exact (outsideCheck_sound box checked hx hd.1 hd.2).elim
end G18

namespace G20
def box : ClosedBox 3 := ⟨![(965267/2097152),(6756869/4194304),(-4826335/4194304)],![(4826335/8388608),(965267/524288),(-965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf5.bound
end G20

namespace G21
def box : ClosedBox 3 := ⟨![(4826335/8388608),(6756869/4194304),(-4826335/4194304)],![(2895801/4194304),(965267/524288),(-965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf6.bound
end G21

namespace G19
def box : ClosedBox 3 := ⟨![(965267/2097152),(6756869/4194304),(-4826335/4194304)],![(2895801/4194304),(965267/524288),(-965267/1048576)]⟩
theorem eq_false : box.half 0 false=G20.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G21.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G20.bound) (by rw [eq_true]; exact G21.bound)
end G19

namespace G17
def box : ClosedBox 3 := ⟨![(965267/2097152),(6756869/4194304),(-2895801/2097152)],![(2895801/4194304),(965267/524288),(-965267/1048576)]⟩
theorem eq_false : box.half 2 false=G18.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G19.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G18.bound) (by rw [eq_true]; exact G19.bound)
end G17

namespace G15
def box : ClosedBox 3 := ⟨![(965267/2097152),(2895801/2097152),(-2895801/2097152)],![(2895801/4194304),(965267/524288),(-965267/1048576)]⟩
theorem eq_false : box.half 1 false=G16.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G17.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G16.bound) (by rw [eq_true]; exact G17.bound)
end G15

namespace G23
def box : ClosedBox 3 := ⟨![(2895801/4194304),(2895801/2097152),(-2895801/2097152)],![(965267/1048576),(6756869/4194304),(-965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf7.bound
end G23

namespace G25
def box : ClosedBox 3 := ⟨![(2895801/4194304),(6756869/4194304),(-2895801/2097152)],![(965267/1048576),(965267/524288),(-4826335/4194304)]⟩
theorem bound : BoxMajorant box := Leaf8.bound
end G25

namespace G26
def box : ClosedBox 3 := ⟨![(2895801/4194304),(6756869/4194304),(-4826335/4194304)],![(965267/1048576),(965267/524288),(-965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf9.bound
end G26

namespace G24
def box : ClosedBox 3 := ⟨![(2895801/4194304),(6756869/4194304),(-2895801/2097152)],![(965267/1048576),(965267/524288),(-965267/1048576)]⟩
theorem eq_false : box.half 2 false=G25.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G26.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G25.bound) (by rw [eq_true]; exact G26.bound)
end G24

namespace G22
def box : ClosedBox 3 := ⟨![(2895801/4194304),(2895801/2097152),(-2895801/2097152)],![(965267/1048576),(965267/524288),(-965267/1048576)]⟩
theorem eq_false : box.half 1 false=G23.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G24.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G23.bound) (by rw [eq_true]; exact G24.bound)
end G22

namespace G14
def box : ClosedBox 3 := ⟨![(965267/2097152),(2895801/2097152),(-2895801/2097152)],![(965267/1048576),(965267/524288),(-965267/1048576)]⟩
theorem eq_false : box.half 0 false=G15.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G22.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G15.bound) (by rw [eq_true]; exact G22.bound)
end G14

namespace G12
def box : ClosedBox 3 := ⟨![(965267/2097152),(2895801/2097152),(-965267/524288)],![(965267/1048576),(965267/524288),(-965267/1048576)]⟩
theorem eq_false : box.half 2 false=G13.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G14.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G13.bound) (by rw [eq_true]; exact G14.bound)
end G12

namespace G0
def box : ClosedBox 3 := ⟨![(965267/2097152),(965267/1048576),(-965267/524288)],![(965267/1048576),(965267/524288),(-965267/1048576)]⟩
theorem eq_false : box.half 1 false=G1.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G12.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G1.bound) (by rw [eq_true]; exact G12.bound)
end G0

end MordellEight.CubicBoxes.B5
namespace MordellEight.RootBounds.B5
open FixedTensor IntegerCube RationalCube Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem box_eq : MordellEight.CubicBoxes.B5.G0.box=RootPartition.B5 := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem majorant : BoxMajorant RootPartition.B5 := by
  rw [←box_eq]
  exact MordellEight.CubicBoxes.B5.G0.bound
#print axioms majorant
end MordellEight.RootBounds.B5
