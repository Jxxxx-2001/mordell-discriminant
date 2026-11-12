import Eight.DyadicStages.C6
noncomputable section
namespace MordellEight.DyadicPilot
open FixedTensor RationalCube
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace N35

def box := N34.box.half 0 false
theorem widths : box.Widths := ClosedBox.half_widths N34.widths 0 false

def controls : Cube := FixedTransfer.step N34.controls 0 false
theorem eq_step : FixedTransfer.step N34.controls 0 false=controls := by rfl
theorem valid : TensorMinorant box (decode controls) := by
  have h := FixedTransfer.step_valid N34.valid N34.widths (shapeCheck_sound _ _ _ _ N34.shape) 0 false
  rw [eq_step] at h
  exact h

theorem shape : (decode controls).shapeCheck 12 12 6=true := by decide +kernel

theorem parameters_checked : IntegerLeaf.parameters box DyadicLogs.Log2.a DyadicLogs.Log2.hi 4835703278458516698824704 1 1771975784371294297358002 (-556438540993668679991296) (-1112877081987337359982592) 2225754163974674719965184=true := by decide +kernel
theorem gap_checked : IntegerCube.nonneg (IntegerLeaf.gap controls 1 1771975784371294297358002 (-556438540993668679991296) (-1112877081987337359982592) 2225754163974674719965184)=true := by decide +kernel
theorem bound : BoxMajorant box :=
  IntegerLeaf.majorant widths valid DyadicLogs.Log2.a DyadicLogs.Log2.hi 4835703278458516698824704 1 1771975784371294297358002 (-556438540993668679991296) (-1112877081987337359982592) 2225754163974674719965184
    parameters_checked gap_checked DyadicLogs.Log2.positive DyadicLogs.Log2.upper

end N35

namespace N36

def box := N34.box.half 0 true
theorem widths : box.Widths := ClosedBox.half_widths N34.widths 0 true

theorem checked : outsideCheck box=true := by decide +kernel
theorem bound : BoxMajorant box := fun x hx hd => (outsideCheck_sound box checked hx hd.1 hd.2).elim

end N36

namespace N37

def box := N33.box.half 2 true
theorem widths : box.Widths := ClosedBox.half_widths N33.widths 2 true

theorem checked : outsideCheck box=true := by decide +kernel
theorem bound : BoxMajorant box := fun x hx hd => (outsideCheck_sound box checked hx hd.1 hd.2).elim

end N37

namespace N38

def box := N32.box.half 1 true
theorem widths : box.Widths := ClosedBox.half_widths N32.widths 1 true

def controls : Cube := FixedTransfer.step N32.controls 1 true
theorem eq_step : FixedTransfer.step N32.controls 1 true=controls := by rfl
theorem valid : TensorMinorant box (decode controls) := by
  have h := FixedTransfer.step_valid N32.valid N32.widths (shapeCheck_sound _ _ _ _ N32.shape) 1 true
  rw [eq_step] at h
  exact h

theorem shape : (decode controls).shapeCheck 12 12 6=true := by decide +kernel

end N38

namespace N39

def box := N38.box.half 2 false
theorem widths : box.Widths := ClosedBox.half_widths N38.widths 2 false

def controls : Cube := FixedTransfer.step N38.controls 2 false
theorem eq_step : FixedTransfer.step N38.controls 2 false=controls := by rfl
theorem valid : TensorMinorant box (decode controls) := by
  have h := FixedTransfer.step_valid N38.valid N38.widths (shapeCheck_sound _ _ _ _ N38.shape) 2 false
  rw [eq_step] at h
  exact h

theorem shape : (decode controls).shapeCheck 12 12 6=true := by decide +kernel

theorem parameters_checked : IntegerLeaf.parameters box DyadicLogs.Log1.a DyadicLogs.Log1.hi 2535301200456458802993406410752 965267 905461698589251991695009621836 (-583468099560977129790553194496) (-583468099560977129790553194496) 1166936199121954259581106388992=true := by decide +kernel
theorem gap_checked : IntegerCube.nonneg (IntegerLeaf.gap controls 965267 905461698589251991695009621836 (-583468099560977129790553194496) (-583468099560977129790553194496) 1166936199121954259581106388992)=true := by decide +kernel
theorem bound : BoxMajorant box :=
  IntegerLeaf.majorant widths valid DyadicLogs.Log1.a DyadicLogs.Log1.hi 2535301200456458802993406410752 965267 905461698589251991695009621836 (-583468099560977129790553194496) (-583468099560977129790553194496) 1166936199121954259581106388992
    parameters_checked gap_checked DyadicLogs.Log1.positive DyadicLogs.Log1.upper

end N39

end MordellEight.DyadicPilot
