import Eight.DyadicStages.C2
noncomputable section
namespace MordellEight.DyadicPilot
open FixedTensor RationalCube
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace N15

def box := N1.box.half 0 true
theorem widths : box.Widths := ClosedBox.half_widths N1.widths 0 true

def controls : Cube := FixedTransfer.step N1.controls 0 true
theorem eq_step : FixedTransfer.step N1.controls 0 true=controls := by rfl
theorem valid : TensorMinorant box (decode controls) := by
  have h := FixedTransfer.step_valid N1.valid N1.widths (shapeCheck_sound _ _ _ _ N1.shape) 0 true
  rw [eq_step] at h
  exact h

theorem shape : (decode controls).shapeCheck 12 12 6=true := by decide +kernel

end N15

namespace N16

def box := N15.box.half 1 false
theorem widths : box.Widths := ClosedBox.half_widths N15.widths 1 false

def controls : Cube := FixedTransfer.step N15.controls 1 false
theorem eq_step : FixedTransfer.step N15.controls 1 false=controls := by rfl
theorem valid : TensorMinorant box (decode controls) := by
  have h := FixedTransfer.step_valid N15.valid N15.widths (shapeCheck_sound _ _ _ _ N15.shape) 1 false
  rw [eq_step] at h
  exact h

theorem shape : (decode controls).shapeCheck 12 12 6=true := by decide +kernel

end N16

namespace N17

def box := N16.box.half 2 false
theorem widths : box.Widths := ClosedBox.half_widths N16.widths 2 false

def controls : Cube := FixedTransfer.step N16.controls 2 false
theorem eq_step : FixedTransfer.step N16.controls 2 false=controls := by rfl
theorem valid : TensorMinorant box (decode controls) := by
  have h := FixedTransfer.step_valid N16.valid N16.widths (shapeCheck_sound _ _ _ _ N16.shape) 2 false
  rw [eq_step] at h
  exact h

theorem shape : (decode controls).shapeCheck 12 12 6=true := by decide +kernel

theorem parameters_checked : IntegerLeaf.parameters box DyadicLogs.Log4.a DyadicLogs.Log4.hi 5070602400912917605986812821504 4826335 (-818955626773241120905743948735) (-1166936199121954259581106388992) (-1166936199121954259581106388992) 2333872398243908519162212777984=true := by decide +kernel
theorem gap_checked : IntegerCube.nonneg (IntegerLeaf.gap controls 4826335 (-818955626773241120905743948735) (-1166936199121954259581106388992) (-1166936199121954259581106388992) 2333872398243908519162212777984)=true := by decide +kernel
theorem bound : BoxMajorant box :=
  IntegerLeaf.majorant widths valid DyadicLogs.Log4.a DyadicLogs.Log4.hi 5070602400912917605986812821504 4826335 (-818955626773241120905743948735) (-1166936199121954259581106388992) (-1166936199121954259581106388992) 2333872398243908519162212777984
    parameters_checked gap_checked DyadicLogs.Log4.positive DyadicLogs.Log4.upper

end N17

namespace N18

def box := N16.box.half 2 true
theorem widths : box.Widths := ClosedBox.half_widths N16.widths 2 true

def controls : Cube := FixedTransfer.step N16.controls 2 true
theorem eq_step : FixedTransfer.step N16.controls 2 true=controls := by rfl
theorem valid : TensorMinorant box (decode controls) := by
  have h := FixedTransfer.step_valid N16.valid N16.widths (shapeCheck_sound _ _ _ _ N16.shape) 2 true
  rw [eq_step] at h
  exact h

theorem shape : (decode controls).shapeCheck 12 12 6=true := by decide +kernel

theorem parameters_checked : IntegerLeaf.parameters box DyadicLogs.Log5.a DyadicLogs.Log5.hi 5070602400912917605986812821504 2895801 1296929359370815109624339207436 (-1166936199121954259581106388992) (-1166936199121954259581106388992) 2333872398243908519162212777984=true := by decide +kernel
theorem gap_checked : IntegerCube.nonneg (IntegerLeaf.gap controls 2895801 1296929359370815109624339207436 (-1166936199121954259581106388992) (-1166936199121954259581106388992) 2333872398243908519162212777984)=true := by decide +kernel
theorem bound : BoxMajorant box :=
  IntegerLeaf.majorant widths valid DyadicLogs.Log5.a DyadicLogs.Log5.hi 5070602400912917605986812821504 2895801 1296929359370815109624339207436 (-1166936199121954259581106388992) (-1166936199121954259581106388992) 2333872398243908519162212777984
    parameters_checked gap_checked DyadicLogs.Log5.positive DyadicLogs.Log5.upper

end N18

namespace N19

def box := N15.box.half 1 true
theorem widths : box.Widths := ClosedBox.half_widths N15.widths 1 true

def controls : Cube := FixedTransfer.step N15.controls 1 true
theorem eq_step : FixedTransfer.step N15.controls 1 true=controls := by rfl
theorem valid : TensorMinorant box (decode controls) := by
  have h := FixedTransfer.step_valid N15.valid N15.widths (shapeCheck_sound _ _ _ _ N15.shape) 1 true
  rw [eq_step] at h
  exact h

theorem shape : (decode controls).shapeCheck 12 12 6=true := by decide +kernel

end N19

end MordellEight.DyadicPilot
