import Eight.DyadicStages.C1
noncomputable section
namespace MordellEight.DyadicPilot
open FixedTensor RationalCube
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace N10

def box := N6.box.half 1 true
theorem widths : box.Widths := ClosedBox.half_widths N6.widths 1 true

def controls : Cube := FixedTransfer.step N6.controls 1 true
theorem eq_step : FixedTransfer.step N6.controls 1 true=controls := by rfl
theorem valid : TensorMinorant box (decode controls) := by
  have h := FixedTransfer.step_valid N6.valid N6.widths (shapeCheck_sound _ _ _ _ N6.shape) 1 true
  rw [eq_step] at h
  exact h

theorem shape : (decode controls).shapeCheck 12 12 6=true := by decide +kernel

theorem parameters_checked : IntegerLeaf.parameters box DyadicLogs.Log1.a DyadicLogs.Log1.hi 2535301200456458802993406410752 965267 613727648808763426799733024588 (-291734049780488564895276597248) (-291734049780488564895276597248) 1166936199121954259581106388992=true := by decide +kernel
theorem gap_checked : IntegerCube.nonneg (IntegerLeaf.gap controls 965267 613727648808763426799733024588 (-291734049780488564895276597248) (-291734049780488564895276597248) 1166936199121954259581106388992)=true := by decide +kernel
theorem bound : BoxMajorant box :=
  IntegerLeaf.majorant widths valid DyadicLogs.Log1.a DyadicLogs.Log1.hi 2535301200456458802993406410752 965267 613727648808763426799733024588 (-291734049780488564895276597248) (-291734049780488564895276597248) 1166936199121954259581106388992
    parameters_checked gap_checked DyadicLogs.Log1.positive DyadicLogs.Log1.upper

end N10

namespace N11

def box := N5.box.half 0 true
theorem widths : box.Widths := ClosedBox.half_widths N5.widths 0 true

def controls : Cube := FixedTransfer.step N5.controls 0 true
theorem eq_step : FixedTransfer.step N5.controls 0 true=controls := by rfl
theorem valid : TensorMinorant box (decode controls) := by
  have h := FixedTransfer.step_valid N5.valid N5.widths (shapeCheck_sound _ _ _ _ N5.shape) 0 true
  rw [eq_step] at h
  exact h

theorem shape : (decode controls).shapeCheck 12 12 6=true := by decide +kernel

theorem parameters_checked : IntegerLeaf.parameters box DyadicLogs.Log3.a DyadicLogs.Log3.hi 20282409603651670423947251286016 8687403 5745211496632162172785211715865 (-2333872398243908519162212777984) (-4667744796487817038324425555968) 9335489592975634076648851111936=true := by decide +kernel
theorem gap_checked : IntegerCube.nonneg (IntegerLeaf.gap controls 8687403 5745211496632162172785211715865 (-2333872398243908519162212777984) (-4667744796487817038324425555968) 9335489592975634076648851111936)=true := by decide +kernel
theorem bound : BoxMajorant box :=
  IntegerLeaf.majorant widths valid DyadicLogs.Log3.a DyadicLogs.Log3.hi 20282409603651670423947251286016 8687403 5745211496632162172785211715865 (-2333872398243908519162212777984) (-4667744796487817038324425555968) 9335489592975634076648851111936
    parameters_checked gap_checked DyadicLogs.Log3.positive DyadicLogs.Log3.upper

end N11

namespace N12

def box := N2.box.half 1 true
theorem widths : box.Widths := ClosedBox.half_widths N2.widths 1 true

def controls : Cube := FixedTransfer.step N2.controls 1 true
theorem eq_step : FixedTransfer.step N2.controls 1 true=controls := by rfl
theorem valid : TensorMinorant box (decode controls) := by
  have h := FixedTransfer.step_valid N2.valid N2.widths (shapeCheck_sound _ _ _ _ N2.shape) 1 true
  rw [eq_step] at h
  exact h

theorem shape : (decode controls).shapeCheck 12 12 6=true := by decide +kernel

end N12

namespace N13

def box := N12.box.half 2 false
theorem widths : box.Widths := ClosedBox.half_widths N12.widths 2 false

def controls : Cube := FixedTransfer.step N12.controls 2 false
theorem eq_step : FixedTransfer.step N12.controls 2 false=controls := by rfl
theorem valid : TensorMinorant box (decode controls) := by
  have h := FixedTransfer.step_valid N12.valid N12.widths (shapeCheck_sound _ _ _ _ N12.shape) 2 false
  rw [eq_step] at h
  exact h

theorem shape : (decode controls).shapeCheck 12 12 6=true := by decide +kernel

theorem parameters_checked : IntegerLeaf.parameters box DyadicLogs.Log4.a DyadicLogs.Log4.hi 5070602400912917605986812821504 4826335 (-818955626773241120905743948735) (-1166936199121954259581106388992) (-1166936199121954259581106388992) 2333872398243908519162212777984=true := by decide +kernel
theorem gap_checked : IntegerCube.nonneg (IntegerLeaf.gap controls 4826335 (-818955626773241120905743948735) (-1166936199121954259581106388992) (-1166936199121954259581106388992) 2333872398243908519162212777984)=true := by decide +kernel
theorem bound : BoxMajorant box :=
  IntegerLeaf.majorant widths valid DyadicLogs.Log4.a DyadicLogs.Log4.hi 5070602400912917605986812821504 4826335 (-818955626773241120905743948735) (-1166936199121954259581106388992) (-1166936199121954259581106388992) 2333872398243908519162212777984
    parameters_checked gap_checked DyadicLogs.Log4.positive DyadicLogs.Log4.upper

end N13

namespace N14

def box := N12.box.half 2 true
theorem widths : box.Widths := ClosedBox.half_widths N12.widths 2 true

def controls : Cube := FixedTransfer.step N12.controls 2 true
theorem eq_step : FixedTransfer.step N12.controls 2 true=controls := by rfl
theorem valid : TensorMinorant box (decode controls) := by
  have h := FixedTransfer.step_valid N12.valid N12.widths (shapeCheck_sound _ _ _ _ N12.shape) 2 true
  rw [eq_step] at h
  exact h

theorem shape : (decode controls).shapeCheck 12 12 6=true := by decide +kernel

theorem parameters_checked : IntegerLeaf.parameters box DyadicLogs.Log5.a DyadicLogs.Log5.hi 5070602400912917605986812821504 2895801 1296929359370815109624339207436 (-1166936199121954259581106388992) (-1166936199121954259581106388992) 2333872398243908519162212777984=true := by decide +kernel
theorem gap_checked : IntegerCube.nonneg (IntegerLeaf.gap controls 2895801 1296929359370815109624339207436 (-1166936199121954259581106388992) (-1166936199121954259581106388992) 2333872398243908519162212777984)=true := by decide +kernel
theorem bound : BoxMajorant box :=
  IntegerLeaf.majorant widths valid DyadicLogs.Log5.a DyadicLogs.Log5.hi 5070602400912917605986812821504 2895801 1296929359370815109624339207436 (-1166936199121954259581106388992) (-1166936199121954259581106388992) 2333872398243908519162212777984
    parameters_checked gap_checked DyadicLogs.Log5.positive DyadicLogs.Log5.upper

end N14

end MordellEight.DyadicPilot
