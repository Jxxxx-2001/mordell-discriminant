import Eight.DyadicStages.C7
noncomputable section
namespace MordellEight.DyadicPilot
open FixedTensor RationalCube
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace N40

def box := N38.box.half 2 true
theorem widths : box.Widths := ClosedBox.half_widths N38.widths 2 true

def controls : Cube := FixedTransfer.step N38.controls 2 true
theorem eq_step : FixedTransfer.step N38.controls 2 true=controls := by rfl
theorem valid : TensorMinorant box (decode controls) := by
  have h := FixedTransfer.step_valid N38.valid N38.widths (shapeCheck_sound _ _ _ _ N38.shape) 2 true
  rw [eq_step] at h
  exact h

theorem shape : (decode controls).shapeCheck 12 12 6=true := by decide +kernel

theorem parameters_checked : IntegerLeaf.parameters box DyadicLogs.Log2.a DyadicLogs.Log2.hi 4835703278458516698824704 1 2884852866358631657340594 (-1112877081987337359982592) (-1112877081987337359982592) 2225754163974674719965184=true := by decide +kernel
theorem gap_checked : IntegerCube.nonneg (IntegerLeaf.gap controls 1 2884852866358631657340594 (-1112877081987337359982592) (-1112877081987337359982592) 2225754163974674719965184)=true := by decide +kernel
theorem bound : BoxMajorant box :=
  IntegerLeaf.majorant widths valid DyadicLogs.Log2.a DyadicLogs.Log2.hi 4835703278458516698824704 1 2884852866358631657340594 (-1112877081987337359982592) (-1112877081987337359982592) 2225754163974674719965184
    parameters_checked gap_checked DyadicLogs.Log2.positive DyadicLogs.Log2.upper

end N40

end MordellEight.DyadicPilot
