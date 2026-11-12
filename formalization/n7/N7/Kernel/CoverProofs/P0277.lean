import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0057
import N7.Kernel.CoverGeometry.G0063
import N7.Kernel.CoverGeometry.G0068
import N7.Kernel.CoverGeometry.G0072
import N7.Kernel.CoverGeometry.G0078
import N7.Kernel.CoverGeometry.G0081
import N7.Kernel.CoverGeometry.G0083
import N7.Kernel.CoverGeometry.G0085
import N7.Kernel.PositiveGroups.G0310
import N7.Kernel.PositiveGroups.G0363
import N7.Kernel.PositiveGroups.G0394
import N7.Kernel.PositiveGroups.G0395
import N7.Kernel.PositiveGroups.G0413
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5484 : BoxMajorant Geometry.b5484 := by
  exact PositiveLeaves.L1475.bound

theorem bound5483 : BoxMajorant Geometry.b5483 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5483 2 (by decide +kernel) x hx hd ho).elim

theorem bound5354 : BoxMajorant Geometry.b5354 := by
  exact PositiveLeaves.L1474.bound

theorem bound5353 : BoxMajorant Geometry.b5353 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5353.Widths)
  · have he : Geometry.b5353.half 2 false=Geometry.b5483 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5483
  · have he : Geometry.b5353.half 2 true=Geometry.b5484 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5484

theorem bound5244 : BoxMajorant Geometry.b5244 := by
  exact PositiveLeaves.L1471.bound

theorem bound5243 : BoxMajorant Geometry.b5243 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5243 2 (by decide +kernel) x hx hd ho).elim

theorem bound5242 : BoxMajorant Geometry.b5242 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5242.Widths)
  · have he : Geometry.b5242.half 1 false=Geometry.b5353 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5353
  · have he : Geometry.b5242.half 1 true=Geometry.b5354 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5354

theorem bound5241 : BoxMajorant Geometry.b5241 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5241 2 (by decide +kernel) x hx hd ho).elim

theorem bound5024 : BoxMajorant Geometry.b5024 := by
  exact PositiveLeaves.L1470.bound

theorem bound5023 : BoxMajorant Geometry.b5023 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5023.Widths)
  · have he : Geometry.b5023.half 0 false=Geometry.b5243 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5243
  · have he : Geometry.b5023.half 0 true=Geometry.b5244 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5244

theorem bound5022 : BoxMajorant Geometry.b5022 := by
  exact PositiveLeaves.L1473.bound

theorem bound5021 : BoxMajorant Geometry.b5021 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5021.Widths)
  · have he : Geometry.b5021.half 0 false=Geometry.b5241 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5241
  · have he : Geometry.b5021.half 0 true=Geometry.b5242 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5242

theorem bound4654 : BoxMajorant Geometry.b4654 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4654.Widths)
  · have he : Geometry.b4654.half 2 false=Geometry.b5023 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5023
  · have he : Geometry.b4654.half 2 true=Geometry.b5024 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5024

theorem bound4653 : BoxMajorant Geometry.b4653 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4653.Widths)
  · have he : Geometry.b4653.half 2 false=Geometry.b5021 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5021
  · have he : Geometry.b4653.half 2 true=Geometry.b5022 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5022

theorem bound4392 : BoxMajorant Geometry.b4392 := by
  exact PositiveLeaves.L1469.bound

theorem bound4391 : BoxMajorant Geometry.b4391 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4391.Widths)
  · have he : Geometry.b4391.half 1 false=Geometry.b4653 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4653
  · have he : Geometry.b4391.half 1 true=Geometry.b4654 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4654

theorem bound4042 : BoxMajorant Geometry.b4042 := by
  exact PositiveLeaves.L1468.bound

theorem bound4041 : BoxMajorant Geometry.b4041 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4041.Widths)
  · have he : Geometry.b4041.half 0 false=Geometry.b4391 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4391
  · have he : Geometry.b4041.half 0 true=Geometry.b4392 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4392

theorem bound3651 : BoxMajorant Geometry.b3651 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3651.Widths)
  · have he : Geometry.b3651.half 2 false=Geometry.b4041 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4041
  · have he : Geometry.b3651.half 2 true=Geometry.b4042 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4042

end N7.Kernel.Cover
