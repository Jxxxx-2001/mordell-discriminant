import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0074
import N7.Kernel.CoverGeometry.G0080
import N7.Kernel.CoverGeometry.G0082
import N7.Kernel.CoverGeometry.G0084
import N7.Kernel.PositiveGroups.G0426
import N7.Kernel.PositiveGroups.G0441
import N7.Kernel.PositiveGroups.G0455
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5436 : BoxMajorant Geometry.b5436 := by
  exact PositiveLeaves.L2830.bound

theorem bound5435 : BoxMajorant Geometry.b5435 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5435 2 (by decide +kernel) x hx hd ho).elim

theorem bound5306 : BoxMajorant Geometry.b5306 := by
  exact PositiveLeaves.L2829.bound

theorem bound5305 : BoxMajorant Geometry.b5305 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5305.Widths)
  · have he : Geometry.b5305.half 2 false=Geometry.b5435 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5435
  · have he : Geometry.b5305.half 2 true=Geometry.b5436 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5436

theorem bound5124 : BoxMajorant Geometry.b5124 := by
  exact PositiveLeaves.L2828.bound

theorem bound5123 : BoxMajorant Geometry.b5123 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5123.Widths)
  · have he : Geometry.b5123.half 1 false=Geometry.b5305 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5305
  · have he : Geometry.b5123.half 1 true=Geometry.b5306 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5306

theorem bound4742 : BoxMajorant Geometry.b4742 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4742.Widths)
  · have he : Geometry.b4742.half 0 false=Geometry.b5123 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5123
  · have he : Geometry.b4742.half 0 true=Geometry.b5124 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5124

end N7.Kernel.Cover
