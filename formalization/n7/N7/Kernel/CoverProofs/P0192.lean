import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0043
import N7.Kernel.CoverGeometry.G0049
import N7.Kernel.CoverGeometry.G0054
import N7.Kernel.CoverGeometry.G0058
import N7.Kernel.CoverGeometry.G0065
import N7.Kernel.CoverGeometry.G0070
import N7.Kernel.CoverGeometry.G0074
import N7.Kernel.PositiveGroups.G0231
import N7.Kernel.PositiveGroups.G0232
import N7.Kernel.PositiveGroups.G0270
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4778 : BoxMajorant Geometry.b4778 := by
  exact PositiveLeaves.L2726.bound

theorem bound4777 : BoxMajorant Geometry.b4777 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4777 2 (by decide +kernel) x hx hd ho).elim

theorem bound4488 : BoxMajorant Geometry.b4488 := by
  exact PositiveLeaves.L2725.bound

theorem bound4487 : BoxMajorant Geometry.b4487 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4487.Widths)
  · have he : Geometry.b4487.half 2 false=Geometry.b4777 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4777
  · have he : Geometry.b4487.half 2 true=Geometry.b4778 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4778

theorem bound4186 : BoxMajorant Geometry.b4186 := by
  exact PositiveLeaves.L2724.bound

theorem bound4185 : BoxMajorant Geometry.b4185 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4185.Widths)
  · have he : Geometry.b4185.half 1 false=Geometry.b4487 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4487
  · have he : Geometry.b4185.half 1 true=Geometry.b4488 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4488

theorem bound3766 : BoxMajorant Geometry.b3766 := by
  exact PositiveLeaves.L2723.bound

theorem bound3765 : BoxMajorant Geometry.b3765 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3765.Widths)
  · have he : Geometry.b3765.half 0 false=Geometry.b4185 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4185
  · have he : Geometry.b3765.half 0 true=Geometry.b4186 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4186

theorem bound3476 : BoxMajorant Geometry.b3476 := by
  exact PositiveLeaves.L2722.bound

theorem bound3475 : BoxMajorant Geometry.b3475 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3475.Widths)
  · have he : Geometry.b3475.half 2 false=Geometry.b3765 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3765
  · have he : Geometry.b3475.half 2 true=Geometry.b3766 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3766

theorem bound3198 : BoxMajorant Geometry.b3198 := by
  exact PositiveLeaves.L2721.bound

theorem bound3197 : BoxMajorant Geometry.b3197 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3197.Widths)
  · have he : Geometry.b3197.half 1 false=Geometry.b3475 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3475
  · have he : Geometry.b3197.half 1 true=Geometry.b3476 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3476

theorem bound2810 : BoxMajorant Geometry.b2810 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2810.Widths)
  · have he : Geometry.b2810.half 0 false=Geometry.b3197 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3197
  · have he : Geometry.b2810.half 0 true=Geometry.b3198 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3198

end N7.Kernel.Cover
