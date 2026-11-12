import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0046
import N7.Kernel.CoverGeometry.G0051
import N7.Kernel.CoverGeometry.G0055
import N7.Kernel.CoverGeometry.G0060
import N7.Kernel.CoverGeometry.G0066
import N7.Kernel.CoverGeometry.G0071
import N7.Kernel.CoverGeometry.G0075
import N7.Kernel.CoverGeometry.G0080
import N7.Kernel.PositiveGroups.G0264
import N7.Kernel.PositiveGroups.G0291
import N7.Kernel.PositiveGroups.G0314
import N7.Kernel.PositiveGroups.G0344
import N7.Kernel.PositiveGroups.G0375
import N7.Kernel.PositiveGroups.G0402
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5176 : BoxMajorant Geometry.b5176 := by
  exact PositiveLeaves.L1990.bound

theorem bound5175 : BoxMajorant Geometry.b5175 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5175 2 (by decide +kernel) x hx hd ho).elim

theorem bound4860 : BoxMajorant Geometry.b4860 := by
  exact PositiveLeaves.L1989.bound

theorem bound4859 : BoxMajorant Geometry.b4859 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4859.Widths)
  · have he : Geometry.b4859.half 0 false=Geometry.b5175 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5175
  · have he : Geometry.b4859.half 0 true=Geometry.b5176 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5176

theorem bound4546 : BoxMajorant Geometry.b4546 := by
  exact PositiveLeaves.L1988.bound

theorem bound4545 : BoxMajorant Geometry.b4545 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4545.Widths)
  · have he : Geometry.b4545.half 2 false=Geometry.b4859 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4859
  · have he : Geometry.b4545.half 2 true=Geometry.b4860 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4860

theorem bound4256 : BoxMajorant Geometry.b4256 := by
  exact PositiveLeaves.L1987.bound

theorem bound4255 : BoxMajorant Geometry.b4255 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4255.Widths)
  · have he : Geometry.b4255.half 1 false=Geometry.b4545 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4545
  · have he : Geometry.b4255.half 1 true=Geometry.b4546 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4546

theorem bound3886 : BoxMajorant Geometry.b3886 := by
  exact PositiveLeaves.L1986.bound

theorem bound3885 : BoxMajorant Geometry.b3885 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3885.Widths)
  · have he : Geometry.b3885.half 0 false=Geometry.b4255 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4255
  · have he : Geometry.b3885.half 0 true=Geometry.b4256 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4256

theorem bound3558 : BoxMajorant Geometry.b3558 := by
  exact PositiveLeaves.L1985.bound

theorem bound3557 : BoxMajorant Geometry.b3557 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3557.Widths)
  · have he : Geometry.b3557.half 2 false=Geometry.b3885 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3885
  · have he : Geometry.b3557.half 2 true=Geometry.b3886 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3886

theorem bound3282 : BoxMajorant Geometry.b3282 := by
  exact PositiveLeaves.L1984.bound

theorem bound3281 : BoxMajorant Geometry.b3281 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3281.Widths)
  · have he : Geometry.b3281.half 1 false=Geometry.b3557 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3557
  · have he : Geometry.b3281.half 1 true=Geometry.b3558 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3558

theorem bound2949 : BoxMajorant Geometry.b2949 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2949.Widths)
  · have he : Geometry.b2949.half 0 false=Geometry.b3281 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3281
  · have he : Geometry.b2949.half 0 true=Geometry.b3282 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3282

end N7.Kernel.Cover
