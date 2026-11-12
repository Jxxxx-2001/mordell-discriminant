import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0012
import N7.Kernel.CoverGeometry.G0017
import N7.Kernel.CoverGeometry.G0024
import N7.Kernel.CoverGeometry.G0034
import N7.Kernel.CoverGeometry.G0039
import N7.Kernel.CoverGeometry.G0045
import N7.Kernel.PositiveGroups.G0040
import N7.Kernel.PositiveGroups.G0066
import N7.Kernel.PositiveGroups.G0102
import N7.Kernel.PositiveGroups.G0142
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2888 : BoxMajorant Geometry.b2888 := by
  exact PositiveLeaves.L2324.bound

theorem bound2887 : BoxMajorant Geometry.b2887 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2887 2 (by decide +kernel) x hx hd ho).elim

theorem bound2546 : BoxMajorant Geometry.b2546 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2546.Widths)
  · have he : Geometry.b2546.half 2 false=Geometry.b2887 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2887
  · have he : Geometry.b2546.half 2 true=Geometry.b2888 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2888

theorem bound2545 : BoxMajorant Geometry.b2545 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2545 2 (by decide +kernel) x hx hd ho).elim

theorem bound2186 : BoxMajorant Geometry.b2186 := by
  exact PositiveLeaves.L2323.bound

theorem bound2185 : BoxMajorant Geometry.b2185 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2185.Widths)
  · have he : Geometry.b2185.half 1 false=Geometry.b2545 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2545
  · have he : Geometry.b2185.half 1 true=Geometry.b2546 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2546

theorem bound1566 : BoxMajorant Geometry.b1566 := by
  exact PositiveLeaves.L2322.bound

theorem bound1565 : BoxMajorant Geometry.b1565 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1565.Widths)
  · have he : Geometry.b1565.half 0 false=Geometry.b2185 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2185
  · have he : Geometry.b1565.half 0 true=Geometry.b2186 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2186

theorem bound1114 : BoxMajorant Geometry.b1114 := by
  exact PositiveLeaves.L2321.bound

theorem bound1113 : BoxMajorant Geometry.b1113 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1113.Widths)
  · have he : Geometry.b1113.half 2 false=Geometry.b1565 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1565
  · have he : Geometry.b1113.half 2 true=Geometry.b1566 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1566

theorem bound808 : BoxMajorant Geometry.b808 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b808.Widths)
  · have he : Geometry.b808.half 1 false=Geometry.b1113 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1113
  · have he : Geometry.b808.half 1 true=Geometry.b1114 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1114

end N7.Kernel.Cover
