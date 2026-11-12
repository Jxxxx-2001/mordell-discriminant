import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0012
import N7.Kernel.CoverGeometry.G0017
import N7.Kernel.CoverGeometry.G0024
import N7.Kernel.CoverGeometry.G0034
import N7.Kernel.CoverGeometry.G0040
import N7.Kernel.CoverGeometry.G0045
import N7.Kernel.PositiveGroups.G0019
import N7.Kernel.PositiveGroups.G0039
import N7.Kernel.PositiveGroups.G0040
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2910 : BoxMajorant Geometry.b2910 := by
  exact PositiveLeaves.L2263.bound

theorem bound2909 : BoxMajorant Geometry.b2909 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2909 2 (by decide +kernel) x hx hd ho).elim

theorem bound2564 : BoxMajorant Geometry.b2564 := by
  exact PositiveLeaves.L2262.bound

theorem bound2563 : BoxMajorant Geometry.b2563 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2563.Widths)
  · have he : Geometry.b2563.half 2 false=Geometry.b2909 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2909
  · have he : Geometry.b2563.half 2 true=Geometry.b2910 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2910

theorem bound2202 : BoxMajorant Geometry.b2202 := by
  exact PositiveLeaves.L2261.bound

theorem bound2201 : BoxMajorant Geometry.b2201 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2201.Widths)
  · have he : Geometry.b2201.half 1 false=Geometry.b2563 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2563
  · have he : Geometry.b2201.half 1 true=Geometry.b2564 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2564

theorem bound1584 : BoxMajorant Geometry.b1584 := by
  exact PositiveLeaves.L2260.bound

theorem bound1583 : BoxMajorant Geometry.b1583 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1583.Widths)
  · have he : Geometry.b1583.half 0 false=Geometry.b2201 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2201
  · have he : Geometry.b1583.half 0 true=Geometry.b2202 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2202

theorem bound1126 : BoxMajorant Geometry.b1126 := by
  exact PositiveLeaves.L2259.bound

theorem bound1125 : BoxMajorant Geometry.b1125 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1125.Widths)
  · have he : Geometry.b1125.half 2 false=Geometry.b1583 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1583
  · have he : Geometry.b1125.half 2 true=Geometry.b1584 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1584

theorem bound815 : BoxMajorant Geometry.b815 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b815.Widths)
  · have he : Geometry.b815.half 1 false=Geometry.b1125 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1125
  · have he : Geometry.b815.half 1 true=Geometry.b1126 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1126

end N7.Kernel.Cover
