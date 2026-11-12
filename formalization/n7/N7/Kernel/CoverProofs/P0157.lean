import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0010
import N7.Kernel.CoverGeometry.G0015
import N7.Kernel.CoverGeometry.G0021
import N7.Kernel.CoverGeometry.G0031
import N7.Kernel.PositiveGroups.G0097
import N7.Kernel.PositiveGroups.G0098
import N7.Kernel.PositiveGroups.G0140
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2010 : BoxMajorant Geometry.b2010 := by
  exact PositiveLeaves.L507.bound

theorem bound2009 : BoxMajorant Geometry.b2009 := by
  exact PositiveLeaves.L508.bound

theorem bound2008 : BoxMajorant Geometry.b2008 := by
  exact PositiveLeaves.L510.bound

theorem bound2007 : BoxMajorant Geometry.b2007 := by
  exact PositiveLeaves.L511.bound

theorem bound1386 : BoxMajorant Geometry.b1386 := by
  exact PositiveLeaves.L506.bound

theorem bound1385 : BoxMajorant Geometry.b1385 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1385.Widths)
  · have he : Geometry.b1385.half 2 false=Geometry.b2009 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2009
  · have he : Geometry.b1385.half 2 true=Geometry.b2010 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2010

theorem bound1384 : BoxMajorant Geometry.b1384 := by
  exact PositiveLeaves.L509.bound

theorem bound1383 : BoxMajorant Geometry.b1383 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1383.Widths)
  · have he : Geometry.b1383.half 2 false=Geometry.b2007 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2007
  · have he : Geometry.b1383.half 2 true=Geometry.b2008 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2008

theorem bound986 : BoxMajorant Geometry.b986 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b986.Widths)
  · have he : Geometry.b986.half 1 false=Geometry.b1385 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1385
  · have he : Geometry.b986.half 1 true=Geometry.b1386 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1386

theorem bound985 : BoxMajorant Geometry.b985 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b985.Widths)
  · have he : Geometry.b985.half 1 false=Geometry.b1383 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1383
  · have he : Geometry.b985.half 1 true=Geometry.b1384 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1384

theorem bound690 : BoxMajorant Geometry.b690 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b690.Widths)
  · have he : Geometry.b690.half 0 false=Geometry.b985 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound985
  · have he : Geometry.b690.half 0 true=Geometry.b986 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound986

end N7.Kernel.Cover
