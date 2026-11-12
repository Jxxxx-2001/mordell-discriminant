import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0010
import N7.Kernel.CoverGeometry.G0014
import N7.Kernel.CoverGeometry.G0020
import N7.Kernel.CoverGeometry.G0029
import N7.Kernel.PositiveGroups.G0157
import N7.Kernel.PositiveGroups.G0203
import N7.Kernel.PositiveGroups.G0204
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1892 : BoxMajorant Geometry.b1892 := by
  exact PositiveLeaves.L745.bound

theorem bound1891 : BoxMajorant Geometry.b1891 := by
  exact PositiveLeaves.L746.bound

theorem bound1890 : BoxMajorant Geometry.b1890 := by
  exact PositiveLeaves.L747.bound

theorem bound1889 : BoxMajorant Geometry.b1889 := by
  exact PositiveLeaves.L748.bound

theorem bound1888 : BoxMajorant Geometry.b1888 := by
  exact PositiveLeaves.L749.bound

theorem bound1887 : BoxMajorant Geometry.b1887 := by
  exact PositiveLeaves.L750.bound

theorem bound1312 : BoxMajorant Geometry.b1312 := by
  exact PositiveLeaves.L744.bound

theorem bound1311 : BoxMajorant Geometry.b1311 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1311.Widths)
  · have he : Geometry.b1311.half 2 false=Geometry.b1891 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1891
  · have he : Geometry.b1311.half 2 true=Geometry.b1892 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1892

theorem bound1310 : BoxMajorant Geometry.b1310 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1310.Widths)
  · have he : Geometry.b1310.half 2 false=Geometry.b1889 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1889
  · have he : Geometry.b1310.half 2 true=Geometry.b1890 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1890

theorem bound1309 : BoxMajorant Geometry.b1309 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1309.Widths)
  · have he : Geometry.b1309.half 2 false=Geometry.b1887 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1887
  · have he : Geometry.b1309.half 2 true=Geometry.b1888 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1888

theorem bound944 : BoxMajorant Geometry.b944 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b944.Widths)
  · have he : Geometry.b944.half 1 false=Geometry.b1311 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1311
  · have he : Geometry.b944.half 1 true=Geometry.b1312 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1312

theorem bound943 : BoxMajorant Geometry.b943 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b943.Widths)
  · have he : Geometry.b943.half 1 false=Geometry.b1309 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1309
  · have he : Geometry.b943.half 1 true=Geometry.b1310 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1310

theorem bound652 : BoxMajorant Geometry.b652 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b652.Widths)
  · have he : Geometry.b652.half 0 false=Geometry.b943 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound943
  · have he : Geometry.b652.half 0 true=Geometry.b944 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound944

end N7.Kernel.Cover
