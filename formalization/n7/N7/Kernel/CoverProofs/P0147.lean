import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0010
import N7.Kernel.CoverGeometry.G0015
import N7.Kernel.CoverGeometry.G0021
import N7.Kernel.CoverGeometry.G0030
import N7.Kernel.PositiveGroups.G0196
import N7.Kernel.PositiveGroups.G0235
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1962 : BoxMajorant Geometry.b1962 := by
  exact PositiveLeaves.L600.bound

theorem bound1961 : BoxMajorant Geometry.b1961 := by
  exact PositiveLeaves.L601.bound

theorem bound1960 : BoxMajorant Geometry.b1960 := by
  exact PositiveLeaves.L602.bound

theorem bound1959 : BoxMajorant Geometry.b1959 := by
  exact PositiveLeaves.L603.bound

theorem bound1958 : BoxMajorant Geometry.b1958 := by
  exact PositiveLeaves.L604.bound

theorem bound1957 : BoxMajorant Geometry.b1957 := by
  exact PositiveLeaves.L605.bound

theorem bound1956 : BoxMajorant Geometry.b1956 := by
  exact PositiveLeaves.L606.bound

theorem bound1955 : BoxMajorant Geometry.b1955 := by
  exact PositiveLeaves.L607.bound

theorem bound1350 : BoxMajorant Geometry.b1350 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1350.Widths)
  · have he : Geometry.b1350.half 2 false=Geometry.b1961 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1961
  · have he : Geometry.b1350.half 2 true=Geometry.b1962 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1962

theorem bound1349 : BoxMajorant Geometry.b1349 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1349.Widths)
  · have he : Geometry.b1349.half 2 false=Geometry.b1959 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1959
  · have he : Geometry.b1349.half 2 true=Geometry.b1960 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1960

theorem bound1348 : BoxMajorant Geometry.b1348 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1348.Widths)
  · have he : Geometry.b1348.half 2 false=Geometry.b1957 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1957
  · have he : Geometry.b1348.half 2 true=Geometry.b1958 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1958

theorem bound1347 : BoxMajorant Geometry.b1347 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1347.Widths)
  · have he : Geometry.b1347.half 2 false=Geometry.b1955 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1955
  · have he : Geometry.b1347.half 2 true=Geometry.b1956 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1956

theorem bound964 : BoxMajorant Geometry.b964 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b964.Widths)
  · have he : Geometry.b964.half 1 false=Geometry.b1349 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1349
  · have he : Geometry.b964.half 1 true=Geometry.b1350 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1350

theorem bound963 : BoxMajorant Geometry.b963 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b963.Widths)
  · have he : Geometry.b963.half 1 false=Geometry.b1347 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1347
  · have he : Geometry.b963.half 1 true=Geometry.b1348 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1348

theorem bound670 : BoxMajorant Geometry.b670 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b670.Widths)
  · have he : Geometry.b670.half 0 false=Geometry.b963 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound963
  · have he : Geometry.b670.half 0 true=Geometry.b964 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound964

end N7.Kernel.Cover
