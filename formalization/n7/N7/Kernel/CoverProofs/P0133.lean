import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0010
import N7.Kernel.CoverGeometry.G0014
import N7.Kernel.CoverGeometry.G0020
import N7.Kernel.CoverGeometry.G0029
import N7.Kernel.PositiveGroups.G0118
import N7.Kernel.PositiveGroups.G0158
import N7.Kernel.PositiveGroups.G0207
import N7.Kernel.PositiveGroups.G0208
import N7.Kernel.PositiveGroups.G0209
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1870 : BoxMajorant Geometry.b1870 := by
  exact PositiveLeaves.L775.bound

theorem bound1869 : BoxMajorant Geometry.b1869 := by
  exact PositiveLeaves.L776.bound

theorem bound1868 : BoxMajorant Geometry.b1868 := by
  exact PositiveLeaves.L777.bound

theorem bound1867 : BoxMajorant Geometry.b1867 := by
  exact PositiveLeaves.L778.bound

theorem bound1866 : BoxMajorant Geometry.b1866 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1866 3 (by decide +kernel) x hx hd ho).elim

theorem bound1865 : BoxMajorant Geometry.b1865 := by
  exact PositiveLeaves.L780.bound

theorem bound1298 : BoxMajorant Geometry.b1298 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1298.Widths)
  · have he : Geometry.b1298.half 2 false=Geometry.b1869 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1869
  · have he : Geometry.b1298.half 2 true=Geometry.b1870 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1870

theorem bound1297 : BoxMajorant Geometry.b1297 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1297.Widths)
  · have he : Geometry.b1297.half 2 false=Geometry.b1867 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1867
  · have he : Geometry.b1297.half 2 true=Geometry.b1868 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1868

theorem bound1296 : BoxMajorant Geometry.b1296 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1296.Widths)
  · have he : Geometry.b1296.half 2 false=Geometry.b1865 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1865
  · have he : Geometry.b1296.half 2 true=Geometry.b1866 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1866

theorem bound1295 : BoxMajorant Geometry.b1295 := by
  exact PositiveLeaves.L781.bound

theorem bound936 : BoxMajorant Geometry.b936 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b936.Widths)
  · have he : Geometry.b936.half 1 false=Geometry.b1297 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1297
  · have he : Geometry.b936.half 1 true=Geometry.b1298 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1298

theorem bound935 : BoxMajorant Geometry.b935 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b935.Widths)
  · have he : Geometry.b935.half 1 false=Geometry.b1295 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1295
  · have he : Geometry.b935.half 1 true=Geometry.b1296 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1296

theorem bound646 : BoxMajorant Geometry.b646 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b646.Widths)
  · have he : Geometry.b646.half 0 false=Geometry.b935 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound935
  · have he : Geometry.b646.half 0 true=Geometry.b936 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound936

end N7.Kernel.Cover
