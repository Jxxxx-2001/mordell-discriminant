import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0010
import N7.Kernel.CoverGeometry.G0014
import N7.Kernel.CoverGeometry.G0020
import N7.Kernel.CoverGeometry.G0029
import N7.Kernel.PositiveGroups.G0205
import N7.Kernel.PositiveGroups.G0244
import N7.Kernel.PositiveGroups.G0245
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1900 : BoxMajorant Geometry.b1900 := by
  exact PositiveLeaves.L733.bound

theorem bound1899 : BoxMajorant Geometry.b1899 := by
  exact PositiveLeaves.L734.bound

theorem bound1898 : BoxMajorant Geometry.b1898 := by
  exact PositiveLeaves.L735.bound

theorem bound1897 : BoxMajorant Geometry.b1897 := by
  exact PositiveLeaves.L736.bound

theorem bound1896 : BoxMajorant Geometry.b1896 := by
  exact PositiveLeaves.L737.bound

theorem bound1895 : BoxMajorant Geometry.b1895 := by
  exact PositiveLeaves.L738.bound

theorem bound1894 : BoxMajorant Geometry.b1894 := by
  exact PositiveLeaves.L739.bound

theorem bound1893 : BoxMajorant Geometry.b1893 := by
  exact PositiveLeaves.L740.bound

theorem bound1316 : BoxMajorant Geometry.b1316 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1316.Widths)
  · have he : Geometry.b1316.half 2 false=Geometry.b1899 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1899
  · have he : Geometry.b1316.half 2 true=Geometry.b1900 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1900

theorem bound1315 : BoxMajorant Geometry.b1315 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1315.Widths)
  · have he : Geometry.b1315.half 2 false=Geometry.b1897 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1897
  · have he : Geometry.b1315.half 2 true=Geometry.b1898 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1898

theorem bound1314 : BoxMajorant Geometry.b1314 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1314.Widths)
  · have he : Geometry.b1314.half 2 false=Geometry.b1895 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1895
  · have he : Geometry.b1314.half 2 true=Geometry.b1896 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1896

theorem bound1313 : BoxMajorant Geometry.b1313 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1313.Widths)
  · have he : Geometry.b1313.half 2 false=Geometry.b1893 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1893
  · have he : Geometry.b1313.half 2 true=Geometry.b1894 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1894

theorem bound946 : BoxMajorant Geometry.b946 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b946.Widths)
  · have he : Geometry.b946.half 1 false=Geometry.b1315 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1315
  · have he : Geometry.b946.half 1 true=Geometry.b1316 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1316

theorem bound945 : BoxMajorant Geometry.b945 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b945.Widths)
  · have he : Geometry.b945.half 1 false=Geometry.b1313 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1313
  · have he : Geometry.b945.half 1 true=Geometry.b1314 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1314

theorem bound656 : BoxMajorant Geometry.b656 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b656.Widths)
  · have he : Geometry.b656.half 0 false=Geometry.b945 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound945
  · have he : Geometry.b656.half 0 true=Geometry.b946 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound946

end N7.Kernel.Cover
