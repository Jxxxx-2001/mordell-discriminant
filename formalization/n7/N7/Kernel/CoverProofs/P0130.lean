import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0010
import N7.Kernel.CoverGeometry.G0014
import N7.Kernel.CoverGeometry.G0020
import N7.Kernel.CoverGeometry.G0028
import N7.Kernel.PositiveGroups.G0119
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1852 : BoxMajorant Geometry.b1852 := by
  exact PositiveLeaves.L798.bound

theorem bound1851 : BoxMajorant Geometry.b1851 := by
  exact PositiveLeaves.L799.bound

theorem bound1850 : BoxMajorant Geometry.b1850 := by
  exact PositiveLeaves.L800.bound

theorem bound1849 : BoxMajorant Geometry.b1849 := by
  exact PositiveLeaves.L801.bound

theorem bound1286 : BoxMajorant Geometry.b1286 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1286.Widths)
  · have he : Geometry.b1286.half 2 false=Geometry.b1851 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1851
  · have he : Geometry.b1286.half 2 true=Geometry.b1852 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1852

theorem bound1285 : BoxMajorant Geometry.b1285 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1285.Widths)
  · have he : Geometry.b1285.half 2 false=Geometry.b1849 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1849
  · have he : Geometry.b1285.half 2 true=Geometry.b1850 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1850

theorem bound930 : BoxMajorant Geometry.b930 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b930.Widths)
  · have he : Geometry.b930.half 1 false=Geometry.b1285 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1285
  · have he : Geometry.b930.half 1 true=Geometry.b1286 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1286

theorem bound929 : BoxMajorant Geometry.b929 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b929 3 (by decide +kernel) x hx hd ho).elim

theorem bound641 : BoxMajorant Geometry.b641 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b641.Widths)
  · have he : Geometry.b641.half 0 false=Geometry.b929 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound929
  · have he : Geometry.b641.half 0 true=Geometry.b930 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound930

end N7.Kernel.Cover
