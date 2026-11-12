import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.LocalBridge
import N7.Kernel.CoverGeometry.G0090
import N7.Kernel.CoverGeometry.G0091
import N7.Kernel.CoverGeometry.G0092
import N7.Kernel.Local.C3LargeMajorant
import N7.Kernel.PositiveGroups.G0463
import N7.Kernel.PositiveGroups.G0471
import N7.Kernel.PositiveGroups.G0472
import N7.Kernel.PositiveGroups.G0480
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5940 : BoxMajorant Geometry.b5940 := by
  exact PositiveLeaves.L1280.bound

theorem bound5939 : BoxMajorant Geometry.b5939 := by
  intro x hx hd _
  have hn := nearCheck_sound Geometry.b5939 Local.C3.center Local.C3.largeRadius (by decide +kernel) hx
  simpa only [GapAnalytic.distance,GapAnalytic.eval3] using Local.C3.large_near_majorant hn hd.2.2.2.2.1

theorem bound5932 : BoxMajorant Geometry.b5932 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5932.Widths)
  · have he : Geometry.b5932.half 2 false=Geometry.b5939 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5939
  · have he : Geometry.b5932.half 2 true=Geometry.b5940 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5940

theorem bound5931 : BoxMajorant Geometry.b5931 := by
  exact PositiveLeaves.L1282.bound

theorem bound5926 : BoxMajorant Geometry.b5926 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5926.Widths)
  · have he : Geometry.b5926.half 1 false=Geometry.b5931 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5931
  · have he : Geometry.b5926.half 1 true=Geometry.b5932 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5932

theorem bound5925 : BoxMajorant Geometry.b5925 := by
  exact PositiveLeaves.L1283.bound

theorem bound5878 : BoxMajorant Geometry.b5878 := by
  exact PositiveLeaves.L1279.bound

theorem bound5877 : BoxMajorant Geometry.b5877 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5877.Widths)
  · have he : Geometry.b5877.half 0 false=Geometry.b5925 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5925
  · have he : Geometry.b5877.half 0 true=Geometry.b5926 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5926

theorem bound5840 : BoxMajorant Geometry.b5840 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5840.Widths)
  · have he : Geometry.b5840.half 2 false=Geometry.b5877 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5877
  · have he : Geometry.b5840.half 2 true=Geometry.b5878 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5878

theorem bound5839 : BoxMajorant Geometry.b5839 := by
  exact PositiveLeaves.L1284.bound

theorem bound5808 : BoxMajorant Geometry.b5808 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5808.Widths)
  · have he : Geometry.b5808.half 1 false=Geometry.b5839 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5839
  · have he : Geometry.b5808.half 1 true=Geometry.b5840 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5840

end N7.Kernel.Cover
