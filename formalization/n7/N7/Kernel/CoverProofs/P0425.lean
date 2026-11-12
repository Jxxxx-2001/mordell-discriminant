import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.LocalBridge
import N7.Kernel.CoverGeometry.G0092
import N7.Kernel.Local.C1LargeMajorant
import N7.Kernel.PositiveGroups.G0506
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5936 : BoxMajorant Geometry.b5936 := by
  exact PositiveLeaves.L336.bound

theorem bound5935 : BoxMajorant Geometry.b5935 := by
  intro x hx hd _
  have hn := nearCheck_sound Geometry.b5935 Local.C1.center Local.C1.largeRadius (by decide +kernel) hx
  simpa only [GapAnalytic.distance,GapAnalytic.eval3] using Local.C1.large_near_majorant hn

theorem bound5934 : BoxMajorant Geometry.b5934 := by
  exact PositiveLeaves.L338.bound

theorem bound5933 : BoxMajorant Geometry.b5933 := by
  intro x hx hd _
  have hn := nearCheck_sound Geometry.b5933 Local.C1.center Local.C1.largeRadius (by decide +kernel) hx
  simpa only [GapAnalytic.distance,GapAnalytic.eval3] using Local.C1.large_near_majorant hn

theorem bound5928 : BoxMajorant Geometry.b5928 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5928.Widths)
  · have he : Geometry.b5928.half 1 false=Geometry.b5935 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5935
  · have he : Geometry.b5928.half 1 true=Geometry.b5936 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5936

theorem bound5927 : BoxMajorant Geometry.b5927 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5927.Widths)
  · have he : Geometry.b5927.half 1 false=Geometry.b5933 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5933
  · have he : Geometry.b5927.half 1 true=Geometry.b5934 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5934

theorem bound5909 : BoxMajorant Geometry.b5909 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5909.Widths)
  · have he : Geometry.b5909.half 0 false=Geometry.b5927 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5927
  · have he : Geometry.b5909.half 0 true=Geometry.b5928 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5928

end N7.Kernel.Cover
