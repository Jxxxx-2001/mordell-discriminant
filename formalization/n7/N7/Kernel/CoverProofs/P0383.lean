import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0090
import N7.Kernel.CoverGeometry.G0091
import N7.Kernel.PositiveGroups.G0463
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5882 : BoxMajorant Geometry.b5882 := by
  exact PositiveLeaves.L1270.bound

theorem bound5881 : BoxMajorant Geometry.b5881 := by
  exact PositiveLeaves.L1271.bound

theorem bound5844 : BoxMajorant Geometry.b5844 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5844.Widths)
  · have he : Geometry.b5844.half 2 false=Geometry.b5881 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5881
  · have he : Geometry.b5844.half 2 true=Geometry.b5882 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5882

theorem bound5843 : BoxMajorant Geometry.b5843 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5843 0 (by decide +kernel) x hx hd ho).elim

theorem bound5811 : BoxMajorant Geometry.b5811 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5811.Widths)
  · have he : Geometry.b5811.half 1 false=Geometry.b5843 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5843
  · have he : Geometry.b5811.half 1 true=Geometry.b5844 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5844

end N7.Kernel.Cover
