import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0071
import N7.Kernel.CoverGeometry.G0077
import N7.Kernel.CoverGeometry.G0081
import N7.Kernel.PositiveGroups.G0435
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5206 : BoxMajorant Geometry.b5206 := by
  exact PositiveLeaves.L1705.bound

theorem bound5205 : BoxMajorant Geometry.b5205 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5205 2 (by decide +kernel) x hx hd ho).elim

theorem bound4946 : BoxMajorant Geometry.b4946 := by
  exact PositiveLeaves.L1704.bound

theorem bound4945 : BoxMajorant Geometry.b4945 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4945.Widths)
  · have he : Geometry.b4945.half 0 false=Geometry.b5205 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5205
  · have he : Geometry.b4945.half 0 true=Geometry.b5206 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5206

theorem bound4597 : BoxMajorant Geometry.b4597 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4597.Widths)
  · have he : Geometry.b4597.half 2 false=Geometry.b4945 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4945
  · have he : Geometry.b4597.half 2 true=Geometry.b4946 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4946

end N7.Kernel.Cover
