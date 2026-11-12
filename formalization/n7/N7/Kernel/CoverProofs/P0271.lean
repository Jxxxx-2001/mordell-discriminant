import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0046
import N7.Kernel.CoverGeometry.G0052
import N7.Kernel.CoverGeometry.G0056
import N7.Kernel.CoverGeometry.G0062
import N7.Kernel.CoverGeometry.G0067
import N7.Kernel.CoverGeometry.G0072
import N7.Kernel.CoverGeometry.G0077
import N7.Kernel.PositiveGroups.G0288
import N7.Kernel.PositiveGroups.G0289
import N7.Kernel.PositiveGroups.G0312
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4966 : BoxMajorant Geometry.b4966 := by
  exact PositiveLeaves.L1660.bound

theorem bound4965 : BoxMajorant Geometry.b4965 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4965 2 (by decide +kernel) x hx hd ho).elim

theorem bound4614 : BoxMajorant Geometry.b4614 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4614.Widths)
  · have he : Geometry.b4614.half 2 false=Geometry.b4965 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4965
  · have he : Geometry.b4614.half 2 true=Geometry.b4966 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4966

theorem bound4613 : BoxMajorant Geometry.b4613 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4613 2 (by decide +kernel) x hx hd ho).elim

theorem bound4342 : BoxMajorant Geometry.b4342 := by
  exact PositiveLeaves.L1659.bound

theorem bound4341 : BoxMajorant Geometry.b4341 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4341.Widths)
  · have he : Geometry.b4341.half 1 false=Geometry.b4613 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4613
  · have he : Geometry.b4341.half 1 true=Geometry.b4614 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4614

theorem bound3984 : BoxMajorant Geometry.b3984 := by
  exact PositiveLeaves.L1657.bound

theorem bound3983 : BoxMajorant Geometry.b3983 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3983 2 (by decide +kernel) x hx hd ho).elim

theorem bound3982 : BoxMajorant Geometry.b3982 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3982.Widths)
  · have he : Geometry.b3982.half 0 false=Geometry.b4341 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4341
  · have he : Geometry.b3982.half 0 true=Geometry.b4342 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4342

theorem bound3981 : BoxMajorant Geometry.b3981 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3981 2 (by decide +kernel) x hx hd ho).elim

theorem bound3614 : BoxMajorant Geometry.b3614 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3614.Widths)
  · have he : Geometry.b3614.half 2 false=Geometry.b3983 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3983
  · have he : Geometry.b3614.half 2 true=Geometry.b3984 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3984

theorem bound3613 : BoxMajorant Geometry.b3613 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3613.Widths)
  · have he : Geometry.b3613.half 2 false=Geometry.b3981 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3981
  · have he : Geometry.b3613.half 2 true=Geometry.b3982 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3982

theorem bound3342 : BoxMajorant Geometry.b3342 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3342.Widths)
  · have he : Geometry.b3342.half 1 false=Geometry.b3613 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3613
  · have he : Geometry.b3342.half 1 true=Geometry.b3614 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3614

theorem bound3341 : BoxMajorant Geometry.b3341 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3341 2 (by decide +kernel) x hx hd ho).elim

theorem bound3002 : BoxMajorant Geometry.b3002 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3002.Widths)
  · have he : Geometry.b3002.half 0 false=Geometry.b3341 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3341
  · have he : Geometry.b3002.half 0 true=Geometry.b3342 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3342

end N7.Kernel.Cover
