import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0071
import N7.Kernel.CoverGeometry.G0077
import N7.Kernel.CoverGeometry.G0081
import N7.Kernel.PositiveGroups.G0416
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5198 : BoxMajorant Geometry.b5198 := by
  exact PositiveLeaves.L1721.bound

theorem bound5197 : BoxMajorant Geometry.b5197 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5197 2 (by decide +kernel) x hx hd ho).elim

theorem bound4936 : BoxMajorant Geometry.b4936 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4936.Widths)
  · have he : Geometry.b4936.half 0 false=Geometry.b5197 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5197
  · have he : Geometry.b4936.half 0 true=Geometry.b5198 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5198

theorem bound4935 : BoxMajorant Geometry.b4935 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4935 2 (by decide +kernel) x hx hd ho).elim

theorem bound4592 : BoxMajorant Geometry.b4592 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4592.Widths)
  · have he : Geometry.b4592.half 2 false=Geometry.b4935 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4935
  · have he : Geometry.b4592.half 2 true=Geometry.b4936 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4936

end N7.Kernel.Cover
