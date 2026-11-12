import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0045
import N7.Kernel.CoverGeometry.G0050
import N7.Kernel.CoverGeometry.G0055
import N7.Kernel.CoverGeometry.G0059
import N7.Kernel.PositiveGroups.G0349
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound3836 : BoxMajorant Geometry.b3836 := by
  exact PositiveLeaves.L2127.bound

theorem bound3835 : BoxMajorant Geometry.b3835 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3835 2 (by decide +kernel) x hx hd ho).elim

theorem bound3530 : BoxMajorant Geometry.b3530 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3530.Widths)
  · have he : Geometry.b3530.half 2 false=Geometry.b3835 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3835
  · have he : Geometry.b3530.half 2 true=Geometry.b3836 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3836

theorem bound3529 : BoxMajorant Geometry.b3529 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3529 2 (by decide +kernel) x hx hd ho).elim

theorem bound3256 : BoxMajorant Geometry.b3256 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3256.Widths)
  · have he : Geometry.b3256.half 1 false=Geometry.b3529 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3529
  · have he : Geometry.b3256.half 1 true=Geometry.b3530 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3530

theorem bound3255 : BoxMajorant Geometry.b3255 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3255 2 (by decide +kernel) x hx hd ho).elim

theorem bound2931 : BoxMajorant Geometry.b2931 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2931.Widths)
  · have he : Geometry.b2931.half 0 false=Geometry.b3255 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3255
  · have he : Geometry.b2931.half 0 true=Geometry.b3256 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3256

end N7.Kernel.Cover
