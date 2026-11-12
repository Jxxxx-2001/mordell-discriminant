import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0009
import N7.Kernel.CoverGeometry.G0014
import N7.Kernel.CoverGeometry.G0019
import N7.Kernel.CoverGeometry.G0028
import N7.Kernel.PositiveGroups.G0124
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1826 : BoxMajorant Geometry.b1826 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1826 3 (by decide +kernel) x hx hd ho).elim

theorem bound1825 : BoxMajorant Geometry.b1825 := by
  exact PositiveLeaves.L843.bound

theorem bound1824 : BoxMajorant Geometry.b1824 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1824 3 (by decide +kernel) x hx hd ho).elim

theorem bound1823 : BoxMajorant Geometry.b1823 := by
  exact PositiveLeaves.L845.bound

theorem bound1268 : BoxMajorant Geometry.b1268 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1268.Widths)
  · have he : Geometry.b1268.half 2 false=Geometry.b1825 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1825
  · have he : Geometry.b1268.half 2 true=Geometry.b1826 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1826

theorem bound1267 : BoxMajorant Geometry.b1267 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1267.Widths)
  · have he : Geometry.b1267.half 2 false=Geometry.b1823 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1823
  · have he : Geometry.b1267.half 2 true=Geometry.b1824 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1824

theorem bound916 : BoxMajorant Geometry.b916 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b916.Widths)
  · have he : Geometry.b916.half 1 false=Geometry.b1267 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1267
  · have he : Geometry.b916.half 1 true=Geometry.b1268 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1268

theorem bound915 : BoxMajorant Geometry.b915 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b915 3 (by decide +kernel) x hx hd ho).elim

theorem bound627 : BoxMajorant Geometry.b627 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b627.Widths)
  · have he : Geometry.b627.half 0 false=Geometry.b915 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound915
  · have he : Geometry.b627.half 0 true=Geometry.b916 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound916

end N7.Kernel.Cover
