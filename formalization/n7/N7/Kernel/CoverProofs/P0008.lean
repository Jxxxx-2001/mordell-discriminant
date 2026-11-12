import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0000
import N7.Kernel.CoverGeometry.G0001
import N7.Kernel.CoverGeometry.G0002
import N7.Kernel.CoverGeometry.G0003
import N7.Kernel.CoverGeometry.G0005
import N7.Kernel.CoverGeometry.G0009
import N7.Kernel.CoverGeometry.G0013
import N7.Kernel.CoverGeometry.G0018
import N7.Kernel.CoverGeometry.G0025
import N7.Kernel.CoverGeometry.G0035
import N7.Kernel.CoverGeometry.G0041
import N7.Kernel.PositiveGroups.G0143
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2648 : BoxMajorant Geometry.b2648 := by
  exact PositiveLeaves.L1348.bound

theorem bound2647 : BoxMajorant Geometry.b2647 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2647 0 (by decide +kernel) x hx hd ho).elim

theorem bound2276 : BoxMajorant Geometry.b2276 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2276 0 (by decide +kernel) x hx hd ho).elim

theorem bound2275 : BoxMajorant Geometry.b2275 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2275.Widths)
  · have he : Geometry.b2275.half 1 false=Geometry.b2647 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2647
  · have he : Geometry.b2275.half 1 true=Geometry.b2648 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2648

theorem bound1660 : BoxMajorant Geometry.b1660 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1660.Widths)
  · have he : Geometry.b1660.half 0 false=Geometry.b2275 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2275
  · have he : Geometry.b1660.half 0 true=Geometry.b2276 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2276

theorem bound1659 : BoxMajorant Geometry.b1659 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1659 2 (by decide +kernel) x hx hd ho).elim

theorem bound1168 : BoxMajorant Geometry.b1168 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1168.Widths)
  · have he : Geometry.b1168.half 2 false=Geometry.b1659 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1659
  · have he : Geometry.b1168.half 2 true=Geometry.b1660 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1660

theorem bound1167 : BoxMajorant Geometry.b1167 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1167 0 (by decide +kernel) x hx hd ho).elim

theorem bound852 : BoxMajorant Geometry.b852 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b852 0 (by decide +kernel) x hx hd ho).elim

theorem bound851 : BoxMajorant Geometry.b851 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b851.Widths)
  · have he : Geometry.b851.half 1 false=Geometry.b1167 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1167
  · have he : Geometry.b851.half 1 true=Geometry.b1168 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1168

theorem bound578 : BoxMajorant Geometry.b578 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b578.Widths)
  · have he : Geometry.b578.half 0 false=Geometry.b851 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound851
  · have he : Geometry.b578.half 0 true=Geometry.b852 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound852

theorem bound577 : BoxMajorant Geometry.b577 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b577 2 (by decide +kernel) x hx hd ho).elim

theorem bound368 : BoxMajorant Geometry.b368 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b368.Widths)
  · have he : Geometry.b368.half 2 false=Geometry.b577 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound577
  · have he : Geometry.b368.half 2 true=Geometry.b578 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound578

theorem bound367 : BoxMajorant Geometry.b367 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b367 0 (by decide +kernel) x hx hd ho).elim

theorem bound232 : BoxMajorant Geometry.b232 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b232 0 (by decide +kernel) x hx hd ho).elim

theorem bound231 : BoxMajorant Geometry.b231 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b231.Widths)
  · have he : Geometry.b231.half 1 false=Geometry.b367 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound367
  · have he : Geometry.b231.half 1 true=Geometry.b368 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound368

theorem bound136 : BoxMajorant Geometry.b136 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b136.Widths)
  · have he : Geometry.b136.half 0 false=Geometry.b231 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound231
  · have he : Geometry.b136.half 0 true=Geometry.b232 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound232

theorem bound135 : BoxMajorant Geometry.b135 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b135 2 (by decide +kernel) x hx hd ho).elim

theorem bound76 : BoxMajorant Geometry.b76 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b76.Widths)
  · have he : Geometry.b76.half 2 false=Geometry.b135 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound135
  · have he : Geometry.b76.half 2 true=Geometry.b136 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound136

theorem bound75 : BoxMajorant Geometry.b75 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b75 0 (by decide +kernel) x hx hd ho).elim

theorem bound39 : BoxMajorant Geometry.b39 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b39.Widths)
  · have he : Geometry.b39.half 1 false=Geometry.b75 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound75
  · have he : Geometry.b39.half 1 true=Geometry.b76 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound76

end N7.Kernel.Cover
