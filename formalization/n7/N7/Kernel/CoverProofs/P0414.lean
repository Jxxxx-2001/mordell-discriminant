import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0087
import N7.Kernel.CoverGeometry.G0088
import N7.Kernel.CoverGeometry.G0089
import N7.Kernel.CoverGeometry.G0090
import N7.Kernel.CoverGeometry.G0091
import N7.Kernel.PositiveGroups.G0482
import N7.Kernel.PositiveGroups.G0485
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5826 : BoxMajorant Geometry.b5826 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5826 0 (by decide +kernel) x hx hd ho).elim

theorem bound5825 : BoxMajorant Geometry.b5825 := by
  exact PositiveLeaves.L351.bound

theorem bound5786 : BoxMajorant Geometry.b5786 := by
  exact PositiveLeaves.L349.bound

theorem bound5785 : BoxMajorant Geometry.b5785 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5785.Widths)
  · have he : Geometry.b5785.half 0 false=Geometry.b5825 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5825
  · have he : Geometry.b5785.half 0 true=Geometry.b5826 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5826

theorem bound5728 : BoxMajorant Geometry.b5728 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5728.Widths)
  · have he : Geometry.b5728.half 2 false=Geometry.b5785 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5785
  · have he : Geometry.b5728.half 2 true=Geometry.b5786 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5786

theorem bound5727 : BoxMajorant Geometry.b5727 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5727 0 (by decide +kernel) x hx hd ho).elim

theorem bound5692 : BoxMajorant Geometry.b5692 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5692 0 (by decide +kernel) x hx hd ho).elim

theorem bound5691 : BoxMajorant Geometry.b5691 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5691.Widths)
  · have he : Geometry.b5691.half 1 false=Geometry.b5727 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5727
  · have he : Geometry.b5691.half 1 true=Geometry.b5728 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5728

theorem bound5658 : BoxMajorant Geometry.b5658 := by
  exact PositiveLeaves.L347.bound

theorem bound5657 : BoxMajorant Geometry.b5657 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5657.Widths)
  · have he : Geometry.b5657.half 0 false=Geometry.b5691 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5691
  · have he : Geometry.b5657.half 0 true=Geometry.b5692 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5692

theorem bound5614 : BoxMajorant Geometry.b5614 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5614.Widths)
  · have he : Geometry.b5614.half 2 false=Geometry.b5657 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5657
  · have he : Geometry.b5614.half 2 true=Geometry.b5658 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5658

end N7.Kernel.Cover
