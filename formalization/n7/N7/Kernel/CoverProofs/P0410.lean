import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0087
import N7.Kernel.CoverGeometry.G0088
import N7.Kernel.CoverGeometry.G0089
import N7.Kernel.CoverGeometry.G0090
import N7.Kernel.PositiveGroups.G0478
import N7.Kernel.PositiveGroups.G0483
import N7.Kernel.PositiveGroups.G0484
import N7.Kernel.PositiveGroups.G0486
import N7.Kernel.PositiveGroups.G0487
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5764 : BoxMajorant Geometry.b5764 := by
  exact PositiveLeaves.L413.bound

theorem bound5763 : BoxMajorant Geometry.b5763 := by
  exact PositiveLeaves.L414.bound

theorem bound5762 : BoxMajorant Geometry.b5762 := by
  exact PositiveLeaves.L415.bound

theorem bound5761 : BoxMajorant Geometry.b5761 := by
  exact PositiveLeaves.L416.bound

theorem bound5712 : BoxMajorant Geometry.b5712 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5712.Widths)
  · have he : Geometry.b5712.half 2 false=Geometry.b5763 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5763
  · have he : Geometry.b5712.half 2 true=Geometry.b5764 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5764

theorem bound5711 : BoxMajorant Geometry.b5711 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5711.Widths)
  · have he : Geometry.b5711.half 2 false=Geometry.b5761 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5761
  · have he : Geometry.b5711.half 2 true=Geometry.b5762 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5762

theorem bound5682 : BoxMajorant Geometry.b5682 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5682.Widths)
  · have he : Geometry.b5682.half 1 false=Geometry.b5711 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5711
  · have he : Geometry.b5682.half 1 true=Geometry.b5712 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5712

theorem bound5681 : BoxMajorant Geometry.b5681 := by
  exact PositiveLeaves.L417.bound

theorem bound5644 : BoxMajorant Geometry.b5644 := by
  exact PositiveLeaves.L412.bound

theorem bound5643 : BoxMajorant Geometry.b5643 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5643.Widths)
  · have he : Geometry.b5643.half 0 false=Geometry.b5681 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5681
  · have he : Geometry.b5643.half 0 true=Geometry.b5682 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5682

theorem bound5606 : BoxMajorant Geometry.b5606 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5606.Widths)
  · have he : Geometry.b5606.half 2 false=Geometry.b5643 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5643
  · have he : Geometry.b5606.half 2 true=Geometry.b5644 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5644

theorem bound5605 : BoxMajorant Geometry.b5605 := by
  exact PositiveLeaves.L418.bound

theorem bound5577 : BoxMajorant Geometry.b5577 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5577.Widths)
  · have he : Geometry.b5577.half 1 false=Geometry.b5605 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5605
  · have he : Geometry.b5577.half 1 true=Geometry.b5606 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5606

end N7.Kernel.Cover
