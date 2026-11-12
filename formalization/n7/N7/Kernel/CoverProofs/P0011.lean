import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0000
import N7.Kernel.CoverGeometry.G0001
import N7.Kernel.CoverGeometry.G0002
import N7.Kernel.CoverGeometry.G0003
import N7.Kernel.CoverGeometry.G0005
import N7.Kernel.CoverGeometry.G0009
import N7.Kernel.PositiveGroups.FourPilot
import N7.Kernel.PositiveGroups.G0001
import N7.Kernel.PositiveGroups.G0003
import N7.Kernel.PositiveGroups.G0007
import N7.Kernel.PositiveGroups.G0014
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound584 : BoxMajorant Geometry.b584 := by
  exact PositiveLeaves.L1237.bound

theorem bound583 : BoxMajorant Geometry.b583 := by
  exact PositiveLeaves.L1238.bound

theorem bound376 : BoxMajorant Geometry.b376 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b376.Widths)
  · have he : Geometry.b376.half 2 false=Geometry.b583 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound583
  · have he : Geometry.b376.half 2 true=Geometry.b584 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound584

theorem bound375 : BoxMajorant Geometry.b375 := by
  exact PositiveLeaves.L1239.bound

theorem bound242 : BoxMajorant Geometry.b242 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b242.Widths)
  · have he : Geometry.b242.half 1 false=Geometry.b375 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound375
  · have he : Geometry.b242.half 1 true=Geometry.b376 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound376

theorem bound241 : BoxMajorant Geometry.b241 := by
  exact PositiveLeaves.L1240.bound

theorem bound142 : BoxMajorant Geometry.b142 := by
  exact PositiveLeaves.L1236.bound

theorem bound141 : BoxMajorant Geometry.b141 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b141.Widths)
  · have he : Geometry.b141.half 0 false=Geometry.b241 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound241
  · have he : Geometry.b141.half 0 true=Geometry.b242 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound242

theorem bound82 : BoxMajorant Geometry.b82 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b82.Widths)
  · have he : Geometry.b82.half 2 false=Geometry.b141 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound141
  · have he : Geometry.b82.half 2 true=Geometry.b142 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound142

theorem bound81 : BoxMajorant Geometry.b81 := by
  exact PositiveLeaves.L1241.bound

theorem bound44 : BoxMajorant Geometry.b44 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b44.Widths)
  · have he : Geometry.b44.half 1 false=Geometry.b81 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound81
  · have he : Geometry.b44.half 1 true=Geometry.b82 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound82

end N7.Kernel.Cover
