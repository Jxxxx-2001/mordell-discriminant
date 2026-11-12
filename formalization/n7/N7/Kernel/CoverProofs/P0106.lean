import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0009
import N7.Kernel.CoverGeometry.G0013
import N7.Kernel.CoverGeometry.G0014
import N7.Kernel.CoverGeometry.G0019
import N7.Kernel.CoverGeometry.G0027
import N7.Kernel.CoverGeometry.G0036
import N7.Kernel.PositiveGroups.G0056
import N7.Kernel.PositiveGroups.G0126
import N7.Kernel.PositiveGroups.G0127
import N7.Kernel.PositiveGroups.G0164
import N7.Kernel.PositiveGroups.G0165
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2310 : BoxMajorant Geometry.b2310 := by
  exact PositiveLeaves.L1056.bound

theorem bound2309 : BoxMajorant Geometry.b2309 := by
  exact PositiveLeaves.L1057.bound

theorem bound2308 : BoxMajorant Geometry.b2308 := by
  exact PositiveLeaves.L1059.bound

theorem bound2307 : BoxMajorant Geometry.b2307 := by
  exact PositiveLeaves.L1060.bound

theorem bound1762 : BoxMajorant Geometry.b1762 := by
  exact PositiveLeaves.L1053.bound

theorem bound1761 : BoxMajorant Geometry.b1761 := by
  exact PositiveLeaves.L1054.bound

theorem bound1760 : BoxMajorant Geometry.b1760 := by
  exact PositiveLeaves.L1055.bound

theorem bound1759 : BoxMajorant Geometry.b1759 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1759.Widths)
  · have he : Geometry.b1759.half 0 false=Geometry.b2309 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2309
  · have he : Geometry.b1759.half 0 true=Geometry.b2310 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2310

theorem bound1758 : BoxMajorant Geometry.b1758 := by
  exact PositiveLeaves.L1058.bound

theorem bound1757 : BoxMajorant Geometry.b1757 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1757.Widths)
  · have he : Geometry.b1757.half 0 false=Geometry.b2307 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2307
  · have he : Geometry.b1757.half 0 true=Geometry.b2308 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2308

theorem bound1234 : BoxMajorant Geometry.b1234 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1234.Widths)
  · have he : Geometry.b1234.half 2 false=Geometry.b1761 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1761
  · have he : Geometry.b1234.half 2 true=Geometry.b1762 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1762

theorem bound1233 : BoxMajorant Geometry.b1233 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1233.Widths)
  · have he : Geometry.b1233.half 2 false=Geometry.b1759 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1759
  · have he : Geometry.b1233.half 2 true=Geometry.b1760 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1760

theorem bound1232 : BoxMajorant Geometry.b1232 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1232.Widths)
  · have he : Geometry.b1232.half 2 false=Geometry.b1757 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1757
  · have he : Geometry.b1232.half 2 true=Geometry.b1758 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1758

theorem bound1231 : BoxMajorant Geometry.b1231 := by
  exact PositiveLeaves.L1061.bound

theorem bound896 : BoxMajorant Geometry.b896 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b896.Widths)
  · have he : Geometry.b896.half 1 false=Geometry.b1233 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1233
  · have he : Geometry.b896.half 1 true=Geometry.b1234 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1234

theorem bound895 : BoxMajorant Geometry.b895 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b895.Widths)
  · have he : Geometry.b895.half 1 false=Geometry.b1231 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1231
  · have he : Geometry.b895.half 1 true=Geometry.b1232 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1232

theorem bound613 : BoxMajorant Geometry.b613 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b613.Widths)
  · have he : Geometry.b613.half 0 false=Geometry.b895 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound895
  · have he : Geometry.b613.half 0 true=Geometry.b896 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound896

end N7.Kernel.Cover
