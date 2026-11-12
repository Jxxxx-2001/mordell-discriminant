import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0042
import N7.Kernel.CoverGeometry.G0048
import N7.Kernel.CoverGeometry.G0053
import N7.Kernel.CoverGeometry.G0057
import N7.Kernel.CoverGeometry.G0063
import N7.Kernel.PositiveGroups.G0281
import N7.Kernel.PositiveGroups.G0306
import N7.Kernel.PositiveGroups.G0328
import N7.Kernel.PositiveGroups.G0355
import N7.Kernel.PositiveGroups.G0356
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4090 : BoxMajorant Geometry.b4090 := by
  exact PositiveLeaves.L907.bound

theorem bound4089 : BoxMajorant Geometry.b4089 := by
  exact PositiveLeaves.L908.bound

theorem bound4088 : BoxMajorant Geometry.b4088 := by
  exact PositiveLeaves.L909.bound

theorem bound4087 : BoxMajorant Geometry.b4087 := by
  exact PositiveLeaves.L910.bound

theorem bound3688 : BoxMajorant Geometry.b3688 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3688.Widths)
  · have he : Geometry.b3688.half 2 false=Geometry.b4089 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4089
  · have he : Geometry.b3688.half 2 true=Geometry.b4090 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4090

theorem bound3687 : BoxMajorant Geometry.b3687 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3687.Widths)
  · have he : Geometry.b3687.half 2 false=Geometry.b4087 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4087
  · have he : Geometry.b3687.half 2 true=Geometry.b4088 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4088

theorem bound3422 : BoxMajorant Geometry.b3422 := by
  exact PositiveLeaves.L906.bound

theorem bound3421 : BoxMajorant Geometry.b3421 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3421.Widths)
  · have he : Geometry.b3421.half 1 false=Geometry.b3687 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3687
  · have he : Geometry.b3421.half 1 true=Geometry.b3688 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3688

theorem bound3102 : BoxMajorant Geometry.b3102 := by
  exact PositiveLeaves.L905.bound

theorem bound3101 : BoxMajorant Geometry.b3101 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3101.Widths)
  · have he : Geometry.b3101.half 0 false=Geometry.b3421 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3421
  · have he : Geometry.b3101.half 0 true=Geometry.b3422 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3422

theorem bound2700 : BoxMajorant Geometry.b2700 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2700.Widths)
  · have he : Geometry.b2700.half 2 false=Geometry.b3101 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3101
  · have he : Geometry.b2700.half 2 true=Geometry.b3102 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3102

end N7.Kernel.Cover
