import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0042
import N7.Kernel.CoverGeometry.G0048
import N7.Kernel.CoverGeometry.G0053
import N7.Kernel.CoverGeometry.G0057
import N7.Kernel.CoverGeometry.G0063
import N7.Kernel.PositiveGroups.G0281
import N7.Kernel.PositiveGroups.G0305
import N7.Kernel.PositiveGroups.G0306
import N7.Kernel.PositiveGroups.G0327
import N7.Kernel.PositiveGroups.G0328
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4086 : BoxMajorant Geometry.b4086 := by
  exact PositiveLeaves.L913.bound

theorem bound4085 : BoxMajorant Geometry.b4085 := by
  exact PositiveLeaves.L914.bound

theorem bound3686 : BoxMajorant Geometry.b3686 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3686.Widths)
  · have he : Geometry.b3686.half 2 false=Geometry.b4085 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4085
  · have he : Geometry.b3686.half 2 true=Geometry.b4086 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4086

theorem bound3685 : BoxMajorant Geometry.b3685 := by
  exact PositiveLeaves.L915.bound

theorem bound3420 : BoxMajorant Geometry.b3420 := by
  exact PositiveLeaves.L912.bound

theorem bound3419 : BoxMajorant Geometry.b3419 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3419.Widths)
  · have he : Geometry.b3419.half 1 false=Geometry.b3685 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3685
  · have he : Geometry.b3419.half 1 true=Geometry.b3686 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3686

theorem bound3100 : BoxMajorant Geometry.b3100 := by
  exact PositiveLeaves.L911.bound

theorem bound3099 : BoxMajorant Geometry.b3099 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3099.Widths)
  · have he : Geometry.b3099.half 0 false=Geometry.b3419 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3419
  · have he : Geometry.b3099.half 0 true=Geometry.b3420 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3420

theorem bound2699 : BoxMajorant Geometry.b2699 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2699.Widths)
  · have he : Geometry.b2699.half 2 false=Geometry.b3099 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3099
  · have he : Geometry.b2699.half 2 true=Geometry.b3100 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3100

end N7.Kernel.Cover
