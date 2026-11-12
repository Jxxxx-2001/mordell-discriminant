import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0043
import N7.Kernel.CoverGeometry.G0049
import N7.Kernel.CoverGeometry.G0054
import N7.Kernel.CoverGeometry.G0058
import N7.Kernel.CoverGeometry.G0065
import N7.Kernel.CoverGeometry.G0070
import N7.Kernel.CoverGeometry.G0074
import N7.Kernel.PositiveGroups.G0271
import N7.Kernel.PositiveGroups.G0322
import N7.Kernel.PositiveGroups.G0352
import N7.Kernel.PositiveGroups.G0353
import N7.Kernel.PositiveGroups.G0383
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4776 : BoxMajorant Geometry.b4776 := by
  exact PositiveLeaves.L2737.bound

theorem bound4775 : BoxMajorant Geometry.b4775 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4775 2 (by decide +kernel) x hx hd ho).elim

theorem bound4486 : BoxMajorant Geometry.b4486 := by
  exact PositiveLeaves.L2736.bound

theorem bound4485 : BoxMajorant Geometry.b4485 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4485.Widths)
  · have he : Geometry.b4485.half 2 false=Geometry.b4775 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4775
  · have he : Geometry.b4485.half 2 true=Geometry.b4776 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4776

theorem bound4184 : BoxMajorant Geometry.b4184 := by
  exact PositiveLeaves.L2735.bound

theorem bound4183 : BoxMajorant Geometry.b4183 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4183.Widths)
  · have he : Geometry.b4183.half 1 false=Geometry.b4485 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4485
  · have he : Geometry.b4183.half 1 true=Geometry.b4486 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4486

theorem bound3762 : BoxMajorant Geometry.b3762 := by
  exact PositiveLeaves.L2733.bound

theorem bound3761 : BoxMajorant Geometry.b3761 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3761 2 (by decide +kernel) x hx hd ho).elim

theorem bound3760 : BoxMajorant Geometry.b3760 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3760.Widths)
  · have he : Geometry.b3760.half 0 false=Geometry.b4183 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4183
  · have he : Geometry.b3760.half 0 true=Geometry.b4184 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4184

theorem bound3759 : BoxMajorant Geometry.b3759 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3759 2 (by decide +kernel) x hx hd ho).elim

theorem bound3472 : BoxMajorant Geometry.b3472 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3472.Widths)
  · have he : Geometry.b3472.half 2 false=Geometry.b3761 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3761
  · have he : Geometry.b3472.half 2 true=Geometry.b3762 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3762

theorem bound3471 : BoxMajorant Geometry.b3471 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3471.Widths)
  · have he : Geometry.b3471.half 2 false=Geometry.b3759 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3759
  · have he : Geometry.b3471.half 2 true=Geometry.b3760 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3760

theorem bound3194 : BoxMajorant Geometry.b3194 := by
  exact PositiveLeaves.L2732.bound

theorem bound3193 : BoxMajorant Geometry.b3193 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3193.Widths)
  · have he : Geometry.b3193.half 1 false=Geometry.b3471 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3471
  · have he : Geometry.b3193.half 1 true=Geometry.b3472 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3472

theorem bound2808 : BoxMajorant Geometry.b2808 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2808.Widths)
  · have he : Geometry.b2808.half 0 false=Geometry.b3193 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3193
  · have he : Geometry.b2808.half 0 true=Geometry.b3194 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3194

end N7.Kernel.Cover
