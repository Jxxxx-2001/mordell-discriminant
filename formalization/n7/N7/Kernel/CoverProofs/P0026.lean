import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0007
import N7.Kernel.CoverGeometry.G0011
import N7.Kernel.CoverGeometry.G0016
import N7.Kernel.CoverGeometry.G0022
import N7.Kernel.CoverGeometry.G0032
import N7.Kernel.CoverGeometry.G0038
import N7.Kernel.CoverGeometry.G0043
import N7.Kernel.CoverGeometry.G0049
import N7.Kernel.CoverGeometry.G0053
import N7.Kernel.CoverGeometry.G0058
import N7.Kernel.CoverGeometry.G0064
import N7.Kernel.CoverGeometry.G0069
import N7.Kernel.CoverGeometry.G0073
import N7.Kernel.CoverGeometry.G0079
import N7.Kernel.CoverGeometry.G0082
import N7.Kernel.CoverGeometry.G0084
import N7.Kernel.PositiveGroups.G0232
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5404 : BoxMajorant Geometry.b5404 := by
  exact PositiveLeaves.L2934.bound

theorem bound5403 : BoxMajorant Geometry.b5403 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5403 2 (by decide +kernel) x hx hd ho).elim

theorem bound5282 : BoxMajorant Geometry.b5282 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5282.Widths)
  · have he : Geometry.b5282.half 2 false=Geometry.b5403 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5403
  · have he : Geometry.b5282.half 2 true=Geometry.b5404 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5404

theorem bound5281 : BoxMajorant Geometry.b5281 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5281 2 (by decide +kernel) x hx hd ho).elim

theorem bound5104 : BoxMajorant Geometry.b5104 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5104.Widths)
  · have he : Geometry.b5104.half 1 false=Geometry.b5281 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5281
  · have he : Geometry.b5104.half 1 true=Geometry.b5282 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5282

theorem bound5103 : BoxMajorant Geometry.b5103 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5103 2 (by decide +kernel) x hx hd ho).elim

theorem bound4720 : BoxMajorant Geometry.b4720 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4720.Widths)
  · have he : Geometry.b4720.half 0 false=Geometry.b5103 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5103
  · have he : Geometry.b4720.half 0 true=Geometry.b5104 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5104

theorem bound4719 : BoxMajorant Geometry.b4719 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4719 2 (by decide +kernel) x hx hd ho).elim

theorem bound4442 : BoxMajorant Geometry.b4442 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4442.Widths)
  · have he : Geometry.b4442.half 2 false=Geometry.b4719 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4719
  · have he : Geometry.b4442.half 2 true=Geometry.b4720 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4720

theorem bound4441 : BoxMajorant Geometry.b4441 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4441 2 (by decide +kernel) x hx hd ho).elim

theorem bound4150 : BoxMajorant Geometry.b4150 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4150.Widths)
  · have he : Geometry.b4150.half 1 false=Geometry.b4441 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4441
  · have he : Geometry.b4150.half 1 true=Geometry.b4442 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4442

theorem bound4149 : BoxMajorant Geometry.b4149 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4149 2 (by decide +kernel) x hx hd ho).elim

theorem bound3730 : BoxMajorant Geometry.b3730 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3730.Widths)
  · have he : Geometry.b3730.half 0 false=Geometry.b4149 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4149
  · have he : Geometry.b3730.half 0 true=Geometry.b4150 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4150

theorem bound3729 : BoxMajorant Geometry.b3729 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3729 2 (by decide +kernel) x hx hd ho).elim

theorem bound3454 : BoxMajorant Geometry.b3454 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3454.Widths)
  · have he : Geometry.b3454.half 2 false=Geometry.b3729 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3729
  · have he : Geometry.b3454.half 2 true=Geometry.b3730 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3730

theorem bound3453 : BoxMajorant Geometry.b3453 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3453 2 (by decide +kernel) x hx hd ho).elim

theorem bound3182 : BoxMajorant Geometry.b3182 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3182.Widths)
  · have he : Geometry.b3182.half 1 false=Geometry.b3453 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3453
  · have he : Geometry.b3182.half 1 true=Geometry.b3454 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3454

theorem bound3181 : BoxMajorant Geometry.b3181 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3181 2 (by decide +kernel) x hx hd ho).elim

theorem bound2788 : BoxMajorant Geometry.b2788 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2788.Widths)
  · have he : Geometry.b2788.half 0 false=Geometry.b3181 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3181
  · have he : Geometry.b2788.half 0 true=Geometry.b3182 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3182

theorem bound2787 : BoxMajorant Geometry.b2787 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2787 2 (by decide +kernel) x hx hd ho).elim

theorem bound2450 : BoxMajorant Geometry.b2450 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2450.Widths)
  · have he : Geometry.b2450.half 2 false=Geometry.b2787 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2787
  · have he : Geometry.b2450.half 2 true=Geometry.b2788 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2788

theorem bound2449 : BoxMajorant Geometry.b2449 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2449 2 (by decide +kernel) x hx hd ho).elim

theorem bound2096 : BoxMajorant Geometry.b2096 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2096.Widths)
  · have he : Geometry.b2096.half 1 false=Geometry.b2449 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2449
  · have he : Geometry.b2096.half 1 true=Geometry.b2450 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2450

theorem bound2095 : BoxMajorant Geometry.b2095 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2095 2 (by decide +kernel) x hx hd ho).elim

theorem bound1448 : BoxMajorant Geometry.b1448 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1448.Widths)
  · have he : Geometry.b1448.half 0 false=Geometry.b2095 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2095
  · have he : Geometry.b1448.half 0 true=Geometry.b2096 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2096

theorem bound1447 : BoxMajorant Geometry.b1447 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1447 2 (by decide +kernel) x hx hd ho).elim

theorem bound1034 : BoxMajorant Geometry.b1034 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1034.Widths)
  · have he : Geometry.b1034.half 2 false=Geometry.b1447 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1447
  · have he : Geometry.b1034.half 2 true=Geometry.b1448 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1448

theorem bound1033 : BoxMajorant Geometry.b1033 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1033 2 (by decide +kernel) x hx hd ho).elim

theorem bound752 : BoxMajorant Geometry.b752 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b752.Widths)
  · have he : Geometry.b752.half 1 false=Geometry.b1033 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1033
  · have he : Geometry.b752.half 1 true=Geometry.b1034 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1034

theorem bound751 : BoxMajorant Geometry.b751 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b751 2 (by decide +kernel) x hx hd ho).elim

theorem bound483 : BoxMajorant Geometry.b483 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b483.Widths)
  · have he : Geometry.b483.half 0 false=Geometry.b751 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound751
  · have he : Geometry.b483.half 0 true=Geometry.b752 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound752

end N7.Kernel.Cover
