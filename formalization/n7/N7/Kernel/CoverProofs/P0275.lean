import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0057
import N7.Kernel.CoverGeometry.G0063
import N7.Kernel.CoverGeometry.G0068
import N7.Kernel.CoverGeometry.G0072
import N7.Kernel.CoverGeometry.G0078
import N7.Kernel.CoverGeometry.G0081
import N7.Kernel.CoverGeometry.G0083
import N7.Kernel.PositiveGroups.G0364
import N7.Kernel.PositiveGroups.G0396
import N7.Kernel.PositiveGroups.G0433
import N7.Kernel.PositiveGroups.G0434
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5352 : BoxMajorant Geometry.b5352 := by
  exact PositiveLeaves.L1496.bound

theorem bound5351 : BoxMajorant Geometry.b5351 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5351 2 (by decide +kernel) x hx hd ho).elim

theorem bound5236 : BoxMajorant Geometry.b5236 := by
  exact PositiveLeaves.L1493.bound

theorem bound5235 : BoxMajorant Geometry.b5235 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5235 2 (by decide +kernel) x hx hd ho).elim

theorem bound5234 : BoxMajorant Geometry.b5234 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5234.Widths)
  · have he : Geometry.b5234.half 1 false=Geometry.b5351 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5351
  · have he : Geometry.b5234.half 1 true=Geometry.b5352 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5352

theorem bound5233 : BoxMajorant Geometry.b5233 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5233 2 (by decide +kernel) x hx hd ho).elim

theorem bound5012 : BoxMajorant Geometry.b5012 := by
  exact PositiveLeaves.L1491.bound

theorem bound5011 : BoxMajorant Geometry.b5011 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5011 2 (by decide +kernel) x hx hd ho).elim

theorem bound5010 : BoxMajorant Geometry.b5010 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5010.Widths)
  · have he : Geometry.b5010.half 0 false=Geometry.b5235 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5235
  · have he : Geometry.b5010.half 0 true=Geometry.b5236 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5236

theorem bound5009 : BoxMajorant Geometry.b5009 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5009 2 (by decide +kernel) x hx hd ho).elim

theorem bound5008 : BoxMajorant Geometry.b5008 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5008.Widths)
  · have he : Geometry.b5008.half 0 false=Geometry.b5233 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5233
  · have he : Geometry.b5008.half 0 true=Geometry.b5234 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5234

theorem bound5007 : BoxMajorant Geometry.b5007 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5007 2 (by decide +kernel) x hx hd ho).elim

theorem bound4648 : BoxMajorant Geometry.b4648 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4648.Widths)
  · have he : Geometry.b4648.half 2 false=Geometry.b5011 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5011
  · have he : Geometry.b4648.half 2 true=Geometry.b5012 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5012

theorem bound4647 : BoxMajorant Geometry.b4647 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4647.Widths)
  · have he : Geometry.b4647.half 2 false=Geometry.b5009 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5009
  · have he : Geometry.b4647.half 2 true=Geometry.b5010 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5010

theorem bound4646 : BoxMajorant Geometry.b4646 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4646.Widths)
  · have he : Geometry.b4646.half 2 false=Geometry.b5007 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5007
  · have he : Geometry.b4646.half 2 true=Geometry.b5008 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5008

theorem bound4645 : BoxMajorant Geometry.b4645 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4645 2 (by decide +kernel) x hx hd ho).elim

theorem bound4386 : BoxMajorant Geometry.b4386 := by
  exact PositiveLeaves.L1490.bound

theorem bound4385 : BoxMajorant Geometry.b4385 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4385.Widths)
  · have he : Geometry.b4385.half 1 false=Geometry.b4647 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4647
  · have he : Geometry.b4385.half 1 true=Geometry.b4648 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4648

theorem bound4384 : BoxMajorant Geometry.b4384 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4384.Widths)
  · have he : Geometry.b4384.half 1 false=Geometry.b4645 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4645
  · have he : Geometry.b4384.half 1 true=Geometry.b4646 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4646

theorem bound4383 : BoxMajorant Geometry.b4383 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4383 2 (by decide +kernel) x hx hd ho).elim

theorem bound4038 : BoxMajorant Geometry.b4038 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4038.Widths)
  · have he : Geometry.b4038.half 0 false=Geometry.b4385 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4385
  · have he : Geometry.b4038.half 0 true=Geometry.b4386 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4386

theorem bound4037 : BoxMajorant Geometry.b4037 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4037.Widths)
  · have he : Geometry.b4037.half 0 false=Geometry.b4383 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4383
  · have he : Geometry.b4037.half 0 true=Geometry.b4384 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4384

theorem bound3649 : BoxMajorant Geometry.b3649 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3649.Widths)
  · have he : Geometry.b3649.half 2 false=Geometry.b4037 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4037
  · have he : Geometry.b3649.half 2 true=Geometry.b4038 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4038

end N7.Kernel.Cover
