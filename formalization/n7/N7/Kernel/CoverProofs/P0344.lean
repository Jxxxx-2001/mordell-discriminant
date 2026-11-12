import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0074
import N7.Kernel.CoverGeometry.G0080
import N7.Kernel.CoverGeometry.G0082
import N7.Kernel.CoverGeometry.G0083
import N7.Kernel.CoverGeometry.G0085
import N7.Kernel.PositiveGroups.G0440
import N7.Kernel.PositiveGroups.G0454
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5444 : BoxMajorant Geometry.b5444 := by
  exact PositiveLeaves.L2816.bound

theorem bound5443 : BoxMajorant Geometry.b5443 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5443 2 (by decide +kernel) x hx hd ho).elim

theorem bound5442 : BoxMajorant Geometry.b5442 := by
  exact PositiveLeaves.L2818.bound

theorem bound5441 : BoxMajorant Geometry.b5441 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5441 2 (by decide +kernel) x hx hd ho).elim

theorem bound5314 : BoxMajorant Geometry.b5314 := by
  exact PositiveLeaves.L2815.bound

theorem bound5313 : BoxMajorant Geometry.b5313 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5313.Widths)
  · have he : Geometry.b5313.half 2 false=Geometry.b5443 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5443
  · have he : Geometry.b5313.half 2 true=Geometry.b5444 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5444

theorem bound5312 : BoxMajorant Geometry.b5312 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5312.Widths)
  · have he : Geometry.b5312.half 2 false=Geometry.b5441 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5441
  · have he : Geometry.b5312.half 2 true=Geometry.b5442 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5442

theorem bound5311 : BoxMajorant Geometry.b5311 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5311 2 (by decide +kernel) x hx hd ho).elim

theorem bound5128 : BoxMajorant Geometry.b5128 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5128.Widths)
  · have he : Geometry.b5128.half 1 false=Geometry.b5313 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5313
  · have he : Geometry.b5128.half 1 true=Geometry.b5314 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5314

theorem bound5127 : BoxMajorant Geometry.b5127 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5127.Widths)
  · have he : Geometry.b5127.half 1 false=Geometry.b5311 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5311
  · have he : Geometry.b5127.half 1 true=Geometry.b5312 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5312

theorem bound4745 : BoxMajorant Geometry.b4745 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4745.Widths)
  · have he : Geometry.b4745.half 0 false=Geometry.b5127 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5127
  · have he : Geometry.b4745.half 0 true=Geometry.b5128 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5128

end N7.Kernel.Cover
