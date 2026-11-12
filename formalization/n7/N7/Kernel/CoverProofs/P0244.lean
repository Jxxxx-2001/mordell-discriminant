import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0040
import N7.Kernel.CoverGeometry.G0046
import N7.Kernel.CoverGeometry.G0051
import N7.Kernel.CoverGeometry.G0056
import N7.Kernel.CoverGeometry.G0061
import N7.Kernel.CoverGeometry.G0067
import N7.Kernel.CoverGeometry.G0071
import N7.Kernel.CoverGeometry.G0076
import N7.Kernel.PositiveGroups.G0289
import N7.Kernel.PositiveGroups.G0313
import N7.Kernel.PositiveGroups.G0375
import N7.Kernel.PositiveGroups.G0402
import N7.Kernel.PositiveGroups.G0421
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4892 : BoxMajorant Geometry.b4892 := by
  exact PositiveLeaves.L1835.bound

theorem bound4891 : BoxMajorant Geometry.b4891 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4891 2 (by decide +kernel) x hx hd ho).elim

theorem bound4890 : BoxMajorant Geometry.b4890 := by
  exact PositiveLeaves.L1837.bound

theorem bound4889 : BoxMajorant Geometry.b4889 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4889 2 (by decide +kernel) x hx hd ho).elim

theorem bound4888 : BoxMajorant Geometry.b4888 := by
  exact PositiveLeaves.L1841.bound

theorem bound4887 : BoxMajorant Geometry.b4887 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4887 2 (by decide +kernel) x hx hd ho).elim

theorem bound4886 : BoxMajorant Geometry.b4886 := by
  exact PositiveLeaves.L1843.bound

theorem bound4885 : BoxMajorant Geometry.b4885 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4885 2 (by decide +kernel) x hx hd ho).elim

theorem bound4566 : BoxMajorant Geometry.b4566 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4566.Widths)
  · have he : Geometry.b4566.half 2 false=Geometry.b4891 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4891
  · have he : Geometry.b4566.half 2 true=Geometry.b4892 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4892

theorem bound4565 : BoxMajorant Geometry.b4565 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4565.Widths)
  · have he : Geometry.b4565.half 2 false=Geometry.b4889 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4889
  · have he : Geometry.b4565.half 2 true=Geometry.b4890 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4890

theorem bound4564 : BoxMajorant Geometry.b4564 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4564.Widths)
  · have he : Geometry.b4564.half 2 false=Geometry.b4887 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4887
  · have he : Geometry.b4564.half 2 true=Geometry.b4888 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4888

theorem bound4563 : BoxMajorant Geometry.b4563 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4563.Widths)
  · have he : Geometry.b4563.half 2 false=Geometry.b4885 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4885
  · have he : Geometry.b4563.half 2 true=Geometry.b4886 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4886

theorem bound4294 : BoxMajorant Geometry.b4294 := by
  exact PositiveLeaves.L1834.bound

theorem bound4293 : BoxMajorant Geometry.b4293 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4293.Widths)
  · have he : Geometry.b4293.half 1 false=Geometry.b4565 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4565
  · have he : Geometry.b4293.half 1 true=Geometry.b4566 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4566

theorem bound4292 : BoxMajorant Geometry.b4292 := by
  exact PositiveLeaves.L1840.bound

theorem bound4291 : BoxMajorant Geometry.b4291 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4291.Widths)
  · have he : Geometry.b4291.half 1 false=Geometry.b4563 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4563
  · have he : Geometry.b4291.half 1 true=Geometry.b4564 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4564

theorem bound3940 : BoxMajorant Geometry.b3940 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3940.Widths)
  · have he : Geometry.b3940.half 0 false=Geometry.b4293 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4293
  · have he : Geometry.b3940.half 0 true=Geometry.b4294 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4294

theorem bound3939 : BoxMajorant Geometry.b3939 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3939 2 (by decide +kernel) x hx hd ho).elim

theorem bound3938 : BoxMajorant Geometry.b3938 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3938.Widths)
  · have he : Geometry.b3938.half 0 false=Geometry.b4291 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4291
  · have he : Geometry.b3938.half 0 true=Geometry.b4292 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4292

theorem bound3937 : BoxMajorant Geometry.b3937 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3937 2 (by decide +kernel) x hx hd ho).elim

theorem bound3590 : BoxMajorant Geometry.b3590 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3590.Widths)
  · have he : Geometry.b3590.half 2 false=Geometry.b3939 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3939
  · have he : Geometry.b3590.half 2 true=Geometry.b3940 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3940

theorem bound3589 : BoxMajorant Geometry.b3589 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3589.Widths)
  · have he : Geometry.b3589.half 2 false=Geometry.b3937 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3937
  · have he : Geometry.b3589.half 2 true=Geometry.b3938 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3938

theorem bound3320 : BoxMajorant Geometry.b3320 := by
  exact PositiveLeaves.L1833.bound

theorem bound3319 : BoxMajorant Geometry.b3319 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3319.Widths)
  · have he : Geometry.b3319.half 1 false=Geometry.b3589 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3589
  · have he : Geometry.b3319.half 1 true=Geometry.b3590 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3590

theorem bound2984 : BoxMajorant Geometry.b2984 := by
  exact PositiveLeaves.L1832.bound

theorem bound2983 : BoxMajorant Geometry.b2983 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2983.Widths)
  · have he : Geometry.b2983.half 0 false=Geometry.b3319 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3319
  · have he : Geometry.b2983.half 0 true=Geometry.b3320 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3320

theorem bound2606 : BoxMajorant Geometry.b2606 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2606.Widths)
  · have he : Geometry.b2606.half 2 false=Geometry.b2983 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2983
  · have he : Geometry.b2606.half 2 true=Geometry.b2984 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2984

end N7.Kernel.Cover
