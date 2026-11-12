import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0046
import N7.Kernel.CoverGeometry.G0052
import N7.Kernel.CoverGeometry.G0056
import N7.Kernel.CoverGeometry.G0062
import N7.Kernel.CoverGeometry.G0067
import N7.Kernel.CoverGeometry.G0071
import N7.Kernel.CoverGeometry.G0077
import N7.Kernel.CoverGeometry.G0081
import N7.Kernel.PositiveGroups.G0370
import N7.Kernel.PositiveGroups.G0400
import N7.Kernel.PositiveGroups.G0417
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound5208 : BoxMajorant Geometry.b5208 := by
  exact PositiveLeaves.L1695.bound

theorem bound5207 : BoxMajorant Geometry.b5207 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b5207 2 (by decide +kernel) x hx hd ho).elim

theorem bound4954 : BoxMajorant Geometry.b4954 := by
  exact PositiveLeaves.L1687.bound

theorem bound4953 : BoxMajorant Geometry.b4953 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4953 2 (by decide +kernel) x hx hd ho).elim

theorem bound4952 : BoxMajorant Geometry.b4952 := by
  exact PositiveLeaves.L1689.bound

theorem bound4951 : BoxMajorant Geometry.b4951 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4951 2 (by decide +kernel) x hx hd ho).elim

theorem bound4950 : BoxMajorant Geometry.b4950 := by
  exact PositiveLeaves.L1693.bound

theorem bound4949 : BoxMajorant Geometry.b4949 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4949 2 (by decide +kernel) x hx hd ho).elim

theorem bound4948 : BoxMajorant Geometry.b4948 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4948.Widths)
  · have he : Geometry.b4948.half 0 false=Geometry.b5207 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5207
  · have he : Geometry.b4948.half 0 true=Geometry.b5208 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5208

theorem bound4947 : BoxMajorant Geometry.b4947 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4947 2 (by decide +kernel) x hx hd ho).elim

theorem bound4604 : BoxMajorant Geometry.b4604 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4604.Widths)
  · have he : Geometry.b4604.half 2 false=Geometry.b4953 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4953
  · have he : Geometry.b4604.half 2 true=Geometry.b4954 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4954

theorem bound4603 : BoxMajorant Geometry.b4603 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4603.Widths)
  · have he : Geometry.b4603.half 2 false=Geometry.b4951 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4951
  · have he : Geometry.b4603.half 2 true=Geometry.b4952 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4952

theorem bound4602 : BoxMajorant Geometry.b4602 := by
  exact PositiveLeaves.L1692.bound

theorem bound4601 : BoxMajorant Geometry.b4601 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4601.Widths)
  · have he : Geometry.b4601.half 2 false=Geometry.b4949 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4949
  · have he : Geometry.b4601.half 2 true=Geometry.b4950 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4950

theorem bound4600 : BoxMajorant Geometry.b4600 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4600.Widths)
  · have he : Geometry.b4600.half 2 false=Geometry.b4947 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4947
  · have he : Geometry.b4600.half 2 true=Geometry.b4948 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4948

theorem bound4599 : BoxMajorant Geometry.b4599 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4599 2 (by decide +kernel) x hx hd ho).elim

theorem bound4334 : BoxMajorant Geometry.b4334 := by
  exact PositiveLeaves.L1686.bound

theorem bound4333 : BoxMajorant Geometry.b4333 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4333.Widths)
  · have he : Geometry.b4333.half 1 false=Geometry.b4603 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4603
  · have he : Geometry.b4333.half 1 true=Geometry.b4604 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4604

theorem bound4332 : BoxMajorant Geometry.b4332 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4332.Widths)
  · have he : Geometry.b4332.half 1 false=Geometry.b4601 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4601
  · have he : Geometry.b4332.half 1 true=Geometry.b4602 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4602

theorem bound4331 : BoxMajorant Geometry.b4331 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4331.Widths)
  · have he : Geometry.b4331.half 1 false=Geometry.b4599 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4599
  · have he : Geometry.b4331.half 1 true=Geometry.b4600 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4600

theorem bound3976 : BoxMajorant Geometry.b3976 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3976.Widths)
  · have he : Geometry.b3976.half 0 false=Geometry.b4333 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4333
  · have he : Geometry.b3976.half 0 true=Geometry.b4334 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4334

theorem bound3975 : BoxMajorant Geometry.b3975 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3975 2 (by decide +kernel) x hx hd ho).elim

theorem bound3974 : BoxMajorant Geometry.b3974 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3974.Widths)
  · have he : Geometry.b3974.half 0 false=Geometry.b4331 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4331
  · have he : Geometry.b3974.half 0 true=Geometry.b4332 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4332

theorem bound3973 : BoxMajorant Geometry.b3973 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3973 2 (by decide +kernel) x hx hd ho).elim

theorem bound3610 : BoxMajorant Geometry.b3610 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3610.Widths)
  · have he : Geometry.b3610.half 2 false=Geometry.b3975 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3975
  · have he : Geometry.b3610.half 2 true=Geometry.b3976 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3976

theorem bound3609 : BoxMajorant Geometry.b3609 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3609.Widths)
  · have he : Geometry.b3609.half 2 false=Geometry.b3973 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3973
  · have he : Geometry.b3609.half 2 true=Geometry.b3974 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3974

theorem bound3338 : BoxMajorant Geometry.b3338 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3338.Widths)
  · have he : Geometry.b3338.half 1 false=Geometry.b3609 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3609
  · have he : Geometry.b3338.half 1 true=Geometry.b3610 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3610

theorem bound3337 : BoxMajorant Geometry.b3337 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3337 2 (by decide +kernel) x hx hd ho).elim

theorem bound2999 : BoxMajorant Geometry.b2999 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2999.Widths)
  · have he : Geometry.b2999.half 0 false=Geometry.b3337 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3337
  · have he : Geometry.b2999.half 0 true=Geometry.b3338 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3338

end N7.Kernel.Cover
