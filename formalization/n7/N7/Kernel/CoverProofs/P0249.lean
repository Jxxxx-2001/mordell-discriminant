import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0051
import N7.Kernel.CoverGeometry.G0056
import N7.Kernel.CoverGeometry.G0061
import N7.Kernel.CoverGeometry.G0067
import N7.Kernel.CoverGeometry.G0071
import N7.Kernel.CoverGeometry.G0076
import N7.Kernel.PositiveGroups.G0419
import N7.Kernel.PositiveGroups.G0420
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound4902 : BoxMajorant Geometry.b4902 := by
  exact PositiveLeaves.L1798.bound

theorem bound4901 : BoxMajorant Geometry.b4901 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4901 2 (by decide +kernel) x hx hd ho).elim

theorem bound4900 : BoxMajorant Geometry.b4900 := by
  exact PositiveLeaves.L1800.bound

theorem bound4899 : BoxMajorant Geometry.b4899 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4899 2 (by decide +kernel) x hx hd ho).elim

theorem bound4898 : BoxMajorant Geometry.b4898 := by
  exact PositiveLeaves.L1804.bound

theorem bound4897 : BoxMajorant Geometry.b4897 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4897 2 (by decide +kernel) x hx hd ho).elim

theorem bound4896 : BoxMajorant Geometry.b4896 := by
  exact PositiveLeaves.L1806.bound

theorem bound4895 : BoxMajorant Geometry.b4895 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4895 2 (by decide +kernel) x hx hd ho).elim

theorem bound4572 : BoxMajorant Geometry.b4572 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4572.Widths)
  · have he : Geometry.b4572.half 2 false=Geometry.b4901 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4901
  · have he : Geometry.b4572.half 2 true=Geometry.b4902 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4902

theorem bound4571 : BoxMajorant Geometry.b4571 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4571.Widths)
  · have he : Geometry.b4571.half 2 false=Geometry.b4899 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4899
  · have he : Geometry.b4571.half 2 true=Geometry.b4900 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4900

theorem bound4570 : BoxMajorant Geometry.b4570 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4570.Widths)
  · have he : Geometry.b4570.half 2 false=Geometry.b4897 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4897
  · have he : Geometry.b4570.half 2 true=Geometry.b4898 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4898

theorem bound4569 : BoxMajorant Geometry.b4569 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4569.Widths)
  · have he : Geometry.b4569.half 2 false=Geometry.b4895 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4895
  · have he : Geometry.b4569.half 2 true=Geometry.b4896 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4896

theorem bound4304 : BoxMajorant Geometry.b4304 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4304.Widths)
  · have he : Geometry.b4304.half 1 false=Geometry.b4571 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4571
  · have he : Geometry.b4304.half 1 true=Geometry.b4572 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4572

theorem bound4303 : BoxMajorant Geometry.b4303 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4303 2 (by decide +kernel) x hx hd ho).elim

theorem bound4302 : BoxMajorant Geometry.b4302 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4302.Widths)
  · have he : Geometry.b4302.half 1 false=Geometry.b4569 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4569
  · have he : Geometry.b4302.half 1 true=Geometry.b4570 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4570

theorem bound4301 : BoxMajorant Geometry.b4301 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b4301 2 (by decide +kernel) x hx hd ho).elim

theorem bound3950 : BoxMajorant Geometry.b3950 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3950.Widths)
  · have he : Geometry.b3950.half 0 false=Geometry.b4303 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4303
  · have he : Geometry.b3950.half 0 true=Geometry.b4304 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4304

theorem bound3949 : BoxMajorant Geometry.b3949 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3949 2 (by decide +kernel) x hx hd ho).elim

theorem bound3948 : BoxMajorant Geometry.b3948 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3948.Widths)
  · have he : Geometry.b3948.half 0 false=Geometry.b4301 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4301
  · have he : Geometry.b3948.half 0 true=Geometry.b4302 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4302

theorem bound3947 : BoxMajorant Geometry.b3947 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b3947 2 (by decide +kernel) x hx hd ho).elim

theorem bound3596 : BoxMajorant Geometry.b3596 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3596.Widths)
  · have he : Geometry.b3596.half 2 false=Geometry.b3949 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3949
  · have he : Geometry.b3596.half 2 true=Geometry.b3950 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3950

theorem bound3595 : BoxMajorant Geometry.b3595 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3595.Widths)
  · have he : Geometry.b3595.half 2 false=Geometry.b3947 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3947
  · have he : Geometry.b3595.half 2 true=Geometry.b3948 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3948

theorem bound3327 : BoxMajorant Geometry.b3327 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3327.Widths)
  · have he : Geometry.b3327.half 1 false=Geometry.b3595 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3595
  · have he : Geometry.b3327.half 1 true=Geometry.b3596 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3596

end N7.Kernel.Cover
