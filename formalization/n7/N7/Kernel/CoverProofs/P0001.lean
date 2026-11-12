import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0000
import N7.Kernel.CoverGeometry.G0001
import N7.Kernel.CoverGeometry.G0002
import N7.Kernel.CoverGeometry.G0003
import N7.Kernel.CoverGeometry.G0004
import N7.Kernel.CoverGeometry.G0007
import N7.Kernel.CoverGeometry.G0011
import N7.Kernel.CoverGeometry.G0016
import N7.Kernel.CoverGeometry.G0022
import N7.Kernel.CoverGeometry.G0032
import N7.Kernel.CoverGeometry.G0038
import N7.Kernel.CoverGeometry.G0043
import N7.Kernel.PositiveGroups.G0186
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2784 : BoxMajorant Geometry.b2784 := by
  exact PositiveLeaves.L2960.bound

theorem bound2783 : BoxMajorant Geometry.b2783 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2783 2 (by decide +kernel) x hx hd ho).elim

theorem bound2446 : BoxMajorant Geometry.b2446 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2446.Widths)
  · have he : Geometry.b2446.half 2 false=Geometry.b2783 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2783
  · have he : Geometry.b2446.half 2 true=Geometry.b2784 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2784

theorem bound2445 : BoxMajorant Geometry.b2445 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2445 2 (by decide +kernel) x hx hd ho).elim

theorem bound2092 : BoxMajorant Geometry.b2092 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2092.Widths)
  · have he : Geometry.b2092.half 1 false=Geometry.b2445 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2445
  · have he : Geometry.b2092.half 1 true=Geometry.b2446 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2446

theorem bound2091 : BoxMajorant Geometry.b2091 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2091 2 (by decide +kernel) x hx hd ho).elim

theorem bound1444 : BoxMajorant Geometry.b1444 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1444.Widths)
  · have he : Geometry.b1444.half 0 false=Geometry.b2091 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2091
  · have he : Geometry.b1444.half 0 true=Geometry.b2092 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2092

theorem bound1443 : BoxMajorant Geometry.b1443 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1443 2 (by decide +kernel) x hx hd ho).elim

theorem bound1030 : BoxMajorant Geometry.b1030 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1030.Widths)
  · have he : Geometry.b1030.half 2 false=Geometry.b1443 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1443
  · have he : Geometry.b1030.half 2 true=Geometry.b1444 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1444

theorem bound1029 : BoxMajorant Geometry.b1029 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1029 2 (by decide +kernel) x hx hd ho).elim

theorem bound748 : BoxMajorant Geometry.b748 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b748.Widths)
  · have he : Geometry.b748.half 1 false=Geometry.b1029 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1029
  · have he : Geometry.b748.half 1 true=Geometry.b1030 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1030

theorem bound747 : BoxMajorant Geometry.b747 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b747 2 (by decide +kernel) x hx hd ho).elim

theorem bound480 : BoxMajorant Geometry.b480 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b480.Widths)
  · have he : Geometry.b480.half 0 false=Geometry.b747 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound747
  · have he : Geometry.b480.half 0 true=Geometry.b748 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound748

theorem bound479 : BoxMajorant Geometry.b479 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b479 2 (by decide +kernel) x hx hd ho).elim

theorem bound306 : BoxMajorant Geometry.b306 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b306.Widths)
  · have he : Geometry.b306.half 2 false=Geometry.b479 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound479
  · have he : Geometry.b306.half 2 true=Geometry.b480 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound480

theorem bound305 : BoxMajorant Geometry.b305 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b305 2 (by decide +kernel) x hx hd ho).elim

theorem bound192 : BoxMajorant Geometry.b192 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b192.Widths)
  · have he : Geometry.b192.half 1 false=Geometry.b305 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound305
  · have he : Geometry.b192.half 1 true=Geometry.b306 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound306

theorem bound191 : BoxMajorant Geometry.b191 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b191 2 (by decide +kernel) x hx hd ho).elim

theorem bound112 : BoxMajorant Geometry.b112 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b112.Widths)
  · have he : Geometry.b112.half 0 false=Geometry.b191 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound191
  · have he : Geometry.b112.half 0 true=Geometry.b192 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound192

theorem bound111 : BoxMajorant Geometry.b111 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b111 2 (by decide +kernel) x hx hd ho).elim

theorem bound62 : BoxMajorant Geometry.b62 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b62.Widths)
  · have he : Geometry.b62.half 2 false=Geometry.b111 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound111
  · have he : Geometry.b62.half 2 true=Geometry.b112 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound112

theorem bound61 : BoxMajorant Geometry.b61 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b61 2 (by decide +kernel) x hx hd ho).elim

theorem bound32 : BoxMajorant Geometry.b32 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b32.Widths)
  · have he : Geometry.b32.half 1 false=Geometry.b61 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound61
  · have he : Geometry.b32.half 1 true=Geometry.b62 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound62

end N7.Kernel.Cover
