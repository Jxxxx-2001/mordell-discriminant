import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0000
import N7.Kernel.CoverGeometry.G0001
import N7.Kernel.CoverGeometry.G0002
import N7.Kernel.CoverGeometry.G0004
import N7.Kernel.CoverGeometry.G0006
import N7.Kernel.CoverGeometry.G0010
import N7.Kernel.CoverGeometry.G0015
import N7.Kernel.CoverGeometry.G0021
import N7.Kernel.CoverGeometry.G0031
import N7.Kernel.CoverGeometry.G0037
import N7.Kernel.CoverGeometry.G0042
import N7.Kernel.CoverGeometry.G0043
import N7.Kernel.CoverProofs.P0156
import N7.Kernel.PositiveGroups.G0007
import N7.Kernel.PositiveGroups.G0014
import N7.Kernel.PositiveGroups.G0079
import N7.Kernel.PositiveGroups.G0080
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2751 : BoxMajorant Geometry.b2751 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2751 0 (by decide +kernel) x hx hd ho).elim

theorem bound2416 : BoxMajorant Geometry.b2416 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2416 0 (by decide +kernel) x hx hd ho).elim

theorem bound2415 : BoxMajorant Geometry.b2415 := by
  exact PositiveLeaves.L536.bound

theorem bound2414 : BoxMajorant Geometry.b2414 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2414 0 (by decide +kernel) x hx hd ho).elim

theorem bound2413 : BoxMajorant Geometry.b2413 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2413.Widths)
  · have he : Geometry.b2413.half 1 false=Geometry.b2751 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2751
  · have he : Geometry.b2413.half 1 true=Geometry.b2752 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2752

theorem bound1998 : BoxMajorant Geometry.b1998 := by
  exact PositiveLeaves.L531.bound

theorem bound1997 : BoxMajorant Geometry.b1997 := by
  exact PositiveLeaves.L532.bound

theorem bound1996 : BoxMajorant Geometry.b1996 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1996.Widths)
  · have he : Geometry.b1996.half 0 false=Geometry.b2415 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2415
  · have he : Geometry.b1996.half 0 true=Geometry.b2416 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2416

theorem bound1995 : BoxMajorant Geometry.b1995 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1995.Widths)
  · have he : Geometry.b1995.half 0 false=Geometry.b2413 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2413
  · have he : Geometry.b1995.half 0 true=Geometry.b2414 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2414

theorem bound1376 : BoxMajorant Geometry.b1376 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1376.Widths)
  · have he : Geometry.b1376.half 2 false=Geometry.b1997 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1997
  · have he : Geometry.b1376.half 2 true=Geometry.b1998 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1998

theorem bound1375 : BoxMajorant Geometry.b1375 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1375 0 (by decide +kernel) x hx hd ho).elim

theorem bound1374 : BoxMajorant Geometry.b1374 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1374.Widths)
  · have he : Geometry.b1374.half 2 false=Geometry.b1995 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1995
  · have he : Geometry.b1374.half 2 true=Geometry.b1996 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1996

theorem bound1373 : BoxMajorant Geometry.b1373 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1373 0 (by decide +kernel) x hx hd ho).elim

theorem bound980 : BoxMajorant Geometry.b980 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b980 0 (by decide +kernel) x hx hd ho).elim

theorem bound979 : BoxMajorant Geometry.b979 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b979.Widths)
  · have he : Geometry.b979.half 1 false=Geometry.b1375 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1375
  · have he : Geometry.b979.half 1 true=Geometry.b1376 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1376

theorem bound978 : BoxMajorant Geometry.b978 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b978 0 (by decide +kernel) x hx hd ho).elim

theorem bound977 : BoxMajorant Geometry.b977 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b977.Widths)
  · have he : Geometry.b977.half 1 false=Geometry.b1373 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1373
  · have he : Geometry.b977.half 1 true=Geometry.b1374 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1374

theorem bound686 : BoxMajorant Geometry.b686 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b686.Widths)
  · have he : Geometry.b686.half 0 false=Geometry.b979 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound979
  · have he : Geometry.b686.half 0 true=Geometry.b980 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound980

theorem bound685 : BoxMajorant Geometry.b685 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b685.Widths)
  · have he : Geometry.b685.half 0 false=Geometry.b977 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound977
  · have he : Geometry.b685.half 0 true=Geometry.b978 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound978

theorem bound684 : BoxMajorant Geometry.b684 := by
  exact PositiveLeaves.L544.bound

theorem bound683 : BoxMajorant Geometry.b683 := by
  exact PositiveLeaves.L545.bound

theorem bound438 : BoxMajorant Geometry.b438 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b438.Widths)
  · have he : Geometry.b438.half 2 false=Geometry.b685 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound685
  · have he : Geometry.b438.half 2 true=Geometry.b686 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound686

theorem bound437 : BoxMajorant Geometry.b437 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b437 0 (by decide +kernel) x hx hd ho).elim

theorem bound436 : BoxMajorant Geometry.b436 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b436.Widths)
  · have he : Geometry.b436.half 2 false=Geometry.b683 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound683
  · have he : Geometry.b436.half 2 true=Geometry.b684 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound684

theorem bound435 : BoxMajorant Geometry.b435 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b435 0 (by decide +kernel) x hx hd ho).elim

theorem bound278 : BoxMajorant Geometry.b278 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b278 0 (by decide +kernel) x hx hd ho).elim

theorem bound277 : BoxMajorant Geometry.b277 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b277.Widths)
  · have he : Geometry.b277.half 1 false=Geometry.b437 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound437
  · have he : Geometry.b277.half 1 true=Geometry.b438 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound438

theorem bound276 : BoxMajorant Geometry.b276 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b276 0 (by decide +kernel) x hx hd ho).elim

theorem bound275 : BoxMajorant Geometry.b275 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b275.Widths)
  · have he : Geometry.b275.half 1 false=Geometry.b435 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound435
  · have he : Geometry.b275.half 1 true=Geometry.b436 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound436

theorem bound172 : BoxMajorant Geometry.b172 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b172.Widths)
  · have he : Geometry.b172.half 0 false=Geometry.b277 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound277
  · have he : Geometry.b172.half 0 true=Geometry.b278 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound278

theorem bound171 : BoxMajorant Geometry.b171 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b171.Widths)
  · have he : Geometry.b171.half 0 false=Geometry.b275 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound275
  · have he : Geometry.b171.half 0 true=Geometry.b276 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound276

theorem bound100 : BoxMajorant Geometry.b100 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b100.Widths)
  · have he : Geometry.b100.half 2 false=Geometry.b171 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound171
  · have he : Geometry.b100.half 2 true=Geometry.b172 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound172

theorem bound99 : BoxMajorant Geometry.b99 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b99 0 (by decide +kernel) x hx hd ho).elim

theorem bound53 : BoxMajorant Geometry.b53 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b53.Widths)
  · have he : Geometry.b53.half 1 false=Geometry.b99 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound99
  · have he : Geometry.b53.half 1 true=Geometry.b100 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound100

end N7.Kernel.Cover
