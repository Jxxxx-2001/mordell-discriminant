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
import N7.Kernel.CoverGeometry.G0030
import N7.Kernel.CoverGeometry.G0031
import N7.Kernel.CoverProofs.P0151
import N7.Kernel.CoverProofs.P0152
import N7.Kernel.CoverProofs.P0153
import N7.Kernel.CoverProofs.P0154
import N7.Kernel.CoverProofs.P0155
import N7.Kernel.PositiveGroups.G0001
import N7.Kernel.PositiveGroups.G0004
import N7.Kernel.PositiveGroups.G0007
import N7.Kernel.PositiveGroups.G0028
import N7.Kernel.PositiveGroups.G0029
import N7.Kernel.PositiveGroups.G0051
import N7.Kernel.PositiveGroups.G0052
import N7.Kernel.PositiveGroups.G0079
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound1984 : BoxMajorant Geometry.b1984 := by
  exact PositiveLeaves.L562.bound

theorem bound1983 : BoxMajorant Geometry.b1983 := by
  exact PositiveLeaves.L563.bound

theorem bound1982 : BoxMajorant Geometry.b1982 := by
  exact PositiveLeaves.L566.bound

theorem bound1981 : BoxMajorant Geometry.b1981 := by
  exact PositiveLeaves.L567.bound

theorem bound1980 : BoxMajorant Geometry.b1980 := by
  exact PositiveLeaves.L568.bound

theorem bound1979 : BoxMajorant Geometry.b1979 := by
  exact PositiveLeaves.L569.bound

theorem bound1978 : BoxMajorant Geometry.b1978 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b1978 3 (by decide +kernel) x hx hd ho).elim

theorem bound1977 : BoxMajorant Geometry.b1977 := by
  exact PositiveLeaves.L571.bound

theorem bound1372 : BoxMajorant Geometry.b1372 := by
  exact PositiveLeaves.L550.bound

theorem bound1366 : BoxMajorant Geometry.b1366 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1366.Widths)
  · have he : Geometry.b1366.half 2 false=Geometry.b1983 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1983
  · have he : Geometry.b1366.half 2 true=Geometry.b1984 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1984

theorem bound1365 : BoxMajorant Geometry.b1365 := by
  exact PositiveLeaves.L564.bound

theorem bound1364 : BoxMajorant Geometry.b1364 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1364.Widths)
  · have he : Geometry.b1364.half 2 false=Geometry.b1981 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1981
  · have he : Geometry.b1364.half 2 true=Geometry.b1982 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1982

theorem bound1363 : BoxMajorant Geometry.b1363 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1363.Widths)
  · have he : Geometry.b1363.half 2 false=Geometry.b1979 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1979
  · have he : Geometry.b1363.half 2 true=Geometry.b1980 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1980

theorem bound1362 : BoxMajorant Geometry.b1362 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1362.Widths)
  · have he : Geometry.b1362.half 2 false=Geometry.b1977 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1977
  · have he : Geometry.b1362.half 2 true=Geometry.b1978 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1978

theorem bound1361 : BoxMajorant Geometry.b1361 := by
  exact PositiveLeaves.L572.bound

theorem bound976 : BoxMajorant Geometry.b976 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b976.Widths)
  · have he : Geometry.b976.half 1 false=Geometry.b1371 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1371
  · have he : Geometry.b976.half 1 true=Geometry.b1372 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1372

theorem bound975 : BoxMajorant Geometry.b975 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b975.Widths)
  · have he : Geometry.b975.half 1 false=Geometry.b1369 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1369
  · have he : Geometry.b975.half 1 true=Geometry.b1370 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1370

theorem bound974 : BoxMajorant Geometry.b974 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b974.Widths)
  · have he : Geometry.b974.half 1 false=Geometry.b1367 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1367
  · have he : Geometry.b974.half 1 true=Geometry.b1368 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1368

theorem bound973 : BoxMajorant Geometry.b973 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b973.Widths)
  · have he : Geometry.b973.half 1 false=Geometry.b1365 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1365
  · have he : Geometry.b973.half 1 true=Geometry.b1366 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1366

theorem bound972 : BoxMajorant Geometry.b972 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b972.Widths)
  · have he : Geometry.b972.half 1 false=Geometry.b1363 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1363
  · have he : Geometry.b972.half 1 true=Geometry.b1364 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1364

theorem bound971 : BoxMajorant Geometry.b971 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b971.Widths)
  · have he : Geometry.b971.half 1 false=Geometry.b1361 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1361
  · have he : Geometry.b971.half 1 true=Geometry.b1362 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1362

theorem bound682 : BoxMajorant Geometry.b682 := by
  exact PositiveLeaves.L549.bound

theorem bound681 : BoxMajorant Geometry.b681 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b681.Widths)
  · have he : Geometry.b681.half 0 false=Geometry.b975 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound975
  · have he : Geometry.b681.half 0 true=Geometry.b976 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound976

theorem bound680 : BoxMajorant Geometry.b680 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b680 1 (by decide +kernel) x hx hd ho).elim

theorem bound679 : BoxMajorant Geometry.b679 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b679.Widths)
  · have he : Geometry.b679.half 0 false=Geometry.b973 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound973
  · have he : Geometry.b679.half 0 true=Geometry.b974 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound974

theorem bound678 : BoxMajorant Geometry.b678 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b678 1 (by decide +kernel) x hx hd ho).elim

theorem bound677 : BoxMajorant Geometry.b677 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b677.Widths)
  · have he : Geometry.b677.half 0 false=Geometry.b971 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound971
  · have he : Geometry.b677.half 0 true=Geometry.b972 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound972

theorem bound434 : BoxMajorant Geometry.b434 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b434.Widths)
  · have he : Geometry.b434.half 2 false=Geometry.b681 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound681
  · have he : Geometry.b434.half 2 true=Geometry.b682 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound682

theorem bound433 : BoxMajorant Geometry.b433 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b433.Widths)
  · have he : Geometry.b433.half 2 false=Geometry.b679 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound679
  · have he : Geometry.b433.half 2 true=Geometry.b680 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound680

theorem bound432 : BoxMajorant Geometry.b432 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b432.Widths)
  · have he : Geometry.b432.half 2 false=Geometry.b677 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound677
  · have he : Geometry.b432.half 2 true=Geometry.b678 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound678

theorem bound431 : BoxMajorant Geometry.b431 := by
  exact PositiveLeaves.L573.bound

theorem bound274 : BoxMajorant Geometry.b274 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b274.Widths)
  · have he : Geometry.b274.half 1 false=Geometry.b433 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound433
  · have he : Geometry.b274.half 1 true=Geometry.b434 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound434

theorem bound273 : BoxMajorant Geometry.b273 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b273.Widths)
  · have he : Geometry.b273.half 1 false=Geometry.b431 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound431
  · have he : Geometry.b273.half 1 true=Geometry.b432 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound432

theorem bound170 : BoxMajorant Geometry.b170 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b170 1 (by decide +kernel) x hx hd ho).elim

theorem bound169 : BoxMajorant Geometry.b169 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b169.Widths)
  · have he : Geometry.b169.half 0 false=Geometry.b273 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound273
  · have he : Geometry.b169.half 0 true=Geometry.b274 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound274

theorem bound168 : BoxMajorant Geometry.b168 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b168 1 (by decide +kernel) x hx hd ho).elim

theorem bound167 : BoxMajorant Geometry.b167 := by
  exact PositiveLeaves.L575.bound

theorem bound98 : BoxMajorant Geometry.b98 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b98.Widths)
  · have he : Geometry.b98.half 2 false=Geometry.b169 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound169
  · have he : Geometry.b98.half 2 true=Geometry.b170 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound170

theorem bound97 : BoxMajorant Geometry.b97 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b97.Widths)
  · have he : Geometry.b97.half 2 false=Geometry.b167 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound167
  · have he : Geometry.b97.half 2 true=Geometry.b168 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound168

theorem bound52 : BoxMajorant Geometry.b52 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b52.Widths)
  · have he : Geometry.b52.half 1 false=Geometry.b97 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound97
  · have he : Geometry.b52.half 1 true=Geometry.b98 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound98

end N7.Kernel.Cover
