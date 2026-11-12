import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0000
import N7.Kernel.CoverGeometry.G0001
import N7.Kernel.CoverGeometry.G0002
import N7.Kernel.CoverGeometry.G0003
import N7.Kernel.CoverGeometry.G0005
import N7.Kernel.CoverGeometry.G0008
import N7.Kernel.CoverGeometry.G0009
import N7.Kernel.CoverGeometry.G0013
import N7.Kernel.CoverProofs.P0076
import N7.Kernel.CoverProofs.P0077
import N7.Kernel.CoverProofs.P0078
import N7.Kernel.CoverProofs.P0079
import N7.Kernel.PositiveGroups.G0005
import N7.Kernel.PositiveGroups.G0010
import N7.Kernel.PositiveGroups.G0020
import N7.Kernel.PositiveGroups.G0021
import N7.Kernel.PositiveGroups.G0042
import N7.Kernel.PositiveGroups.G0068
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound848 : BoxMajorant Geometry.b848 := by
  exact PositiveLeaves.L1365.bound

theorem bound846 : BoxMajorant Geometry.b846 := by
  exact PositiveLeaves.L1394.bound

theorem bound844 : BoxMajorant Geometry.b844 := by
  exact PositiveLeaves.L1407.bound

theorem bound575 : BoxMajorant Geometry.b575 := by
  exact PositiveLeaves.L1359.bound

theorem bound574 : BoxMajorant Geometry.b574 := by
  exact PositiveLeaves.L1360.bound

theorem bound573 : BoxMajorant Geometry.b573 := by
  exact PositiveLeaves.L1361.bound

theorem bound572 : BoxMajorant Geometry.b572 := by
  exact PositiveLeaves.L1364.bound

theorem bound571 : BoxMajorant Geometry.b571 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b571.Widths)
  · have he : Geometry.b571.half 0 false=Geometry.b847 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound847
  · have he : Geometry.b571.half 0 true=Geometry.b848 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound848

theorem bound570 : BoxMajorant Geometry.b570 := by
  exact PositiveLeaves.L1389.bound

theorem bound569 : BoxMajorant Geometry.b569 := by
  exact PositiveLeaves.L1390.bound

theorem bound568 : BoxMajorant Geometry.b568 := by
  exact PositiveLeaves.L1393.bound

theorem bound567 : BoxMajorant Geometry.b567 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b567.Widths)
  · have he : Geometry.b567.half 0 false=Geometry.b845 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound845
  · have he : Geometry.b567.half 0 true=Geometry.b846 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound846

theorem bound566 : BoxMajorant Geometry.b566 := by
  exact PositiveLeaves.L1406.bound

theorem bound565 : BoxMajorant Geometry.b565 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b565.Widths)
  · have he : Geometry.b565.half 0 false=Geometry.b843 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound843
  · have he : Geometry.b565.half 0 true=Geometry.b844 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound844

theorem bound366 : BoxMajorant Geometry.b366 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b366.Widths)
  · have he : Geometry.b366.half 2 false=Geometry.b575 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound575
  · have he : Geometry.b366.half 2 true=Geometry.b576 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound576

theorem bound365 : BoxMajorant Geometry.b365 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b365.Widths)
  · have he : Geometry.b365.half 2 false=Geometry.b573 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound573
  · have he : Geometry.b365.half 2 true=Geometry.b574 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound574

theorem bound364 : BoxMajorant Geometry.b364 := by
  exact PositiveLeaves.L1363.bound

theorem bound363 : BoxMajorant Geometry.b363 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b363.Widths)
  · have he : Geometry.b363.half 2 false=Geometry.b571 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound571
  · have he : Geometry.b363.half 2 true=Geometry.b572 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound572

theorem bound362 : BoxMajorant Geometry.b362 := by
  exact PositiveLeaves.L1388.bound

theorem bound361 : BoxMajorant Geometry.b361 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b361.Widths)
  · have he : Geometry.b361.half 2 false=Geometry.b569 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound569
  · have he : Geometry.b361.half 2 true=Geometry.b570 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound570

theorem bound360 : BoxMajorant Geometry.b360 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b360.Widths)
  · have he : Geometry.b360.half 2 false=Geometry.b567 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound567
  · have he : Geometry.b360.half 2 true=Geometry.b568 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound568

theorem bound359 : BoxMajorant Geometry.b359 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b359.Widths)
  · have he : Geometry.b359.half 2 false=Geometry.b565 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound565
  · have he : Geometry.b359.half 2 true=Geometry.b566 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound566

theorem bound230 : BoxMajorant Geometry.b230 := by
  exact PositiveLeaves.L1356.bound

theorem bound229 : BoxMajorant Geometry.b229 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b229.Widths)
  · have he : Geometry.b229.half 1 false=Geometry.b365 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound365
  · have he : Geometry.b229.half 1 true=Geometry.b366 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound366

theorem bound228 : BoxMajorant Geometry.b228 := by
  exact PositiveLeaves.L1362.bound

theorem bound227 : BoxMajorant Geometry.b227 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b227.Widths)
  · have he : Geometry.b227.half 1 false=Geometry.b363 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound363
  · have he : Geometry.b227.half 1 true=Geometry.b364 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound364

theorem bound226 : BoxMajorant Geometry.b226 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b226.Widths)
  · have he : Geometry.b226.half 1 false=Geometry.b361 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound361
  · have he : Geometry.b226.half 1 true=Geometry.b362 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound362

theorem bound225 : BoxMajorant Geometry.b225 := by
  exact PositiveLeaves.L1391.bound

theorem bound224 : BoxMajorant Geometry.b224 := by
  exact PositiveLeaves.L1392.bound

theorem bound223 : BoxMajorant Geometry.b223 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b223.Widths)
  · have he : Geometry.b223.half 1 false=Geometry.b359 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound359
  · have he : Geometry.b223.half 1 true=Geometry.b360 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound360

theorem bound134 : BoxMajorant Geometry.b134 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b134.Widths)
  · have he : Geometry.b134.half 0 false=Geometry.b229 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound229
  · have he : Geometry.b134.half 0 true=Geometry.b230 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound230

theorem bound133 : BoxMajorant Geometry.b133 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b133.Widths)
  · have he : Geometry.b133.half 0 false=Geometry.b227 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound227
  · have he : Geometry.b133.half 0 true=Geometry.b228 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound228

theorem bound132 : BoxMajorant Geometry.b132 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b132.Widths)
  · have he : Geometry.b132.half 0 false=Geometry.b225 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound225
  · have he : Geometry.b132.half 0 true=Geometry.b226 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound226

theorem bound131 : BoxMajorant Geometry.b131 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b131.Widths)
  · have he : Geometry.b131.half 0 false=Geometry.b223 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound223
  · have he : Geometry.b131.half 0 true=Geometry.b224 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound224

theorem bound74 : BoxMajorant Geometry.b74 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b74.Widths)
  · have he : Geometry.b74.half 2 false=Geometry.b133 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound133
  · have he : Geometry.b74.half 2 true=Geometry.b134 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound134

theorem bound73 : BoxMajorant Geometry.b73 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b73.Widths)
  · have he : Geometry.b73.half 2 false=Geometry.b131 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound131
  · have he : Geometry.b73.half 2 true=Geometry.b132 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound132

theorem bound38 : BoxMajorant Geometry.b38 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b38.Widths)
  · have he : Geometry.b38.half 1 false=Geometry.b73 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound73
  · have he : Geometry.b38.half 1 true=Geometry.b74 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound74

end N7.Kernel.Cover
