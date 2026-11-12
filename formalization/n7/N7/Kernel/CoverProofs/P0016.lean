import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0000
import N7.Kernel.CoverGeometry.G0001
import N7.Kernel.CoverGeometry.G0002
import N7.Kernel.CoverGeometry.G0004
import N7.Kernel.CoverGeometry.G0006
import N7.Kernel.CoverGeometry.G0009
import N7.Kernel.CoverGeometry.G0010
import N7.Kernel.CoverProofs.P0116
import N7.Kernel.CoverProofs.P0117
import N7.Kernel.CoverProofs.P0118
import N7.Kernel.CoverProofs.P0119
import N7.Kernel.CoverProofs.P0120
import N7.Kernel.CoverProofs.P0121
import N7.Kernel.CoverProofs.P0122
import N7.Kernel.CoverProofs.P0123
import N7.Kernel.CoverProofs.P0124
import N7.Kernel.CoverProofs.P0125
import N7.Kernel.CoverProofs.P0126
import N7.Kernel.CoverProofs.P0127
import N7.Kernel.CoverProofs.P0128
import N7.Kernel.CoverProofs.P0129
import N7.Kernel.CoverProofs.P0130
import N7.Kernel.CoverProofs.P0131
import N7.Kernel.CoverProofs.P0132
import N7.Kernel.CoverProofs.P0133
import N7.Kernel.CoverProofs.P0134
import N7.Kernel.CoverProofs.P0135
import N7.Kernel.PositiveGroups.G0008
import N7.Kernel.PositiveGroups.G0015
import N7.Kernel.PositiveGroups.G0029
import N7.Kernel.PositiveGroups.G0030
import N7.Kernel.PositiveGroups.G0053
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound644 : BoxMajorant Geometry.b644 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b644 3 (by decide +kernel) x hx hd ho).elim

theorem bound642 : BoxMajorant Geometry.b642 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b642 3 (by decide +kernel) x hx hd ho).elim

theorem bound640 : BoxMajorant Geometry.b640 := by
  exact PositiveLeaves.L803.bound

theorem bound639 : BoxMajorant Geometry.b639 := by
  exact PositiveLeaves.L804.bound

theorem bound636 : BoxMajorant Geometry.b636 := by
  exact PositiveLeaves.L814.bound

theorem bound635 : BoxMajorant Geometry.b635 := by
  exact PositiveLeaves.L815.bound

theorem bound632 : BoxMajorant Geometry.b632 := by
  exact PositiveLeaves.L823.bound

theorem bound630 : BoxMajorant Geometry.b630 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b630 1 (by decide +kernel) x hx hd ho).elim

theorem bound628 : BoxMajorant Geometry.b628 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b628 1 (by decide +kernel) x hx hd ho).elim

theorem bound623 : BoxMajorant Geometry.b623 := by
  exact PositiveLeaves.L877.bound

theorem bound414 : BoxMajorant Geometry.b414 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b414.Widths)
  · have he : Geometry.b414.half 2 false=Geometry.b647 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound647
  · have he : Geometry.b414.half 2 true=Geometry.b648 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound648

theorem bound413 : BoxMajorant Geometry.b413 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b413.Widths)
  · have he : Geometry.b413.half 2 false=Geometry.b645 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound645
  · have he : Geometry.b413.half 2 true=Geometry.b646 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound646

theorem bound412 : BoxMajorant Geometry.b412 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b412.Widths)
  · have he : Geometry.b412.half 2 false=Geometry.b643 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound643
  · have he : Geometry.b412.half 2 true=Geometry.b644 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound644

theorem bound411 : BoxMajorant Geometry.b411 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b411.Widths)
  · have he : Geometry.b411.half 2 false=Geometry.b641 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound641
  · have he : Geometry.b411.half 2 true=Geometry.b642 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound642

theorem bound410 : BoxMajorant Geometry.b410 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b410.Widths)
  · have he : Geometry.b410.half 2 false=Geometry.b639 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound639
  · have he : Geometry.b410.half 2 true=Geometry.b640 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound640

theorem bound409 : BoxMajorant Geometry.b409 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b409.Widths)
  · have he : Geometry.b409.half 2 false=Geometry.b637 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound637
  · have he : Geometry.b409.half 2 true=Geometry.b638 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound638

theorem bound408 : BoxMajorant Geometry.b408 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b408.Widths)
  · have he : Geometry.b408.half 2 false=Geometry.b635 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound635
  · have he : Geometry.b408.half 2 true=Geometry.b636 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound636

theorem bound407 : BoxMajorant Geometry.b407 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b407.Widths)
  · have he : Geometry.b407.half 2 false=Geometry.b633 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound633
  · have he : Geometry.b407.half 2 true=Geometry.b634 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound634

theorem bound406 : BoxMajorant Geometry.b406 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b406.Widths)
  · have he : Geometry.b406.half 2 false=Geometry.b631 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound631
  · have he : Geometry.b406.half 2 true=Geometry.b632 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound632

theorem bound405 : BoxMajorant Geometry.b405 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b405.Widths)
  · have he : Geometry.b405.half 2 false=Geometry.b629 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound629
  · have he : Geometry.b405.half 2 true=Geometry.b630 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound630

theorem bound404 : BoxMajorant Geometry.b404 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b404.Widths)
  · have he : Geometry.b404.half 2 false=Geometry.b627 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound627
  · have he : Geometry.b404.half 2 true=Geometry.b628 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound628

theorem bound403 : BoxMajorant Geometry.b403 := by
  exact PositiveLeaves.L847.bound

theorem bound402 : BoxMajorant Geometry.b402 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b402.Widths)
  · have he : Geometry.b402.half 2 false=Geometry.b625 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound625
  · have he : Geometry.b402.half 2 true=Geometry.b626 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound626

theorem bound401 : BoxMajorant Geometry.b401 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b401.Widths)
  · have he : Geometry.b401.half 2 false=Geometry.b623 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound623
  · have he : Geometry.b401.half 2 true=Geometry.b624 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound624

theorem bound400 : BoxMajorant Geometry.b400 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b400.Widths)
  · have he : Geometry.b400.half 2 false=Geometry.b621 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound621
  · have he : Geometry.b400.half 2 true=Geometry.b622 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound622

theorem bound399 : BoxMajorant Geometry.b399 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b399.Widths)
  · have he : Geometry.b399.half 2 false=Geometry.b619 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound619
  · have he : Geometry.b399.half 2 true=Geometry.b620 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound620

theorem bound264 : BoxMajorant Geometry.b264 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b264.Widths)
  · have he : Geometry.b264.half 1 false=Geometry.b413 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound413
  · have he : Geometry.b264.half 1 true=Geometry.b414 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound414

theorem bound263 : BoxMajorant Geometry.b263 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b263.Widths)
  · have he : Geometry.b263.half 1 false=Geometry.b411 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound411
  · have he : Geometry.b263.half 1 true=Geometry.b412 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound412

theorem bound262 : BoxMajorant Geometry.b262 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b262.Widths)
  · have he : Geometry.b262.half 1 false=Geometry.b409 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound409
  · have he : Geometry.b262.half 1 true=Geometry.b410 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound410

theorem bound261 : BoxMajorant Geometry.b261 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b261.Widths)
  · have he : Geometry.b261.half 1 false=Geometry.b407 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound407
  · have he : Geometry.b261.half 1 true=Geometry.b408 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound408

theorem bound260 : BoxMajorant Geometry.b260 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b260.Widths)
  · have he : Geometry.b260.half 1 false=Geometry.b405 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound405
  · have he : Geometry.b260.half 1 true=Geometry.b406 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound406

theorem bound259 : BoxMajorant Geometry.b259 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b259.Widths)
  · have he : Geometry.b259.half 1 false=Geometry.b403 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound403
  · have he : Geometry.b259.half 1 true=Geometry.b404 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound404

theorem bound258 : BoxMajorant Geometry.b258 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b258.Widths)
  · have he : Geometry.b258.half 1 false=Geometry.b401 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound401
  · have he : Geometry.b258.half 1 true=Geometry.b402 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound402

theorem bound257 : BoxMajorant Geometry.b257 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b257.Widths)
  · have he : Geometry.b257.half 1 false=Geometry.b399 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound399
  · have he : Geometry.b257.half 1 true=Geometry.b400 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound400

theorem bound160 : BoxMajorant Geometry.b160 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b160.Widths)
  · have he : Geometry.b160.half 0 false=Geometry.b263 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound263
  · have he : Geometry.b160.half 0 true=Geometry.b264 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound264

theorem bound159 : BoxMajorant Geometry.b159 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b159.Widths)
  · have he : Geometry.b159.half 0 false=Geometry.b261 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound261
  · have he : Geometry.b159.half 0 true=Geometry.b262 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound262

theorem bound158 : BoxMajorant Geometry.b158 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b158.Widths)
  · have he : Geometry.b158.half 0 false=Geometry.b259 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound259
  · have he : Geometry.b158.half 0 true=Geometry.b260 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound260

theorem bound157 : BoxMajorant Geometry.b157 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b157.Widths)
  · have he : Geometry.b157.half 0 false=Geometry.b257 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound257
  · have he : Geometry.b157.half 0 true=Geometry.b258 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound258

theorem bound92 : BoxMajorant Geometry.b92 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b92.Widths)
  · have he : Geometry.b92.half 2 false=Geometry.b159 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound159
  · have he : Geometry.b92.half 2 true=Geometry.b160 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound160

theorem bound91 : BoxMajorant Geometry.b91 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b91.Widths)
  · have he : Geometry.b91.half 2 false=Geometry.b157 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound157
  · have he : Geometry.b91.half 2 true=Geometry.b158 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound158

theorem bound49 : BoxMajorant Geometry.b49 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b49.Widths)
  · have he : Geometry.b49.half 1 false=Geometry.b91 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound91
  · have he : Geometry.b49.half 1 true=Geometry.b92 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound92

end N7.Kernel.Cover
