import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0000
import N7.Kernel.CoverGeometry.G0001
import N7.Kernel.CoverGeometry.G0003
import N7.Kernel.CoverGeometry.G0005
import N7.Kernel.CoverGeometry.G0007
import N7.Kernel.CoverGeometry.G0008
import N7.Kernel.CoverGeometry.G0012
import N7.Kernel.CoverProofs.P0044
import N7.Kernel.CoverProofs.P0045
import N7.Kernel.CoverProofs.P0046
import N7.Kernel.CoverProofs.P0047
import N7.Kernel.CoverProofs.P0048
import N7.Kernel.CoverProofs.P0049
import N7.Kernel.CoverProofs.P0050
import N7.Kernel.CoverProofs.P0051
import N7.Kernel.PositiveGroups.G0012
import N7.Kernel.PositiveGroups.G0013
import N7.Kernel.PositiveGroups.G0025
import N7.Kernel.PositiveGroups.G0026
import N7.Kernel.PositiveGroups.G0027
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound788 : BoxMajorant Geometry.b788 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b788 0 (by decide +kernel) x hx hd ho).elim

theorem bound786 : BoxMajorant Geometry.b786 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b786 0 (by decide +kernel) x hx hd ho).elim

theorem bound522 : BoxMajorant Geometry.b522 := by
  exact PositiveLeaves.L2375.bound

theorem bound521 : BoxMajorant Geometry.b521 := by
  exact PositiveLeaves.L2376.bound

theorem bound520 : BoxMajorant Geometry.b520 := by
  exact PositiveLeaves.L2377.bound

theorem bound519 : BoxMajorant Geometry.b519 := by
  exact PositiveLeaves.L2378.bound

theorem bound517 : BoxMajorant Geometry.b517 := by
  exact PositiveLeaves.L2383.bound

theorem bound516 : BoxMajorant Geometry.b516 := by
  exact PositiveLeaves.L2384.bound

theorem bound514 : BoxMajorant Geometry.b514 := by
  exact PositiveLeaves.L2391.bound

theorem bound512 : BoxMajorant Geometry.b512 := by
  exact PositiveLeaves.L2396.bound

theorem bound508 : BoxMajorant Geometry.b508 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b508.Widths)
  · have he : Geometry.b508.half 0 false=Geometry.b787 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound787
  · have he : Geometry.b508.half 0 true=Geometry.b788 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound788

theorem bound507 : BoxMajorant Geometry.b507 := by
  exact PositiveLeaves.L2424.bound

theorem bound506 : BoxMajorant Geometry.b506 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b506.Widths)
  · have he : Geometry.b506.half 0 false=Geometry.b785 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound785
  · have he : Geometry.b506.half 0 true=Geometry.b786 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound786

theorem bound505 : BoxMajorant Geometry.b505 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b505 2 (by decide +kernel) x hx hd ho).elim

theorem bound332 : BoxMajorant Geometry.b332 := by
  exact PositiveLeaves.L2374.bound

theorem bound331 : BoxMajorant Geometry.b331 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b331.Widths)
  · have he : Geometry.b331.half 2 false=Geometry.b521 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound521
  · have he : Geometry.b331.half 2 true=Geometry.b522 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound522

theorem bound330 : BoxMajorant Geometry.b330 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b330.Widths)
  · have he : Geometry.b330.half 2 false=Geometry.b519 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound519
  · have he : Geometry.b330.half 2 true=Geometry.b520 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound520

theorem bound329 : BoxMajorant Geometry.b329 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b329.Widths)
  · have he : Geometry.b329.half 2 false=Geometry.b517 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound517
  · have he : Geometry.b329.half 2 true=Geometry.b518 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound518

theorem bound328 : BoxMajorant Geometry.b328 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b328.Widths)
  · have he : Geometry.b328.half 2 false=Geometry.b515 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound515
  · have he : Geometry.b328.half 2 true=Geometry.b516 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound516

theorem bound327 : BoxMajorant Geometry.b327 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b327.Widths)
  · have he : Geometry.b327.half 2 false=Geometry.b513 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound513
  · have he : Geometry.b327.half 2 true=Geometry.b514 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound514

theorem bound326 : BoxMajorant Geometry.b326 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b326.Widths)
  · have he : Geometry.b326.half 2 false=Geometry.b511 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound511
  · have he : Geometry.b326.half 2 true=Geometry.b512 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound512

theorem bound325 : BoxMajorant Geometry.b325 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b325.Widths)
  · have he : Geometry.b325.half 2 false=Geometry.b509 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound509
  · have he : Geometry.b325.half 2 true=Geometry.b510 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound510

theorem bound324 : BoxMajorant Geometry.b324 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b324.Widths)
  · have he : Geometry.b324.half 2 false=Geometry.b507 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound507
  · have he : Geometry.b324.half 2 true=Geometry.b508 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound508

theorem bound323 : BoxMajorant Geometry.b323 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b323 0 (by decide +kernel) x hx hd ho).elim

theorem bound322 : BoxMajorant Geometry.b322 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b322.Widths)
  · have he : Geometry.b322.half 2 false=Geometry.b505 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound505
  · have he : Geometry.b322.half 2 true=Geometry.b506 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound506

theorem bound321 : BoxMajorant Geometry.b321 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b321 0 (by decide +kernel) x hx hd ho).elim

theorem bound208 : BoxMajorant Geometry.b208 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b208.Widths)
  · have he : Geometry.b208.half 1 false=Geometry.b331 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound331
  · have he : Geometry.b208.half 1 true=Geometry.b332 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound332

theorem bound207 : BoxMajorant Geometry.b207 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b207.Widths)
  · have he : Geometry.b207.half 1 false=Geometry.b329 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound329
  · have he : Geometry.b207.half 1 true=Geometry.b330 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound330

theorem bound206 : BoxMajorant Geometry.b206 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b206.Widths)
  · have he : Geometry.b206.half 1 false=Geometry.b327 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound327
  · have he : Geometry.b206.half 1 true=Geometry.b328 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound328

theorem bound205 : BoxMajorant Geometry.b205 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b205.Widths)
  · have he : Geometry.b205.half 1 false=Geometry.b325 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound325
  · have he : Geometry.b205.half 1 true=Geometry.b326 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound326

theorem bound204 : BoxMajorant Geometry.b204 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b204 0 (by decide +kernel) x hx hd ho).elim

theorem bound203 : BoxMajorant Geometry.b203 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b203.Widths)
  · have he : Geometry.b203.half 1 false=Geometry.b323 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound323
  · have he : Geometry.b203.half 1 true=Geometry.b324 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound324

theorem bound202 : BoxMajorant Geometry.b202 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b202 0 (by decide +kernel) x hx hd ho).elim

theorem bound201 : BoxMajorant Geometry.b201 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b201.Widths)
  · have he : Geometry.b201.half 1 false=Geometry.b321 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound321
  · have he : Geometry.b201.half 1 true=Geometry.b322 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound322

theorem bound120 : BoxMajorant Geometry.b120 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b120.Widths)
  · have he : Geometry.b120.half 0 false=Geometry.b207 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound207
  · have he : Geometry.b120.half 0 true=Geometry.b208 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound208

theorem bound119 : BoxMajorant Geometry.b119 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b119.Widths)
  · have he : Geometry.b119.half 0 false=Geometry.b205 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound205
  · have he : Geometry.b119.half 0 true=Geometry.b206 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound206

theorem bound118 : BoxMajorant Geometry.b118 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b118.Widths)
  · have he : Geometry.b118.half 0 false=Geometry.b203 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound203
  · have he : Geometry.b118.half 0 true=Geometry.b204 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound204

theorem bound117 : BoxMajorant Geometry.b117 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b117.Widths)
  · have he : Geometry.b117.half 0 false=Geometry.b201 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound201
  · have he : Geometry.b117.half 0 true=Geometry.b202 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound202

theorem bound66 : BoxMajorant Geometry.b66 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b66.Widths)
  · have he : Geometry.b66.half 2 false=Geometry.b119 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound119
  · have he : Geometry.b66.half 2 true=Geometry.b120 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound120

theorem bound65 : BoxMajorant Geometry.b65 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b65.Widths)
  · have he : Geometry.b65.half 2 false=Geometry.b117 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound117
  · have he : Geometry.b65.half 2 true=Geometry.b118 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound118

theorem bound34 : BoxMajorant Geometry.b34 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b34.Widths)
  · have he : Geometry.b34.half 1 false=Geometry.b65 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound65
  · have he : Geometry.b34.half 1 true=Geometry.b66 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound66

end N7.Kernel.Cover
