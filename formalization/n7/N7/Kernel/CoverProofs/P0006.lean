import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0000
import N7.Kernel.CoverGeometry.G0001
import N7.Kernel.CoverGeometry.G0002
import N7.Kernel.CoverGeometry.G0003
import N7.Kernel.CoverGeometry.G0005
import N7.Kernel.CoverGeometry.G0008
import N7.Kernel.CoverProofs.P0063
import N7.Kernel.CoverProofs.P0064
import N7.Kernel.CoverProofs.P0065
import N7.Kernel.CoverProofs.P0066
import N7.Kernel.CoverProofs.P0067
import N7.Kernel.CoverProofs.P0068
import N7.Kernel.CoverProofs.P0069
import N7.Kernel.CoverProofs.P0070
import N7.Kernel.CoverProofs.P0071
import N7.Kernel.CoverProofs.P0072
import N7.Kernel.CoverProofs.P0073
import N7.Kernel.CoverProofs.P0074
import N7.Kernel.CoverProofs.P0075
import N7.Kernel.PositiveGroups.G0010
import N7.Kernel.PositiveGroups.G0011
import N7.Kernel.PositiveGroups.G0021
import N7.Kernel.PositiveGroups.G0022
import N7.Kernel.PositiveGroups.G0023
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound564 : BoxMajorant Geometry.b564 := by
  exact PositiveLeaves.L1413.bound

theorem bound563 : BoxMajorant Geometry.b563 := by
  exact PositiveLeaves.L1414.bound

theorem bound562 : BoxMajorant Geometry.b562 := by
  exact PositiveLeaves.L1416.bound

theorem bound560 : BoxMajorant Geometry.b560 := by
  exact PositiveLeaves.L1432.bound

theorem bound553 : BoxMajorant Geometry.b553 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b553 2 (by decide +kernel) x hx hd ho).elim

theorem bound551 : BoxMajorant Geometry.b551 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b551 2 (by decide +kernel) x hx hd ho).elim

theorem bound550 : BoxMajorant Geometry.b550 := by
  exact PositiveLeaves.L2165.bound

theorem bound549 : BoxMajorant Geometry.b549 := by
  exact PositiveLeaves.L2166.bound

theorem bound548 : BoxMajorant Geometry.b548 := by
  exact PositiveLeaves.L2167.bound

theorem bound547 : BoxMajorant Geometry.b547 := by
  exact PositiveLeaves.L2168.bound

theorem bound545 : BoxMajorant Geometry.b545 := by
  exact PositiveLeaves.L2228.bound

theorem bound544 : BoxMajorant Geometry.b544 := by
  exact PositiveLeaves.L2229.bound

theorem bound542 : BoxMajorant Geometry.b542 := by
  exact PositiveLeaves.L2240.bound

theorem bound539 : BoxMajorant Geometry.b539 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b539 2 (by decide +kernel) x hx hd ho).elim

theorem bound537 : BoxMajorant Geometry.b537 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b537 2 (by decide +kernel) x hx hd ho).elim

theorem bound358 : BoxMajorant Geometry.b358 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b358.Widths)
  · have he : Geometry.b358.half 2 false=Geometry.b563 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound563
  · have he : Geometry.b358.half 2 true=Geometry.b564 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound564

theorem bound357 : BoxMajorant Geometry.b357 := by
  exact PositiveLeaves.L1415.bound

theorem bound356 : BoxMajorant Geometry.b356 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b356.Widths)
  · have he : Geometry.b356.half 2 false=Geometry.b561 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound561
  · have he : Geometry.b356.half 2 true=Geometry.b562 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound562

theorem bound355 : BoxMajorant Geometry.b355 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b355.Widths)
  · have he : Geometry.b355.half 2 false=Geometry.b559 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound559
  · have he : Geometry.b355.half 2 true=Geometry.b560 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound560

theorem bound354 : BoxMajorant Geometry.b354 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b354.Widths)
  · have he : Geometry.b354.half 2 false=Geometry.b557 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound557
  · have he : Geometry.b354.half 2 true=Geometry.b558 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound558

theorem bound353 : BoxMajorant Geometry.b353 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b353.Widths)
  · have he : Geometry.b353.half 2 false=Geometry.b555 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound555
  · have he : Geometry.b353.half 2 true=Geometry.b556 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound556

theorem bound352 : BoxMajorant Geometry.b352 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b352.Widths)
  · have he : Geometry.b352.half 2 false=Geometry.b553 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound553
  · have he : Geometry.b352.half 2 true=Geometry.b554 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound554

theorem bound351 : BoxMajorant Geometry.b351 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b351.Widths)
  · have he : Geometry.b351.half 2 false=Geometry.b551 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound551
  · have he : Geometry.b351.half 2 true=Geometry.b552 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound552

theorem bound350 : BoxMajorant Geometry.b350 := by
  exact PositiveLeaves.L2164.bound

theorem bound349 : BoxMajorant Geometry.b349 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b349.Widths)
  · have he : Geometry.b349.half 2 false=Geometry.b549 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound549
  · have he : Geometry.b349.half 2 true=Geometry.b550 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound550

theorem bound348 : BoxMajorant Geometry.b348 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b348.Widths)
  · have he : Geometry.b348.half 2 false=Geometry.b547 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound547
  · have he : Geometry.b348.half 2 true=Geometry.b548 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound548

theorem bound347 : BoxMajorant Geometry.b347 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b347.Widths)
  · have he : Geometry.b347.half 2 false=Geometry.b545 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound545
  · have he : Geometry.b347.half 2 true=Geometry.b546 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound546

theorem bound346 : BoxMajorant Geometry.b346 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b346.Widths)
  · have he : Geometry.b346.half 2 false=Geometry.b543 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound543
  · have he : Geometry.b346.half 2 true=Geometry.b544 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound544

theorem bound345 : BoxMajorant Geometry.b345 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b345.Widths)
  · have he : Geometry.b345.half 2 false=Geometry.b541 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound541
  · have he : Geometry.b345.half 2 true=Geometry.b542 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound542

theorem bound344 : BoxMajorant Geometry.b344 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b344.Widths)
  · have he : Geometry.b344.half 2 false=Geometry.b539 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound539
  · have he : Geometry.b344.half 2 true=Geometry.b540 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound540

theorem bound343 : BoxMajorant Geometry.b343 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b343.Widths)
  · have he : Geometry.b343.half 2 false=Geometry.b537 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound537
  · have he : Geometry.b343.half 2 true=Geometry.b538 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound538

theorem bound222 : BoxMajorant Geometry.b222 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b222.Widths)
  · have he : Geometry.b222.half 1 false=Geometry.b357 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound357
  · have he : Geometry.b222.half 1 true=Geometry.b358 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound358

theorem bound221 : BoxMajorant Geometry.b221 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b221.Widths)
  · have he : Geometry.b221.half 1 false=Geometry.b355 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound355
  · have he : Geometry.b221.half 1 true=Geometry.b356 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound356

theorem bound220 : BoxMajorant Geometry.b220 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b220.Widths)
  · have he : Geometry.b220.half 1 false=Geometry.b353 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound353
  · have he : Geometry.b220.half 1 true=Geometry.b354 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound354

theorem bound219 : BoxMajorant Geometry.b219 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b219.Widths)
  · have he : Geometry.b219.half 1 false=Geometry.b351 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound351
  · have he : Geometry.b219.half 1 true=Geometry.b352 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound352

theorem bound218 : BoxMajorant Geometry.b218 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b218.Widths)
  · have he : Geometry.b218.half 1 false=Geometry.b349 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound349
  · have he : Geometry.b218.half 1 true=Geometry.b350 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound350

theorem bound217 : BoxMajorant Geometry.b217 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b217.Widths)
  · have he : Geometry.b217.half 1 false=Geometry.b347 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound347
  · have he : Geometry.b217.half 1 true=Geometry.b348 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound348

theorem bound216 : BoxMajorant Geometry.b216 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b216.Widths)
  · have he : Geometry.b216.half 1 false=Geometry.b345 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound345
  · have he : Geometry.b216.half 1 true=Geometry.b346 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound346

theorem bound215 : BoxMajorant Geometry.b215 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b215.Widths)
  · have he : Geometry.b215.half 1 false=Geometry.b343 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound343
  · have he : Geometry.b215.half 1 true=Geometry.b344 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound344

theorem bound130 : BoxMajorant Geometry.b130 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b130.Widths)
  · have he : Geometry.b130.half 0 false=Geometry.b221 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound221
  · have he : Geometry.b130.half 0 true=Geometry.b222 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound222

theorem bound129 : BoxMajorant Geometry.b129 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b129.Widths)
  · have he : Geometry.b129.half 0 false=Geometry.b219 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound219
  · have he : Geometry.b129.half 0 true=Geometry.b220 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound220

theorem bound128 : BoxMajorant Geometry.b128 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b128.Widths)
  · have he : Geometry.b128.half 0 false=Geometry.b217 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound217
  · have he : Geometry.b128.half 0 true=Geometry.b218 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound218

theorem bound127 : BoxMajorant Geometry.b127 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b127.Widths)
  · have he : Geometry.b127.half 0 false=Geometry.b215 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound215
  · have he : Geometry.b127.half 0 true=Geometry.b216 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound216

theorem bound72 : BoxMajorant Geometry.b72 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b72.Widths)
  · have he : Geometry.b72.half 2 false=Geometry.b129 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound129
  · have he : Geometry.b72.half 2 true=Geometry.b130 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound130

theorem bound71 : BoxMajorant Geometry.b71 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b71.Widths)
  · have he : Geometry.b71.half 2 false=Geometry.b127 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound127
  · have he : Geometry.b71.half 2 true=Geometry.b128 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound128

theorem bound37 : BoxMajorant Geometry.b37 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b37.Widths)
  · have he : Geometry.b37.half 1 false=Geometry.b71 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound71
  · have he : Geometry.b37.half 1 true=Geometry.b72 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound72

end N7.Kernel.Cover
