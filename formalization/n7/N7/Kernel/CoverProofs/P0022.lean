import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.CoverGeometry.G0000
import N7.Kernel.CoverGeometry.G0001
import N7.Kernel.CoverGeometry.G0002
import N7.Kernel.CoverGeometry.G0004
import N7.Kernel.CoverGeometry.G0006
import N7.Kernel.CoverGeometry.G0007
import N7.Kernel.CoverGeometry.G0010
import N7.Kernel.CoverGeometry.G0011
import N7.Kernel.CoverGeometry.G0015
import N7.Kernel.CoverProofs.P0157
import N7.Kernel.CoverProofs.P0158
import N7.Kernel.CoverProofs.P0159
import N7.Kernel.CoverProofs.P0160
import N7.Kernel.CoverProofs.P0161
import N7.Kernel.CoverProofs.P0162
import N7.Kernel.CoverProofs.P0163
import N7.Kernel.CoverProofs.P0164
import N7.Kernel.CoverProofs.P0165
import N7.Kernel.CoverProofs.P0166
import N7.Kernel.CoverProofs.P0167
import N7.Kernel.CoverProofs.P0168
import N7.Kernel.CoverProofs.P0169
import N7.Kernel.CoverProofs.P0170
import N7.Kernel.CoverProofs.P0171
import N7.Kernel.CoverProofs.P0172
import N7.Kernel.PositiveGroups.G0009
import N7.Kernel.PositiveGroups.G0017
import N7.Kernel.PositiveGroups.G0018
import N7.Kernel.PositiveGroups.G0037
import N7.Kernel.PositiveGroups.G0038
import N7.Kernel.PositiveGroups.G0063
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound981 : BoxMajorant Geometry.b981 := by
  exact PositiveLeaves.L523.bound

theorem bound707 : BoxMajorant Geometry.b707 := by
  exact PositiveLeaves.L95.bound

theorem bound706 : BoxMajorant Geometry.b706 := by
  exact PositiveLeaves.L97.bound

theorem bound705 : BoxMajorant Geometry.b705 := by
  exact PositiveLeaves.L98.bound

theorem bound704 : BoxMajorant Geometry.b704 := by
  exact PositiveLeaves.L100.bound

theorem bound703 : BoxMajorant Geometry.b703 := by
  exact PositiveLeaves.L101.bound

theorem bound691 : BoxMajorant Geometry.b691 := by
  exact PositiveLeaves.L505.bound

theorem bound689 : BoxMajorant Geometry.b689 := by
  exact PositiveLeaves.L512.bound

theorem bound688 : BoxMajorant Geometry.b688 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b688.Widths)
  · have he : Geometry.b688.half 0 false=Geometry.b983 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound983
  · have he : Geometry.b688.half 0 true=Geometry.b984 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound984

theorem bound687 : BoxMajorant Geometry.b687 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b687.Widths)
  · have he : Geometry.b687.half 0 false=Geometry.b981 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound981
  · have he : Geometry.b687.half 0 true=Geometry.b982 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound982

theorem bound452 : BoxMajorant Geometry.b452 := by
  exact PositiveLeaves.L92.bound

theorem bound451 : BoxMajorant Geometry.b451 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b451.Widths)
  · have he : Geometry.b451.half 2 false=Geometry.b707 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound707
  · have he : Geometry.b451.half 2 true=Geometry.b708 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound708

theorem bound450 : BoxMajorant Geometry.b450 := by
  exact PositiveLeaves.L96.bound

theorem bound449 : BoxMajorant Geometry.b449 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b449.Widths)
  · have he : Geometry.b449.half 2 false=Geometry.b705 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound705
  · have he : Geometry.b449.half 2 true=Geometry.b706 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound706

theorem bound448 : BoxMajorant Geometry.b448 := by
  exact PositiveLeaves.L99.bound

theorem bound447 : BoxMajorant Geometry.b447 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b447.Widths)
  · have he : Geometry.b447.half 2 false=Geometry.b703 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound703
  · have he : Geometry.b447.half 2 true=Geometry.b704 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound704

theorem bound446 : BoxMajorant Geometry.b446 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b446.Widths)
  · have he : Geometry.b446.half 2 false=Geometry.b701 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound701
  · have he : Geometry.b446.half 2 true=Geometry.b702 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound702

theorem bound445 : BoxMajorant Geometry.b445 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b445.Widths)
  · have he : Geometry.b445.half 2 false=Geometry.b699 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound699
  · have he : Geometry.b445.half 2 true=Geometry.b700 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound700

theorem bound444 : BoxMajorant Geometry.b444 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b444.Widths)
  · have he : Geometry.b444.half 2 false=Geometry.b697 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound697
  · have he : Geometry.b444.half 2 true=Geometry.b698 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound698

theorem bound443 : BoxMajorant Geometry.b443 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b443.Widths)
  · have he : Geometry.b443.half 2 false=Geometry.b695 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound695
  · have he : Geometry.b443.half 2 true=Geometry.b696 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound696

theorem bound442 : BoxMajorant Geometry.b442 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b442.Widths)
  · have he : Geometry.b442.half 2 false=Geometry.b693 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound693
  · have he : Geometry.b442.half 2 true=Geometry.b694 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound694

theorem bound441 : BoxMajorant Geometry.b441 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b441.Widths)
  · have he : Geometry.b441.half 2 false=Geometry.b691 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound691
  · have he : Geometry.b441.half 2 true=Geometry.b692 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound692

theorem bound440 : BoxMajorant Geometry.b440 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b440.Widths)
  · have he : Geometry.b440.half 2 false=Geometry.b689 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound689
  · have he : Geometry.b440.half 2 true=Geometry.b690 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound690

theorem bound439 : BoxMajorant Geometry.b439 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b439.Widths)
  · have he : Geometry.b439.half 2 false=Geometry.b687 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound687
  · have he : Geometry.b439.half 2 true=Geometry.b688 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound688

theorem bound286 : BoxMajorant Geometry.b286 := by
  exact PositiveLeaves.L91.bound

theorem bound285 : BoxMajorant Geometry.b285 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b285.Widths)
  · have he : Geometry.b285.half 1 false=Geometry.b451 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound451
  · have he : Geometry.b285.half 1 true=Geometry.b452 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound452

theorem bound284 : BoxMajorant Geometry.b284 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b284.Widths)
  · have he : Geometry.b284.half 1 false=Geometry.b449 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound449
  · have he : Geometry.b284.half 1 true=Geometry.b450 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound450

theorem bound283 : BoxMajorant Geometry.b283 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b283.Widths)
  · have he : Geometry.b283.half 1 false=Geometry.b447 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound447
  · have he : Geometry.b283.half 1 true=Geometry.b448 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound448

theorem bound282 : BoxMajorant Geometry.b282 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b282.Widths)
  · have he : Geometry.b282.half 1 false=Geometry.b445 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound445
  · have he : Geometry.b282.half 1 true=Geometry.b446 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound446

theorem bound281 : BoxMajorant Geometry.b281 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b281.Widths)
  · have he : Geometry.b281.half 1 false=Geometry.b443 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound443
  · have he : Geometry.b281.half 1 true=Geometry.b444 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound444

theorem bound280 : BoxMajorant Geometry.b280 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b280.Widths)
  · have he : Geometry.b280.half 1 false=Geometry.b441 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound441
  · have he : Geometry.b280.half 1 true=Geometry.b442 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound442

theorem bound279 : BoxMajorant Geometry.b279 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b279.Widths)
  · have he : Geometry.b279.half 1 false=Geometry.b439 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound439
  · have he : Geometry.b279.half 1 true=Geometry.b440 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound440

theorem bound178 : BoxMajorant Geometry.b178 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b178.Widths)
  · have he : Geometry.b178.half 0 false=Geometry.b285 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound285
  · have he : Geometry.b178.half 0 true=Geometry.b286 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound286

theorem bound177 : BoxMajorant Geometry.b177 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b177.Widths)
  · have he : Geometry.b177.half 0 false=Geometry.b283 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound283
  · have he : Geometry.b177.half 0 true=Geometry.b284 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound284

theorem bound176 : BoxMajorant Geometry.b176 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b176.Widths)
  · have he : Geometry.b176.half 0 false=Geometry.b281 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound281
  · have he : Geometry.b176.half 0 true=Geometry.b282 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound282

theorem bound175 : BoxMajorant Geometry.b175 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b175.Widths)
  · have he : Geometry.b175.half 0 false=Geometry.b279 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound279
  · have he : Geometry.b175.half 0 true=Geometry.b280 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound280

theorem bound104 : BoxMajorant Geometry.b104 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b104.Widths)
  · have he : Geometry.b104.half 2 false=Geometry.b177 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound177
  · have he : Geometry.b104.half 2 true=Geometry.b178 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound178

theorem bound103 : BoxMajorant Geometry.b103 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b103.Widths)
  · have he : Geometry.b103.half 2 false=Geometry.b175 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound175
  · have he : Geometry.b103.half 2 true=Geometry.b176 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound176

theorem bound57 : BoxMajorant Geometry.b57 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b57.Widths)
  · have he : Geometry.b57.half 1 false=Geometry.b103 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound103
  · have he : Geometry.b57.half 1 true=Geometry.b104 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound104

end N7.Kernel.Cover
