import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0000
import N7.Kernel.CoverGeometry.G0001
import N7.Kernel.CoverGeometry.G0002
import N7.Kernel.CoverGeometry.G0003
import N7.Kernel.CoverGeometry.G0005
import N7.Kernel.CoverGeometry.G0006
import N7.Kernel.CoverGeometry.G0009
import N7.Kernel.CoverGeometry.G0013
import N7.Kernel.CoverProofs.P0089
import N7.Kernel.CoverProofs.P0090
import N7.Kernel.CoverProofs.P0091
import N7.Kernel.CoverProofs.P0092
import N7.Kernel.CoverProofs.P0093
import N7.Kernel.CoverProofs.P0094
import N7.Kernel.CoverProofs.P0095
import N7.Kernel.CoverProofs.P0096
import N7.Kernel.CoverProofs.P0097
import N7.Kernel.CoverProofs.P0098
import N7.Kernel.CoverProofs.P0099
import N7.Kernel.CoverProofs.P0100
import N7.Kernel.CoverProofs.P0101
import N7.Kernel.CoverProofs.P0102
import N7.Kernel.CoverProofs.P0103
import N7.Kernel.CoverProofs.P0104
import N7.Kernel.PositiveGroups.G0002
import N7.Kernel.PositiveGroups.G0008
import N7.Kernel.PositiveGroups.G0015
import N7.Kernel.PositiveGroups.G0032
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound866 : BoxMajorant Geometry.b866 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b866 0 (by decide +kernel) x hx hd ho).elim

theorem bound601 : BoxMajorant Geometry.b601 := by
  exact PositiveLeaves.L1111.bound

theorem bound600 : BoxMajorant Geometry.b600 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b600.Widths)
  · have he : Geometry.b600.half 0 false=Geometry.b877 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound877
  · have he : Geometry.b600.half 0 true=Geometry.b878 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound878

theorem bound599 : BoxMajorant Geometry.b599 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b599.Widths)
  · have he : Geometry.b599.half 0 false=Geometry.b875 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound875
  · have he : Geometry.b599.half 0 true=Geometry.b876 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound876

theorem bound598 : BoxMajorant Geometry.b598 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b598.Widths)
  · have he : Geometry.b598.half 0 false=Geometry.b873 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound873
  · have he : Geometry.b598.half 0 true=Geometry.b874 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound874

theorem bound597 : BoxMajorant Geometry.b597 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b597.Widths)
  · have he : Geometry.b597.half 0 false=Geometry.b871 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound871
  · have he : Geometry.b597.half 0 true=Geometry.b872 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound872

theorem bound596 : BoxMajorant Geometry.b596 := by
  exact PositiveLeaves.L1150.bound

theorem bound595 : BoxMajorant Geometry.b595 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b595.Widths)
  · have he : Geometry.b595.half 0 false=Geometry.b869 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound869
  · have he : Geometry.b595.half 0 true=Geometry.b870 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound870

theorem bound594 : BoxMajorant Geometry.b594 := by
  exact PositiveLeaves.L1160.bound

theorem bound593 : BoxMajorant Geometry.b593 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b593.Widths)
  · have he : Geometry.b593.half 0 false=Geometry.b867 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound867
  · have he : Geometry.b593.half 0 true=Geometry.b868 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound868

theorem bound592 : BoxMajorant Geometry.b592 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b592 1 (by decide +kernel) x hx hd ho).elim

theorem bound591 : BoxMajorant Geometry.b591 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b591.Widths)
  · have he : Geometry.b591.half 0 false=Geometry.b865 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound865
  · have he : Geometry.b591.half 0 true=Geometry.b866 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound866

theorem bound590 : BoxMajorant Geometry.b590 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b590 1 (by decide +kernel) x hx hd ho).elim

theorem bound589 : BoxMajorant Geometry.b589 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b589.Widths)
  · have he : Geometry.b589.half 0 false=Geometry.b863 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound863
  · have he : Geometry.b589.half 0 true=Geometry.b864 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound864

theorem bound388 : BoxMajorant Geometry.b388 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b388.Widths)
  · have he : Geometry.b388.half 2 false=Geometry.b601 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound601
  · have he : Geometry.b388.half 2 true=Geometry.b602 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound602

theorem bound387 : BoxMajorant Geometry.b387 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b387.Widths)
  · have he : Geometry.b387.half 2 false=Geometry.b599 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound599
  · have he : Geometry.b387.half 2 true=Geometry.b600 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound600

theorem bound386 : BoxMajorant Geometry.b386 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b386.Widths)
  · have he : Geometry.b386.half 2 false=Geometry.b597 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound597
  · have he : Geometry.b386.half 2 true=Geometry.b598 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound598

theorem bound385 : BoxMajorant Geometry.b385 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b385.Widths)
  · have he : Geometry.b385.half 2 false=Geometry.b595 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound595
  · have he : Geometry.b385.half 2 true=Geometry.b596 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound596

theorem bound384 : BoxMajorant Geometry.b384 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b384.Widths)
  · have he : Geometry.b384.half 2 false=Geometry.b593 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound593
  · have he : Geometry.b384.half 2 true=Geometry.b594 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound594

theorem bound383 : BoxMajorant Geometry.b383 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b383.Widths)
  · have he : Geometry.b383.half 2 false=Geometry.b591 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound591
  · have he : Geometry.b383.half 2 true=Geometry.b592 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound592

theorem bound382 : BoxMajorant Geometry.b382 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b382.Widths)
  · have he : Geometry.b382.half 2 false=Geometry.b589 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound589
  · have he : Geometry.b382.half 2 true=Geometry.b590 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound590

theorem bound381 : BoxMajorant Geometry.b381 := by
  exact PositiveLeaves.L1184.bound

theorem bound250 : BoxMajorant Geometry.b250 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b250.Widths)
  · have he : Geometry.b250.half 1 false=Geometry.b387 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound387
  · have he : Geometry.b250.half 1 true=Geometry.b388 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound388

theorem bound249 : BoxMajorant Geometry.b249 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b249.Widths)
  · have he : Geometry.b249.half 1 false=Geometry.b385 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound385
  · have he : Geometry.b249.half 1 true=Geometry.b386 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound386

theorem bound248 : BoxMajorant Geometry.b248 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b248.Widths)
  · have he : Geometry.b248.half 1 false=Geometry.b383 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound383
  · have he : Geometry.b248.half 1 true=Geometry.b384 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound384

theorem bound247 : BoxMajorant Geometry.b247 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b247.Widths)
  · have he : Geometry.b247.half 1 false=Geometry.b381 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound381
  · have he : Geometry.b247.half 1 true=Geometry.b382 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound382

theorem bound152 : BoxMajorant Geometry.b152 := by
  exact PositiveLeaves.L1102.bound

theorem bound151 : BoxMajorant Geometry.b151 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b151.Widths)
  · have he : Geometry.b151.half 0 false=Geometry.b249 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound249
  · have he : Geometry.b151.half 0 true=Geometry.b250 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound250

theorem bound150 : BoxMajorant Geometry.b150 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b150 1 (by decide +kernel) x hx hd ho).elim

theorem bound149 : BoxMajorant Geometry.b149 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b149.Widths)
  · have he : Geometry.b149.half 0 false=Geometry.b247 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound247
  · have he : Geometry.b149.half 0 true=Geometry.b248 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound248

theorem bound88 : BoxMajorant Geometry.b88 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b88.Widths)
  · have he : Geometry.b88.half 2 false=Geometry.b151 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound151
  · have he : Geometry.b88.half 2 true=Geometry.b152 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound152

theorem bound87 : BoxMajorant Geometry.b87 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b87.Widths)
  · have he : Geometry.b87.half 2 false=Geometry.b149 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound149
  · have he : Geometry.b87.half 2 true=Geometry.b150 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound150

theorem bound47 : BoxMajorant Geometry.b47 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b47.Widths)
  · have he : Geometry.b47.half 1 false=Geometry.b87 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound87
  · have he : Geometry.b47.half 1 true=Geometry.b88 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound88

end N7.Kernel.Cover
