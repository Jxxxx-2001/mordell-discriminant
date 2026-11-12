import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0007
import N7.Kernel.CoverGeometry.G0011
import N7.Kernel.CoverGeometry.G0016
import N7.Kernel.CoverGeometry.G0022
import N7.Kernel.CoverGeometry.G0032
import N7.Kernel.CoverGeometry.G0038
import N7.Kernel.CoverGeometry.G0043
import N7.Kernel.PositiveGroups.G0076
import N7.Kernel.PositiveGroups.G0077
import N7.Kernel.PositiveGroups.G0113
import N7.Kernel.PositiveGroups.G0114
import N7.Kernel.PositiveGroups.G0153
import N7.Kernel.PositiveGroups.G0154
import N7.Kernel.PositiveGroups.G0190
import N7.Kernel.PositiveGroups.G0191
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2796 : BoxMajorant Geometry.b2796 := by
  exact PositiveLeaves.L2917.bound

theorem bound2795 : BoxMajorant Geometry.b2795 := by
  exact PositiveLeaves.L2918.bound

theorem bound2794 : BoxMajorant Geometry.b2794 := by
  exact PositiveLeaves.L2919.bound

theorem bound2793 : BoxMajorant Geometry.b2793 := by
  exact PositiveLeaves.L2920.bound

theorem bound2792 : BoxMajorant Geometry.b2792 := by
  exact PositiveLeaves.L2921.bound

theorem bound2791 : BoxMajorant Geometry.b2791 := by
  exact PositiveLeaves.L2922.bound

theorem bound2790 : BoxMajorant Geometry.b2790 := by
  exact PositiveLeaves.L2927.bound

theorem bound2789 : BoxMajorant Geometry.b2789 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2789 2 (by decide +kernel) x hx hd ho).elim

theorem bound2456 : BoxMajorant Geometry.b2456 := by
  exact PositiveLeaves.L2916.bound

theorem bound2455 : BoxMajorant Geometry.b2455 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2455.Widths)
  · have he : Geometry.b2455.half 2 false=Geometry.b2795 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2795
  · have he : Geometry.b2455.half 2 true=Geometry.b2796 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2796

theorem bound2454 : BoxMajorant Geometry.b2454 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2454.Widths)
  · have he : Geometry.b2454.half 2 false=Geometry.b2793 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2793
  · have he : Geometry.b2454.half 2 true=Geometry.b2794 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2794

theorem bound2453 : BoxMajorant Geometry.b2453 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2453.Widths)
  · have he : Geometry.b2453.half 2 false=Geometry.b2791 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2791
  · have he : Geometry.b2453.half 2 true=Geometry.b2792 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2792

theorem bound2452 : BoxMajorant Geometry.b2452 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2452.Widths)
  · have he : Geometry.b2452.half 2 false=Geometry.b2789 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2789
  · have he : Geometry.b2452.half 2 true=Geometry.b2790 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2790

theorem bound2451 : BoxMajorant Geometry.b2451 := by
  exact PositiveLeaves.L2929.bound

theorem bound2104 : BoxMajorant Geometry.b2104 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2104.Widths)
  · have he : Geometry.b2104.half 1 false=Geometry.b2455 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2455
  · have he : Geometry.b2104.half 1 true=Geometry.b2456 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2456

theorem bound2103 : BoxMajorant Geometry.b2103 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2103.Widths)
  · have he : Geometry.b2103.half 1 false=Geometry.b2453 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2453
  · have he : Geometry.b2103.half 1 true=Geometry.b2454 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2454

theorem bound2102 : BoxMajorant Geometry.b2102 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2102 0 (by decide +kernel) x hx hd ho).elim

theorem bound2101 : BoxMajorant Geometry.b2101 := by
  exact PositiveLeaves.L2925.bound

theorem bound2100 : BoxMajorant Geometry.b2100 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2100.Widths)
  · have he : Geometry.b2100.half 1 false=Geometry.b2451 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2451
  · have he : Geometry.b2100.half 1 true=Geometry.b2452 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2452

theorem bound2099 : BoxMajorant Geometry.b2099 := by
  exact PositiveLeaves.L2930.bound

theorem bound2098 : BoxMajorant Geometry.b2098 := by
  exact PositiveLeaves.L2932.bound

theorem bound2097 : BoxMajorant Geometry.b2097 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2097 2 (by decide +kernel) x hx hd ho).elim

theorem bound1456 : BoxMajorant Geometry.b1456 := by
  exact PositiveLeaves.L2915.bound

theorem bound1455 : BoxMajorant Geometry.b1455 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1455.Widths)
  · have he : Geometry.b1455.half 0 false=Geometry.b2103 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2103
  · have he : Geometry.b1455.half 0 true=Geometry.b2104 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2104

theorem bound1454 : BoxMajorant Geometry.b1454 := by
  exact PositiveLeaves.L2923.bound

theorem bound1453 : BoxMajorant Geometry.b1453 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1453.Widths)
  · have he : Geometry.b1453.half 0 false=Geometry.b2101 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2101
  · have he : Geometry.b1453.half 0 true=Geometry.b2102 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2102

theorem bound1452 : BoxMajorant Geometry.b1452 := by
  exact PositiveLeaves.L2926.bound

theorem bound1451 : BoxMajorant Geometry.b1451 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1451.Widths)
  · have he : Geometry.b1451.half 0 false=Geometry.b2099 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2099
  · have he : Geometry.b1451.half 0 true=Geometry.b2100 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2100

theorem bound1450 : BoxMajorant Geometry.b1450 := by
  exact PositiveLeaves.L2931.bound

theorem bound1449 : BoxMajorant Geometry.b1449 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1449.Widths)
  · have he : Geometry.b1449.half 0 false=Geometry.b2097 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2097
  · have he : Geometry.b1449.half 0 true=Geometry.b2098 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2098

theorem bound1038 : BoxMajorant Geometry.b1038 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1038.Widths)
  · have he : Geometry.b1038.half 2 false=Geometry.b1455 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1455
  · have he : Geometry.b1038.half 2 true=Geometry.b1456 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1456

theorem bound1037 : BoxMajorant Geometry.b1037 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1037.Widths)
  · have he : Geometry.b1037.half 2 false=Geometry.b1453 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1453
  · have he : Geometry.b1037.half 2 true=Geometry.b1454 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1454

theorem bound1036 : BoxMajorant Geometry.b1036 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1036.Widths)
  · have he : Geometry.b1036.half 2 false=Geometry.b1451 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1451
  · have he : Geometry.b1036.half 2 true=Geometry.b1452 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1452

theorem bound1035 : BoxMajorant Geometry.b1035 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1035.Widths)
  · have he : Geometry.b1035.half 2 false=Geometry.b1449 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1449
  · have he : Geometry.b1035.half 2 true=Geometry.b1450 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1450

theorem bound754 : BoxMajorant Geometry.b754 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b754.Widths)
  · have he : Geometry.b754.half 1 false=Geometry.b1037 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1037
  · have he : Geometry.b754.half 1 true=Geometry.b1038 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1038

theorem bound753 : BoxMajorant Geometry.b753 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b753.Widths)
  · have he : Geometry.b753.half 1 false=Geometry.b1035 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1035
  · have he : Geometry.b753.half 1 true=Geometry.b1036 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1036

theorem bound484 : BoxMajorant Geometry.b484 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b484.Widths)
  · have he : Geometry.b484.half 0 false=Geometry.b753 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound753
  · have he : Geometry.b484.half 0 true=Geometry.b754 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound754

end N7.Kernel.Cover
