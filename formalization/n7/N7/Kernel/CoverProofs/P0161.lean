import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0010
import N7.Kernel.CoverGeometry.G0015
import N7.Kernel.CoverGeometry.G0021
import N7.Kernel.CoverGeometry.G0031
import N7.Kernel.CoverGeometry.G0037
import N7.Kernel.CoverGeometry.G0038
import N7.Kernel.CoverGeometry.G0043
import N7.Kernel.CoverProofs.P0319
import N7.Kernel.CoverProofs.P0320
import N7.Kernel.CoverProofs.P0321
import N7.Kernel.CoverProofs.P0322
import N7.Kernel.CoverProofs.P0323
import N7.Kernel.CoverProofs.P0324
import N7.Kernel.CoverProofs.P0325
import N7.Kernel.CoverProofs.P0326
import N7.Kernel.CoverProofs.P0327
import N7.Kernel.CoverProofs.P0328
import N7.Kernel.CoverProofs.P0329
import N7.Kernel.CoverProofs.P0330
import N7.Kernel.CoverProofs.P0331
import N7.Kernel.CoverProofs.P0332
import N7.Kernel.PositiveGroups.G0176
import N7.Kernel.PositiveGroups.G0219
import N7.Kernel.PositiveGroups.G0220
import N7.Kernel.PositiveGroups.G0256
import N7.Kernel.PositiveGroups.G0257
import N7.Kernel.PositiveGroups.G0258
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound2778 : BoxMajorant Geometry.b2778 := by
  exact PositiveLeaves.L148.bound

theorem bound2777 : BoxMajorant Geometry.b2777 := by
  exact PositiveLeaves.L149.bound

theorem bound2776 : BoxMajorant Geometry.b2776 := by
  exact PositiveLeaves.L151.bound

theorem bound2771 : BoxMajorant Geometry.b2771 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2771 0 (by decide +kernel) x hx hd ho).elim

theorem bound2769 : BoxMajorant Geometry.b2769 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2769 0 (by decide +kernel) x hx hd ho).elim

theorem bound2767 : BoxMajorant Geometry.b2767 := by
  exact PositiveLeaves.L182.bound

theorem bound2762 : BoxMajorant Geometry.b2762 := by
  exact PositiveLeaves.L274.bound

theorem bound2761 : BoxMajorant Geometry.b2761 := by
  exact PositiveLeaves.L275.bound

theorem bound2438 : BoxMajorant Geometry.b2438 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2438.Widths)
  · have he : Geometry.b2438.half 1 false=Geometry.b2777 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2777
  · have he : Geometry.b2438.half 1 true=Geometry.b2778 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2778

theorem bound2437 : BoxMajorant Geometry.b2437 := by
  exact PositiveLeaves.L150.bound

theorem bound2436 : BoxMajorant Geometry.b2436 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2436.Widths)
  · have he : Geometry.b2436.half 1 false=Geometry.b2775 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2775
  · have he : Geometry.b2436.half 1 true=Geometry.b2776 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2776

theorem bound2435 : BoxMajorant Geometry.b2435 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2435.Widths)
  · have he : Geometry.b2435.half 1 false=Geometry.b2773 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2773
  · have he : Geometry.b2435.half 1 true=Geometry.b2774 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2774

theorem bound2434 : BoxMajorant Geometry.b2434 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2434 0 (by decide +kernel) x hx hd ho).elim

theorem bound2433 : BoxMajorant Geometry.b2433 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2433.Widths)
  · have he : Geometry.b2433.half 1 false=Geometry.b2771 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2771
  · have he : Geometry.b2433.half 1 true=Geometry.b2772 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2772

theorem bound2432 : BoxMajorant Geometry.b2432 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b2432 0 (by decide +kernel) x hx hd ho).elim

theorem bound2431 : BoxMajorant Geometry.b2431 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2431.Widths)
  · have he : Geometry.b2431.half 1 false=Geometry.b2769 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2769
  · have he : Geometry.b2431.half 1 true=Geometry.b2770 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2770

theorem bound2430 : BoxMajorant Geometry.b2430 := by
  exact PositiveLeaves.L179.bound

theorem bound2429 : BoxMajorant Geometry.b2429 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2429.Widths)
  · have he : Geometry.b2429.half 1 false=Geometry.b2767 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2767
  · have he : Geometry.b2429.half 1 true=Geometry.b2768 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2768

theorem bound2428 : BoxMajorant Geometry.b2428 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2428.Widths)
  · have he : Geometry.b2428.half 1 false=Geometry.b2765 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2765
  · have he : Geometry.b2428.half 1 true=Geometry.b2766 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2766

theorem bound2427 : BoxMajorant Geometry.b2427 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2427.Widths)
  · have he : Geometry.b2427.half 1 false=Geometry.b2763 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2763
  · have he : Geometry.b2427.half 1 true=Geometry.b2764 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2764

theorem bound2426 : BoxMajorant Geometry.b2426 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2426.Widths)
  · have he : Geometry.b2426.half 1 false=Geometry.b2761 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2761
  · have he : Geometry.b2426.half 1 true=Geometry.b2762 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2762

theorem bound2425 : BoxMajorant Geometry.b2425 := by
  exact PositiveLeaves.L276.bound

theorem bound2424 : BoxMajorant Geometry.b2424 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2424.Widths)
  · have he : Geometry.b2424.half 1 false=Geometry.b2759 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2759
  · have he : Geometry.b2424.half 1 true=Geometry.b2760 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2760

theorem bound2423 : BoxMajorant Geometry.b2423 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2423.Widths)
  · have he : Geometry.b2423.half 1 false=Geometry.b2757 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2757
  · have he : Geometry.b2423.half 1 true=Geometry.b2758 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2758

theorem bound2028 : BoxMajorant Geometry.b2028 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2028.Widths)
  · have he : Geometry.b2028.half 0 false=Geometry.b2437 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2437
  · have he : Geometry.b2028.half 0 true=Geometry.b2438 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2438

theorem bound2027 : BoxMajorant Geometry.b2027 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2027.Widths)
  · have he : Geometry.b2027.half 0 false=Geometry.b2435 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2435
  · have he : Geometry.b2027.half 0 true=Geometry.b2436 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2436

theorem bound2026 : BoxMajorant Geometry.b2026 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2026.Widths)
  · have he : Geometry.b2026.half 0 false=Geometry.b2433 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2433
  · have he : Geometry.b2026.half 0 true=Geometry.b2434 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2434

theorem bound2025 : BoxMajorant Geometry.b2025 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2025.Widths)
  · have he : Geometry.b2025.half 0 false=Geometry.b2431 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2431
  · have he : Geometry.b2025.half 0 true=Geometry.b2432 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2432

theorem bound2024 : BoxMajorant Geometry.b2024 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2024.Widths)
  · have he : Geometry.b2024.half 0 false=Geometry.b2429 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2429
  · have he : Geometry.b2024.half 0 true=Geometry.b2430 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2430

theorem bound2023 : BoxMajorant Geometry.b2023 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2023.Widths)
  · have he : Geometry.b2023.half 0 false=Geometry.b2427 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2427
  · have he : Geometry.b2023.half 0 true=Geometry.b2428 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2428

theorem bound2022 : BoxMajorant Geometry.b2022 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2022.Widths)
  · have he : Geometry.b2022.half 0 false=Geometry.b2425 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2425
  · have he : Geometry.b2022.half 0 true=Geometry.b2426 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2426

theorem bound2021 : BoxMajorant Geometry.b2021 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2021.Widths)
  · have he : Geometry.b2021.half 0 false=Geometry.b2423 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2423
  · have he : Geometry.b2021.half 0 true=Geometry.b2424 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2424

theorem bound1396 : BoxMajorant Geometry.b1396 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1396.Widths)
  · have he : Geometry.b1396.half 2 false=Geometry.b2027 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2027
  · have he : Geometry.b1396.half 2 true=Geometry.b2028 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2028

theorem bound1395 : BoxMajorant Geometry.b1395 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1395.Widths)
  · have he : Geometry.b1395.half 2 false=Geometry.b2025 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2025
  · have he : Geometry.b1395.half 2 true=Geometry.b2026 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2026

theorem bound1394 : BoxMajorant Geometry.b1394 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1394.Widths)
  · have he : Geometry.b1394.half 2 false=Geometry.b2023 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2023
  · have he : Geometry.b1394.half 2 true=Geometry.b2024 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2024

theorem bound1393 : BoxMajorant Geometry.b1393 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1393.Widths)
  · have he : Geometry.b1393.half 2 false=Geometry.b2021 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2021
  · have he : Geometry.b1393.half 2 true=Geometry.b2022 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2022

theorem bound994 : BoxMajorant Geometry.b994 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b994.Widths)
  · have he : Geometry.b994.half 1 false=Geometry.b1395 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1395
  · have he : Geometry.b994.half 1 true=Geometry.b1396 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1396

theorem bound993 : BoxMajorant Geometry.b993 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b993.Widths)
  · have he : Geometry.b993.half 1 false=Geometry.b1393 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1393
  · have he : Geometry.b993.half 1 true=Geometry.b1394 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1394

theorem bound695 : BoxMajorant Geometry.b695 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b695.Widths)
  · have he : Geometry.b695.half 0 false=Geometry.b993 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound993
  · have he : Geometry.b695.half 0 true=Geometry.b994 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound994

end N7.Kernel.Cover
