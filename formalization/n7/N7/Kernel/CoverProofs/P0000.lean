import N7.Kernel.Bernstein.BoxEquality
import N7.Kernel.Cover.Glue
import N7.Kernel.Cover.Outside
import N7.Kernel.CoverGeometry.G0000
import N7.Kernel.CoverProofs.P0001
import N7.Kernel.CoverProofs.P0002
import N7.Kernel.CoverProofs.P0003
import N7.Kernel.CoverProofs.P0004
import N7.Kernel.CoverProofs.P0005
import N7.Kernel.CoverProofs.P0006
import N7.Kernel.CoverProofs.P0007
import N7.Kernel.CoverProofs.P0008
import N7.Kernel.CoverProofs.P0009
import N7.Kernel.CoverProofs.P0010
import N7.Kernel.CoverProofs.P0011
import N7.Kernel.CoverProofs.P0012
import N7.Kernel.CoverProofs.P0013
import N7.Kernel.CoverProofs.P0014
import N7.Kernel.CoverProofs.P0015
import N7.Kernel.CoverProofs.P0016
import N7.Kernel.CoverProofs.P0017
import N7.Kernel.CoverProofs.P0018
import N7.Kernel.CoverProofs.P0019
import N7.Kernel.CoverProofs.P0020
import N7.Kernel.CoverProofs.P0021
import N7.Kernel.CoverProofs.P0022
import N7.Kernel.CoverProofs.P0023
import N7.Kernel.CoverProofs.P0024
import N7.Kernel.CoverProofs.P0025
namespace N7.Kernel.Cover
set_option maxHeartbeats 0
set_option maxRecDepth 64000
theorem bound56 : BoxMajorant Geometry.b56 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b56 0 (by decide +kernel) x hx hd ho).elim

theorem bound54 : BoxMajorant Geometry.b54 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b54 0 (by decide +kernel) x hx hd ho).elim

theorem bound42 : BoxMajorant Geometry.b42 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b42 0 (by decide +kernel) x hx hd ho).elim

theorem bound40 : BoxMajorant Geometry.b40 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b40 0 (by decide +kernel) x hx hd ho).elim

theorem bound31 : BoxMajorant Geometry.b31 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b31 2 (by decide +kernel) x hx hd ho).elim

theorem bound30 : BoxMajorant Geometry.b30 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b30.Widths)
  · have he : Geometry.b30.half 0 false=Geometry.b59 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound59
  · have he : Geometry.b30.half 0 true=Geometry.b60 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound60

theorem bound29 : BoxMajorant Geometry.b29 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b29.Widths)
  · have he : Geometry.b29.half 0 false=Geometry.b57 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound57
  · have he : Geometry.b29.half 0 true=Geometry.b58 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound58

theorem bound28 : BoxMajorant Geometry.b28 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b28.Widths)
  · have he : Geometry.b28.half 0 false=Geometry.b55 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound55
  · have he : Geometry.b28.half 0 true=Geometry.b56 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound56

theorem bound27 : BoxMajorant Geometry.b27 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b27.Widths)
  · have he : Geometry.b27.half 0 false=Geometry.b53 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound53
  · have he : Geometry.b27.half 0 true=Geometry.b54 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound54

theorem bound26 : BoxMajorant Geometry.b26 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b26.Widths)
  · have he : Geometry.b26.half 0 false=Geometry.b51 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound51
  · have he : Geometry.b26.half 0 true=Geometry.b52 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound52

theorem bound25 : BoxMajorant Geometry.b25 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b25.Widths)
  · have he : Geometry.b25.half 0 false=Geometry.b49 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound49
  · have he : Geometry.b25.half 0 true=Geometry.b50 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound50

theorem bound24 : BoxMajorant Geometry.b24 := by
  intro x hx hd ho
  exact (outsideCheck_sound Geometry.b24 1 (by decide +kernel) x hx hd ho).elim

theorem bound23 : BoxMajorant Geometry.b23 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b23.Widths)
  · have he : Geometry.b23.half 0 false=Geometry.b47 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound47
  · have he : Geometry.b23.half 0 true=Geometry.b48 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound48

theorem bound22 : BoxMajorant Geometry.b22 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b22.Widths)
  · have he : Geometry.b22.half 0 false=Geometry.b45 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound45
  · have he : Geometry.b22.half 0 true=Geometry.b46 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound46

theorem bound21 : BoxMajorant Geometry.b21 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b21.Widths)
  · have he : Geometry.b21.half 0 false=Geometry.b43 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound43
  · have he : Geometry.b21.half 0 true=Geometry.b44 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound44

theorem bound20 : BoxMajorant Geometry.b20 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b20.Widths)
  · have he : Geometry.b20.half 0 false=Geometry.b41 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound41
  · have he : Geometry.b20.half 0 true=Geometry.b42 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound42

theorem bound19 : BoxMajorant Geometry.b19 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b19.Widths)
  · have he : Geometry.b19.half 0 false=Geometry.b39 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound39
  · have he : Geometry.b19.half 0 true=Geometry.b40 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound40

theorem bound18 : BoxMajorant Geometry.b18 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b18.Widths)
  · have he : Geometry.b18.half 0 false=Geometry.b37 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound37
  · have he : Geometry.b18.half 0 true=Geometry.b38 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound38

theorem bound17 : BoxMajorant Geometry.b17 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b17.Widths)
  · have he : Geometry.b17.half 0 false=Geometry.b35 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound35
  · have he : Geometry.b17.half 0 true=Geometry.b36 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound36

theorem bound16 : BoxMajorant Geometry.b16 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b16.Widths)
  · have he : Geometry.b16.half 0 false=Geometry.b33 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound33
  · have he : Geometry.b16.half 0 true=Geometry.b34 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound34

theorem bound15 : BoxMajorant Geometry.b15 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b15.Widths)
  · have he : Geometry.b15.half 0 false=Geometry.b31 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound31
  · have he : Geometry.b15.half 0 true=Geometry.b32 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound32

theorem bound14 : BoxMajorant Geometry.b14 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b14.Widths)
  · have he : Geometry.b14.half 2 false=Geometry.b29 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound29
  · have he : Geometry.b14.half 2 true=Geometry.b30 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound30

theorem bound13 : BoxMajorant Geometry.b13 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b13.Widths)
  · have he : Geometry.b13.half 2 false=Geometry.b27 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound27
  · have he : Geometry.b13.half 2 true=Geometry.b28 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound28

theorem bound12 : BoxMajorant Geometry.b12 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b12.Widths)
  · have he : Geometry.b12.half 2 false=Geometry.b25 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound25
  · have he : Geometry.b12.half 2 true=Geometry.b26 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound26

theorem bound11 : BoxMajorant Geometry.b11 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b11.Widths)
  · have he : Geometry.b11.half 2 false=Geometry.b23 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound23
  · have he : Geometry.b11.half 2 true=Geometry.b24 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound24

theorem bound10 : BoxMajorant Geometry.b10 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b10.Widths)
  · have he : Geometry.b10.half 2 false=Geometry.b21 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound21
  · have he : Geometry.b10.half 2 true=Geometry.b22 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound22

theorem bound9 : BoxMajorant Geometry.b9 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b9.Widths)
  · have he : Geometry.b9.half 2 false=Geometry.b19 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound19
  · have he : Geometry.b9.half 2 true=Geometry.b20 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound20

theorem bound8 : BoxMajorant Geometry.b8 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b8.Widths)
  · have he : Geometry.b8.half 2 false=Geometry.b17 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound17
  · have he : Geometry.b8.half 2 true=Geometry.b18 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound18

theorem bound7 : BoxMajorant Geometry.b7 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b7.Widths)
  · have he : Geometry.b7.half 2 false=Geometry.b15 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound15
  · have he : Geometry.b7.half 2 true=Geometry.b16 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound16

theorem bound6 : BoxMajorant Geometry.b6 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b6.Widths)
  · have he : Geometry.b6.half 1 false=Geometry.b13 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound13
  · have he : Geometry.b6.half 1 true=Geometry.b14 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound14

theorem bound5 : BoxMajorant Geometry.b5 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b5.Widths)
  · have he : Geometry.b5.half 1 false=Geometry.b11 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound11
  · have he : Geometry.b5.half 1 true=Geometry.b12 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound12

theorem bound4 : BoxMajorant Geometry.b4 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b4.Widths)
  · have he : Geometry.b4.half 1 false=Geometry.b9 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound9
  · have he : Geometry.b4.half 1 true=Geometry.b10 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound10

theorem bound3 : BoxMajorant Geometry.b3 := by
  apply BoxMajorant.half 1 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b3.Widths)
  · have he : Geometry.b3.half 1 false=Geometry.b7 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound7
  · have he : Geometry.b3.half 1 true=Geometry.b8 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound8

theorem bound2 : BoxMajorant Geometry.b2 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b2.Widths)
  · have he : Geometry.b2.half 0 false=Geometry.b5 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound5
  · have he : Geometry.b2.half 0 true=Geometry.b6 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound6

theorem bound1 : BoxMajorant Geometry.b1 := by
  apply BoxMajorant.half 0 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b1.Widths)
  · have he : Geometry.b1.half 0 false=Geometry.b3 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound3
  · have he : Geometry.b1.half 0 true=Geometry.b4 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound4

theorem bound0 : BoxMajorant Geometry.b0 := by
  apply BoxMajorant.half 2 (by unfold ClosedBox.Widths; decide +kernel : Geometry.b0.Widths)
  · have he : Geometry.b0.half 2 false=Geometry.b1 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound1
  · have he : Geometry.b0.half 2 true=Geometry.b2 := ClosedBox.equalCheck_sound (by decide +kernel)
    rw [he]
    exact bound2

end N7.Kernel.Cover
