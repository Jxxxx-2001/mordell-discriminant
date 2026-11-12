import Eight.RootCorner
import Eight.RootGeometry.TangentCorner
import Eight.RootGeometry.B1

namespace MordellEight.RootBounds.B1
open RootCorner
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem leaf : BoxMajorant RootGeometry.B1.L17 := by
  intro x hx hd
  obtain ⟨hu,hv,ht⟩ := RootGeometry.TangentCorner.negative RootGeometry.B1.L17
    (p := ((965267/1048576):ℝ)) (q := ((965267/1048576):ℝ)) (s := ((965267/1048576):ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [RootGeometry.B1.L17,Matrix.cons_val_two])
    (by norm_num [RootGeometry.B1.L17,Matrix.cons_val_two])
    (by norm_num [RootGeometry.B1.L17,Matrix.cons_val_two]) hx hd
  rw [hu,hv,ht]
  have h := point_bound (1/2) (1/2) (1/4) (965267/262144) (787923897379715771411335/604462909807314587353088) (787923934663928730156565/604462909807314587353088) 16
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  convert h using 1 <;> norm_num [coord, RootTensor.box, domainBox, Matrix.cons_val_two]

theorem majorant : BoxMajorant RootPartition.B1 := RootGeometry.B1.majorant leaf
#print axioms majorant
end MordellEight.RootBounds.B1
