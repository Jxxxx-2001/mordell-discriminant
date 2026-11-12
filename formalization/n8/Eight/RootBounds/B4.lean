import Eight.RootCorner
import Eight.RootGeometry.TangentCorner
import Eight.RootGeometry.B4

namespace MordellEight.RootBounds.B4
open RootCorner
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem leaf : BoxMajorant RootGeometry.B4.L11 := by
  intro x hx hd
  obtain ⟨hu,hv,ht⟩ := RootGeometry.TangentCorner.negative RootGeometry.B4.L11
    (p := ((965267/2097152):ℝ)) (q := ((965267/524288):ℝ)) (s := ((965267/1048576):ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [RootGeometry.B4.L11,Matrix.cons_val_two])
    (by norm_num [RootGeometry.B4.L11,Matrix.cons_val_two])
    (by norm_num [RootGeometry.B4.L11,Matrix.cons_val_two]) hx hd
  rw [hu,hv,ht]
  have h := point_bound (1/4) 1 (1/4) (8687403/2097152) (858648874517029297450355/604462909807314587353088) (1719080864955679462538941/1208925819614629174706176) 8
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  convert h using 1 <;> norm_num [coord, RootTensor.box, domainBox, Matrix.cons_val_two]

theorem majorant : BoxMajorant RootPartition.B4 := RootGeometry.B4.majorant leaf
#print axioms majorant
end MordellEight.RootBounds.B4
