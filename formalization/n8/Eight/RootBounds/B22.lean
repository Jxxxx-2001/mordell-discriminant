import Eight.RootCorner
import Eight.RootGeometry.TangentCorner
import Eight.RootGeometry.B22

namespace MordellEight.RootBounds.B22
open RootCorner
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem leaf : BoxMajorant RootGeometry.B22.L7 := by
  intro x hx hd
  obtain ⟨hu,hv,ht⟩ := RootGeometry.TangentCorner.positive RootGeometry.B22.L7
    (p := ((965267/2097152):ℝ)) (q := ((965267/524288):ℝ)) (s := ((965267/1048576):ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [RootGeometry.B22.L7,Matrix.cons_val_two])
    (by norm_num [RootGeometry.B22.L7,Matrix.cons_val_two])
    (by norm_num [RootGeometry.B22.L7,Matrix.cons_val_two]) hx hd
  rw [hu,hv,ht]
  have h := point_bound (1/4) 1 (3/4) (2895801/8388608) (-642921733996016123024121/604462909807314587353088) (-1285812829842480024601213/1208925819614629174706176) 8
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  convert h using 1 <;> norm_num [coord, RootTensor.box, domainBox, Matrix.cons_val_two]

theorem majorant : BoxMajorant RootPartition.B22 := RootGeometry.B22.majorant leaf
#print axioms majorant
end MordellEight.RootBounds.B22
