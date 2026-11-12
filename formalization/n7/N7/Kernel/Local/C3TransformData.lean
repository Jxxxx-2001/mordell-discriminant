import N7.Kernel.Local.C3HessianData
import N7.Kernel.LocalCongruence
set_option autoImplicit false
namespace N7.Kernel.Local.C3
open LocalGeometry Checks Matrix
def largeRadius : ℚ := (1/2048:ℚ)
def T : Matrix (Fin 3) (Fin 3) ℚ := ![![1,(-229438633/1000000000:ℚ),(4112453/25000000:ℚ)],![0,1,(4112453/25000000:ℚ)],![0,0,1]]
def S : Matrix (Fin 3) (Fin 3) ℚ := ![![1,(229438633/1000000000:ℚ),(-5056008594596749/25000000000000000:ℚ)],![0,1,(-4112453/25000000:ℚ)],![0,0,1]]
theorem inverse_checked : T*S=1 := by decide +kernel
theorem inverse_real : realMatrix T*realMatrix S=1 := by
  rw [← realMatrix_mul,inverse_checked,realMatrix_one]
theorem large_distance_pos : 0<centerDistance center-4*largeRadius := by norm_num [centerDistance,center,largeRadius,Matrix.cons_val_two]
end N7.Kernel.Local.C3
