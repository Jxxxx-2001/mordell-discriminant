import N7.Kernel.Local.C1Contact
import N7.Kernel.Local.C1LargeCertificate
import N7.Kernel.LocalSegments
set_option autoImplicit false
namespace N7.Kernel.Local.C1
open GapAnalytic LocalGeometry
theorem large_near_gap {x : Fin 3 → ℝ} (hn : Near center largeRadius x) : 0≤gap exactMajorant x := by
  apply gap_nonneg_near exactMajorant center largeRadius large_distance_pos contact_value contact_gradient _ hn
  intro y hy
  simpa [Matrix.submatrix,indices] using large_hessian_psd hy
theorem large_near_majorant {x : Fin 3 → ℝ} (hn : Near center largeRadius x) : Real.log (distance x)≤eval3 exactMajorant x := sub_nonneg.mp (large_near_gap hn)
#print axioms large_near_majorant
end N7.Kernel.Local.C1
