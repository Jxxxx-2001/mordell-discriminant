import N7.Kernel.Local.C3Contact
import N7.Kernel.Local.C3LargeCertificate
import N7.Kernel.LocalSegments
set_option autoImplicit false
namespace N7.Kernel.Local.C3
open GapAnalytic LocalGeometry
theorem large_near_gap {x : Fin 3 → ℝ} (hn : Near center largeRadius x) : 0≤gap boundaryPolynomial x := by
  apply gap_nonneg_near boundaryPolynomial center largeRadius large_distance_pos contact_value contact_gradient _ hn
  intro y hy
  simpa [Matrix.submatrix,indices] using large_hessian_psd hy
theorem multiplier_checked : 0≤gramMultiplier.bound.lo := by decide +kernel
theorem multiplier_nonneg : 0≤gramMultiplier.real := by
  have h : (0:ℝ)≤(gramMultiplier.bound.lo:ℝ) := by exact_mod_cast multiplier_checked
  exact h.trans (KernelCoeff.bound_sound gramMultiplier).1
theorem large_near_majorant {x : Fin 3 → ℝ} (hn : Near center largeRadius x) (hg : (x 2)^2≤x 0*x 1) : Real.log (distance x)≤eval3 exactMajorant x := by
  apply sub_nonneg.mp
  exact gap_nonneg_of_gram_correction exactMajorant gramMultiplier x multiplier_nonneg (sub_nonneg.mpr hg) (large_near_gap hn)
#print axioms large_near_majorant
end N7.Kernel.Local.C3
