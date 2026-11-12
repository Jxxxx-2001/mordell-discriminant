import N7.Kernel.Local.C0Contact
import N7.Kernel.Local.C0LargeCertificate
import N7.Kernel.Local.C0Inward
import N7.Kernel.LocalSegments
set_option autoImplicit false
set_option maxRecDepth 64000
set_option maxHeartbeats 0
namespace N7.Kernel.Local.C0
open GapAnalytic LocalGeometry Matrix Set

theorem large_near_gap {x : Fin 3 → ℝ} (hn : Near center largeRadius x) (hx : 0≤x 0) : 0≤gap exactMajorant x := by
  have hc0 : center 0=0 := rfl
  have hf := near_face0 hc0 (by norm_num [largeRadius] : 0≤largeRadius) hn
  have hface : 0≤gap exactMajorant (face0 x) := by
    apply gap_nonneg_of_face_segment exactMajorant (point center) (face0 x)
      (by norm_num [point,center]) (by simp [face0]) contact_value
    · simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.succ_zero_eq_one,Fin.succ_one_eq_two,add_zero]
      rw [contact_gradient1,contact_gradient2]
      norm_num [face0,point,center]
    · intro s hs
      exact (near_distance_pos large_distance_pos (near_line hf hs)).ne'
    · intro s hs w hw
      apply face_quadratic_nonneg _ _ w hw
      exact large_hessian_psd (near_line hf hs)
  apply gap_nonneg_of_face0 exactMajorant x hx hface
  · intro s hs
    exact (near_distance_pos large_distance_pos (near_face0_line hc0 hn hs)).ne'
  · intro s hs
    exact C0Inward.gradient_nonneg (near_face0_line hc0 hn hs)

theorem large_near_majorant {x : Fin 3 → ℝ} (hn : Near center largeRadius x) (hx : 0≤x 0) : Real.log (distance x)≤eval3 exactMajorant x := sub_nonneg.mp (large_near_gap hn hx)
#print axioms large_near_majorant
end N7.Kernel.Local.C0
