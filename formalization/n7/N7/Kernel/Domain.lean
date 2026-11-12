import N7.Kernel.MaximumMoments

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace N7.Kernel
open Finset N7.Analysis

def PairDomain (u v t : ℝ) : Prop :=
  0 ≤ u ∧ 0 ≤ v ∧ u ≤ 9/5 ∧ v ≤ 9/5 ∧ t^2 ≤ u*v ∧ 1/3 ≤ u+v-2*t

theorem radius_le_energy (z : Configuration) (i : Fin 7) : radius z i ≤ normSum z := by
  rw [normSum_eq_norm]
  exact Finset.single_le_sum (fun j _ => sq_nonneg ‖z j‖) (mem_univ i)

theorem remaining_moment_cauchy (z : Configuration) (i : Fin 7) :
    (radialMoment z 2-(radius z i)^2)^2 ≤
      (normSum z-radius z i)*(radialMoment z 3-(radius z i)^3) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (univ.erase i)
    (fun j : Fin 7 => ‖z j‖) (fun j => ‖z j‖^3)
  have h1 : (∑ j ∈ univ.erase i, ‖z j‖^2)=normSum z-radius z i := by
    rw [sum_erase_eq_sub,normSum_eq_norm]
    rfl
  have h2 : (∑ j ∈ univ.erase i, ‖z j‖*‖z j‖^3)=radialMoment z 2-(radius z i)^2 := by
    have he (j : Fin 7) : ‖z j‖*‖z j‖^3=(radius z j)^2 := by unfold radius; ring
    simp_rw [he]
    exact sum_erase_eq_sub _ i
  have h3 : (∑ j ∈ univ.erase i, (‖z j‖^3)^2)=radialMoment z 3-(radius z i)^3 := by
    have he (j : Fin 7) : (‖z j‖^3)^2=(radius z j)^3 := by unfold radius; ring
    simp_rw [he]
    exact sum_erase_eq_sub _ i
  rwa [h2,h1,h3] at h

def radiusPolynomial (s : ℝ) : ℝ := 504*s^3-1344*s^2+1001*s-735
def radialElimination (s u : ℝ) : ℝ :=
  72*s^3*(7-s)+72*(u-s^2)^2-198*u*(7-s)+847*(7-s)

theorem radial_polynomial_of_moments {s u v : ℝ}
    (hs : 2≤s) (hs7 : s≤7) (hu : u≤28/3)
    (hc : (u-s^2)^2≤(7-s)*(v-s^3))
    (hv : 72*v-198*u+847≤0) : radiusPolynomial s≤0 := by
  have hm := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hs7) hv
  have hf : radialElimination s u≤0 := by
    unfold radialElimination
    nlinarith [hc,hm]
  have hs2 : 2*s≤s^2 := by nlinarith
  have hb : 72*(u+28/3-2*s^2)-198*(7-s)≤0 := by nlinarith
  have hdiff := mul_nonneg_of_nonpos_of_nonpos (show u-28/3≤0 by linarith) hb
  have he : radialElimination s u-radialElimination s (28/3)=
      (u-28/3)*(72*(u+28/3-2*s^2)-198*(7-s)) := by
    unfold radialElimination
    ring
  have hp : radialElimination s (28/3)=radiusPolynomial s := by
    unfold radialElimination radiusPolynomial
    ring
  rw [←he,hp] at hdiff
  linarith

theorem radiusPolynomial_strict_above_two {x y : ℝ} (hx : 2≤x) (hxy : x<y) :
    radiusPolynomial x < radiusPolynomial y := by
  have hy : 2≤y := hx.trans hxy.le
  have hx2 : 2*x≤x^2 := by nlinarith
  have hy2 : 2*y≤y^2 := by nlinarith
  have hxy2 : 2*x+2*y-4≤x*y := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]
  have hf : 0<504*(y^2+x*y+x^2)-1344*(y+x)+1001 := by nlinarith
  have hp := mul_pos (sub_pos.mpr hxy) hf
  have he : radiusPolynomial y-radiusPolynomial x =
      (y-x)*(504*(y^2+x*y+x^2)-1344*(y+x)+1001) := by
    unfold radiusPolynomial
    ring
  linarith

theorem radius_bound_of_polynomial {s : ℝ} (hs : radiusPolynomial s≤0) : s≤21/10 := by
  by_contra h
  have hlt := radiusPolynomial_strict_above_two (by norm_num : (2:ℝ)≤21/10) (lt_of_not_ge h)
  have hp : 0<radiusPolynomial (21/10) := by norm_num [radiusPolynomial]
  linarith

theorem maximum_radius_upper {z : Configuration} (hz : IsGlobalMaximum z) (i : Fin 7) :
    radius (normalized z) i≤9/5 := by
  rw [radius_normalized]
  by_cases hs : 2≤radius z i
  · have hc := remaining_moment_cauchy z i
    rw [hz.1] at hc
    have hs7 : radius z i≤7 := by simpa [hz.1] using radius_le_energy z i
    have h3 := maximum_third_moment hz
    have hp := radial_polynomial_of_moments hs hs7 (maximum_radialMoment_two hz) hc
      (by nlinarith [sq_nonneg ‖powerSum z 3‖])
    have h := radius_bound_of_polynomial hp
    linarith
  · have hr : radius z i<2 := lt_of_not_ge hs
    linarith

/-- Every genuine seven-point maximum lies in this complete pair domain. -/
theorem maximum_pairDomain {z : Configuration} (hz : IsGlobalMaximum z)
    (i j : Fin 7) (hij : i≠j) :
    PairDomain (‖normalized z i‖^2) (‖normalized z j‖^2)
      (normalized z i*star (normalized z j)).re := by
  have hd := maximum_normalized_distance hz i j hij
  rw [norm_sub_eq_realDot] at hd
  exact ⟨sq_nonneg _,sq_nonneg _,maximum_radius_upper hz i,
    maximum_radius_upper hz j,realDot_sq_le _ _,hd⟩

#print axioms maximum_pairDomain
end N7.Kernel
