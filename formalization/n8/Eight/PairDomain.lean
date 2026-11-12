import Eight.Moments
import Eight.RadiusBound

namespace MordellEight
open Finset
set_option maxHeartbeats 0

theorem radius_le_energy (z : Configuration) (i : Fin 8) : radius z i≤energy z := by
  rw [energy_eq_norm]
  exact Finset.single_le_sum (fun j _ => sq_nonneg ‖z j‖) (mem_univ i)

theorem remaining_moment_cauchy (z : Configuration) (i : Fin 8) :
    (radialMoment z 2-(radius z i)^2)^2 ≤
      (energy z-radius z i)*(radialMoment z 3-(radius z i)^3) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (univ.erase i)
    (fun j : Fin 8 => ‖z j‖) (fun j => ‖z j‖^3)
  have h1 : (∑ j ∈ univ.erase i, ‖z j‖^2)=energy z-radius z i := by
    rw [sum_erase_eq_sub,energy_eq_norm]
    rfl
  have h2 : (∑ j ∈ univ.erase i, ‖z j‖*‖z j‖^3)=radialMoment z 2-(radius z i)^2 := by
    have he (j : Fin 8) : ‖z j‖*‖z j‖^3=(radius z j)^2 := by unfold radius; ring
    simp_rw [he]
    exact sum_erase_eq_sub _ i
  have h3 : (∑ j ∈ univ.erase i, (‖z j‖^3)^2)=radialMoment z 3-(radius z i)^3 := by
    have he (j : Fin 8) : (‖z j‖^3)^2=(radius z j)^3 := by unfold radius; ring
    simp_rw [he]
    exact sum_erase_eq_sub _ i
  rwa [h2,h1,h3] at h

def radialElimination (s u : ℝ) : ℝ :=
  98*s^3*(8-s)+98*(u-s^2)^2-273*u*(8-s)+1352*(8-s)

theorem radial_polynomial_of_moments {s u v : ℝ}
    (hs : 1≤s) (hs8 : s≤8) (hu : u≤32/3)
    (hc : (u-s^2)^2≤(8-s)*(v-s^3))
    (hv : 98*v-273*u+1352≤0) : radiusPolynomial s≤0 := by
  have hm := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hs8) hv
  have hf : radialElimination s u≤0 := by
    unfold radialElimination
    nlinarith [hc,hm]
  have hq : 0<s^2-(39/28)*s+10/21 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (show 0≤s-11/28 by linarith)]
  have hb : 98*(u+32/3-2*s^2)-273*(8-s)≤0 := by nlinarith
  have hdiff := mul_nonneg_of_nonpos_of_nonpos
    (show u-32/3≤0 by linarith) hb
  have he : radialElimination s u-radialElimination s (32/3)=
      (u-32/3)*(98*(u+32/3-2*s^2)-273*(8-s)) := by
    unfold radialElimination
    ring
  have hp : radialElimination s (32/3)=(8/9)*radiusPolynomial s := by
    unfold radialElimination radiusPolynomial
    ring
  rw [←he,hp] at hdiff
  linarith

theorem maximum_radius_upper {z : Configuration} (hz : energy z=8)
    (hm : ∀ y : Configuration, energy y=8 → delta y≤delta z) (i : Fin 8) :
    radius (normalized z) i≤radiusUpper := by
  rw [radius_normalized]
  by_cases hs : 1≤radius z i
  · apply normalized_radius_bound_of_polynomial
    have hc := remaining_moment_cauchy z i
    rw [hz] at hc
    have hs8 : radius z i≤8 := by simpa [hz] using radius_le_energy z i
    have h3 := maximum_third_moment hz hm
    apply radial_polynomial_of_moments hs hs8 (maximum_radialMoment_two hz hm) hc
    nlinarith [sq_nonneg ‖powerSum z 3‖]
  · have hr : radius z i<1 := lt_of_not_ge hs
    norm_num [radiusUpper]
    linarith

/-- Only maximizers are placed in the necessary domain; arbitrary energy-eight inputs are not. -/
theorem maximum_pairDomain {z : Configuration} (hz : energy z=8)
    (hm : ∀ y : Configuration, energy y=8 → delta y≤delta z)
    (i j : Fin 8) (hij : i≠j) :
    PairDomain (‖normalized z i‖^2) (‖normalized z j‖^2)
      (realDot (normalized z i) (normalized z j)) := by
  have hd := maximum_normalized_distance hz hm i j hij
  rw [norm_sub_eq_realDot] at hd
  exact ⟨sq_nonneg _,sq_nonneg _,maximum_radius_upper hz hm i,
    maximum_radius_upper hz hm j,realDot_sq_le _ _,hd⟩

end MordellEight
