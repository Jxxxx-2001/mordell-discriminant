import Eight.CenterContact.Local
import Eight.KernelBridge
import Eight.KernelSum

namespace MordellEight

/-- The center-neighborhood theorem is connected to the very matrix kernel used in pair sums. -/
theorem center_neighborhood_majorant {x : Fin 3 → ℝ} (hn : CenterContact.Near x)
    (hx : 0≤x 0) :
    Real.log (x 0+x 1-2*x 2)≤majorantFromMatrices (x 0) (x 1) (x 2) := by
  rw [←exact_majorant_eq_kernel]
  exact CenterContact.near_gap_nonneg hn hx

theorem swapped_center_neighborhood_majorant {u v t : ℝ}
    (hn : CenterContact.Near ![v,u,t]) (hv : 0≤v) :
    Real.log (u+v-2*t)≤majorantFromMatrices u v t := by
  have h := center_neighborhood_majorant hn hv
  change Real.log (v+u-2*t)≤majorantFromMatrices v u t at h
  rw [majorantFromMatrices_swap v u t] at h
  simpa only [add_comm v u] using h

end MordellEight
