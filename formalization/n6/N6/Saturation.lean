import Mathlib.Tactic.Ring

namespace N6.Saturation
variable {R : Type*} [CommRing R]

-- Keep D as a shared expression when cancelling a saturation factor.
theorem cancel_B (t B D u : R) (hS : t * B * D - 1 = 0)
    (hu : B * u = 0) : u = 0 := by
  have hBD : t * B * D = 1 := sub_eq_zero.mp hS
  calc
    u = 1 * u := (one_mul u).symm
    _ = (t * B * D) * u := by rw [hBD]
    _ = (t * D) * (B * u) := by ring
    _ = 0 := by rw [hu, mul_zero]

theorem cancel_D (t B D u : R) (hS : t * B * D - 1 = 0)
    (hu : D * u = 0) : u = 0 := by
  have hBD : t * B * D = 1 := sub_eq_zero.mp hS
  calc
    u = 1 * u := (one_mul u).symm
    _ = (t * B * D) * u := by rw [hBD]
    _ = (t * B) * (D * u) := by ring
    _ = 0 := by rw [hu, mul_zero]

#print axioms cancel_B
#print axioms cancel_D
end N6.Saturation
