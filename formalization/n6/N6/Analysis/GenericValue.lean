import N6.Analysis.DiscriminantScaling
import N6.Pentagon.Witness

set_option autoImplicit false

namespace N6.GenericValue

theorem six_pow_six_lt_sharp : (6 : ℝ)^6 < sharpConstant := by
  norm_num [sharpConstant]

/-- Apply after a checked real branch calculation has bounded its actual value. -/
theorem not_globalMaximum_of_sq_lt (z : Configuration) (V : ℝ)
    (value_eq : discriminant z^2 = V) (bound : V < (6 : ℝ)^12) :
    ¬ IsGlobalMaximum z := by
  intro hz
  have h : (6 : ℝ)^6 ≤ discriminant z :=
    six_pow_six_lt_sharp.le.trans (Pentagon.global_maximum_lower_bound hz)
  have hh : (6 : ℝ)^12 ≤ V := calc
    (6 : ℝ)^12 = ((6 : ℝ)^6)^2 := by norm_num
    _ ≤ discriminant z^2 := pow_le_pow_left₀ (by norm_num) h 2
    _ = V := value_eq
  exact (not_lt_of_ge hh) bound

theorem exclude_real_branch (z : Configuration) (hn : normSum z = 6)
    (α : ℂ) (hα : α ≠ 0) (a D V : ℝ)
    (ha : physicalScalar (scaleConfiguration α z) = a)
    (hD : complexDiscriminant (scaleConfiguration α z) = (D : ℂ))
    (hV : V = a^15 * D^2 / (5 : ℝ)^30) (bound : V < (6 : ℝ)^12) :
    ¬ IsGlobalMaximum z :=
  not_globalMaximum_of_sq_lt z V (discriminant_sq_of_real_branch z hn α hα a D V ha hD hV) bound

#print axioms not_globalMaximum_of_sq_lt
#print axioms exclude_real_branch
end N6.GenericValue
