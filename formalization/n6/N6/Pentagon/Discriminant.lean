import N6.Pentagon.Basic

set_option autoImplicit false

namespace N6.Pentagon

theorem discriminant_expand (z : Configuration) :
    discriminant z =
      Complex.normSq (z 0-z 1)*Complex.normSq (z 0-z 2)*
      Complex.normSq (z 0-z 3)*Complex.normSq (z 0-z 4)*Complex.normSq (z 0-z 5)*
      Complex.normSq (z 1-z 2)*Complex.normSq (z 1-z 3)*
      Complex.normSq (z 1-z 4)*Complex.normSq (z 1-z 5)*
      Complex.normSq (z 2-z 3)*Complex.normSq (z 2-z 4)*Complex.normSq (z 2-z 5)*
      Complex.normSq (z 3-z 4)*Complex.normSq (z 3-z 5)*Complex.normSq (z 4-z 5) := by
  unfold discriminant
  rw [pairs_explicit]
  repeat' (rw [Finset.prod_insert] <;> try decide)
  try simp only [Finset.prod_singleton, Finset.prod_empty, mul_one]
  ring

/-- The center contributes five unit factors; the remaining factors are the ten pentagon chords. -/
theorem unit_configuration_discriminant {ω : ℂ} (hω : IsPrimitiveRoot ω 5) :
    discriminant (pentagonConfiguration 1 ω) = 3125 := by
  rw [discriminant_expand]
  simp only [pentagonConfiguration, Fin.cases_zero, Fin.cases_succ, one_mul]
  change
    Complex.normSq (0-ω^0)*Complex.normSq (0-ω^1)*Complex.normSq (0-ω^2)*
    Complex.normSq (0-ω^3)*Complex.normSq (0-ω^4)*
    Complex.normSq (ω^0-ω^1)*Complex.normSq (ω^0-ω^2)*
    Complex.normSq (ω^0-ω^3)*Complex.normSq (ω^0-ω^4)*
    Complex.normSq (ω^1-ω^2)*Complex.normSq (ω^1-ω^3)*Complex.normSq (ω^1-ω^4)*
    Complex.normSq (ω^2-ω^3)*Complex.normSq (ω^2-ω^4)*Complex.normSq (ω^3-ω^4) = 3125
  have hz (k : ℕ) : Complex.normSq (0-ω^k) = 1 := by
    simp only [zero_sub, Complex.normSq_neg, primitive_power_normSq hω]
  rw [hz 0, hz 1, hz 2, hz 3, hz 4]
  simp only [one_mul]
  rw [primitive_distance hω 0 1 (by decide),
    primitive_distance hω 0 2 (by decide), primitive_distance hω 0 3 (by decide),
    primitive_distance hω 0 4 (by decide), primitive_distance hω 1 2 (by decide),
    primitive_distance hω 1 3 (by decide), primitive_distance hω 1 4 (by decide),
    primitive_distance hω 2 3 (by decide), primitive_distance hω 2 4 (by decide),
    primitive_distance hω 3 4 (by decide)]
  norm_num only [Nat.reduceSub]
  rw [show Complex.normSq (1-ω^3) = Complex.normSq (1-ω^2) from
      primitive_distance_complement hω 2 (by decide),
    show Complex.normSq (1-ω^4) = Complex.normSq (1-ω) from
      by simpa using primitive_distance_complement hω 1 (by decide)]
  simp only [pow_one]
  calc
    _ = (Complex.normSq (1-ω)*Complex.normSq (1-ω^2))^5 := by ring
    _ = 3125 := by rw [primitive_chord_product hω]; norm_num

theorem configuration_discriminant {ω : ℂ} (hω : IsPrimitiveRoot ω 5) (u : ℂ) :
    discriminant (pentagonConfiguration u ω) = (Complex.normSq u)^15 * 3125 := by
  rw [configuration_scale, discriminant_scale, unit_configuration_discriminant hω]

theorem configuration_discriminant_sharp {u ω : ℂ}
    (hu : Complex.normSq u = (6 : ℝ)/5) (hω : IsPrimitiveRoot ω 5) :
    discriminant (pentagonConfiguration u ω) = sharpConstant := by
  rw [configuration_discriminant hω, hu]
  norm_num [sharpConstant]

end N6.Pentagon
