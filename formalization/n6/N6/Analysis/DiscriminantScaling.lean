import N6.Analysis.PhysicalScalar
import N6.Pentagon.OrderedDiscriminant

set_option autoImplicit false

namespace N6.GenericValue

/-- Only the norm budget and a nonzero scaling are needed for this normalization. -/
theorem forceParameter_mul_normSq (z : Configuration) (hn : normSum z = 6)
    (α : ℂ) (hα : α ≠ 0) :
    forceParameter (scaleConfiguration α z) * Complex.normSq α = 5 := by
  have hN : Complex.normSq α ≠ 0 := mt Complex.normSq_eq_zero.mp hα
  have hq : normSum (scaleConfiguration α z) = Complex.normSq α * 6 := by
    change normSum (fun i => α*z i) = _
    rw [normSum_scale, hn]
  change 30 / normSum (scaleConfiguration α z) * Complex.normSq α = 5
  rw [hq]
  field_simp [hN] <;> ring

/-- This equality applies also when the scaled complex discriminant is nonreal. -/
theorem discriminant_sq_normalized (z : Configuration) (hn : normSum z = 6)
    (α : ℂ) (hα : α ≠ 0) :
    discriminant z ^ 2 =
      physicalScalar (scaleConfiguration α z)^15 *
      Complex.normSq (complexDiscriminant (scaleConfiguration α z)) / (5 : ℝ)^30 := by
  have hκ := forceParameter_mul_normSq z hn α hα
  have hD : Complex.normSq (complexDiscriminant (scaleConfiguration α z)) =
      (Complex.normSq α^15 * discriminant z)^2 := by
    rw [Pentagon.complexDiscriminant_normSq]
    exact congrArg (fun t : ℝ => t^2) (discriminant_scale z α)
  rw [hD, physicalScalar]
  apply (eq_div_iff (by norm_num : (5 : ℝ)^30 ≠ 0)).mpr
  calc
    discriminant z^2 * 5^30 = discriminant z^2 *
        (forceParameter (scaleConfiguration α z) * Complex.normSq α)^30 := by rw [hκ]
    _ = _ := by ring

/-- Equivalent formulation with the real part of D * conjugate D. -/
theorem discriminant_sq_conjugate (z : Configuration) (hn : normSum z = 6)
    (α : ℂ) (hα : α ≠ 0) (a : ℝ) (D : ℂ)
    (ha : physicalScalar (scaleConfiguration α z) = a)
    (hD : complexDiscriminant (scaleConfiguration α z) = D) :
    discriminant z^2 = a^15 * (D * star D).re / (5 : ℝ)^30 := by
  simpa only [ha, hD, Complex.star_def, Complex.mul_conj, Complex.ofReal_re] using
    discriminant_sq_normalized z hn α hα

/-- Matches the real one-variable expression V on any branch where D is real. -/
theorem discriminant_sq_of_real_branch (z : Configuration) (hn : normSum z = 6)
    (α : ℂ) (hα : α ≠ 0) (a D V : ℝ)
    (ha : physicalScalar (scaleConfiguration α z) = a)
    (hD : complexDiscriminant (scaleConfiguration α z) = (D : ℂ))
    (hV : V = a^15 * D^2 / (5 : ℝ)^30) : discriminant z^2 = V := by
  rw [hV]
  simpa only [ha, hD, Complex.normSq_ofReal, pow_two D] using
    discriminant_sq_normalized z hn α hα

#print axioms discriminant_sq_normalized
#print axioms discriminant_sq_of_real_branch
end N6.GenericValue
