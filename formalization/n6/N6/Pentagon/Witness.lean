import N6.Pentagon.OrderedDiscriminant

set_option autoImplicit false

namespace N6.Pentagon

noncomputable def witnessScale : ℂ := (Real.sqrt ((6 : ℝ)/5) : ℂ)
noncomputable def witnessRoot : ℂ := Complex.exp (2*Real.pi*Complex.I/5)
noncomputable def sharpWitness : Configuration := pentagonConfiguration witnessScale witnessRoot

theorem witnessScale_normSq : Complex.normSq witnessScale = (6 : ℝ)/5 := by
  rw [witnessScale, Complex.normSq_ofReal]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 6/5 by norm_num)]

theorem witnessRoot_primitive : IsPrimitiveRoot witnessRoot 5 :=
  Complex.isPrimitiveRoot_exp 5 (by decide)

theorem sharpWitness_normSum : normSum sharpWitness = 6 :=
  configuration_normSum_six witnessScale_normSq witnessRoot_primitive

theorem sharpWitness_discriminant : discriminant sharpWitness = sharpConstant :=
  configuration_discriminant_sharp witnessScale_normSq witnessRoot_primitive

theorem sharpWitness_isCenteredPentagon : IsCenteredPentagon sharpWitness :=
  configuration_isCenteredPentagon witnessScale_normSq witnessRoot_primitive

theorem exists_sharp_configuration :
    ∃ z : Configuration, normSum z = 6 ∧ discriminant z = sharpConstant :=
  ⟨sharpWitness, sharpWitness_normSum, sharpWitness_discriminant⟩

theorem global_maximum_lower_bound {z : Configuration} (hz : IsGlobalMaximum z) :
    sharpConstant ≤ discriminant z := by
  have h := hz.2 sharpWitness sharpWitness_normSum
  rw [sharpWitness_discriminant] at h
  exact h

end N6.Pentagon
