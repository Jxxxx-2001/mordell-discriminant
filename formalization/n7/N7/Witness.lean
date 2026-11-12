import N7.Statement

set_option autoImplicit false

namespace N7

theorem witnessScale_norm_sq : ‖witnessScale‖^2 = (7 : ℝ)/6 := by
  rw [witnessScale, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sq_sqrt (by norm_num)

theorem witnessRoot_primitive : IsPrimitiveRoot witnessRoot 6 :=
  Complex.isPrimitiveRoot_exp 6 (by decide)

theorem unitWitness_energy : energy unitWitness = 6 := by
  have hnorm := witnessRoot_primitive.norm'_eq_one (by decide : 6 ≠ 0)
  simp [energy, Chalk.energy, unitWitness, Fin.sum_univ_succ, norm_pow, hnorm]

theorem unitWitness_delta : delta unitWitness = (6 : ℝ)^6 := by
  change Chalk.delta (Fin.cases 0 (fun j : Fin 6 => witnessRoot^j.val)) = _
  rw [Chalk.delta_cons,
    Chalk.unit_ring_delta (by decide : 0 < 6) witnessRoot_primitive]
  have hnorm := witnessRoot_primitive.norm'_eq_one (by decide : 6 ≠ 0)
  simp [norm_pow, hnorm]

theorem sharpWitness_energy : energy sharpWitness = 7 := by
  have hu : Chalk.energy unitWitness = 6 := unitWitness_energy
  change Chalk.energy (fun i => witnessScale * unitWitness i) = _
  rw [Chalk.energy_scale, witnessScale_norm_sq, hu]
  norm_num

theorem sharpWitness_delta : delta sharpWitness = sharpConstant := by
  have hu : Chalk.delta unitWitness = (6 : ℝ)^6 := unitWitness_delta
  change Chalk.delta (fun i => witnessScale * unitWitness i) = _
  rw [Chalk.delta_scale, witnessScale_norm_sq, hu]
  rw [show Nat.choose 7 2 = 21 by decide]
  norm_num [sharpConstant]

theorem sharpWitness_isCenteredHexagon : IsCenteredHexagon sharpWitness := by
  exact ⟨1, norm_one, Equiv.refl _, fun _ => (one_mul _).symm⟩

/-- Explicit sharpness witness, independent of any classification of stationary points. -/
theorem mordell_seven_sharp_witness :
    energy sharpWitness = 7 ∧ delta sharpWitness = sharpConstant :=
  ⟨sharpWitness_energy, sharpWitness_delta⟩

#print axioms mordell_seven_sharp_witness
#print axioms sharpWitness_isCenteredHexagon

end N7
