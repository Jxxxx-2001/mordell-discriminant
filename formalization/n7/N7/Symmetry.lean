import N7.Witness

set_option autoImplicit false

namespace N7

noncomputable def orderedDelta (z : Configuration) : ℝ :=
  ∏ i, ∏ j, if i ≠ j then ‖z i-z j‖^2 else 1

theorem orderedDelta_eq_square (z : Configuration) :
    orderedDelta z = delta z^2 := by
  let g := fun i j : Fin 7 => if i < j then ‖z i-z j‖^2 else 1
  have entry (i j : Fin 7) :
      (if i ≠ j then ‖z i-z j‖^2 else 1) = g i j * g j i := by
    rcases lt_trichotomy i j with h | h | h
    · simp [g, h, ne_of_lt h, not_lt.mpr h.le]
    · subst j
      simp [g]
    · simp [g, h, ne_of_gt h, not_lt.mpr h.le, norm_sub_rev (z j) (z i)]
  calc
    orderedDelta z = (∏ i, ∏ j, g i j) * (∏ i, ∏ j, g j i) := by
      simp only [orderedDelta, entry, Finset.prod_mul_distrib]
    _ = (∏ i, ∏ j, g i j)^2 := by
      rw [Finset.prod_comm (f := fun i j => g j i)]
      ring
    _ = delta z^2 := rfl

theorem energy_relabel (z : Configuration) (σ : Equiv.Perm (Fin 7)) :
    energy (fun i => z (σ i)) = energy z :=
  Equiv.sum_comp σ (fun i => ‖z i‖^2)

theorem orderedDelta_relabel (z : Configuration) (σ : Equiv.Perm (Fin 7)) :
    orderedDelta (fun i => z (σ i)) = orderedDelta z := by
  unfold orderedDelta
  apply Fintype.prod_equiv σ
  intro i
  rw [← Equiv.prod_comp σ (fun j =>
    if σ i ≠ j then ‖z (σ i)-z j‖^2 else 1)]
  simp only [σ.injective.ne_iff]

theorem delta_relabel (z : Configuration) (σ : Equiv.Perm (Fin 7)) :
    delta (fun i => z (σ i)) = delta z := by
  have h := orderedDelta_relabel z σ
  rw [orderedDelta_eq_square, orderedDelta_eq_square] at h
  nlinarith [delta_nonneg (fun i => z (σ i)), delta_nonneg z]

theorem energy_rotation (z : Configuration) {u : ℂ} (hu : ‖u‖ = 1) :
    energy (fun i => u*z i) = energy z := by
  change Chalk.energy (fun i => u*z i) = Chalk.energy z
  rw [Chalk.energy_scale, hu]
  simp

theorem delta_rotation (z : Configuration) {u : ℂ} (hu : ‖u‖ = 1) :
    delta (fun i => u*z i) = delta z := by
  change Chalk.delta (fun i => u*z i) = Chalk.delta z
  rw [Chalk.delta_scale, hu]
  simp

/-- Every configuration described by the equality predicate attains the claimed value. -/
theorem centeredHexagon_sharp {z : Configuration} (hz : IsCenteredHexagon z) :
    energy z = 7 ∧ delta z = sharpConstant := by
  obtain ⟨u, hu, σ, he⟩ := hz
  have hfun : (fun i => z (σ i)) = (fun i => u*sharpWitness i) := funext he
  have hn := energy_rotation sharpWitness hu
  have hd := delta_rotation sharpWitness hu
  rw [← hfun, energy_relabel, sharpWitness_energy] at hn
  rw [← hfun, delta_relabel, sharpWitness_delta] at hd
  exact ⟨hn, hd⟩

#print axioms centeredHexagon_sharp

end N7
