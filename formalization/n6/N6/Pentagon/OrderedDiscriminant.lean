import N6.Pentagon.Discriminant
import N6.Analysis.DualStationarity

set_option autoImplicit false

namespace N6.Pentagon

noncomputable def orderedDiscriminant (z : Configuration) : ℝ :=
  ∏ i, ∏ j, if i ≠ j then Complex.normSq (z i-z j) else 1

theorem orderedDiscriminant_eq_square (z : Configuration) :
    orderedDiscriminant z = discriminant z^2 := by
  rw [discriminant_expand]
  simp only [orderedDiscriminant, Fin.prod_univ_succ, Fin.prod_univ_zero]
  simp [Fin.ext_iff, Fin.succ, normSq_sub_comm] <;> ring_nf
  all_goals
    rw [normSq_sub_comm (z 1) (z 0)]
    ring

/-- The product of derivative values agrees in norm with the squared real discriminant. -/
theorem complexDiscriminant_normSq (x : Configuration) :
    Complex.normSq (complexDiscriminant x) = discriminant x^2 := by
  rw [← orderedDiscriminant_eq_square]
  unfold complexDiscriminant orderedDiscriminant
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [rootPolynomial_derivative_eval]
  simp only [rootCofactor, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, map_prod]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  simp only [ne_eq, not_true_eq_false, if_false, mul_one]
  apply Finset.prod_congr rfl
  intro j hj
  simp only [if_pos (Finset.ne_of_mem_erase hj).symm]

theorem normSum_relabel (z : Configuration) (σ : Equiv.Perm (Fin 6)) :
    normSum (fun i => z (σ i)) = normSum z :=
  Equiv.sum_comp σ (fun i => Complex.normSq (z i))

theorem orderedDiscriminant_relabel (z : Configuration) (σ : Equiv.Perm (Fin 6)) :
    orderedDiscriminant (fun i => z (σ i)) = orderedDiscriminant z := by
  unfold orderedDiscriminant
  apply Fintype.prod_equiv σ
  intro i
  rw [← Equiv.prod_comp σ (fun j =>
    if σ i ≠ j then Complex.normSq (z (σ i)-z j) else 1)]
  simp only [σ.injective.ne_iff]

theorem discriminant_relabel (z : Configuration) (σ : Equiv.Perm (Fin 6)) :
    discriminant (fun i => z (σ i)) = discriminant z := by
  have h := orderedDiscriminant_relabel z σ
  rw [orderedDiscriminant_eq_square, orderedDiscriminant_eq_square] at h
  nlinarith [discriminant_nonneg (fun i => z (σ i)), discriminant_nonneg z]

/-- The equality model in Statement is a true sharp configuration, for any labeling. -/
theorem centeredPentagon_sharp {z : Configuration} (hz : IsCenteredPentagon z) :
    normSum z = 6 ∧ discriminant z = sharpConstant := by
  obtain ⟨u, ω, hu, hω, σ, h0, hr⟩ := hz
  have he : (fun i => z (σ i)) = pentagonConfiguration u ω := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [pentagonConfiguration, Fin.cases_zero] using h0
    · simpa only [pentagonConfiguration, Fin.cases_succ] using hr j
  have hn := configuration_normSum_six hu hω
  have hd := configuration_discriminant_sharp hu hω
  rw [← he, normSum_relabel] at hn
  rw [← he, discriminant_relabel] at hd
  exact ⟨hn, hd⟩

end N6.Pentagon
