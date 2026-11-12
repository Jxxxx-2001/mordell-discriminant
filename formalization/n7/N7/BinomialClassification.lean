import N7.Analysis.Normalization
import N7.Symmetry
import Mathlib.Data.Fin.Tuple.Basic

set_option autoImplicit false

namespace N7
open Polynomial Analysis

/-- Seven distinct exhibited roots give the required permutation, including multiplicities. -/
theorem perm_of_candidate_roots (z v : Configuration) (hv : Function.Injective v)
    (roots : ∀ i, (rootProduct z).eval (v i) = 0) :
    ∃ σ : Equiv.Perm (Fin 7), ∀ i, z (σ i) = v i := by
  classical
  have each (i : Fin 7) : ∃ j, z j = v i := by
    have h : (∏ j, (v i - z j)) = 0 := by
      simpa only [rootProduct, eval_prod, eval_sub, eval_X, eval_C] using roots i
    obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp h
    exact ⟨j, (sub_eq_zero.mp hj).symm⟩
  choose f hf using each
  have inj : Function.Injective f := by
    intro i j hij
    apply hv
    exact (hf i).symm.trans ((congrArg z hij).trans (hf j))
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp inj), hf⟩

theorem scaled_unitWitness_injective {u : ℂ} (hu : u ≠ 0) :
    Function.Injective (fun i => u * unitWitness i) := by
  have he : (fun i => u * unitWitness i) =
      Fin.cons (α := fun _ : Fin 7 => ℂ) 0 (fun j : Fin 6 => u * witnessRoot^j.val) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [unitWitness]
  rw [he]
  apply Fin.cons_injective_of_injective
  · rintro ⟨j, hj⟩
    exact (mul_ne_zero hu (pow_ne_zero _ (witnessRoot_primitive.ne_zero (by decide)))) hj
  · intro i j hij
    exact Fin.ext (witnessRoot_primitive.pow_inj i.isLt j.isLt (mul_left_cancel₀ hu hij))

/-- A nonzero binomial coefficient determines the entire configuration up to scale. -/
theorem orbit_of_binomial (z : Configuration) (e : ℂ) (he : e ≠ 0)
    (hp : rootProduct z = X^7 + C e * X) :
    ∃ u : ℂ, ∃ σ : Equiv.Perm (Fin 7), ∀ i, z (σ i) = u * unitWitness i := by
  classical
  have hn : ∃ i, z i ≠ 0 := by
    by_contra! hall
    have hzero : rootProduct z = X^7 := by simp [rootProduct, hall]
    have hc := congrArg (fun p : ℂ[X] => p.coeff 1) (hzero.symm.trans hp)
    exact he (by simpa [coeff_X_pow, coeff_C_mul_X] using hc.symm)
  obtain ⟨j, hj⟩ := hn
  let u := z j
  have hu : u ≠ 0 := hj
  have hroot : u^7 + e*u = 0 := by
    have h : (rootProduct z).eval (z j) = 0 := by
      simp only [rootProduct, eval_prod, eval_sub, eval_X, eval_C]
      exact Finset.prod_eq_zero (Finset.mem_univ j) (sub_self _)
    rw [hp] at h
    simpa [u] using h
  have prodzero : u * (u^6 + e) = 0 := by linear_combination hroot
  have hu6 : u^6+e=0 := (mul_eq_zero.mp prodzero).resolve_left hu
  have roots (i : Fin 7) : (rootProduct z).eval (u * unitWitness i) = 0 := by
    rw [hp]
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [unitWitness]
    · have hw6 : (witnessRoot^k.val)^6 = 1 := by
        rw [← pow_mul, Nat.mul_comm k.val 6, pow_mul,
          witnessRoot_primitive.pow_eq_one, one_pow]
      have houter : (u * witnessRoot^k.val)^6 + e = 0 := by
        rw [mul_pow, hw6, mul_one, hu6]
      simp only [unitWitness, Fin.cases_succ, eval_add, eval_pow, eval_X, eval_mul, eval_C]
      linear_combination (u * witnessRoot^k.val)*houter
  obtain ⟨σ, hσ⟩ := perm_of_candidate_roots z _ (scaled_unitWitness_injective hu) roots
  exact ⟨u, σ, hσ⟩

theorem centered_of_orbit (z : Configuration) (hn : energy z = 7) (u : ℂ)
    (σ : Equiv.Perm (Fin 7)) (hv : ∀ i, z (σ i) = u * unitWitness i) :
    IsCenteredHexagon z := by
  have hnorm : ‖u‖^2 = (7 : ℝ)/6 := by
    have h := energy_relabel z σ
    rw [show (fun i => z (σ i)) = (fun i => u * unitWitness i) from funext hv] at h
    change Chalk.energy (fun i => u * unitWitness i) = energy z at h
    rw [Chalk.energy_scale, show Chalk.energy unitWitness = 6 from unitWitness_energy, hn] at h
    linarith
  have hs : witnessScale ≠ 0 := by
    intro h
    have hsq := witnessScale_norm_sq
    norm_num [h] at hsq
  have hu : ‖u‖ = ‖witnessScale‖ := by
    nlinarith [norm_nonneg u, norm_nonneg witnessScale, witnessScale_norm_sq]
  refine ⟨u / witnessScale, ?_, σ, ?_⟩
  · rw [norm_div, hu, div_self (norm_ne_zero_iff.mpr hs)]
  · intro i
    rw [hv i]
    simp only [sharpWitness, ← mul_assoc, div_mul_cancel₀ _ hs]

theorem centered_of_binomial (z : Configuration) (hn : energy z = 7)
    (e : ℂ) (he : e ≠ 0) (hp : rootProduct z = X^7 + C e * X) :
    IsCenteredHexagon z := by
  obtain ⟨u, σ, hv⟩ := orbit_of_binomial z e he hp
  exact centered_of_orbit z hn u σ hv

theorem centered_of_scaled_binomial (z : Configuration) (hn : energy z = 7)
    (α e : ℂ) (hα : α ≠ 0) (he : e ≠ 0)
    (hp : rootProduct (scaleConfiguration α z) = X^7 + C e * X) :
    IsCenteredHexagon z := by
  obtain ⟨u, σ, hv⟩ := orbit_of_binomial (scaleConfiguration α z) e he hp
  apply centered_of_orbit z hn (α⁻¹*u) σ
  intro i
  have h : z (σ i) = α⁻¹ * scaleConfiguration α z (σ i) := by
    simp [scaleConfiguration, ← mul_assoc, hα]
  rw [h, hv i, mul_assoc]

/-- Distinctness supplies the nonzero coefficient, rather than imposing it on a maximum. -/
theorem binomial_coefficient_ne_zero (z : Configuration) (hz : Function.Injective z)
    (e : ℂ) (hp : rootProduct z = X^7 + C e * X) : e ≠ 0 := by
  intro he
  have hall (i : Fin 7) : z i = 0 := by
    have h : (rootProduct z).eval (z i) = 0 := by
      simp only [rootProduct, eval_prod, eval_sub, eval_X, eval_C]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
    rw [hp, he] at h
    simpa using h
  have h01 := hz ((hall 0).trans (hall 1).symm)
  exact (by decide : (0 : Fin 7) ≠ 1) h01

theorem maximum_centered_of_scaled_binomial {z : Configuration} (hz : IsGlobalMaximum z)
    (α e : ℂ) (hα : α ≠ 0)
    (hp : rootProduct (scaleConfiguration α z) = X^7 + C e * X) :
    IsCenteredHexagon z := by
  exact centered_of_scaled_binomial z (by simpa only [normSum_eq_energy] using hz.1)
    α e hα (binomial_coefficient_ne_zero _ (scaled_injective hz hα) e hp) hp

#print axioms centered_of_binomial
#print axioms centered_of_scaled_binomial
#print axioms maximum_centered_of_scaled_binomial

end N7
