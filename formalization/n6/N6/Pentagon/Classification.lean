import N6.Pentagon.Basic
import N6.Analysis.SexticCoefficients
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

namespace N6.Pentagon
open Polynomial

/-- Six distinct exhibited roots exhaust the six indexed entries, with multiplicity
    accounted for by the bijection of indices. -/
theorem perm_of_candidate_roots (z v : Configuration) (hv : Function.Injective v)
    (roots : ∀ i, (rootPolynomial z).eval (v i) = 0) :
    ∃ σ : Equiv.Perm (Fin 6), ∀ i, z (σ i) = v i := by
  classical
  have each (i : Fin 6) : ∃ j, z j = v i := by
    have h : (∏ j, (v i - z j)) = 0 := by
      simpa only [rootPolynomial, eval_prod, eval_sub, eval_X, eval_C] using roots i
    obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp h
    exact ⟨j, (sub_eq_zero.mp hj).symm⟩
  choose f hf using each
  have inj : Function.Injective f := by
    intro i j hij
    apply hv
    exact (hf i).symm.trans ((congrArg z hij).trans (hf j))
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp inj), hf⟩

theorem pentagon_injective {u ω : ℂ} (hu : u ≠ 0) (hω : IsPrimitiveRoot ω 5) :
    Function.Injective (pentagonConfiguration u ω) := by
  change Function.Injective (Fin.cons (α := fun _ : Fin 6 => ℂ) 0 (fun j : Fin 5 => u * ω^j.val))
  apply Fin.cons_injective_of_injective
  · rintro ⟨j, hj⟩
    exact (mul_ne_zero hu (pow_ne_zero _ (hω.ne_zero (by decide)))) hj
  · intro i j hij
    exact Fin.ext (hω.pow_inj i.isLt j.isLt (mul_left_cancel₀ hu hij))

/-- The unnormalized binomial already determines the orbit up to scale and relabeling. -/
theorem orbit_of_binomial (z : Configuration) (d : ℂ) (hd : d ≠ 0)
    (hp : rootPolynomial z = X^6 + C d*X) :
    ∃ u ω : ℂ, IsPrimitiveRoot ω 5 ∧
      ∃ σ : Equiv.Perm (Fin 6), ∀ i, z (σ i) = pentagonConfiguration u ω i := by
  classical
  have hn : ∃ i, z i ≠ 0 := by
    by_contra! hall
    have hzero : rootPolynomial z = X^6 := by simp [rootPolynomial, hall]
    have hc := congrArg (fun p : ℂ[X] => p.coeff 1) (hzero.symm.trans hp)
    exact hd (by simpa [coeff_X_pow, coeff_C_mul_X] using hc.symm)
  obtain ⟨j, hj⟩ := hn
  let u := z j
  have hu : u ≠ 0 := hj
  have hroot : u^6 + d*u = 0 := by
    have h := rootPolynomial_eval z j
    rw [hp] at h
    simpa [u] using h
  have prodzero : u * (u^5 + d) = 0 := by linear_combination hroot
  have hu5 : u^5+d=0 := (mul_eq_zero.mp prodzero).resolve_left hu
  let ω : ℂ := Complex.exp (2*Real.pi*Complex.I/5)
  have hω : IsPrimitiveRoot ω 5 := Complex.isPrimitiveRoot_exp 5 (by decide)
  have roots (i : Fin 6) : (rootPolynomial z).eval (pentagonConfiguration u ω i) = 0 := by
    rw [hp]
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [pentagonConfiguration]
    · have hw5 : (ω^k.val)^5 = 1 := by
        rw [← pow_mul, Nat.mul_comm k.val 5, pow_mul, hω.pow_eq_one, one_pow]
      have houter : (u * ω^k.val)^5 + d = 0 := by
        rw [mul_pow, hw5, mul_one, hu5]
      simp only [pentagonConfiguration, Fin.cases_succ, eval_add, eval_pow, eval_X, eval_mul, eval_C]
      linear_combination (u * ω^k.val)*houter
  exact ⟨u, ω, hω, perm_of_candidate_roots z _ (pentagon_injective hu hω) roots⟩

theorem centered_of_orbit (z : Configuration) (hn : normSum z = 6) (u ω : ℂ)
    (hω : IsPrimitiveRoot ω 5) (σ : Equiv.Perm (Fin 6))
    (hv : ∀ i, z (σ i) = pentagonConfiguration u ω i) : IsCenteredPentagon z := by
  have hnorm : normSum (pentagonConfiguration u ω) = 6 := calc
    normSum (pentagonConfiguration u ω) = normSum (fun i => z (σ i)) :=
      congrArg normSum (funext (fun i => (hv i).symm))
    _ = normSum z := Equiv.sum_comp σ (fun i => Complex.normSq (z i))
    _ = 6 := hn
  rw [configuration_normSum hω] at hnorm
  refine ⟨u, ω, by linarith, hω, σ, ?_, ?_⟩
  · simpa [pentagonConfiguration] using hv 0
  · intro j
    simpa [pentagonConfiguration] using hv j.succ

theorem centered_of_binomial (z : Configuration) (hn : normSum z = 6)
    (d : ℂ) (hd : d ≠ 0) (hp : rootPolynomial z = X^6 + C d*X) : IsCenteredPentagon z := by
  obtain ⟨u, ω, hω, σ, hv⟩ := orbit_of_binomial z d hd hp
  exact centered_of_orbit z hn u ω hω σ hv

theorem centered_of_scaled_binomial (z : Configuration) (hn : normSum z = 6)
    (α d : ℂ) (hα : α ≠ 0) (hd : d ≠ 0)
    (hp : rootPolynomial (scaleConfiguration α z) = X^6 + C d*X) : IsCenteredPentagon z := by
  obtain ⟨u, ω, hω, σ, hv⟩ := orbit_of_binomial (scaleConfiguration α z) d hd hp
  apply centered_of_orbit z hn (α⁻¹*u) ω hω σ
  intro i
  have h : z (σ i) = α⁻¹ * pentagonConfiguration u ω i := by
    calc
      z (σ i) = α⁻¹ * scaleConfiguration α z (σ i) := by
        simp [scaleConfiguration, ← mul_assoc, hα]
      _ = α⁻¹ * pentagonConfiguration u ω i := congrArg (fun t : ℂ => α⁻¹*t) (hv i)
  rw [h]
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [pentagonConfiguration]
  · simp [pentagonConfiguration, mul_assoc]

#print axioms perm_of_candidate_roots
#print axioms centered_of_binomial
#print axioms centered_of_scaled_binomial
end N6.Pentagon
