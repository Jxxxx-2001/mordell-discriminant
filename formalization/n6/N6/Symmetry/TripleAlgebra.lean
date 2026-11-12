import N6.Pentagon.OrderedDiscriminant
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false

namespace N6.Symmetry.Triple
open Polynomial

noncomputable def configuration (u v ω : ℂ) : Configuration :=
  fun i => Fin.addCases (m := 3) (n := 3) (motive := fun _ => ℂ)
    (fun j : Fin 3 => u*ω^j.val) (fun j : Fin 3 => v*ω^j.val) i

theorem orbit_cube (u ω : ℂ) (hω : IsPrimitiveRoot ω 3) (j : Fin 3) :
    (u*ω^j.val)^3 = u^3 := by
  rw [mul_pow, ← pow_mul, Nat.mul_comm j.val 3, pow_mul, hω.pow_eq_one, one_pow, mul_one]

private theorem cubic_identity {R : Type*} [CommRing R] (Y u w : R)
    (h : 1+w+w^2=0) (h3 : w^3=1) :
    (Y-u)*(Y-u*w)*(Y-u*w^2) = Y^3-u^3 := by
  linear_combination (-u*Y^2+u^2*Y)*h+(u^2*Y-u^3)*h3

theorem orbit_factor (u ω : ℂ) (hω : IsPrimitiveRoot ω 3) :
    (∏ j : Fin 3, (X-C (u*ω^j.val))) = X^3-C (u^3) := by
  have hg : 1+ω+ω^2=0 := by
    have h := hω.geom_sum_eq_zero (by decide : 1<3)
    norm_num [Finset.sum_range_succ] at h
    linear_combination h
  have hgp : 1+C ω+(C ω : ℂ[X])^2=0 := by
    simpa only [map_add,map_one,map_zero,map_pow] using congrArg (C : ℂ → ℂ[X]) hg
  have hp : (C ω : ℂ[X])^3=1 := by
    simpa only [map_one,map_pow] using congrArg (C : ℂ → ℂ[X]) hω.pow_eq_one
  simpa [Fin.prod_univ_succ, mul_assoc] using cubic_identity (X : ℂ[X]) (C u) (C ω) hgp hp

theorem polynomial (u v ω : ℂ) (hω : IsPrimitiveRoot ω 3) :
    rootPolynomial (configuration u v ω) =
      (X^3-C (u^3))*(X^3-C (v^3)) := by
  unfold rootPolynomial
  rw [Fin.prod_univ_add (a:=3) (b:=3)]
  simp only [configuration, Fin.addCases_left, Fin.addCases_right]
  rw [orbit_factor u ω hω, orbit_factor v ω hω]

private theorem derivative_at_cube (A B w : ℂ) (hw : w^3=A) :
    (((X^3-C A)*(X^3-C B) : ℂ[X]).derivative).eval w = 3*w^2*(A-B) := by
  norm_num [derivative_mul, derivative_sub, derivative_X_pow, hw] <;> ring

private theorem orbit_product (u ω L : ℂ) (hω : IsPrimitiveRoot ω 3) :
    (∏ j : Fin 3, 3*(u*ω^j.val)^2*L) = 3^3*u^6*L^3 := by
  calc
    _ = 3^3*u^6*L^3*(ω^3)^2 := by simp [Fin.prod_univ_succ] <;> ring
    _ = _ := by rw [hω.pow_eq_one]; ring

theorem complex_discriminant (u v ω : ℂ) (hω : IsPrimitiveRoot ω 3) :
    complexDiscriminant (configuration u v ω) =
      -(3:ℂ)^6*u^6*v^6*(u^3-v^3)^6 := by
  let P : ℂ[X] := (X^3-C (u^3))*(X^3-C (v^3))
  have hu (j : Fin 3) : P.derivative.eval (u*ω^j.val) =
      3*(u*ω^j.val)^2*(u^3-v^3) := derivative_at_cube _ _ _ (orbit_cube u ω hω j)
  have hv (j : Fin 3) : P.derivative.eval (v*ω^j.val) =
      3*(v*ω^j.val)^2*(v^3-u^3) := by
    unfold P
    rw [mul_comm (X^3-C (u^3) : ℂ[X]) (X^3-C (v^3))]
    exact derivative_at_cube _ _ _ (orbit_cube v ω hω j)
  unfold complexDiscriminant
  rw [polynomial u v ω hω, Fin.prod_univ_add (a:=3) (b:=3)]
  simp only [configuration, Fin.addCases_left, Fin.addCases_right]
  change (∏ j : Fin 3, P.derivative.eval (u*ω^j.val)) *
    (∏ j : Fin 3, P.derivative.eval (v*ω^j.val)) = _
  simp only [hu, hv]
  rw [orbit_product u ω (u^3-v^3) hω, orbit_product v ω (v^3-u^3) hω]
  ring

theorem discriminant_formula (u v ω : ℂ) (hω : IsPrimitiveRoot ω 3) :
    discriminant (configuration u v ω) =
      3^6 * (Complex.normSq u)^3 * (Complex.normSq v)^3 * (Complex.normSq (u^3-v^3))^3 := by
  have hu0 := Complex.normSq_nonneg u
  have hv0 := Complex.normSq_nonneg v
  have hd0 := Complex.normSq_nonneg (u^3-v^3)
  apply (pow_left_inj₀ (discriminant_nonneg _) (by positivity) (by decide : 2 ≠ 0)).mp
  rw [← Pentagon.complexDiscriminant_normSq, complex_discriminant u v ω hω]
  have h3 : Complex.normSq (3:ℂ) = 9 := by norm_num [Complex.normSq_apply]
  simp only [Complex.normSq_mul, Complex.normSq_neg, map_pow, h3]
  ring

theorem budget (u v ω : ℂ) (hω : IsPrimitiveRoot ω 3) :
    normSum (configuration u v ω) = 3*Complex.normSq u+3*Complex.normSq v := by
  have hw : Complex.normSq ω = 1 := by
    rw [Complex.normSq_eq_norm_sq, hω.norm'_eq_one (by decide)]; norm_num
  unfold normSum
  rw [Fin.sum_univ_add (a:=3) (b:=3)]
  simp only [configuration, Fin.addCases_left, Fin.addCases_right]
  simp [Complex.normSq_mul, map_pow, hw, Fin.sum_univ_succ] <;> ring

end N6.Symmetry.Triple


