import N6.Symmetry.TripleAlgebra
import N6.Pentagon.Classification

set_option autoImplicit false

namespace N6.Symmetry.Triple
open Polynomial

/-- The one real inequality needed after applying the complex triangle inequality. -/
theorem radius_bound (r s : ℝ) (hr : 0≤r) (hs : 0≤s) (budget : r^2+s^2=2) :
    r*s*(r^3+s^3) ≤ 2 := by
  let x := r*s
  have hx0 : 0≤x := mul_nonneg hr hs
  have hx1 : x≤1 := by dsimp [x]; nlinarith [sq_nonneg (r-s)]
  have square : (r*s*(r^3+s^3))^2 = 8*x^2-6*x^4+2*x^5 := by
    calc
      _ = x^2*((r^2+s^2)^3-3*x^2*(r^2+s^2)+2*x^3) := by dsimp [x]; ring
      _ = _ := by rw [budget]; ring
  have cert : 4 - (8*x^2-6*x^4+2*x^5) =
      2*(1-x)*(1+(1-x)*(x^2*(1-x)+3*x+1)) := by ring
  have hdiff : 0 ≤ 1-x := sub_nonneg.mpr hx1
  have hpos : 0 ≤ 2*(1-x)*(1+(1-x)*(x^2*(1-x)+3*x+1)) := by positivity
  nlinarith only [square, cert, hpos, sq_nonneg (r*s*(r^3+s^3)-2)]

theorem configuration_bound (u v ω : ℂ) (hω : IsPrimitiveRoot ω 3)
    (hn : normSum (configuration u v ω) = 6) :
    discriminant (configuration u v ω) ≤ 6^6 := by
  have raw := budget u v ω hω
  rw [hn, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at raw
  have radii : ‖u‖^2+‖v‖^2=2 := by linarith
  have ht : ‖u^3-v^3‖ ≤ ‖u‖^3+‖v‖^3 := by
    have htri := _root_.norm_sub_le (u^(3 : ℕ)) (v^(3 : ℕ))
    rw [Complex.norm_pow u (3 : ℕ), Complex.norm_pow v (3 : ℕ)] at htri
    exact htri
  have h : ‖u‖*‖v‖*‖u^3-v^3‖ ≤ 2 :=
    (mul_le_mul_of_nonneg_left ht (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans
      (radius_bound _ _ (norm_nonneg u) (norm_nonneg v) radii)
  calc
    discriminant (configuration u v ω) = 3^6*(‖u‖*‖v‖*‖u^3-v^3‖)^6 := by
      rw [discriminant_formula u v ω hω]
      simp only [Complex.normSq_eq_norm_sq]
      ring
    _ ≤ 3^6*(2:ℝ)^6 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h 6) (by norm_num)
    _ = _ := by norm_num

/-- A factored cubic-in-X³ binomial has precisely the two required orbits up to relabeling.
    Use the original injective six-tuple as the distinct exhibited roots of the candidate. -/
theorem exists_orbits (z : Configuration) (hz : Function.Injective z) (b e : ℂ)
    (hp : rootPolynomial z = X^6 + C b*X^3 + C e) :
    ∃ u v ω : ℂ, IsPrimitiveRoot ω 3 ∧
      ∃ σ : Equiv.Perm (Fin 6), ∀ i, configuration u v ω (σ i) = z i := by
  let u := z 0
  let q := -b-u^3
  let v : ℂ := q ^ ((3 : ℂ)⁻¹)
  have hv : v^3=q := Complex.cpow_nat_inv_pow _ (by decide : (3:ℕ)≠0)
  have hu : u^6+b*u^3+e=0 := by
    have h := rootPolynomial_eval z 0
    rw [hp] at h
    simpa [u] using h
  have he : u^3*v^3=e := by rw [hv]; dsimp [q]; linear_combination -hu
  have hb : -(u^3+v^3)=b := by rw [hv]; dsimp [q]; ring
  let ω : ℂ := Complex.exp (2*Real.pi*Complex.I/3)
  have hω : IsPrimitiveRoot ω 3 := Complex.isPrimitiveRoot_exp 3 (by decide)
  have eqp : rootPolynomial (configuration u v ω) = rootPolynomial z := by
    rw [polynomial u v ω hω, hp]
    calc
      _ = X^6 + C (-(u^3+v^3))*X^3 + C (u^3*v^3) := by
        simp only [map_neg, map_add, map_mul]; ring
      _ = _ := by rw [he, hb]
  obtain ⟨σ,hσ⟩ := Pentagon.perm_of_candidate_roots (configuration u v ω) z hz
    (fun i => by rw [eqp]; exact rootPolynomial_eval z i)
  exact ⟨u,v,ω,hω,σ,hσ⟩

theorem trinomial_bound (z : Configuration) (hn : normSum z=6) (hz : Function.Injective z)
    (b e : ℂ) (hp : rootPolynomial z = X^6 + C b*X^3 + C e) :
    discriminant z ≤ 6^6 := by
  obtain ⟨u,v,ω,hω,σ,hperm⟩ := exists_orbits z hz b e hp
  have hconf : (fun i => configuration u v ω (σ i)) = z := funext hperm
  have hnorm := Pentagon.normSum_relabel (configuration u v ω) σ
  rw [hconf, hn] at hnorm
  have hd := Pentagon.discriminant_relabel (configuration u v ω) σ
  rw [hconf] at hd
  exact hd.le.trans (configuration_bound u v ω hω hnorm.symm)

#print axioms radius_bound
#print axioms configuration_bound
#print axioms trinomial_bound
end N6.Symmetry.Triple
