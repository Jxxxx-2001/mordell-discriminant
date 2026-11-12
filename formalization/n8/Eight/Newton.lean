import Eight.Normalized
import Eight.Witness
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta

namespace MordellEight
open Finset Polynomial
set_option maxHeartbeats 0

noncomputable def pointMultiset (z : Configuration) : Multiset ℂ := Finset.univ.val.map z
theorem pointMultiset_card (z : Configuration) : (pointMultiset z).card=8 := by simp [pointMultiset]

theorem aeval_psum_value (z : Configuration) (k : ℕ) :
    MvPolynomial.aeval z (MvPolynomial.psum (Fin 8) ℂ k)=∑ i,(z i)^k := by
  simp [MvPolynomial.psum]

/-- Newton's identities eliminate every intermediate coefficient using the actual power sums. -/
theorem esymm_vanish_of_powerSums (z : Configuration)
    (hp : ∀ k : ℕ,0<k → k<7 → (∑ i,(z i)^k)=0)
    (k : ℕ) (hk : 0<k) (hk8 : k<7) : (pointMultiset z).esymm k=0 := by
  have h := congrArg (MvPolynomial.aeval z) (MvPolynomial.mul_esymm_eq_sum (Fin 8) ℂ k)
  simp only [map_mul,map_pow,map_sum,map_natCast,map_neg,map_one,
    MvPolynomial.aeval_esymm_eq_multiset_esymm,aeval_psum_value] at h
  have hs : (∑ a ∈ (Finset.antidiagonal k).filter (fun a => a.1<k),
      (-1 : ℂ)^a.1*(pointMultiset z).esymm a.1*(∑ i,(z i)^a.2))=0 := by
    apply Finset.sum_eq_zero
    intro a ha
    have hsum : a.1+a.2=k := Finset.mem_antidiagonal.mp (Finset.mem_filter.mp ha).1
    have hlt := (Finset.mem_filter.mp ha).2
    rw [hp a.2 (by omega) (by omega),mul_zero]
  change (k : ℂ)*(pointMultiset z).esymm k=(-1 : ℂ)^(k+1)*
    (∑ a ∈ (Finset.antidiagonal k).filter (fun a => a.1<k),
      (-1 : ℂ)^a.1*(pointMultiset z).esymm a.1*(∑ i,(z i)^a.2)) at h
  rw [hs,mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hk.ne')

theorem pointPolynomial_finprod (z : Configuration) :
    pointPolynomial z=∏ i : Fin 8,(Polynomial.X-Polynomial.C (z i)) := rfl

theorem pointPolynomial_root (z : Configuration) (i : Fin 8) : (pointPolynomial z).eval (z i)=0 := by
  rw [pointPolynomial_finprod,Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

theorem esymm_zero_value (z : Configuration) : (pointMultiset z).esymm 0=1 := by
  simp [Multiset.esymm]

theorem esymm_eight_zero {z : Configuration} {i : Fin 8} (hi : z i=0) :
    (pointMultiset z).esymm 8=0 := by
  rw [←pointMultiset_card z]
  simp only [Multiset.esymm,Multiset.powersetCard_self,Multiset.map_singleton,Multiset.sum_singleton]
  apply Multiset.prod_eq_zero_iff.mpr
  exact Multiset.mem_map.mpr ⟨i,by simp,hi⟩

theorem pointPolynomial_shape (z : Configuration)
    (hp : ∀ k : ℕ,0<k → k<7 → (∑ i,(z i)^k)=0)
    (hi : ∃ i,z i=0) :
    pointPolynomial z=Polynomial.X^8-Polynomial.C ((pointMultiset z).esymm 7)*Polynomial.X := by
  obtain ⟨i,hiz⟩ := hi
  have h := Multiset.prod_X_sub_X_eq_sum_esymm (pointMultiset z)
  rw [pointMultiset_card] at h
  change pointPolynomial z=_ at h
  have h1 := esymm_vanish_of_powerSums z hp 1 (by norm_num) (by norm_num)
  have h2 := esymm_vanish_of_powerSums z hp 2 (by norm_num) (by norm_num)
  have h3 := esymm_vanish_of_powerSums z hp 3 (by norm_num) (by norm_num)
  have h4 := esymm_vanish_of_powerSums z hp 4 (by norm_num) (by norm_num)
  have h5 := esymm_vanish_of_powerSums z hp 5 (by norm_num) (by norm_num)
  have h6 := esymm_vanish_of_powerSums z hp 6 (by norm_num) (by norm_num)
  have h9 := esymm_eight_zero hiz
  norm_num [Finset.sum_range_succ,esymm_zero_value,h1,h2,h3,h4,h5,h6,h9] at h
  exact h

theorem nonzero_seventh_power_common (z : Configuration)
    (hp : ∀ k : ℕ,0<k → k<7 → (∑ i,(z i)^k)=0)
    (hi : ∃ i,z i=0) (j : Fin 8) (hj : z j≠0) :
    (z j)^7= (pointMultiset z).esymm 7 := by
  have h := pointPolynomial_root z j
  rw [pointPolynomial_shape z hp hi] at h
  simp only [Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,
    Polynomial.eval_mul,Polynomial.eval_C] at h
  have he : z j*((z j)^7-(pointMultiset z).esymm 7)=0 := by linear_combination h
  have hs := (mul_eq_zero.mp he).resolve_left hj
  exact sub_eq_zero.mp hs

end MordellEight
