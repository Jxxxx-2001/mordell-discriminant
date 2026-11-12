-- Seven-point specialization of Eight/Newton.lean; Vieta sign adjusted for degree seven.
import N7.Analysis.RootPolynomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta
namespace N7.Kernel
open Finset Polynomial
set_option maxHeartbeats 0

noncomputable def pointMultiset (z : Configuration) : Multiset ℂ := Finset.univ.val.map z
theorem pointMultiset_card (z : Configuration) : (pointMultiset z).card=7 := by simp [pointMultiset]

theorem aeval_psum_value (z : Configuration) (k : ℕ) :
    MvPolynomial.aeval z (MvPolynomial.psum (Fin 7) ℂ k)=∑ i,(z i)^k := by
  simp [MvPolynomial.psum]

/-- Newton's identities eliminate every intermediate coefficient using the actual power sums. -/
theorem esymm_vanish_of_powerSums (z : Configuration)
    (hp : ∀ k : ℕ,0<k → k<6 → (∑ i,(z i)^k)=0)
    (k : ℕ) (hk : 0<k) (hk8 : k<6) : (pointMultiset z).esymm k=0 := by
  have h := congrArg (MvPolynomial.aeval z) (MvPolynomial.mul_esymm_eq_sum (Fin 7) ℂ k)
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

theorem rootProduct_finprod (z : Configuration) :
    Analysis.rootProduct z=∏ i : Fin 7,(Polynomial.X-Polynomial.C (z i)) := rfl

theorem rootProduct_root (z : Configuration) (i : Fin 7) : (Analysis.rootProduct z).eval (z i)=0 := by
  rw [rootProduct_finprod,Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

theorem esymm_zero_value (z : Configuration) : (pointMultiset z).esymm 0=1 := by
  simp [Multiset.esymm]

theorem esymm_eight_zero {z : Configuration} {i : Fin 7} (hi : z i=0) :
    (pointMultiset z).esymm 7=0 := by
  rw [←pointMultiset_card z]
  simp only [Multiset.esymm,Multiset.powersetCard_self,Multiset.map_singleton,Multiset.sum_singleton]
  apply Multiset.prod_eq_zero_iff.mpr
  exact Multiset.mem_map.mpr ⟨i,by simp,hi⟩

theorem rootProduct_shape (z : Configuration)
    (hp : ∀ k : ℕ,0<k → k<6 → (∑ i,(z i)^k)=0)
    (hi : ∃ i,z i=0) :
    Analysis.rootProduct z=Polynomial.X^7+Polynomial.C ((pointMultiset z).esymm 6)*Polynomial.X := by
  obtain ⟨i,hiz⟩ := hi
  have h := Multiset.prod_X_sub_X_eq_sum_esymm (pointMultiset z)
  rw [pointMultiset_card] at h
  change Analysis.rootProduct z=_ at h
  have h1 := esymm_vanish_of_powerSums z hp 1 (by norm_num) (by norm_num)
  have h2 := esymm_vanish_of_powerSums z hp 2 (by norm_num) (by norm_num)
  have h3 := esymm_vanish_of_powerSums z hp 3 (by norm_num) (by norm_num)
  have h4 := esymm_vanish_of_powerSums z hp 4 (by norm_num) (by norm_num)
  have h5 := esymm_vanish_of_powerSums z hp 5 (by norm_num) (by norm_num)
  have h9 := esymm_eight_zero hiz
  norm_num [Finset.sum_range_succ,esymm_zero_value,h1,h2,h3,h4,h5,h9] at h
  exact h

end N7.Kernel
#print axioms N7.Kernel.rootProduct_shape
