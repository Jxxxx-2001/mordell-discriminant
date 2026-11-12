import Eight.Necessary

namespace MordellEight
open Finset
set_option maxHeartbeats 0

/-- Split a complete double sum into unordered pairs, with no enumeration of configurations. -/
theorem double_sum_pairs {A : Type*} [AddCommMonoid A] (f : Fin 8 → Fin 8 → A)
    (hd : ∀ i, f i i=0) : (∑ i, ∑ j, f i j)=∑ ij ∈ pairs, (f ij.1 ij.2+f ij.2 ij.1) := by
  have ht (i j : Fin 8) : f i j=(if i < j then f i j else 0)+(if j < i then f i j else 0) := by
    rcases lt_trichotomy i j with h|h|h
    · simp [h,not_lt_of_ge h.le]
    · subst j
      simp [hd]
    · simp [h,not_lt_of_ge h.le]
  calc
    _ = ∑ i : Fin 8, ∑ j : Fin 8, ((if i < j then f i j else 0)+(if j < i then f i j else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_congr rfl (fun j _ => ht i j)
    _ = (∑ i : Fin 8, ∑ j : Fin 8, if i < j then f i j else 0)+
        (∑ i : Fin 8, ∑ j : Fin 8, if j < i then f i j else 0) := by
      simp only [Finset.sum_add_distrib]
    _ = (∑ i : Fin 8, ∑ j : Fin 8, if i < j then f i j else 0)+
        (∑ j : Fin 8, ∑ i : Fin 8, if j < i then f i j else 0) := by
      congr 1
      exact Finset.sum_comm
    _ = (∑ ij ∈ pairs, f ij.1 ij.2)+(∑ ij ∈ pairs, f ij.2 ij.1) := by
      simp only [pairs,Finset.sum_filter,Fintype.sum_prod_type]
    _ = _ := (Finset.sum_add_distrib).symm

noncomputable def force (z : Configuration) (i : Fin 8) : ℂ :=
  ∑ j, (z i-z j)⁻¹

theorem force_eq_erase (z : Configuration) (i : Fin 8) :
    force z i=∑ j ∈ (Finset.univ.erase i), (z i-z j)⁻¹ := by
  rw [force,←Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  simp

theorem pairLinear_force (z w : Configuration) : pairLinear z w=∑ i, w i*force z i := by
  symm
  unfold force
  simp only [Finset.mul_sum,←div_eq_mul_inv]
  rw [double_sum_pairs (fun i j => w i/(z i-z j)) (by intro i; simp)]
  apply Finset.sum_congr rfl
  intro ij hij
  dsimp [pairLinear]
  rw [show z ij.2-z ij.1=-(z ij.1-z ij.2) by ring,div_neg]
  ring

def impulse (i : Fin 8) : Configuration := fun j => if j=i then 1 else 0

/-- The usual complete eight-point stationary equation, derived internally from global maximality. -/
theorem maximum_force {z : Configuration} (hz : energy z=8)
    (hm : ∀ y : Configuration, energy y=8 → delta y≤delta z) (i : Fin 8) :
    (∑ j ∈ Finset.univ.erase i, (z i-z j)⁻¹)= (7/2)*star (z i) := by
  have h := maximum_pairLinear hz hm (impulse i)
  rw [pairLinear_force] at h
  simpa [impulse,innerMoment,←force_eq_erase] using h

noncomputable def laplacian (z w : Configuration) : Configuration :=
  fun i => ∑ j, (w i-w j)/(z i-z j)^2

noncomputable def pairBilinear (z v w : Configuration) : ℂ :=
  ∑ ij ∈ pairs, (v ij.1-v ij.2)*(w ij.1-w ij.2)/(z ij.1-z ij.2)^2

theorem pairBilinear_self (z w : Configuration) : pairBilinear z w w=pairQuadratic z w := by
  unfold pairBilinear pairQuadratic
  apply Finset.sum_congr rfl
  intro ij hij
  rw [div_pow,pow_two (w ij.1-w ij.2)]

theorem pairBilinear_laplacian (z v w : Configuration) :
    pairBilinear z v w=∑ i, v i*laplacian z w i := by
  symm
  unfold laplacian
  simp only [Finset.mul_sum,←mul_div_assoc]
  rw [double_sum_pairs (fun i j => v i*(w i-w j)/(z i-z j)^2) (by intro i; simp)]
  unfold pairBilinear
  apply Finset.sum_congr rfl
  intro ij hij
  rw [show z ij.2-z ij.1=-(z ij.1-z ij.2) by ring,neg_sq]
  ring

theorem laplacian_self (z : Configuration) : laplacian z z=force z := by
  funext i
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : z i-z j=0
  · simp [h]
  · field_simp

end MordellEight
