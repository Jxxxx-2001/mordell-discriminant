-- Reuse of the dimension-independent pair-sum proof from Eight/Pairs.lean.
import N7.Statement
namespace N7.Kernel
open Finset
set_option maxHeartbeats 0

/-- Split a complete double sum into unordered pairs, with no enumeration of configurations. -/
theorem double_sum_pairs {A : Type*} [AddCommMonoid A] (f : Fin 7 → Fin 7 → A)
    (hd : ∀ i, f i i=0) : (∑ i, ∑ j, f i j)=∑ ij ∈ pairs, (f ij.1 ij.2+f ij.2 ij.1) := by
  have ht (i j : Fin 7) : f i j=(if i < j then f i j else 0)+(if j < i then f i j else 0) := by
    rcases lt_trichotomy i j with h|h|h
    · simp [h,not_lt_of_ge h.le]
    · subst j
      simp [hd]
    · simp [h,not_lt_of_ge h.le]
  calc
    _ = ∑ i : Fin 7, ∑ j : Fin 7, ((if i < j then f i j else 0)+(if j < i then f i j else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_congr rfl (fun j _ => ht i j)
    _ = (∑ i : Fin 7, ∑ j : Fin 7, if i < j then f i j else 0)+
        (∑ i : Fin 7, ∑ j : Fin 7, if j < i then f i j else 0) := by
      simp only [Finset.sum_add_distrib]
    _ = (∑ i : Fin 7, ∑ j : Fin 7, if i < j then f i j else 0)+
        (∑ j : Fin 7, ∑ i : Fin 7, if j < i then f i j else 0) := by
      congr 1
      exact Finset.sum_comm
    _ = (∑ ij ∈ pairs, f ij.1 ij.2)+(∑ ij ∈ pairs, f ij.2 ij.1) := by
      simp only [pairs,Finset.sum_filter,Fintype.sum_prod_type]
    _ = _ := (Finset.sum_add_distrib).symm

end N7.Kernel
