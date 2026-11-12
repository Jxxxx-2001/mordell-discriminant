import Eight.Centering

namespace MordellEight
open Finset
set_option maxHeartbeats 0

def complexScale (c : ℂ) (z : Configuration) : Configuration := fun i => c*z i

theorem energy_complexScale (c : ℂ) (z : Configuration) :
    energy (complexScale c z) = ‖c‖^2*energy z := by
  simp only [energy_eq_norm,complexScale,norm_mul,mul_pow,Finset.mul_sum]

theorem delta_complexScale (c : ℂ) (z : Configuration) :
    delta (complexScale c z)=‖c‖^56*delta z := by
  simp only [delta_eq_norm]
  unfold complexScale
  simp_rw [←mul_sub,norm_mul,mul_pow]
  rw [Finset.prod_mul_distrib,Finset.prod_const,pairs_card,←pow_mul]

def relabel (z : Configuration) (σ : Equiv.Perm (Fin 8)) : Configuration := fun i => z (σ i)

theorem energy_relabel (z : Configuration) (σ : Equiv.Perm (Fin 8)) : energy (relabel z σ)=energy z := by
  simp only [energy_eq_norm,relabel]
  exact Equiv.sum_comp σ (fun i => ‖z i‖^2)

theorem double_prod_pairs {A : Type*} [CommMonoid A] (f : Fin 8 → Fin 8 → A)
    (hd : ∀ i,f i i=1) : (∏ i,∏ j,f i j)=∏ ij ∈ pairs,(f ij.1 ij.2*f ij.2 ij.1) := by
  have ht (i j : Fin 8) : f i j=(if i < j then f i j else 1)*(if j < i then f i j else 1) := by
    rcases lt_trichotomy i j with h|h|h
    · simp [h,not_lt_of_ge h.le]
    · subst j
      simp [hd]
    · simp [h,not_lt_of_ge h.le]
  calc
    _ = ∏ i : Fin 8,∏ j : Fin 8,((if i < j then f i j else 1)*(if j < i then f i j else 1)) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact Finset.prod_congr rfl (fun j _ => ht i j)
    _ = (∏ i : Fin 8,∏ j : Fin 8,if i < j then f i j else 1)*
        (∏ i : Fin 8,∏ j : Fin 8,if j < i then f i j else 1) := by
      simp only [Finset.prod_mul_distrib]
    _ = (∏ i : Fin 8,∏ j : Fin 8,if i < j then f i j else 1)*
        (∏ j : Fin 8,∏ i : Fin 8,if j < i then f i j else 1) := by
      congr 1
      exact Finset.prod_comm
    _ = (∏ ij ∈ pairs,f ij.1 ij.2)*(∏ ij ∈ pairs,f ij.2 ij.1) := by
      simp only [pairs,Finset.prod_filter,Fintype.prod_prod_type]
    _ = _ := (Finset.prod_mul_distrib).symm

noncomputable def offDiagProduct (z : Configuration) : ℝ :=
  ∏ i : Fin 8,∏ j : Fin 8,if i=j then 1 else ‖z i-z j‖^2

theorem offDiagProduct_eq (z : Configuration) : offDiagProduct z=(delta z)^2 := by
  unfold offDiagProduct
  rw [double_prod_pairs (fun i j => if i=j then 1 else ‖z i-z j‖^2) (by intro i; simp)]
  calc
    _ = ∏ ij ∈ pairs,(‖z ij.1-z ij.2‖^2*‖z ij.1-z ij.2‖^2) := by
      apply Finset.prod_congr rfl
      intro ij hij
      have hlt := (Finset.mem_filter.mp hij).2
      simp only [if_neg (ne_of_lt hlt),if_neg (ne_of_gt hlt),norm_sub_rev (z ij.2) (z ij.1)]
    _ = delta z*delta z := by simp only [delta_eq_norm]; exact Finset.prod_mul_distrib
    _ = _ := by ring

theorem offDiagProduct_relabel (z : Configuration) (σ : Equiv.Perm (Fin 8)) :
    offDiagProduct (relabel z σ)=offDiagProduct z := by
  calc
    _ = ∏ i : Fin 8,∏ j : Fin 8,if σ i=σ j then 1 else ‖z (σ i)-z (σ j)‖^2 := by
      simp only [offDiagProduct,relabel,σ.injective.eq_iff]
    _ = ∏ i : Fin 8,∏ j : Fin 8,if σ i=j then 1 else ‖z (σ i)-z j‖^2 := by
      apply Finset.prod_congr rfl
      intro i hi
      exact Equiv.prod_comp σ (fun j : Fin 8 => if σ i=j then (1 : ℝ) else ‖z (σ i)-z j‖^2)
    _ = _ := Equiv.prod_comp σ (fun i : Fin 8 =>
      ∏ j : Fin 8,if i=j then (1 : ℝ) else ‖z i-z j‖^2)

theorem delta_relabel (z : Configuration) (σ : Equiv.Perm (Fin 8)) :
    delta (relabel z σ)=delta z := by
  apply (sq_eq_sq₀ (delta_nonneg _) (delta_nonneg _)).mp
  rw [←offDiagProduct_eq,←offDiagProduct_eq,offDiagProduct_relabel]

theorem delta_translate (z : Configuration) (c : ℂ) :
    delta (fun i => z i+c)=delta z := by
  unfold delta
  simp only [add_sub_add_right_eq_sub]

theorem energy_rotate (z : Configuration) (θ : ℝ) :
    energy (complexScale (Complex.exp ((θ : ℂ)*Complex.I)) z)=energy z := by
  rw [energy_complexScale,Complex.norm_exp_ofReal_mul_I,one_pow,one_mul]

theorem delta_rotate (z : Configuration) (θ : ℝ) :
    delta (complexScale (Complex.exp ((θ : ℂ)*Complex.I)) z)=delta z := by
  rw [delta_complexScale,Complex.norm_exp_ofReal_mul_I,one_pow,one_mul]

end MordellEight
