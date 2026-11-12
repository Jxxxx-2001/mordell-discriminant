-- Seven-point specialization of the checked Eight/KernelSum.lean identities.
import N7.Kernel.Semantic
import N7.Kernel.Pairs
namespace N7.Kernel
open Matrix Finset
set_option maxHeartbeats 0
theorem kernel_sum_energy_eq_norm (z : Configuration) : energy z = ∑ i, ‖z i‖^2 := rfl

variable (Q : Fin 6 → Matrix (Fin 4) (Fin 4) ℝ)

theorem harmonic_swap (k : ℕ) (u v t : ℝ) : harmonic k u v t=harmonic k v u t := by
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more k ih ih' => rw [harmonic,harmonic,ih,ih']; ring

theorem real_bilinear_swap {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q.IsHermitian) (x y : Fin n → ℝ) : x ⬝ᵥ (Q*ᵥy)=y ⬝ᵥ (Q*ᵥx) := by
  simp only [dotProduct,Matrix.mulVec,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hs : Q j i=Q i j := by simpa only [star_trivial] using hQ.apply i j
  rw [hs]
  ring

theorem kernelFromMatrices_swap (hQ : ∀ k, (Q k).PosDef) (u v t : ℝ) :
    kernelFromMatrices Q u v t=kernelFromMatrices Q v u t := by
  unfold kernelFromMatrices kernelPiece
  apply Finset.sum_congr rfl
  intro k hk
  rw [harmonic_swap,real_bilinear_swap (hQ k).isHermitian]

theorem real_mul_star_swap (a b : ℂ) : (a*star b).re=(b*star a).re := by
  simp only [Complex.mul_re,Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

theorem real_mul_star_self (a : ℂ) : (a*star a).re=‖a‖^2 := by
  simp only [Complex.star_def,Complex.mul_conj,Complex.ofReal_re,Complex.sq_norm]

theorem actual_kernel_swap (hQ : ∀ k, (Q k).PosDef) {m : ℕ} (z : Fin m → ℂ) (i j : Fin m) :
    kernelFromMatrices Q (‖z i‖^2) (‖z j‖^2) (z i*star (z j)).re=
      kernelFromMatrices Q (‖z j‖^2) (‖z i‖^2) (z j*star (z i)).re := by
  rw [kernelFromMatrices_swap Q hQ,real_mul_star_swap]

theorem majorantFromMatrices_swap (hQ : ∀ k, (Q k).PosDef) (u v t : ℝ) :
    majorantFromMatrices Q u v t=majorantFromMatrices Q v u t := by
  dsimp [majorantFromMatrices]
  rw [kernelFromMatrices_swap Q hQ u v t]
  ring

theorem double_sum_diagonal_pairs (f : Fin 7 → Fin 7 → ℝ) :
    (∑ i,∑ j,f i j)=(∑ i,f i i)+∑ ij ∈ N7.pairs,(f ij.1 ij.2+f ij.2 ij.1) := by
  have he (i j : Fin 7) : f i j=(if i=j then f i i else 0)+(if i=j then 0 else f i j) := by
    by_cases h : i=j <;> simp [h]
  calc
    _ = ∑ i,∑ j,((if i=j then f i i else 0)+(if i=j then 0 else f i j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_congr rfl (fun j _ => he i j)
    _ = (∑ i,f i i)+(∑ i,∑ j,if i=j then 0 else f i j) := by
      simp only [Finset.sum_add_distrib]
      simp
    _ = _ := by
      rw [double_sum_pairs (fun i j => if i=j then 0 else f i j) (by intro i; simp)]
      congr 1

theorem pair_sum_values (r : Fin 7 → ℝ) :
    (∑ ij ∈ N7.pairs,(r ij.1+r ij.2))=6*(∑ i,r i) := by
  have hrow (i : Fin 7) : (∑ j : Fin 7,if i=j then 0 else r i)=6*r i := by
    calc
      _ = ∑ j : Fin 7,(r i-(if j=i then r i else 0)) := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases h : i=j
        · subst j
          simp
        · simp only [if_neg h,if_neg (Ne.symm h),sub_zero]
      _ = 7*r i-r i := by simp only [Finset.sum_sub_distrib]; simp
      _ = _ := by ring
  have h := double_sum_pairs (fun i j => if i=j then 0 else r i) (by intro i; simp)
  simp_rw [hrow] at h
  rw [←Finset.mul_sum] at h
  have hright : (∑ ij ∈ N7.pairs,
      ((if ij.1=ij.2 then 0 else r ij.1)+(if ij.2=ij.1 then 0 else r ij.2)))=
      ∑ ij ∈ N7.pairs,(r ij.1+r ij.2) := by
    apply Finset.sum_congr rfl
    intro ij hij
    have hlt := (Finset.mem_filter.mp hij).2
    simp only [if_neg (ne_of_lt hlt),if_neg (ne_of_gt hlt)]
  rw [hright] at h
  exact h.symm

theorem kernel_double_pairs (hQ : ∀ k, (Q k).PosDef) (z : N7.Configuration) :
    (∑ i,∑ j,kernelFromMatrices Q (‖z i‖^2) (‖z j‖^2) (z i*star (z j)).re)=
      (∑ i,kernelFromMatrices Q (‖z i‖^2) (‖z i‖^2) (‖z i‖^2))+
      2*(∑ ij ∈ N7.pairs,
        kernelFromMatrices Q (‖z ij.1‖^2) (‖z ij.2‖^2) (z ij.1*star (z ij.2)).re) := by
  rw [double_sum_diagonal_pairs]
  simp_rw [real_mul_star_self]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [actual_kernel_swap Q hQ z ij.2 ij.1]
  ring

/-- Exact cancellation of all diagonal terms and constants at normalized energy seven. -/
theorem majorant_pair_sum (hQ : ∀ k, (Q k).PosDef) (z : N7.Configuration) (hE : N7.energy z=6) :
    (∑ ij ∈ N7.pairs,
      majorantFromMatrices Q (‖z ij.1‖^2) (‖z ij.2‖^2) (z ij.1*star (z ij.2)).re)=
      6*Real.log 6-(1/2)*(∑ i,∑ j,kernelFromMatrices Q (‖z i‖^2) (‖z j‖^2) (z i*star (z j)).re) := by
  have hr := pair_sum_values (fun i => ‖z i‖^2)
  rw [←kernel_sum_energy_eq_norm] at hr
  rw [hE] at hr
  have hD := pair_sum_values (fun i => kernelFromMatrices Q (‖z i‖^2) (‖z i‖^2) (‖z i‖^2))
  simp only [Finset.sum_add_distrib] at hr hD
  have hK := kernel_double_pairs Q hQ z
  simp only [majorantFromMatrices,Finset.sum_sub_distrib,Finset.sum_add_distrib,
    ←Finset.mul_sum,←Finset.sum_div,Finset.sum_const,N7.pairs_card,nsmul_eq_mul]
  rw [hr,hD]
  linarith

theorem majorant_pair_sum_le (hQ : ∀ k, (Q k).PosDef) (z : N7.Configuration) (hE : N7.energy z=6) :
    (∑ ij ∈ N7.pairs,
      majorantFromMatrices Q (‖z ij.1‖^2) (‖z ij.2‖^2) (z ij.1*star (z ij.2)).re)≤6*Real.log 6 := by
  rw [majorant_pair_sum Q hQ z hE]
  linarith [kernel_double_sum_nonneg Q hQ z]

end N7.Kernel

#print axioms N7.Kernel.majorant_pair_sum_le
