import Eight.KernelSemantic
import Eight.Pairs

namespace MordellEight
open Matrix Finset
set_option maxHeartbeats 0
attribute [local irreducible] kernelQ allMatrixCoefficients

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

theorem kernelFromMatrices_swap (u v t : ℝ) :
    kernelFromMatrices u v t=kernelFromMatrices v u t := by
  unfold kernelFromMatrices kernelPiece
  apply Finset.sum_congr rfl
  intro k hk
  rw [harmonic_swap,real_bilinear_swap (all_kernel_posDef k).isHermitian]

theorem real_mul_star_swap (a b : ℂ) : (a*star b).re=(b*star a).re := by
  simp only [Complex.mul_re,Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

theorem real_mul_star_self (a : ℂ) : (a*star a).re=‖a‖^2 := by
  simp only [Complex.star_def,Complex.mul_conj,Complex.ofReal_re,Complex.sq_norm]

theorem actual_kernel_swap {m : ℕ} (z : Fin m → ℂ) (i j : Fin m) :
    kernelFromMatrices (‖z i‖^2) (‖z j‖^2) (z i*star (z j)).re=
      kernelFromMatrices (‖z j‖^2) (‖z i‖^2) (z j*star (z i)).re := by
  rw [kernelFromMatrices_swap,real_mul_star_swap]

theorem majorantFromMatrices_swap (u v t : ℝ) :
    majorantFromMatrices u v t=majorantFromMatrices v u t := by
  dsimp [majorantFromMatrices]
  rw [kernelFromMatrices_swap u v t]
  ring

theorem double_sum_diagonal_pairs (f : Fin 8 → Fin 8 → ℝ) :
    (∑ i,∑ j,f i j)=(∑ i,f i i)+∑ ij ∈ MordellEight.pairs,(f ij.1 ij.2+f ij.2 ij.1) := by
  have he (i j : Fin 8) : f i j=(if i=j then f i i else 0)+(if i=j then 0 else f i j) := by
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
      rw [MordellEight.double_sum_pairs (fun i j => if i=j then 0 else f i j) (by intro i; simp)]
      congr 1

theorem pair_sum_values (r : Fin 8 → ℝ) :
    (∑ ij ∈ MordellEight.pairs,(r ij.1+r ij.2))=7*(∑ i,r i) := by
  have hrow (i : Fin 8) : (∑ j : Fin 8,if i=j then 0 else r i)=7*r i := by
    calc
      _ = ∑ j : Fin 8,(r i-(if j=i then r i else 0)) := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases h : i=j
        · subst j
          simp
        · simp only [if_neg h,if_neg (Ne.symm h),sub_zero]
      _ = 8*r i-r i := by simp only [Finset.sum_sub_distrib]; simp
      _ = _ := by ring
  have h := MordellEight.double_sum_pairs (fun i j => if i=j then 0 else r i) (by intro i; simp)
  simp_rw [hrow] at h
  rw [←Finset.mul_sum] at h
  have hright : (∑ ij ∈ MordellEight.pairs,
      ((if ij.1=ij.2 then 0 else r ij.1)+(if ij.2=ij.1 then 0 else r ij.2)))=
      ∑ ij ∈ MordellEight.pairs,(r ij.1+r ij.2) := by
    apply Finset.sum_congr rfl
    intro ij hij
    have hlt := (Finset.mem_filter.mp hij).2
    simp only [if_neg (ne_of_lt hlt),if_neg (ne_of_gt hlt)]
  rw [hright] at h
  exact h.symm

theorem kernel_double_pairs (z : MordellEight.Configuration) :
    (∑ i,∑ j,kernelFromMatrices (‖z i‖^2) (‖z j‖^2) (z i*star (z j)).re)=
      (∑ i,kernelFromMatrices (‖z i‖^2) (‖z i‖^2) (‖z i‖^2))+
      2*(∑ ij ∈ MordellEight.pairs,
        kernelFromMatrices (‖z ij.1‖^2) (‖z ij.2‖^2) (z ij.1*star (z ij.2)).re) := by
  rw [double_sum_diagonal_pairs]
  simp_rw [real_mul_star_self]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [actual_kernel_swap z ij.2 ij.1]
  ring

/-- Exact cancellation of all diagonal terms and constants at normalized energy seven. -/
theorem majorant_pair_sum (z : MordellEight.Configuration) (hE : MordellEight.energy z=7) :
    (∑ ij ∈ MordellEight.pairs,
      majorantFromMatrices (‖z ij.1‖^2) (‖z ij.2‖^2) (z ij.1*star (z ij.2)).re)=
      7*Real.log 7-(1/2)*(∑ i,∑ j,kernelFromMatrices (‖z i‖^2) (‖z j‖^2) (z i*star (z j)).re) := by
  have hr := pair_sum_values (fun i => ‖z i‖^2)
  rw [←energy_eq_norm] at hr
  rw [hE] at hr
  have hD := pair_sum_values (fun i => kernelFromMatrices (‖z i‖^2) (‖z i‖^2) (‖z i‖^2))
  simp only [Finset.sum_add_distrib] at hr hD
  have hK := kernel_double_pairs z
  simp only [majorantFromMatrices,Finset.sum_sub_distrib,Finset.sum_add_distrib,
    ←Finset.mul_sum,←Finset.sum_div,Finset.sum_const,MordellEight.pairs_card,nsmul_eq_mul]
  rw [hr,hD]
  linarith

theorem majorant_pair_sum_le (z : MordellEight.Configuration) (hE : MordellEight.energy z=7) :
    (∑ ij ∈ MordellEight.pairs,
      majorantFromMatrices (‖z ij.1‖^2) (‖z ij.2‖^2) (z ij.1*star (z ij.2)).re)≤7*Real.log 7 := by
  rw [majorant_pair_sum z hE]
  linarith [kernel_double_sum_nonneg z]

end MordellEight
