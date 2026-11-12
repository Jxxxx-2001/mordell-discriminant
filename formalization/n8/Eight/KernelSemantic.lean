import Eight.AllMatrices
import Eight.KernelHarmonics

namespace MordellEight
open Matrix Finset
set_option maxHeartbeats 0
attribute [local irreducible] kernelQ allMatrixCoefficients

noncomputable def radialFeature (k : Fin 7) (u : ℝ) : Fin 4 → ℝ :=
  if k=0 then ![u-7/8,u*(u-1),u^2*(u-1),u^3*(u-1)]
  else fun a => (u-1)^a.val

noncomputable def kernelPiece (k : Fin 7) (u v t : ℝ) : ℝ :=
  harmonic k.val u v t*((radialFeature k u) ⬝ᵥ (kernelQ k*ᵥradialFeature k v))

noncomputable def kernelFromMatrices (u v t : ℝ) : ℝ := ∑ k : Fin 7,kernelPiece k u v t

noncomputable def majorantFromMatrices (u v t : ℝ) : ℝ :=
  (4/7)*(u+v)-1+(1/4)*Real.log 7-kernelFromMatrices u v t-
    (kernelFromMatrices u u u+kernelFromMatrices v v v)/14

noncomputable def momentVector {m : ℕ} (z : Fin m → ℂ) (k : Fin 7) : Fin 4 → ℂ :=
  fun a => ∑ i,(z i)^k.val*(radialFeature k (‖z i‖^2) a : ℂ)

theorem double_sum_swap_sum {m : ℕ} {I : Type*} [Fintype I]
    (f : Fin m → Fin m → I → ℝ) : (∑ i,∑ j,∑ k,f i j k)=∑ k,∑ i,∑ j,f i j k := by
  calc
    _ = ∑ i,∑ k,∑ j,f i j k := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem kernel_actual_expansion {m : ℕ} (z : Fin m → ℂ) (i j : Fin m) :
    kernelFromMatrices (‖z i‖^2) (‖z j‖^2) (z i*star (z j)).re=
      ∑ k : Fin 7,∑ a : Fin 4,∑ b : Fin 4,kernelQ k a b*
        (harmonic k.val (‖z i‖^2) (‖z j‖^2) (z i*star (z j)).re*
          radialFeature k (‖z i‖^2) a*radialFeature k (‖z j‖^2) b) := by
  simp only [kernelFromMatrices,kernelPiece,dotProduct,Matrix.mulVec]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- The full double kernel sum is exactly a sum of seven positive quadratic forms. -/
theorem kernel_double_sum_identity {m : ℕ} (z : Fin m → ℂ) :
    (∑ i,∑ j,kernelFromMatrices (‖z i‖^2) (‖z j‖^2) (z i*star (z j)).re)=
      ∑ k : Fin 7,complexQuadratic (kernelQ k) (momentVector z k) := by
  simp_rw [kernel_actual_expansion]
  rw [double_sum_swap_sum]
  unfold complexQuadratic
  apply Finset.sum_congr rfl
  intro k hk
  rw [double_sum_swap_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [double_sum_swap_sum]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [←Finset.mul_sum]
  rw [weighted_harmonic_sum]
  rfl

theorem kernel_double_sum_nonneg {m : ℕ} (z : Fin m → ℂ) :
    0≤∑ i,∑ j,kernelFromMatrices (‖z i‖^2) (‖z j‖^2) (z i*star (z j)).re := by
  rw [kernel_double_sum_identity]
  exact Finset.sum_nonneg (fun k _ => complexQuadratic_nonneg (all_kernel_posDef k).posSemidef _)

theorem kernel_double_sum_zero_iff {m : ℕ} (z : Fin m → ℂ) :
    (∑ i,∑ j,kernelFromMatrices (‖z i‖^2) (‖z j‖^2) (z i*star (z j)).re)=0 ↔
      ∀ k : Fin 7,momentVector z k=0 := by
  rw [kernel_double_sum_identity]
  constructor
  · intro h k
    have hn : ∀ k ∈ (Finset.univ : Finset (Fin 7)),
        0≤complexQuadratic (kernelQ k) (momentVector z k) :=
      fun k _ => complexQuadratic_nonneg (all_kernel_posDef k).posSemidef _
    have hk := (Finset.sum_eq_zero_iff_of_nonneg hn).mp h k (Finset.mem_univ k)
    exact (complexQuadratic_zero_iff (all_kernel_posDef k) _).mp hk
  · intro h
    apply Finset.sum_eq_zero
    intro k hk
    exact (complexQuadratic_zero_iff (all_kernel_posDef k) _).mpr (h k)

theorem momentVector_zero_real {m : ℕ} (z : Fin m → ℂ) (a : Fin 4) :
    momentVector z 0 a=((∑ i,radialFeature 0 (‖z i‖^2) a : ℝ) : ℂ) := by
  simp only [momentVector,Fin.val_zero,pow_zero,one_mul,Complex.ofReal_sum]

theorem kernel_zero_radius_classification {m : ℕ} (z : Fin m → ℂ)
    (hk : momentVector z 0=0) : ∀ i,‖z i‖^2=0 ∨ ‖z i‖^2=1 := by
  have h1 : (∑ i,‖z i‖^2*(‖z i‖^2-1))=0 := by
    have h := congrArg Complex.re (congrFun hk 1)
    rw [momentVector_zero_real] at h
    simpa only [Complex.ofReal_re,Pi.zero_apply,Complex.zero_re,radialFeature,if_pos rfl,
      Matrix.cons_val_one,Matrix.cons_val_zero] using h
  have h2 : (∑ i,(‖z i‖^2)^2*(‖z i‖^2-1))=0 := by
    have h := congrArg Complex.re (congrFun hk 2)
    rw [momentVector_zero_real] at h
    simpa only [Complex.ofReal_re,Pi.zero_apply,Complex.zero_re,radialFeature,if_pos rfl,
      Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_def] using h
  have hs : (∑ i,‖z i‖^2*(‖z i‖^2-1)^2)=0 := by
    calc
      _ = (∑ i,(‖z i‖^2)^2*(‖z i‖^2-1))-(∑ i,‖z i‖^2*(‖z i‖^2-1)) := by
        rw [←Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by rw [h1,h2]; ring
  intro i
  have he := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j (_ : j∈(Finset.univ : Finset (Fin m))) =>
      mul_nonneg (sq_nonneg ‖z j‖) (sq_nonneg (‖z j‖^2-1)))).mp hs i (Finset.mem_univ i)
  rcases mul_eq_zero.mp he with h|h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp (sq_eq_zero_iff.mp h))

theorem momentVector_first {m : ℕ} (z : Fin m → ℂ) (k : Fin 7) (hk : k≠0) :
    momentVector z k 0=∑ i,(z i)^k.val := by
  simp [momentVector,radialFeature,hk]

end MordellEight
