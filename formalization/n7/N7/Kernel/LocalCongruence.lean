import N7.Kernel.LocalGeometry
import N7.Kernel.LocalSchur
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace N7.Kernel.LocalCongruence
open Matrix Checks GapAnalytic LocalGeometry

def denseSum (n : ℕ) (f : Fin n → DenseKernel) : DenseKernel :=
  (List.ofFn f).foldr denseOps.add denseOps.zero

theorem denseSum_real (n : ℕ) (f : Fin n → DenseKernel) (u v t : ℝ) :
    (denseSum n f).real u v t=∑ i,(f i).real u v t := by
  have hl (ps : List DenseKernel) : (ps.foldr denseOps.add denseOps.zero).real u v t=(ps.map (fun p => p.real u v t)).sum := by
    induction ps with
    | nil => exact (denseSound u v t).zero
    | cons a ps ih =>
      simpa only [List.foldr_cons,List.map_cons,List.sum_cons,(denseSound u v t).add] using congrArg (fun z => a.real u v t+z) ih
  rw [denseSum,hl,List.map_ofFn,List.sum_ofFn]
  rfl

def conjugateDense {n : ℕ} (R : Matrix (Fin n) (Fin n) ℚ)
    (ps : Fin n → Fin n → DenseKernel) (i j : Fin n) : DenseKernel :=
  denseSum n (fun a => denseSum n (fun b => denseOps.scale (R a i*R b j) (ps a b)))

theorem conjugateDense_real {n : ℕ} (R : Matrix (Fin n) (Fin n) ℚ)
    (ps : Fin n → Fin n → DenseKernel) (i j : Fin n) (u v t : ℝ) :
    (conjugateDense R ps i j).real u v t=∑ a,∑ b,(R a i:ℝ)*(R b j:ℝ)*(ps a b).real u v t := by
  simp only [conjugateDense,denseSum_real,(denseSound u v t).scale,Rat.cast_mul]

theorem psd_of_congruence_inverse {n : ℕ} (H B R : Matrix (Fin n) (Fin n) ℝ)
    (hinv : B*R=1) (hp : (B.transpose*H*B).PosSemidef) : H.PosSemidef := by
  have he : R.transpose*(B.transpose*H*B)*R=H := by
    calc
      _=(B*R).transpose*H*(B*R) := by simp only [Matrix.transpose_mul,Matrix.mul_assoc]
      _=H := by rw [hinv]; simp
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,he] using hp.conjTranspose_mul_mul_same R

def conjugateBounds {n : ℕ} (c : Fin 3 → ℚ) (r : ℚ) (indices : Fin n → Fin 3)
    (R : Matrix (Fin n) (Fin n) ℚ) (ps : Fin n → Fin n → DenseKernel) (i j : Fin n) : QInterval :=
  ((ps i j).bound r).add ((invDistanceSq c r).scale ((∑ a,R a i*ddQ (indices a))*(∑ b,R b j*ddQ (indices b))))

theorem conjugateBounds_sound {n : ℕ} (p : ExactKernel) (c : Fin 3 → ℚ) (r : ℚ)
    (indices : Fin n → Fin 3) (R : Matrix (Fin n) (Fin n) ℚ) (ps : Fin n → Fin n → DenseKernel)
    (hpoly : ∀ i j x,(ps i j).real (x 0-c 0) (x 1-c 1) (x 2-c 2)=
      ∑ a,∑ b,(R a i:ℝ)*(R b j:ℝ)*eval3 (partialPoly (partialPoly p (indices a)) (indices b)) x)
    (hc : 0<centerDistance c-4*r) {x : Fin 3 → ℝ} (hn : Near c r x) (i j : Fin n) :
    (conjugateBounds c r indices R ps i j).Contains
      (((realMatrix R).transpose*(hessian p x).submatrix indices indices*realMatrix R) i j) := by
  have hp := DenseKernel.bound_sound r (ps i j) _ _ _ (hn 0) (hn 1) (hn 2)
  rw [hpoly] at hp
  have h := QInterval.add_sound hp (QInterval.scale_sound ((∑ a,R a i*ddQ (indices a))*(∑ b,R b j*ddQ (indices b))) (invDistanceSq_sound hc hn))
  convert h using 1
  simp only [Matrix.mul_apply,Matrix.transpose_apply,realMatrix,Matrix.submatrix_apply,hessian]
  push_cast
  rw [Finset.sum_mul_sum]
  simp only [Finset.sum_mul,ddQ_cast]
  rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  ring

#print axioms conjugateBounds_sound
end N7.Kernel.LocalCongruence
