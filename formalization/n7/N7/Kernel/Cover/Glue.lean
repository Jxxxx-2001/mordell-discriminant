import N7.Kernel.PolynomialBinding
import N7.Kernel.MatrixBounds
import N7.Kernel.DomainReduction
import N7.Kernel.RootTensor.Core
import N7.Kernel.Bernstein.BoxCoordinates
set_option autoImplicit false
set_option maxHeartbeats 0
namespace N7.Kernel.Cover
open Matrix Finset

def BoxMajorant (b : ClosedBox 3) : Prop :=
  ∀ x, b.Contains x → PairDomain (x 0) (x 1) (x 2) → x 0 ≤ x 1 →
    Real.log (x 0+x 1-2*x 2) ≤ exactMajorant.real (x 0) (x 1) (x 2)

theorem BoxMajorant.half {b : ClosedBox 3} (axis : Fin 3) (_hw : b.Widths)
    (hl : BoxMajorant (b.half axis false)) (hr : BoxMajorant (b.half axis true)) :
    BoxMajorant b := by
  intro x hx hd ho
  rcases b.half_cover axis hx with h | h
  · exact hl x h hd ho
  · exact hr x h hd ho

theorem root_contains (u v t : ℝ) (hd : PairDomain u v t) :
    RootTensor.box.Contains ![u,v,t] := by
  rcases hd with ⟨hu,hv,huu,hvv,ht,_⟩
  have hp : u*v ≤ (9/5:ℝ)^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr huu) (sub_nonneg.mpr hvv)]
  have htl : -(7373/4096:ℝ) ≤ t := by nlinarith
  have htu : t ≤ (7373/4096:ℝ) := by nlinarith
  intro i
  fin_cases i <;> norm_num [RootTensor.box, ClosedBox.Contains] <;> constructor <;> linarith

theorem harmonic_swap (n : ℕ) (u v t : ℝ) : harmonic n u v t = harmonic n v u t := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n h1 h2 => simp only [harmonic, h1, h2]; ring

theorem matrix_bilinear_swap (k : Fin 6) (x y : Fin 4 → ℝ) :
    x ⬝ᵥ (matrix k *ᵥ y) = y ⬝ᵥ (matrix k *ᵥ x) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have h : matrix k i j = matrix k j i := by
    simpa only [star_trivial] using (matrix_isHermitian k).apply j i
  rw [h]
  ring

theorem majorant_swap (u v t : ℝ) : majorantFromMatrices matrix u v t = majorantFromMatrices matrix v u t := by
  have hk : kernelFromMatrices matrix u v t = kernelFromMatrices matrix v u t := by
    unfold kernelFromMatrices
    apply Finset.sum_congr rfl
    intro k hk
    unfold kernelPiece
    rw [harmonic_swap, matrix_bilinear_swap]
  unfold majorantFromMatrices
  rw [hk]
  ring

theorem domainMajorant_of_root (h : BoxMajorant RootTensor.box) : DomainMajorant matrix := by
  intro u v t hd
  rcases le_total u v with huv | hvu
  · have hb := h ![u,v,t] (root_contains u v t hd) (by simpa using hd) (by simpa using huv)
    simpa [exact_majorant_eq_kernel] using hb
  · have hd' : PairDomain v u t := by
      rcases hd with ⟨a,b,c,d,e,f⟩
      exact ⟨b,a,d,c,by nlinarith,by linarith⟩
    have hb := h ![v,u,t] (root_contains v u t hd') (by simpa using hd') (by simpa using hvu)
    change Real.log (v+u-2*t) ≤ exactMajorant.real v u t at hb
    rw [exact_majorant_eq_kernel, ←majorant_swap u v t] at hb
    convert hb using 1 <;> congr 1 <;> ring

#print axioms domainMajorant_of_root
end N7.Kernel.Cover
