import Eight.Checks.RationalMatrix
import Eight.Checks.Intervals

namespace MordellEight.Checks
open Matrix Finset
set_option maxHeartbeats 0

theorem quadratic_expand {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ (A*ᵥx)=∑ i,∑ j,x i*A i j*x j := by
  simp only [dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc]

theorem uniform_error_quadratic {n : ℕ} (E : Matrix (Fin n) (Fin n) ℝ)
    (e : ℝ) (he : 0≤e) (hE : ∀ i j,|E i j|≤e) (x : Fin n → ℝ) :
    -(n : ℝ)*e*(∑ i,(x i)^2)≤x ⬝ᵥ (E*ᵥx) := by
  have ht (i j : Fin n) : -e * |x i| * |x j| ≤ x i*E i j*x j := by
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hE i j) (abs_nonneg (x i))) (abs_nonneg (x j))
    have hn := neg_le_abs (x i*E i j*x j)
    simp only [abs_mul] at hn
    nlinarith
  have hs := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin n))) =>
    Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin n))) => ht i j))
  have hsum : (∑ i : Fin n,∑ j : Fin n,-e * |x i| * |x j|)=-e*(∑ i,|x i|)^2 := by
    simp only [←Finset.mul_sum,←Finset.sum_mul,pow_two]
    ring
  rw [hsum,←quadratic_expand] at hs
  have hc : (∑ i,|x i|)^2≤(n : ℝ)*(∑ i,(x i)^2) := by
    simpa [sq_abs,mul_comm] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i : Fin n => |x i|) (fun _ => (1 : ℝ))
  have hm := mul_le_mul_of_nonneg_left hc he
  linarith

theorem diagonal_quadratic {n : ℕ} (d : ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ ((Matrix.diagonal (fun _ : Fin n => d))*ᵥx)=d*(∑ i,(x i)^2) := by
  simp only [dotProduct,Matrix.mulVec_diagonal,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- A uniform entry error is absorbed by an exact diagonal shift in the rational lower matrix. -/
theorem uniform_perturbation_posDef {n : ℕ} (Q C : Matrix (Fin n) (Fin n) ℝ)
    (e : ℝ) (he : 0≤e) (hs : Q.IsHermitian)
    (hb : ∀ i j,|Q i j-C i j|≤e)
    (hp : (C-Matrix.diagonal (fun _ => (n : ℝ)*e)).PosDef) : Q.PosDef := by
  let L := C-Matrix.diagonal (fun _ => (n : ℝ)*e)
  have hcorr : (Q-L).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hs.sub hp.isHermitian)
    intro x
    have hbound := uniform_error_quadratic (Q-C) e he hb x
    have heq : Q-L=(Q-C)+Matrix.diagonal (fun _ => (n : ℝ)*e) := by dsimp [L]; abel
    rw [heq,Matrix.add_mulVec,dotProduct_add]
    simp only [star_trivial,diagonal_quadratic]
    linarith
  have h := hp.add_posSemidef hcorr
  have heq : L+(Q-L)=Q := by abel
  rwa [heq] at h

theorem realMatrix_sub {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℚ) :
    realMatrix (A-B)=realMatrix A-realMatrix B := by ext i j; simp [realMatrix]


end MordellEight.Checks
