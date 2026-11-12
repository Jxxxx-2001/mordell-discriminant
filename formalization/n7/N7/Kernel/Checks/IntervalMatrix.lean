import N7.Kernel.Checks.MatrixPerturbation

namespace N7.Kernel.Checks
open Matrix
set_option maxHeartbeats 0

def intervalMatrixCheck {n : ℕ} (bounds : Matrix (Fin n) (Fin n) QInterval)
    (C U R : Matrix (Fin n) (Fin n) ℚ) (d : Fin n → ℚ) (e : ℚ) : Bool :=
  factorCheck (C-Matrix.diagonal (fun _ => (n : ℚ)*e)) U R d &&
    decide (0≤e ∧ ∀ i j,C i j-e≤(bounds i j).lo ∧ (bounds i j).hi≤C i j+e)

/-- Exact rational certificates imply positive definiteness of the enclosed actual matrix. -/
theorem intervalMatrixCheck_sound {n : ℕ} (bounds : Matrix (Fin n) (Fin n) QInterval)
    (C U R : Matrix (Fin n) (Fin n) ℚ) (d : Fin n → ℚ) (e : ℚ)
    (hc : intervalMatrixCheck bounds C U R d e=true)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hs : Q.IsHermitian)
    (hb : ∀ i j,(bounds i j).Contains (Q i j)) : Q.PosDef := by
  have hc' : factorCheck (C-Matrix.diagonal (fun _ => (n : ℚ)*e)) U R d=true ∧
      decide (0≤e ∧ ∀ i j,C i j-e≤(bounds i j).lo ∧ (bounds i j).hi≤C i j+e)=true := by
    simpa only [intervalMatrixCheck,Bool.and_eq_true] using hc
  have h := of_decide_eq_true hc'.2
  have hp := factorCheck_sound _ U R d hc'.1
  have hp' : (realMatrix C-Matrix.diagonal (fun _ : Fin n => (n : ℝ)*(e : ℝ))).PosDef := by
    simpa only [realMatrix_sub,realMatrix_diagonal,Rat.cast_mul,Rat.cast_natCast] using hp
  apply uniform_perturbation_posDef Q (realMatrix C) (e : ℝ)
    (by exact_mod_cast h.1) hs _ hp'
  intro i j
  have hl : (C i j : ℝ)-(e : ℝ)≤((bounds i j).lo : ℝ) := by exact_mod_cast (h.2 i j).1
  have hu : ((bounds i j).hi : ℝ)≤(C i j : ℝ)+(e : ℝ) := by exact_mod_cast (h.2 i j).2
  change |Q i j-(C i j : ℝ)|≤(e : ℝ)
  exact abs_le.mpr ⟨by linarith [(hb i j).1],by linarith [(hb i j).2]⟩

theorem posDef_of_congruence_inverse {n : ℕ} (H B R : Matrix (Fin n) (Fin n) ℝ)
    (hinv : B*R=1) (hp : (B.transpose*H*B).PosDef) : H.PosDef := by
  have hinj : Function.Injective R.mulVec := by
    intro v w hvw
    have h := congrArg (fun y => B*ᵥy) hvw
    simpa only [Matrix.mulVec_mulVec,hinv,Matrix.one_mulVec] using h
  have heq : R.transpose*(B.transpose*H*B)*R=H := by
    calc
      _=(B*R).transpose*H*(B*R) := by simp only [Matrix.transpose_mul,Matrix.mul_assoc]
      _=H := by rw [hinv]; simp
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,heq] using
    hp.conjTranspose_mul_mul_same hinj

end N7.Kernel.Checks
