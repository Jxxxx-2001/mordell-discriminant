import Eight.Checks.IntervalMatrix
import Eight.CoefficientBounds

namespace MordellEight
open Matrix Checks

noncomputable def kernelMatrixReal {n : ℕ} (c : Matrix (Fin n) (Fin n) KernelCoeff) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => (c i j).real

def kernelMatrixCheck {n : ℕ} (c : Matrix (Fin n) (Fin n) KernelCoeff)
    (C U R : Matrix (Fin n) (Fin n) ℚ) (d : Fin n → ℚ) (e : ℚ) : Bool :=
  intervalMatrixCheck (fun i j => (c i j).bound) C U R d e &&
    decide (∀ i j, c i j = c j i)

theorem kernelMatrixCheck_sound {n : ℕ} (c : Matrix (Fin n) (Fin n) KernelCoeff)
    (C U R : Matrix (Fin n) (Fin n) ℚ) (d : Fin n → ℚ) (e : ℚ)
    (hc : kernelMatrixCheck c C U R d e = true) : (kernelMatrixReal c).PosDef := by
  have h : intervalMatrixCheck (fun i j => (c i j).bound) C U R d e = true ∧
      decide (∀ i j, c i j = c j i) = true := by
    simpa only [kernelMatrixCheck,Bool.and_eq_true] using hc
  apply intervalMatrixCheck_sound _ C U R d e h.1 (kernelMatrixReal c)
  · apply Matrix.IsHermitian.ext
    intro i j
    have he := (of_decide_eq_true h.2) j i
    simpa only [kernelMatrixReal,star_trivial] using congrArg KernelCoeff.real he
  · intro i j
    exact KernelCoeff.bound_sound _

end MordellEight
