import N6.BranchEval.B5.Complete
import N6.BranchEval.RealValues
import N6.Univariate.Branch5NoRoots

set_option autoImplicit false

namespace N6.BranchEval.B5.ProgramData
open N6.SparseCheck N6.BranchEval.Program

theorem physical_impossible (x : Fin 5 → ℂ) (a : ℝ)
    (hf : value x program.factor = 0)
    (hc : N6.Weighted49.coordinate_c (x 4) (x 3) = 0)
    (hk : N6.Weighted49.coordinate_k (x 4) (x 2) = 0)
    (he : N6.Weighted49.coordinate_e (x 4) (x 1) = 0)
    (hd : originalD (x 4) (x 3) (x 2) (x 1) ≠ 0)
    (hphysical : originalR4 (x 4) (x 3) (x 2) (x 1) =
      originalD (x 4) (x 3) (x 2) (x 1) * (a : ℂ))
    (ha : 0 ≤ a ∧ a ≤ 225) : False := by
  obtain ⟨hD,hR,hDR,hH⟩ := endpoints_from_coordinates x hf hc hk he
  have hDi : Di x ≠ 0 := by rwa [← hD]
  have hay : Ay x = (a : ℂ) := by
    apply mul_left_cancel₀ hDi
    calc
      Di x * Ay x = Ri x := hDR
      _ = originalR4 (x 4) (x 3) (x 2) (x 1) := hR.symm
      _ = originalD (x 4) (x 3) (x 2) (x 1) * (a : ℂ) := hphysical
      _ = Di x * (a : ℂ) := by rw [hD]
  rw [hay] at hH
  have hHcast : H (a : ℂ) = (H (K := ℝ) a : ℂ) := N6.BranchEval.ratEval_ofReal hCoefficients a
  have hroot : N6.Univariate.eval N6.Univariate.Branch5.p a = 0 := by
    rw [hHcast] at hH
    rw [← H_real_published]
    exact Complex.ofReal_injective hH
  exact N6.Univariate.Branch5.no_root a ha hroot

#print axioms physical_impossible
end N6.BranchEval.B5.ProgramData
