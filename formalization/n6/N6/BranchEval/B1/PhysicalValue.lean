import N6.BranchEval.B1.Complete
import N6.BranchEval.RealValues

set_option autoImplicit false

namespace N6.BranchEval.B1.ProgramData
open N6.SparseCheck N6.BranchEval.Program

theorem physical_endpoint (x : Fin 5 → ℂ) (a : ℝ)
    (hf : value x program.factor = 0)
    (hc : N6.Weighted49.coordinate_c (x 4) (x 3) = 0)
    (hk : N6.Weighted49.coordinate_k (x 4) (x 2) = 0)
    (he : N6.Weighted49.coordinate_e (x 4) (x 1) = 0)
    (hd : originalD (x 4) (x 3) (x 2) (x 1) ≠ 0)
    (hphysical : originalR4 (x 4) (x 3) (x 2) (x 1) =
      originalD (x 4) (x 3) (x 2) (x 1) * (a : ℂ))
    : a = 225 ∧ x 4 = (32 : ℂ)/45 := by
  obtain ⟨hD,hR,hDR,hH,h225,hB⟩ := endpoints_from_coordinates x hf hc hk he
  have hDi : Di x ≠ 0 := by rwa [← hD]
  have hay : Ay x = (a : ℂ) := by
    apply mul_left_cancel₀ hDi
    calc
      Di x * Ay x = Ri x := hDR
      _ = originalR4 (x 4) (x 3) (x 2) (x 1) := hR.symm
      _ = originalD (x 4) (x 3) (x 2) (x 1) * (a : ℂ) := hphysical
      _ = Di x * (a : ℂ) := by rw [hD]
  have ha : a = 225 := by
    apply Complex.ofReal_injective
    simpa using hay.symm.trans h225
  exact ⟨ha,hB⟩

#print axioms physical_endpoint
end N6.BranchEval.B1.ProgramData
