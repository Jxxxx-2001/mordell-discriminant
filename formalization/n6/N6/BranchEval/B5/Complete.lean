import N6.BranchEval.B5.EndpointSemantics
import N6.BranchEval.B5.CoordinateProjection
import N6.BranchEval.B5.OriginalBindings
import N6.Weighted49.Cover
set_option maxRecDepth 64000
set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
namespace N6.BranchEval.B5.ProgramData
open N6.SparseCheck N6.KroneckerCheck N6.BranchEval.Program
variable {K : Type*} [Field K] [CharZero K]
theorem endpoints_from_coordinates (x : Fin 5 → K) (hf : value x program.factor = 0)
    (hc : N6.Weighted49.coordinate_c (x 4) (x 3) = 0) (hk : N6.Weighted49.coordinate_k (x 4) (x 2) = 0) (he : N6.Weighted49.coordinate_e (x 4) (x 1) = 0) :
    originalD (x 4) (x 3) (x 2) (x 1) = Di x ∧ originalR4 (x 4) (x 3) (x 2) (x 1) = Ri x ∧ Di x*Ay x = Ri x ∧ H (Ay x) = 0 := by
  have h0 := endpoint00 x hf; have h1 := endpoint01 x hf
  rw [inputB_value, project_c x hf hc, project_k x hf hk, project_e x hf he] at h0 h1
  exact ⟨h0,h1,endpoint02 x hf,endpoint03 x hf⟩
theorem endpoints_from_inputs (x : Fin 5 → K) (hf : value x program.factor = 0)
    (h0 : value x N6.Dcolon1.f0Data = 0)
    (h1 : value x N6.Dcolon1.f1Data = 0)
    (h2 : value x N6.Dcolon1.f2Data = 0)
    (h3 : value x N6.Dcolon1.f3Data = 0)
    (hs : x 0*x 4*value x N6.Dcolon1.dData-1=0) :
    originalD (x 4) (x 3) (x 2) (x 1) = Di x ∧ originalR4 (x 4) (x 3) (x 2) (x 1) = Ri x ∧ Di x*Ay x = Ri x ∧ H (Ay x) = 0 := by
  have hw := N6.Weighted49.cover_from_inputs x h0 h1 h2 h3 hs
  exact endpoints_from_coordinates x hf hw.2.1 hw.2.2.1 hw.2.2.2
#print axioms endpoints_from_inputs
end N6.BranchEval.B5.ProgramData
