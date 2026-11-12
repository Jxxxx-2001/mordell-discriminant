import N6.Weighted49.ParentData
import N6.Weighted49.MatrixData
import N6.Weighted49.ActionData
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
def polyLin : {n : Nat} → (Fin n → Mon) → (Fin n → Int) → Poly
  | 0, _, _ => []
  | n + 1, mons, v => merge [(mons 0, v 0)] (polyLin (fun i : Fin n => mons i.succ) (fun i : Fin n => v i.succ))
def columnPoly (m : Mon) (G : Int) (j : Fin 49) (M : Fin 49 → Fin 49 → Int) : Poly :=
  merge [((basisMon j).plus m, G)] (polyLin basisMon (fun i => -M i j))
def variableMon (slot : Nat) : Mon :=
  match slot with | 1 => ⟨0,1,0,0,0⟩ | 2 => ⟨0,0,1,0,0⟩ | 3 => ⟨0,0,0,1,0⟩ | _ => ⟨0,0,0,0,1⟩
end N6.Weighted49
