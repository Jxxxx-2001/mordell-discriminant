import N6.BranchEval.B5.ProgramBlock000
import N6.BranchEval.B5.ProgramBlock001
import N6.BranchEval.B5.ProgramBlock002
import N6.BranchEval.B5.ProgramBlock003
import N6.BranchEval.B5.ProgramBlock004
import N6.BranchEval.B5.ProgramBlock005
import N6.BranchEval.B5.ProgramBlock006
import N6.BranchEval.B5.ProgramBlock007
import N6.BranchEval.B5.ProgramBlock008
import N6.BranchEval.B5.ProgramBlock009
import N6.BranchEval.B5.ProgramBlock010
import N6.BranchEval.B5.ProgramBlock011
import N6.BranchEval.B5.ProgramBlock012
import N6.BranchEval.ProgramSoundness
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega
set_option maxRecDepth 64000
set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
namespace N6.BranchEval.B5.ProgramData
open N6.SparseCheck N6.KroneckerCheck N6.BranchEval.Program
theorem all_blocks_checked (k : Fin 13) : checkBlock program (k.val*64) (min 64 (824-k.val*64)) = true := by
  fin_cases k
  · exact block000_checked
  · exact block001_checked
  · exact block002_checked
  · exact block003_checked
  · exact block004_checked
  · exact block005_checked
  · exact block006_checked
  · exact block007_checked
  · exact block008_checked
  · exact block009_checked
  · exact block010_checked
  · exact block011_checked
  · exact block012_checked
theorem checked_program : Checked program := by
  intro i hi
  change i < 824 at hi
  have hk : i/64 < 13 := by omega
  have hj : i%64 < min 64 (824-(i/64)*64) := by omega
  have h := checked_slot (all_blocks_checked ⟨i/64, hk⟩) hj
  have he : (i/64)*64+i%64 = i := by omega
  simpa only [he] using h
#print axioms checked_program
end N6.BranchEval.B5.ProgramData
