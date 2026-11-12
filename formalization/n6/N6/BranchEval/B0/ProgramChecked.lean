import N6.BranchEval.B0.ProgramBlock000
import N6.BranchEval.B0.ProgramBlock001
import N6.BranchEval.B0.ProgramBlock002
import N6.BranchEval.B0.ProgramBlock003
import N6.BranchEval.B0.ProgramBlock004
import N6.BranchEval.B0.ProgramBlock005
import N6.BranchEval.B0.ProgramBlock006
import N6.BranchEval.B0.ProgramBlock007
import N6.BranchEval.B0.ProgramBlock008
import N6.BranchEval.B0.ProgramBlock009
import N6.BranchEval.B0.ProgramBlock010
import N6.BranchEval.B0.ProgramBlock011
import N6.BranchEval.B0.ProgramBlock012
import N6.BranchEval.B0.ProgramBlock013
import N6.BranchEval.B0.ProgramBlock014
import N6.BranchEval.B0.ProgramBlock015
import N6.BranchEval.B0.ProgramBlock016
import N6.BranchEval.B0.ProgramBlock017
import N6.BranchEval.B0.ProgramBlock018
import N6.BranchEval.B0.ProgramBlock019
import N6.BranchEval.B0.ProgramBlock020
import N6.BranchEval.B0.ProgramBlock021
import N6.BranchEval.B0.ProgramBlock022
import N6.BranchEval.B0.ProgramBlock023
import N6.BranchEval.B0.ProgramBlock024
import N6.BranchEval.B0.ProgramBlock025
import N6.BranchEval.B0.ProgramBlock026
import N6.BranchEval.B0.ProgramBlock027
import N6.BranchEval.B0.ProgramBlock028
import N6.BranchEval.B0.ProgramBlock029
import N6.BranchEval.B0.ProgramBlock030
import N6.BranchEval.B0.ProgramBlock031
import N6.BranchEval.B0.ProgramBlock032
import N6.BranchEval.B0.ProgramBlock033
import N6.BranchEval.B0.ProgramBlock034
import N6.BranchEval.B0.ProgramBlock035
import N6.BranchEval.B0.ProgramBlock036
import N6.BranchEval.B0.ProgramBlock037
import N6.BranchEval.B0.ProgramBlock038
import N6.BranchEval.B0.ProgramBlock039
import N6.BranchEval.B0.ProgramBlock040
import N6.BranchEval.B0.ProgramBlock041
import N6.BranchEval.B0.ProgramBlock042
import N6.BranchEval.B0.ProgramBlock043
import N6.BranchEval.B0.ProgramBlock044
import N6.BranchEval.B0.ProgramBlock045
import N6.BranchEval.B0.ProgramBlock046
import N6.BranchEval.B0.ProgramBlock047
import N6.BranchEval.B0.ProgramBlock048
import N6.BranchEval.B0.ProgramBlock049
import N6.BranchEval.B0.ProgramBlock050
import N6.BranchEval.B0.ProgramBlock051
import N6.BranchEval.ProgramSoundness
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega
set_option maxRecDepth 64000
set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
namespace N6.BranchEval.B0.ProgramData
open N6.SparseCheck N6.KroneckerCheck N6.BranchEval.Program
theorem all_blocks_checked (k : Fin 52) : checkBlock program (k.val*16) (min 16 (820-k.val*16)) = true := by
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
  · exact block013_checked
  · exact block014_checked
  · exact block015_checked
  · exact block016_checked
  · exact block017_checked
  · exact block018_checked
  · exact block019_checked
  · exact block020_checked
  · exact block021_checked
  · exact block022_checked
  · exact block023_checked
  · exact block024_checked
  · exact block025_checked
  · exact block026_checked
  · exact block027_checked
  · exact block028_checked
  · exact block029_checked
  · exact block030_checked
  · exact block031_checked
  · exact block032_checked
  · exact block033_checked
  · exact block034_checked
  · exact block035_checked
  · exact block036_checked
  · exact block037_checked
  · exact block038_checked
  · exact block039_checked
  · exact block040_checked
  · exact block041_checked
  · exact block042_checked
  · exact block043_checked
  · exact block044_checked
  · exact block045_checked
  · exact block046_checked
  · exact block047_checked
  · exact block048_checked
  · exact block049_checked
  · exact block050_checked
  · exact block051_checked
theorem checked_program : Checked program := by
  intro i hi
  change i < 820 at hi
  have hk : i/16 < 52 := by omega
  have hj : i%16 < min 16 (820-(i/16)*16) := by omega
  have h := checked_slot (all_blocks_checked ⟨i/16, hk⟩) hj
  have he : (i/16)*16+i%16 = i := by omega
  simpa only [he] using h
#print axioms checked_program
end N6.BranchEval.B0.ProgramData
