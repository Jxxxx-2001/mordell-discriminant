import N6.BranchEval.B4.ProgramBlock000
import N6.BranchEval.B4.ProgramBlock001
import N6.BranchEval.B4.ProgramBlock002
import N6.BranchEval.B4.ProgramBlock003
import N6.BranchEval.B4.ProgramBlock004
import N6.BranchEval.B4.ProgramBlock005
import N6.BranchEval.B4.ProgramBlock006
import N6.BranchEval.B4.ProgramBlock007
import N6.BranchEval.B4.ProgramBlock008
import N6.BranchEval.B4.ProgramBlock009
import N6.BranchEval.B4.ProgramBlock010
import N6.BranchEval.B4.ProgramBlock011
import N6.BranchEval.B4.ProgramBlock012
import N6.BranchEval.B4.ProgramBlock013
import N6.BranchEval.B4.ProgramBlock014
import N6.BranchEval.B4.ProgramBlock015
import N6.BranchEval.B4.ProgramBlock016
import N6.BranchEval.B4.ProgramBlock017
import N6.BranchEval.B4.ProgramBlock018
import N6.BranchEval.B4.ProgramBlock019
import N6.BranchEval.B4.ProgramBlock020
import N6.BranchEval.B4.ProgramBlock021
import N6.BranchEval.B4.ProgramBlock022
import N6.BranchEval.B4.ProgramBlock023
import N6.BranchEval.B4.ProgramBlock024
import N6.BranchEval.B4.ProgramBlock025
import N6.BranchEval.B4.ProgramBlock026
import N6.BranchEval.B4.ProgramBlock027
import N6.BranchEval.B4.ProgramBlock028
import N6.BranchEval.B4.ProgramBlock029
import N6.BranchEval.B4.ProgramBlock030
import N6.BranchEval.B4.ProgramBlock031
import N6.BranchEval.B4.ProgramBlock032
import N6.BranchEval.B4.ProgramBlock033
import N6.BranchEval.B4.ProgramBlock034
import N6.BranchEval.B4.ProgramBlock035
import N6.BranchEval.B4.ProgramBlock036
import N6.BranchEval.B4.ProgramBlock037
import N6.BranchEval.B4.ProgramBlock038
import N6.BranchEval.B4.ProgramBlock039
import N6.BranchEval.B4.ProgramBlock040
import N6.BranchEval.B4.ProgramBlock041
import N6.BranchEval.B4.ProgramBlock042
import N6.BranchEval.B4.ProgramBlock043
import N6.BranchEval.B4.ProgramBlock044
import N6.BranchEval.B4.ProgramBlock045
import N6.BranchEval.B4.ProgramBlock046
import N6.BranchEval.B4.ProgramBlock047
import N6.BranchEval.B4.ProgramBlock048
import N6.BranchEval.B4.ProgramBlock049
import N6.BranchEval.B4.ProgramBlock050
import N6.BranchEval.B4.ProgramBlock051
import N6.BranchEval.B4.ProgramBlock052
import N6.BranchEval.B4.ProgramBlock053
import N6.BranchEval.B4.ProgramBlock054
import N6.BranchEval.B4.ProgramBlock055
import N6.BranchEval.B4.ProgramBlock056
import N6.BranchEval.B4.ProgramBlock057
import N6.BranchEval.B4.ProgramBlock058
import N6.BranchEval.B4.ProgramBlock059
import N6.BranchEval.B4.ProgramBlock060
import N6.BranchEval.B4.ProgramBlock061
import N6.BranchEval.B4.ProgramBlock062
import N6.BranchEval.B4.ProgramBlock063
import N6.BranchEval.B4.ProgramBlock064
import N6.BranchEval.B4.ProgramBlock065
import N6.BranchEval.B4.ProgramBlock066
import N6.BranchEval.B4.ProgramBlock067
import N6.BranchEval.B4.ProgramBlock068
import N6.BranchEval.B4.ProgramBlock069
import N6.BranchEval.B4.ProgramBlock070
import N6.BranchEval.B4.ProgramBlock071
import N6.BranchEval.B4.ProgramBlock072
import N6.BranchEval.B4.ProgramBlock073
import N6.BranchEval.B4.ProgramBlock074
import N6.BranchEval.B4.ProgramBlock075
import N6.BranchEval.B4.ProgramBlock076
import N6.BranchEval.B4.ProgramBlock077
import N6.BranchEval.B4.ProgramBlock078
import N6.BranchEval.B4.ProgramBlock079
import N6.BranchEval.B4.ProgramBlock080
import N6.BranchEval.B4.ProgramBlock081
import N6.BranchEval.ProgramSoundness
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega
set_option maxRecDepth 64000
set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
namespace N6.BranchEval.B4.ProgramData
open N6.SparseCheck N6.KroneckerCheck N6.BranchEval.Program
theorem all_blocks_checked (k : Fin 82) : checkBlock program (k.val*16) (min 16 (1309-k.val*16)) = true := by
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
  · exact block052_checked
  · exact block053_checked
  · exact block054_checked
  · exact block055_checked
  · exact block056_checked
  · exact block057_checked
  · exact block058_checked
  · exact block059_checked
  · exact block060_checked
  · exact block061_checked
  · exact block062_checked
  · exact block063_checked
  · exact block064_checked
  · exact block065_checked
  · exact block066_checked
  · exact block067_checked
  · exact block068_checked
  · exact block069_checked
  · exact block070_checked
  · exact block071_checked
  · exact block072_checked
  · exact block073_checked
  · exact block074_checked
  · exact block075_checked
  · exact block076_checked
  · exact block077_checked
  · exact block078_checked
  · exact block079_checked
  · exact block080_checked
  · exact block081_checked
theorem checked_program : Checked program := by
  intro i hi
  change i < 1309 at hi
  have hk : i/16 < 82 := by omega
  have hj : i%16 < min 16 (1309-(i/16)*16) := by omega
  have h := checked_slot (all_blocks_checked ⟨i/16, hk⟩) hj
  have he : (i/16)*16+i%16 = i := by omega
  simpa only [he] using h
#print axioms checked_program
end N6.BranchEval.B4.ProgramData
