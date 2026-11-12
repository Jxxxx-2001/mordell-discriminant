import N6.Univariate.Core
import N6.BranchEval.ProgramCore
set_option maxRecDepth 64000
set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
namespace N6.BranchEval.B0.ProgramData
open N6.SparseCheck N6.KroneckerCheck N6.BranchEval.Program
def hCoefficients : List Rat := [((-9 : Rat) / 1), ((1 : Rat) / 1)]
def bCoefficients : List Rat := [((64 : Rat) / 9)]
def vCoefficients : List Rat := [((325619086145088897570576531456 : Rat) / 931322574615478515625)]
end N6.BranchEval.B0.ProgramData
