import N6.Univariate.Core
import N6.BranchEval.ProgramCore
set_option maxRecDepth 64000
set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
namespace N6.BranchEval.B1.ProgramData
open N6.SparseCheck N6.KroneckerCheck N6.BranchEval.Program
def hCoefficients : List Rat := [((-225 : Rat) / 1), ((1 : Rat) / 1)]
def bCoefficients : List Rat := [((32 : Rat) / 45)]
def vCoefficients : List Rat := [((310534559388245484896256 : Rat) / 95367431640625)]
end N6.BranchEval.B1.ProgramData
