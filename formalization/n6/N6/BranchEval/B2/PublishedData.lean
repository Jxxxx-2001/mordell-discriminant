import N6.Univariate.Core
import N6.BranchEval.ProgramCore
set_option maxRecDepth 64000
set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
namespace N6.BranchEval.B2.ProgramData
open N6.SparseCheck N6.KroneckerCheck N6.BranchEval.Program
def hCoefficients : List Rat := [((2025 : Rat) / 1), ((-1386 : Rat) / 1), ((1 : Rat) / 1)]
def bCoefficients : List Rat := [((7988 : Rat) / 405), ((-52 : Rat) / 3645)]
def vCoefficients : List Rat := [((37144335666598255871347654656 : Rat) / 37252902984619140625), ((512752752212267763559053656064 : Rat) / 931322574615478515625)]
end N6.BranchEval.B2.ProgramData
