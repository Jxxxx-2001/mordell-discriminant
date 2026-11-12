import N6.Even.ProgramActualData
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.Even.ProgramData
open N6.SparseCheck
theorem actualD_even_projection : evenPart (N6.ResultantMinors.extractY 6 N6.ResultantMinors.D063) = actualDEvenData := by decide +kernel
#print axioms actualD_even_projection
theorem actualR4_even_projection : evenPart (N6.ResultantMinors.extractY 4 N6.ResultantMinors.D063) = actualR4EvenData := by decide +kernel
#print axioms actualR4_even_projection
theorem actualR02_even_projection : evenPart (N6.ResultantMinors.extractY 2 N6.ResultantMinors.D063) = actualR02EvenData := by decide +kernel
#print axioms actualR02_even_projection
end N6.Even.ProgramData
