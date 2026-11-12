import N6.Quartics21.Case017Data
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000

namespace N6.Quartics21.Case017
open N6.SparseCheck N6.KroneckerCheck
theorem room_ok : roomCheck rad factorPairs = true := by decide +kernel
theorem mass_ok : pairs mass factorPairs < ((2 : Int)^width).natAbs := by decide +kernel
#print axioms room_ok
#print axioms mass_ok
theorem fast_ok : pairs (N6.KroneckerFastPack.fastPack rad width 16) factorPairs = 0 := by decide +kernel
#print axioms fast_ok
end N6.Quartics21.Case017
