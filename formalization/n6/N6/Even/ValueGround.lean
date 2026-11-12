import N6.Even.ValueData
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.Even.ValueCover
open N6.IntegerCover
theorem checked : tree.check p v vden 2176782336 ⟨-10,10,1⟩ = true := by decide +kernel
#print axioms checked
end N6.Even.ValueCover
