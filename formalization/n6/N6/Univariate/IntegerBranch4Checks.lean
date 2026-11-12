import N6.Univariate.IntegerBranch4Data
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.IntegerCover.Branch4
theorem checked : tree.check p v vden 2176782336 ⟨0,225,1⟩ = true := by decide +kernel
#print axioms checked
end N6.IntegerCover.Branch4
