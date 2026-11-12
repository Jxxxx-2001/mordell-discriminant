import N6.Univariate.Branch2Data
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.Univariate.Branch2
theorem checked000 : chunk000.check p v 2176782336 box000 = true := by decide +kernel
#print axioms checked000
theorem checked : tree.check p v 2176782336 ⟨0, 225⟩ = true := by
  exact checked000
#print axioms checked
end N6.Univariate.Branch2
