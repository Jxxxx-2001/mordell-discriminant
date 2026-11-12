import N6.Univariate.Branch3Data
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.Univariate.Branch3
def noRootsTree : Cover := .leaf
theorem noRootsChecked : noRootsTree.check p [] 0 ⟨0, 225⟩ = true := by decide +kernel
#print axioms noRootsChecked
end N6.Univariate.Branch3
