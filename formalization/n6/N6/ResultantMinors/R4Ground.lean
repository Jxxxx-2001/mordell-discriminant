import N6.ResultantMinors.R4Data
set_option maxRecDepth 32000
namespace N6.ResultantMinors
theorem rawR4_projection : extractY 4 D063 = rawR4Data := by decide +kernel
#print axioms rawR4_projection
end N6.ResultantMinors
