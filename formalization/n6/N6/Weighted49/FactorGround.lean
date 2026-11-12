import N6.Weighted49.FactorData
set_option maxRecDepth 32000
set_option maxHeartbeats 1000000
namespace N6.Weighted49.FactorCover
open N6.SparseCheck N6.ResultantMinors
theorem factorChecked : zero (merge globalData (scaled (-1) factorProduct)) = true := by decide +kernel
theorem globalDataBinding :
    (List.ofFn (fun i : Fin 36 => ((⟨0,0,0,0,i.val⟩ : Mon), row_P35Coefficients i))) = globalData := by decide +kernel
#print axioms factorChecked
#print axioms globalDataBinding
end N6.Weighted49.FactorCover
