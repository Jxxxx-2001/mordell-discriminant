import N6.Exceptional.ChartIIIData
import review.KroneckerFastPack
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.Exceptional
open N6.SparseCheck N6.KroneckerCheck
theorem ChartIIIUnit_checked {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) ChartIIIUnitPairs = 0 := by
  apply check x ChartIIIUnitRad 50 ChartIIIUnitPairs
  · decide +kernel
  · decide +kernel
  · rw [← N6.KroneckerFastPack.pairs_fastPack_eq ChartIIIUnitRad 50 7]
    decide +kernel
#print axioms ChartIIIUnit_checked
end N6.Exceptional
