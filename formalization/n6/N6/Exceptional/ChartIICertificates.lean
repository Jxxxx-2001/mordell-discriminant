import N6.Exceptional.ChartIIData
import review.KroneckerFastPack
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.Exceptional
open N6.SparseCheck N6.KroneckerCheck
theorem ChartIIC_checked {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) ChartIICPairs = 0 := by
  apply check x ChartIICRad 329 ChartIICPairs
  · decide +kernel
  · decide +kernel
  · rw [← N6.KroneckerFastPack.pairs_fastPack_eq ChartIICRad 329 11]
    decide +kernel
#print axioms ChartIIC_checked
theorem ChartIID_checked {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) ChartIIDPairs = 0 := by
  apply check x ChartIIDRad 628 ChartIIDPairs
  · decide +kernel
  · decide +kernel
  · rw [← N6.KroneckerFastPack.pairs_fastPack_eq ChartIIDRad 628 11]
    decide +kernel
#print axioms ChartIID_checked
end N6.Exceptional
