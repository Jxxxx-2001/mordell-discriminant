import N6.Exceptional.DeterminantsIndices
import N6.Exceptional.Bindings
import review.Resultant6Jet
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.Exceptional
open N6.SparseCheck N6.Resultant6
theorem detJet000 (b c d e U : ℂ) :
    (cut000 (N6.Resultant6General.presentation 0 b c d e U 0)).det = value (point b c d e U) D000 ∧
    HasDerivAt (fun T : ℂ => (cut000 (N6.Resultant6General.presentation 0 b c d e U T)).det) (value (point b c d e U) J000) 0 := by
  constructor
  · simp [Matrix.det_isEmpty, D000, one, m0000, value, monVal]
  · simpa only [Matrix.det_isEmpty, J000, value] using (hasDerivAt_const (0 : ℂ) (1 : ℂ))
end N6.Exceptional
