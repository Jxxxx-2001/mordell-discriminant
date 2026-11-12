import Eight.DomainCover
import Eight.BernsteinBox
import Eight.RefinedCoefficientBounds

namespace MordellEight.RootTensor
open Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def box : ClosedBox 3 := domainBox
def polynomial : DenseKernel := exactMajorant.dense
theorem polynomial_real (u v t : ℝ) : polynomial.real u v t=exactMajorant.real u v t :=
  ExactKernel.dense_real _ u v t

end MordellEight.RootTensor
