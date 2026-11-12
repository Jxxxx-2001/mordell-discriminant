import N7.Kernel.PolynomialData
import N7.Kernel.Bernstein.BernsteinBox

namespace N7.Kernel.RootTensor
set_option maxHeartbeats 0
set_option maxRecDepth 64000
def box : ClosedBox 3 := ⟨![0,0,(-7373/4096)],![(7373/4096),(7373/4096),(7373/4096)]⟩
def polynomial : DenseKernel := exactMajorant.dense
theorem polynomial_real (u v t : ℝ) : polynomial.real u v t=exactMajorant.real u v t := ExactKernel.dense_real _ u v t

end N7.Kernel.RootTensor
