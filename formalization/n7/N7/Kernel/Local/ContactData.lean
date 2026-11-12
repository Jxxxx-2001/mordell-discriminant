import N7.Kernel.PolynomialData
import N7.Kernel.LocalConvexity
set_option autoImplicit false
namespace N7.Kernel.Local
def gramMultiplier : KernelCoeff := ⟨(712464852167042016589672149946504630752284870/183343686731990868932932772882785066469098489:ℚ),(-350/51:ℚ),(27/34:ℚ)⟩
def boundaryPolynomial : ExactKernel := GapAnalytic.subtractGram exactMajorant gramMultiplier
end N7.Kernel.Local
