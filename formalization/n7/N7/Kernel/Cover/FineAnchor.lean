import N7.Kernel.LogAnchors
import N7.Kernel.Bernstein.CoefficientBounds

namespace N7.Kernel.Cover
theorem fineAnchor_le (p q : Int) (l : ℚ)
    (h : (KernelCoeff.bound ⟨0,(p:ℚ),(q:ℚ)⟩).hi≤l) :
    Real.log (logAnchor p q : ℝ)≤(l:ℝ) := by
  rw [logAnchor_log]
  have hb := (KernelCoeff.bound_sound ⟨0,(p:ℚ),(q:ℚ)⟩).2
  have hc : ((KernelCoeff.bound ⟨0,(p:ℚ),(q:ℚ)⟩).hi:ℝ)≤(l:ℝ) := by exact_mod_cast h
  simpa [KernelCoeff.real] using hb.trans hc
end N7.Kernel.Cover
