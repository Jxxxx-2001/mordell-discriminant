import Eight.ExactDefinition
import Eight.ContactCoordinates

namespace MordellEight.ContactCheck0
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem value_checked : exactMajorant.atAlgebraic (contactU 0) (contactV 0) (contactT 0)=contactValue 0 := by
  decide +kernel

theorem value_real : exactMajorant.real (contactU 0).real (contactV 0).real (contactT 0).real =
    Real.log ((contactDistance 0).real) := by
  have h := congrArg KernelCoeff.real value_checked
  rwa [ExactKernel.atAlgebraic_real,contactValue_real] at h

theorem dv_checked :
    (exactMajorant.dv.atAlgebraic (contactU 0) (contactV 0) (contactT 0)).mulAlgebraic (contactDistance 0) = constantCoefficient (1) := by
  decide +kernel

theorem dv_real : exactMajorant.dv.real (contactU 0).real (contactV 0).real (contactT 0).real =
    (1:ℝ)/(contactDistance 0).real := by
  have h := congrArg KernelCoeff.real dv_checked
  rw [KernelCoeff.mulAlgebraic_real,ExactKernel.atAlgebraic_real,constantCoefficient_real] at h
  exact (eq_div_iff (contactDistance_pos 0).ne').mpr (by simpa using h)

theorem dt_checked :
    (exactMajorant.dt.atAlgebraic (contactU 0) (contactV 0) (contactT 0)).mulAlgebraic (contactDistance 0) = constantCoefficient (-2) := by
  decide +kernel

theorem dt_real : exactMajorant.dt.real (contactU 0).real (contactV 0).real (contactT 0).real =
    (-2:ℝ)/(contactDistance 0).real := by
  have h := congrArg KernelCoeff.real dt_checked
  rw [KernelCoeff.mulAlgebraic_real,ExactKernel.atAlgebraic_real,constantCoefficient_real] at h
  exact (eq_div_iff (contactDistance_pos 0).ne').mpr (by simpa using h)

def normalCoefficient : KernelCoeff := exactMajorant.du.atAlgebraic (contactU 0) (contactV 0) (contactT 0)
theorem normal_lower_checked : (1:ℚ)<normalCoefficient.bound.lo := by decide +kernel
theorem normal_real_pos : 1<exactMajorant.du.real (contactU 0).real (contactV 0).real (contactT 0).real := by
  have hb := KernelCoeff.bound_sound normalCoefficient
  have hl : (1:ℝ)<(normalCoefficient.bound.lo:ℝ) := by exact_mod_cast normal_lower_checked
  have h := lt_of_lt_of_le hl hb.1
  simpa only [normalCoefficient,ExactKernel.atAlgebraic_real] using h

end MordellEight.ContactCheck0
