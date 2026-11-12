import Eight.ExactDefinition
import Eight.ContactCoordinates

namespace MordellEight.ContactCheck3
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem value_checked : exactMajorant.atAlgebraic (contactU 3) (contactV 3) (contactT 3)=contactValue 3 := by
  decide +kernel

theorem value_real : exactMajorant.real (contactU 3).real (contactV 3).real (contactT 3).real =
    Real.log ((contactDistance 3).real) := by
  have h := congrArg KernelCoeff.real value_checked
  rwa [ExactKernel.atAlgebraic_real,contactValue_real] at h

theorem du_checked :
    (exactMajorant.du.atAlgebraic (contactU 3) (contactV 3) (contactT 3)).mulAlgebraic (contactDistance 3) = constantCoefficient (1) := by
  decide +kernel

theorem du_real : exactMajorant.du.real (contactU 3).real (contactV 3).real (contactT 3).real =
    (1:ℝ)/(contactDistance 3).real := by
  have h := congrArg KernelCoeff.real du_checked
  rw [KernelCoeff.mulAlgebraic_real,ExactKernel.atAlgebraic_real,constantCoefficient_real] at h
  exact (eq_div_iff (contactDistance_pos 3).ne').mpr (by simpa using h)

theorem dv_checked :
    (exactMajorant.dv.atAlgebraic (contactU 3) (contactV 3) (contactT 3)).mulAlgebraic (contactDistance 3) = constantCoefficient (1) := by
  decide +kernel

theorem dv_real : exactMajorant.dv.real (contactU 3).real (contactV 3).real (contactT 3).real =
    (1:ℝ)/(contactDistance 3).real := by
  have h := congrArg KernelCoeff.real dv_checked
  rw [KernelCoeff.mulAlgebraic_real,ExactKernel.atAlgebraic_real,constantCoefficient_real] at h
  exact (eq_div_iff (contactDistance_pos 3).ne').mpr (by simpa using h)

theorem dt_checked :
    (exactMajorant.dt.atAlgebraic (contactU 3) (contactV 3) (contactT 3)).mulAlgebraic (contactDistance 3) = constantCoefficient (-2) := by
  decide +kernel

theorem dt_real : exactMajorant.dt.real (contactU 3).real (contactV 3).real (contactT 3).real =
    (-2:ℝ)/(contactDistance 3).real := by
  have h := congrArg KernelCoeff.real dt_checked
  rw [KernelCoeff.mulAlgebraic_real,ExactKernel.atAlgebraic_real,constantCoefficient_real] at h
  exact (eq_div_iff (contactDistance_pos 3).ne').mpr (by simpa using h)

end MordellEight.ContactCheck3
