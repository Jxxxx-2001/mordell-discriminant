import Eight.ExactDefinition
import Eight.ContactCoordinates

namespace MordellEight.ContactCheck2
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem value_checked : exactMajorant.atAlgebraic (contactU 2) (contactV 2) (contactT 2)=contactValue 2 := by
  decide +kernel

theorem value_real : exactMajorant.real (contactU 2).real (contactV 2).real (contactT 2).real =
    Real.log ((contactDistance 2).real) := by
  have h := congrArg KernelCoeff.real value_checked
  rwa [ExactKernel.atAlgebraic_real,contactValue_real] at h

theorem du_checked :
    (exactMajorant.du.atAlgebraic (contactU 2) (contactV 2) (contactT 2)).mulAlgebraic (contactDistance 2) = constantCoefficient (1) := by
  decide +kernel

theorem du_real : exactMajorant.du.real (contactU 2).real (contactV 2).real (contactT 2).real =
    (1:ℝ)/(contactDistance 2).real := by
  have h := congrArg KernelCoeff.real du_checked
  rw [KernelCoeff.mulAlgebraic_real,ExactKernel.atAlgebraic_real,constantCoefficient_real] at h
  exact (eq_div_iff (contactDistance_pos 2).ne').mpr (by simpa using h)

theorem dv_checked :
    (exactMajorant.dv.atAlgebraic (contactU 2) (contactV 2) (contactT 2)).mulAlgebraic (contactDistance 2) = constantCoefficient (1) := by
  decide +kernel

theorem dv_real : exactMajorant.dv.real (contactU 2).real (contactV 2).real (contactT 2).real =
    (1:ℝ)/(contactDistance 2).real := by
  have h := congrArg KernelCoeff.real dv_checked
  rw [KernelCoeff.mulAlgebraic_real,ExactKernel.atAlgebraic_real,constantCoefficient_real] at h
  exact (eq_div_iff (contactDistance_pos 2).ne').mpr (by simpa using h)

theorem dt_checked :
    (exactMajorant.dt.atAlgebraic (contactU 2) (contactV 2) (contactT 2)).mulAlgebraic (contactDistance 2) = constantCoefficient (-2) := by
  decide +kernel

theorem dt_real : exactMajorant.dt.real (contactU 2).real (contactV 2).real (contactT 2).real =
    (-2:ℝ)/(contactDistance 2).real := by
  have h := congrArg KernelCoeff.real dt_checked
  rw [KernelCoeff.mulAlgebraic_real,ExactKernel.atAlgebraic_real,constantCoefficient_real] at h
  exact (eq_div_iff (contactDistance_pos 2).ne').mpr (by simpa using h)

end MordellEight.ContactCheck2
