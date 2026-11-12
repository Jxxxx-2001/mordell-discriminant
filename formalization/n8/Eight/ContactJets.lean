import Eight.ContactChecks.C0
import Eight.ContactChecks.C1
import Eight.ContactChecks.C2
import Eight.ContactChecks.C3
import Eight.GapAnalytic

namespace MordellEight
open GapAnalytic

noncomputable def contactCenter (j : Fin 4) : Fin 3 → ℝ :=
  ![(contactU j).real,(contactV j).real,(contactT j).real]

theorem distance_contactCenter (j : Fin 4) : distance (contactCenter j)=(contactDistance j).real :=
  (contactDistance_real j).symm

theorem value_at_contact (j : Fin 4) :
    exactMajorant.real (contactU j).real (contactV j).real (contactT j).real=
      Real.log ((contactDistance j).real) := by
  fin_cases j
  · exact ContactCheck0.value_real
  · exact ContactCheck1.value_real
  · exact ContactCheck2.value_real
  · exact ContactCheck3.value_real

theorem gap_at_contact (j : Fin 4) : gap exactMajorant (contactCenter j)=0 := by
  rw [gap,distance_contactCenter]
  change exactMajorant.real (contactU j).real (contactV j).real (contactT j).real-
    Real.log ((contactDistance j).real)=0
  rw [value_at_contact,sub_self]

theorem dv_at_contact (j : Fin 4) :
    exactMajorant.dv.real (contactU j).real (contactV j).real (contactT j).real=
      1/(contactDistance j).real := by
  fin_cases j
  · exact ContactCheck0.dv_real
  · exact ContactCheck1.dv_real
  · exact ContactCheck2.dv_real
  · exact ContactCheck3.dv_real

theorem dt_at_contact (j : Fin 4) :
    exactMajorant.dt.real (contactU j).real (contactV j).real (contactT j).real=
      (-2)/(contactDistance j).real := by
  fin_cases j
  · exact ContactCheck0.dt_real
  · exact ContactCheck1.dt_real
  · exact ContactCheck2.dt_real
  · exact ContactCheck3.dt_real

theorem du_at_outer_contact (j : Fin 4) (hj : j≠0) :
    exactMajorant.du.real (contactU j).real (contactV j).real (contactT j).real=
      1/(contactDistance j).real := by
  fin_cases j
  · exact (hj rfl).elim
  · exact ContactCheck1.du_real
  · exact ContactCheck2.du_real
  · exact ContactCheck3.du_real

theorem gradient_at_outer_contact (j : Fin 4) (hj : j≠0) :
    gradient exactMajorant (contactCenter j)=0 := by
  ext i
  fin_cases i
  · change exactMajorant.du.real (contactU j).real (contactV j).real (contactT j).real-
      1/distance (contactCenter j)=0
    rw [du_at_outer_contact j hj,distance_contactCenter,sub_self]
  · change exactMajorant.dv.real (contactU j).real (contactV j).real (contactT j).real-
      1/distance (contactCenter j)=0
    rw [dv_at_contact,distance_contactCenter,sub_self]
  · change exactMajorant.dt.real (contactU j).real (contactV j).real (contactT j).real-
      (-2)/distance (contactCenter j)=0
    rw [dt_at_contact,distance_contactCenter,sub_self]

end MordellEight
