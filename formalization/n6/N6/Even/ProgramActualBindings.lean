import N6.Even.ProgramActualGround
import N6.Even.ProgramBridge
import N6.ResultantMinors.Bindings

set_option autoImplicit false
namespace N6.Even.ProgramData
open N6.SparseCheck

theorem value_evenPart {R : Type*} [CommRing R] (c e : R) (p : Poly) :
    value (N6.ResultantMinors.point 0 c 0 e 0) (evenPart p) =
      value (N6.ResultantMinors.point 0 c 0 e 0) p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    rcases a with ⟨m,z⟩
    by_cases hb : m.b=0 <;> by_cases hd : m.k=0 <;>
      simp [evenPart,hb,hd,value,monVal,N6.ResultantMinors.point_eval0,
        N6.ResultantMinors.point_eval1,N6.ResultantMinors.point_eval2,
        N6.ResultantMinors.point_eval3,N6.ResultantMinors.point_eval4,ih]

theorem actualD_coefficient (c e : ℂ) : actualD c e =
    value (N6.ResultantMinors.point 0 c 0 e 0) (N6.ResultantMinors.extractY 6 N6.ResultantMinors.D063) := by
  rw [←value_evenPart c e,actualD_even_projection]
  simp [actualD,actualDEvenData,actualDEvenDataPart0,value_append,value,monVal,N6.ResultantMinors.point_eval0,N6.ResultantMinors.point_eval1,N6.ResultantMinors.point_eval2,N6.ResultantMinors.point_eval3,N6.ResultantMinors.point_eval4] <;> ring

theorem actualR4_coefficient (c e : ℂ) : actualR4 c e =
    value (N6.ResultantMinors.point 0 c 0 e 0) (N6.ResultantMinors.extractY 4 N6.ResultantMinors.D063) := by
  rw [←value_evenPart c e,actualR4_even_projection]
  simp [actualR4,actualR4EvenData,actualR4EvenDataPart0,value_append,value,monVal,N6.ResultantMinors.point_eval0,N6.ResultantMinors.point_eval1,N6.ResultantMinors.point_eval2,N6.ResultantMinors.point_eval3,N6.ResultantMinors.point_eval4] <;> ring

theorem actualR02_coefficient (c e : ℂ) : actualR02 c e =
    value (N6.ResultantMinors.point 0 c 0 e 0) (N6.ResultantMinors.extractY 2 N6.ResultantMinors.D063) := by
  rw [←value_evenPart c e,actualR02_even_projection]
  simp [actualR02,actualR02EvenData,actualR02EvenDataPart0,value_append,value,monVal,N6.ResultantMinors.point_eval0,N6.ResultantMinors.point_eval1,N6.ResultantMinors.point_eval2,N6.ResultantMinors.point_eval3,N6.ResultantMinors.point_eval4] <;> ring

#print axioms actualR02_coefficient
end N6.Even.ProgramData
