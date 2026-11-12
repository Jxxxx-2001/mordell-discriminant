-- Adapted from the checked Eight.FixedDecode general semantics.
import N7.Kernel.Bernstein.FixedHalf
import N7.Kernel.Bernstein.FixedTensor

namespace N7.Kernel.FixedTransfer
set_option maxHeartbeats 0

def integerOps : QOps Int := ⟨0,(·+·),fun r a => r.num*a⟩
def scalar (a : Int) : ℚ := (a:ℚ)/(2^80:ℚ)
def divScalar (a : Int) (n : ℕ) : Int := a/(2^n:Int)
def roundScalar := RationalCube.roundDownAt 80

theorem scalar_map : Map12 integerOps rationalOps scalar := by
  constructor
  · simp [scalar,integerOps,rationalOps]
  · intro x y; simp [scalar,integerOps,rationalOps,add_div]
  · intro r hr x
    rcases hr with rfl|rfl <;> simp [scalar,integerOps,rationalOps,mul_div_assoc]

theorem scalar_divide (a : Int) (n : ℕ) :
    scalar (divScalar a n)=roundScalar (rationalOps.scale (1/(2^n)) (scalar a)) := by
  simpa [scalar,divScalar,roundScalar,rationalOps,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]
    using FixedTensor.decoded_divide a n

theorem map_divide {A B : Type} {b : QOps B}
    {f : A → B} {divide : A → ℕ → A} {round : B → B}
    (h : ∀ x n, f (divide x n)=round (b.scale (1/(2^n)) (f x)))
    (xs : List A) (n : ℕ) :
    (xs.map (fun a => divide a n)).map f =
      (xs.map f |> List.map (b.scale (1/(2^n))) |> List.map round) := by
  simp only [List.map_map,Function.comp_def,h]

def divRow (row : List Int) (n : ℕ) := row.map (fun a => divScalar a n)
def divPlane (row : List (List Int)) (n : ℕ) := row.map (fun a => divRow a n)
def scalarRow := List.map scalar
def scalarPlane := List.map scalarRow
def roundRow := List.map roundScalar
def roundPlane := List.map roundRow

theorem row_divide (xs : List Int) (n : ℕ) :
    scalarRow (divRow xs n) =
      roundRow (rationalOps.lift.scale (1/(2^n)) (scalarRow xs)) := by
  exact map_divide scalar_divide xs n

theorem plane_divide (xs : List (List Int)) (n : ℕ) :
    scalarPlane (divPlane xs n) =
      roundPlane (rationalOps.lift.lift.scale (1/(2^n)) (scalarPlane xs)) := by
  exact map_divide row_divide xs n

def rowHalf (right : Bool) := halfInt integerOps divScalar right
def planeHalf (right : Bool) := halfInt integerOps.lift divRow right
def cubeHalf (right : Bool) := halfInt integerOps.lift.lift divPlane right

theorem row_half (p : List Int) (right : Bool) :
    scalarRow (rowHalf right p) =
      roundRow (if right then rationalOps.bernRight (scalarRow p) else rationalOps.bernLeft (scalarRow p)) :=
  half_transfer scalar_map rational_scale divScalar roundScalar scalar_divide right p

theorem plane_half (p : List (List Int)) (right : Bool) :
    scalarPlane (planeHalf right p) =
      roundPlane (if right then rationalOps.lift.bernRight (scalarPlane p) else rationalOps.lift.bernLeft (scalarPlane p)) :=
  half_transfer scalar_map.lift rational_scale.lift divRow roundRow row_divide right p

theorem cube_half (p : FixedTensor.Cube) (right : Bool) :
    (cubeHalf right p).map scalarPlane =
      (if right then rationalOps.lift.lift.bernRight (p.map scalarPlane) else rationalOps.lift.lift.bernLeft (p.map scalarPlane)).map roundPlane :=
  half_transfer scalar_map.lift.lift rational_scale.lift.lift divPlane roundPlane plane_divide right p

def step (p : FixedTensor.Cube) (axis : Fin 3) (right : Bool) : FixedTensor.Cube :=
  match axis with
  | 0 => cubeHalf right p
  | 1 => p.map (planeHalf right)
  | 2 => p.map (List.map (rowHalf right))

theorem step_decode (p : FixedTensor.Cube) (axis : Fin 3) (right : Bool) :
    FixedTensor.decode (step p axis right) =
      ((FixedTensor.decode p).splitAxis axis right).roundControls 80 := by
  fin_cases axis
  · exact cube_half p right
  · simp only [step,FixedTensor.decode,List.map_map,Function.comp_def]
    change p.map (fun row => scalarPlane (planeHalf right row)) = _
    simp_rw [plane_half]
    cases right <;> simp [RationalCube.splitAxis,RationalCube.splitV,RationalCube.splitT,
      RationalCube.roundControls,scalarRow,scalarPlane,roundRow,roundPlane,scalar,roundScalar,
      List.map_map,Function.comp_def] <;> intros <;> rfl
  · simp only [step,FixedTensor.decode,List.map_map,Function.comp_def]
    change p.map (fun row => row.map (fun col => scalarRow (rowHalf right col))) = _
    simp_rw [row_half]
    cases right <;> simp [RationalCube.splitAxis,RationalCube.splitV,RationalCube.splitT,
      RationalCube.roundControls,scalarRow,scalarPlane,roundRow,roundPlane,scalar,roundScalar,
      List.map_map,Function.comp_def] <;> intros <;> rfl

end N7.Kernel.FixedTransfer
