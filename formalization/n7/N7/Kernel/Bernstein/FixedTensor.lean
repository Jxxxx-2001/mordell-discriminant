-- Adapted from the checked Eight.FixedTensor general semantics.
import N7.Kernel.Bernstein.BoxCoordinates
import Mathlib.Data.Rat.Floor

namespace N7.Kernel
namespace FixedTensor
set_option maxHeartbeats 0

abbrev Cube := List (List (List Int))

/-- Euclidean integer division is floor division, including negative numerators. -/
theorem divide_floor (a : Int) (k : ℕ) :
    ⌊(a:ℚ)/(2^k:ℚ)⌋ = a/(2^k:Int) := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using Rat.floor_intCast_div_natCast a (2^k)

theorem decoded_divide (a : Int) (k : ℕ) :
    ((a/(2^k:Int):Int):ℚ)/(2^80:ℚ) =
      RationalCube.roundDownAt 80 ((a:ℚ)/(2^80:ℚ)/(2^k:ℚ)) := by
  unfold RationalCube.roundDownAt
  rw [show (a:ℚ)/(2^80:ℚ)/(2^k:ℚ)*(2^80:ℚ)=(a:ℚ)/(2^k:ℚ) by field_simp]
  rw [divide_floor]

def ops : QOps Int := ⟨0, (·+·), fun _ a => a⟩

def half {A : Type} (o : QOps A) (divide : A → Int → A)
    (right : Bool) (p : List A) : List A :=
  let shifted := if right then o.shift 1 p else (o.shift 1 p.reverse).reverse
  shifted.zipIdx.map fun (a,i) => divide a (2^(if right then p.length-1-i else i))

def rowHalf := half ops (fun a d => a/d)
def planeHalf := half ops.lift (fun row d => row.map (fun a => a/d))
def cubeHalf := half ops.lift.lift (fun plane d => plane.map (List.map (fun a => a/d)))

def step (p : Cube) (axis : Fin 3) (right : Bool) : Cube :=
  match axis with
  | 0 => cubeHalf right p
  | 1 => p.map (planeHalf right)
  | 2 => p.map (List.map (rowHalf right))

def decode (p : Cube) : RationalCube :=
  p.map (List.map (List.map (fun (a : Int) => (a:ℚ)/(2^80:ℚ))))

/-- Every concrete integer subdivision is checked against the proved rational semantics. -/
def stepCheck (p q : Cube) (axis : Fin 3) (right : Bool) : Bool :=
  (((decode p).splitAxis axis right).roundControls 80).check (decode q)

end FixedTensor
end N7.Kernel
