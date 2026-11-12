import Eight.IntegerCube

namespace MordellEight.IntegerBasis
open FixedTensor IntegerCube
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Four integer tensors shared by every tangent leaf. -/
def controls (tag : Fin 4) : Cube :=
  (List.range 13).map fun i => (List.range 13).map fun j => (List.range 7).map fun k =>
    let w : Int := Nat.choose 12 i * Nat.choose 12 j * Nat.choose 6 k
    match tag with
    | 0 => w
    | 1 => w*i/12
    | 2 => w*j/12
    | 3 => w*k/6

theorem one_checked : (raw (controls 0)).check BernsteinBasis.One.controls=true := by decide +kernel
theorem u_checked : (raw (controls 1)).check BernsteinBasis.U.controls=true := by decide +kernel
theorem v_checked : (raw (controls 2)).check BernsteinBasis.V.controls=true := by decide +kernel
theorem t_checked : (raw (controls 3)).check BernsteinBasis.T.controls=true := by decide +kernel

theorem one : raw (controls 0)=BernsteinBasis.One.controls := RationalCube.check_sound one_checked
theorem u : raw (controls 1)=BernsteinBasis.U.controls := RationalCube.check_sound u_checked
theorem v : raw (controls 2)=BernsteinBasis.V.controls := RationalCube.check_sound v_checked
theorem t : raw (controls 3)=BernsteinBasis.T.controls := RationalCube.check_sound t_checked

end MordellEight.IntegerBasis
