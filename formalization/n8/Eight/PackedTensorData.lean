import Eight.FixedTensor

namespace MordellEight.PackedTensorData

/-- Thirteen planes of 91 unsigned fixed-width cells. The signed coefficient
is the selected cell minus `offset`. The representation carries no correctness
assumption: existing tensor checks must verify every decoded coefficient. -/
def decode (bits : ℕ) (offset : Int) (planes : List Nat) : FixedTensor.Cube :=
  (List.range 13).map fun i => (List.range 13).map fun j => (List.range 7).map fun k =>
    Int.ofNat (((planes[i]?).getD 0 >>> ((j*7+k)*bits)) &&& ((1 <<< bits)-1)) - offset

end MordellEight.PackedTensorData
