-- Adapted from the checked Eight.IntegerCube general semantics.
import N7.Kernel.Bernstein.FixedDecode

namespace N7.Kernel.IntegerCube
open FixedTensor FixedTransfer
set_option maxHeartbeats 0

def raw (p : Cube) : RationalCube := p.map (List.map (List.map (fun z : Int => (z : ℚ))))
def add : Cube → Cube → Cube := integerOps.lift.lift.lift.add
def scale (n : Int) (p : Cube) : Cube := p.map (List.map (List.map (n*·)))
def nonneg (p : Cube) : Bool := p.all (fun row => row.all (fun col => col.all (fun z => decide (0≤z))))

theorem raw_map : Map12 integerOps rationalOps (fun z : Int => (z : ℚ)) := by
  constructor
  · rfl
  · intros; exact Int.cast_add _ _
  · intro r hr z
    rcases hr with rfl|rfl <;> simp [integerOps,rationalOps]

theorem raw_add (p q : Cube) : raw (add p q)=RationalCube.ops.add (raw p) (raw q) :=
  raw_map.lift.lift.lift.add p q

theorem raw_scale (n : Int) (p : Cube) :
    raw (scale n p)=RationalCube.ops.scale (n:ℚ) (raw p) := by
  simp [raw,scale,RationalCube.ops,QOps.lift,rationalOps,List.map_map,Function.comp_def]

theorem raw_decode (p : Cube) :
    raw p=RationalCube.ops.scale (2^80) (decode p) := by
  have hs (z : Int) : (2^80:ℚ)*((z:ℚ)/2^80)=(z:ℚ) := by field_simp
  simp [raw,decode,RationalCube.ops,QOps.lift,rationalOps,List.map_map,Function.comp_def,hs]

theorem nonneg_sound (p : Cube) (h : nonneg p=true) : (raw p).nonnegCheck=true := by
  simp only [nonneg,List.all_eq_true] at h
  simp only [raw,RationalCube.nonnegCheck,List.all_map,List.all_eq_true,Function.comp_def]
  intro row hr col hc z hz
  exact decide_eq_true (by exact_mod_cast (of_decide_eq_true (h row hr col hc z hz) : (0:Int)≤z))

end N7.Kernel.IntegerCube
