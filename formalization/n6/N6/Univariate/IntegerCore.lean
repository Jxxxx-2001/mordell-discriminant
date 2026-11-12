import Init

/- Fixed-denominator interval arithmetic. No rational normalization is performed
   inside a leaf. The denominator is part of the data, checked by the semantics. -/
namespace N6.IntegerCover

structure Bounds where
  lo : Int
  hi : Int
  den : Nat
  deriving DecidableEq, Repr

def Bounds.point (a : Int) : Bounds := ⟨a, a, 1⟩
def Bounds.addConst (a : Int) (b : Bounds) : Bounds :=
  ⟨a*b.den + b.lo, a*b.den + b.hi, b.den⟩
def Bounds.mul (a b : Bounds) : Bounds :=
  ⟨min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi)),
   max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi)),
   a.den*b.den⟩
def Bounds.left (b : Bounds) : Bounds := ⟨2*b.lo, b.lo+b.hi, 2*b.den⟩
def Bounds.right (b : Bounds) : Bounds := ⟨b.lo+b.hi, 2*b.hi, 2*b.den⟩

def range : List Int → Bounds → Bounds
  | [], _ => Bounds.point 0
  | a :: p, b => (b.mul (range p b)).addConst a

inductive Cover where
  | leaf : Cover
  | split : Cover → Cover → Cover
  deriving Repr

def Cover.check (p v : List Int) (vden limit : Nat) (b : Bounds) : Cover → Bool
  | .leaf =>
      decide (0 < (range p b).lo ∨ (range p b).hi < 0 ∨
        (-(limit*vden*(range v b).den : Int) < (range v b).lo ∧
         (range v b).hi < (limit*vden*(range v b).den : Int)))
  | .split a c => a.check p v vden limit b.left && c.check p v vden limit b.right

end N6.IntegerCover
