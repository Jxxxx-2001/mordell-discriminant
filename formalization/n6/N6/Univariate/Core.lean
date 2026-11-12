import Init.Data.Rat

/- Computable part of the five-point ValueCover method, specialized to Horner lists.
   Keeping this file independent of Mathlib makes numeric certificates inexpensive. -/
namespace N6.Univariate

structure Bounds where
  lo : Rat
  hi : Rat
  deriving DecidableEq, Repr

def Bounds.point (q : Rat) : Bounds := ⟨q, q⟩
def Bounds.add (a b : Bounds) : Bounds := ⟨a.lo + b.lo, a.hi + b.hi⟩
def Bounds.mul (a b : Bounds) : Bounds :=
  ⟨min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi)),
   max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))⟩
def Bounds.left (b : Bounds) (t : Rat) : Bounds := ⟨b.lo, min b.hi t⟩
def Bounds.right (b : Bounds) (t : Rat) : Bounds := ⟨max b.lo t, b.hi⟩

def range : List Rat → Bounds → Bounds
  | [], _ => Bounds.point 0
  | a :: p, b => (Bounds.point a).add (b.mul (range p b))

inductive Cover where
  | leaf : Cover
  | split : Rat → Cover → Cover → Cover
  deriving Repr

def Cover.check (p v : List Rat) (limit : Rat) (b : Bounds) : Cover → Bool
  | .leaf => decide (0 < (range p b).lo ∨ (range p b).hi < 0 ∨
      (-limit < (range v b).lo ∧ (range v b).hi < limit))
  | .split t a c => a.check p v limit (b.left t) && c.check p v limit (b.right t)

end N6.Univariate
