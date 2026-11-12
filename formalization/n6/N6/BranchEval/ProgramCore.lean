import N6.SparseProductReduceCore

namespace N6.BranchEval.Program
open N6.SparseCheck N6.KroneckerCheck

structure NF where
  num : Poly
  den : Int
  deriving DecidableEq

inductive Op where
  | input (slot : Nat)
  | lit (z d : Int)
  | add (a b : Nat)
  | mul (a b : Nat)
  deriving DecidableEq

structure Row where
  out : NF
  op : Op
  scale : Int
  quot : Poly

/-- Tables may use chunked arrays or generated total lookups; only the declared
    prefix is used. This keeps large literal tables outside the generic proof. -/
structure Table where
  size : Nat
  inputSize : Nat
  row : Nat → Row
  input : Nat → NF
  factor : Poly

def coefScale (c : Int) (p : Poly) : Poly := p.map (fun a => (a.1,c*a.2))
def unitPoly : Poly := [(⟨0,0,0,0,0⟩,1)]
def litNF (z d : Int) : NF := ⟨coefScale z unitPoly,d⟩

/-- Archived input certificate is s*(do*(ns/ds)-no)=f*q.
    Multiply the complete identity, including the right side, by ds. -/
def basePairs (f : Poly) (r : Row) (a : NF) : Products :=
  [(coefScale (r.scale*r.out.den) a.num,unitPoly),
   (coefScale (-(r.scale*a.den)) r.out.num,unitPoly),
   (coefScale (-a.den) f,r.quot)]

def addPairs (f : Poly) (r : Row) (a b : NF) : Products :=
  [(coefScale (r.scale*r.out.den*b.den) a.num,unitPoly),
   (coefScale (r.scale*r.out.den*a.den) b.num,unitPoly),
   (coefScale (-(r.scale*a.den*b.den)) r.out.num,unitPoly),(coefScale (-1) f,r.quot)]

def mulPairs (f : Poly) (r : Row) (a b : NF) : Products :=
  [(coefScale (r.scale*r.out.den) a.num,b.num),
   (coefScale (-(r.scale*a.den*b.den)) r.out.num,unitPoly),(coefScale (-1) f,r.quot)]

def parts (P : Table) (r : Row) : Products :=
  match r.op with
  | .input j => basePairs P.factor r (P.input j)
  | .lit z d => basePairs P.factor r (litNF z d)
  | .add a b => addPairs P.factor r (P.row a).out (P.row b).out
  | .mul a b => mulPairs P.factor r (P.row a).out (P.row b).out

def opOK (P : Table) (i : Nat) : Op → Bool
  | .input j => decide (j < P.inputSize ∧ (P.input j).den ≠ 0)
  | .lit _ d => decide (d ≠ 0)
  | .add a b | .mul a b => decide (a < i ∧ b < i ∧ (P.row a).out.den ≠ 0 ∧ (P.row b).out.den ≠ 0)

def checkAt (P : Table) (i : Nat) : Bool :=
  decide ((P.row i).scale ≠ 0 ∧ (P.row i).out.den ≠ 0) &&
    (opOK P i (P.row i).op && zero (N6.SparseProductReduce.reduceProducts (parts P (P.row i))))

def checkBlock (P : Table) (start count : Nat) : Bool :=
  (List.range count).all (fun j => checkAt P (start+j))

/-- A reference stops expansion at that shared, already interpreted node.
    swap records the source operand order when the archived operation sorted its indices. -/
inductive SourceExpr where
  | ref (node : Nat)
  | input (slot : Nat)
  | lit (z d : Int)
  | add (swap : Bool) (a b : SourceExpr)
  | mul (swap : Bool) (a b : SourceExpr)

def matchesExpr (P : Table) : SourceExpr → Nat → Bool
  | .ref j,i => decide (i = j ∧ i < P.size)
  | .input j,i => decide (i < P.size ∧ (P.row i).op = .input j)
  | .lit z d,i => decide (i < P.size ∧ (P.row i).op = .lit z d)
  | .add rev l r,i =>
    match (P.row i).op with
    | .add a b => decide (i < P.size) &&
        (matchesExpr P l (if rev then b else a) && matchesExpr P r (if rev then a else b))
    | _ => false
  | .mul rev l r,i =>
    match (P.row i).op with
    | .mul a b => decide (i < P.size) &&
        (matchesExpr P l (if rev then b else a) && matchesExpr P r (if rev then a else b))
    | _ => false

end N6.BranchEval.Program
