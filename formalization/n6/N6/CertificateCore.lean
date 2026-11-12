import Init.Data.Int.Bitwise.Lemmas

universe u

namespace N6.SparseCheck
open N6.SparseCheck

structure Mon where
  t : Nat
  e : Nat
  k : Nat
  c : Nat
  b : Nat
  deriving DecidableEq, Repr

abbrev Term := Mon × Int

abbrev Poly := List Term

def Mon.plus (u v : Mon) : Mon :=
  ⟨u.t + v.t, u.e + v.e, u.k + v.k, u.c + v.c, u.b + v.b⟩

-- Only an ordering hint. Merging coefficients requires full exponent equality.

def Mon.key (m : Mon) : Nat :=
  (((m.t * 64 + m.e) * 64 + m.k) * 64 + m.c) * 64 + m.b

def mulTerm (a b : Term) : Term := (a.1.plus b.1, a.2 * b.2)

def mergeAux : Nat → Poly → Poly → Poly
  | 0, p, q => p ++ q
  | _ + 1, [], q => q
  | _ + 1, a :: p, [] => a :: p
  | n + 1, a :: p, b :: q =>
    if a.1 = b.1 then (a.1, a.2 + b.2) :: mergeAux n p q
    else if a.1.key < b.1.key then a :: mergeAux n p (b :: q)
    else b :: mergeAux n (a :: p) q

def merge (p q : Poly) : Poly := mergeAux (p.length + q.length) p q

def mul (p q : Poly) : Poly :=
  match p with
  | [] => []
  | a :: tail => merge (q.map (mulTerm a)) (mul tail q)

def zero : Poly → Bool
  | [] => true
  | a :: p => decide (a.2 = 0) && zero p

def smokeP : Poly := [(⟨0,0,0,0,0⟩, 1), (⟨0,1,0,0,0⟩, 2)]

def smokeN : Poly := [(⟨0,0,0,0,0⟩, -1), (⟨0,1,0,0,0⟩, -2)]

end N6.SparseCheck

namespace N6.KroneckerCheck
open N6.SparseCheck

structure Rad where
  k : Nat
  e : Nat
  c : Nat
  b : Nat

def code (r : Rad) (m : Mon) : Nat :=
  m.k + r.k * (m.e + r.e * (m.c + r.c * (m.b + r.b * m.t)))

def decode (r : Rad) (n : Nat) : Mon :=
  ⟨n/r.k/r.e/r.c/r.b, (n/r.k)%r.e, n%r.k, (n/r.k/r.e)%r.c, (n/r.k/r.e/r.c)%r.b⟩

abbrev Fits (r : Rad) (m : Mon) := m.k < r.k ∧ m.e < r.e ∧ m.c < r.c ∧ m.b < r.b

def mass : Poly → Nat
  | [] => 0
  | a::p => a.2.natAbs + mass p

def place (bits key : Nat) : Int := ((1 : Nat) <<< (bits * key) : Nat)

def pack (r : Rad) (bits : Nat) : Poly → Int
  | [] => 0
  | a::p => a.2 * place bits (code r a.1) + pack r bits p

abbrev Products := List (Poly × Poly)

/-- A proof-only collection. Ground checks operate on the separate factors. -/

def raw : Products → Poly
  | [] => []
  | z::rest => (z.1.flatMap (fun a => z.2.map (mulTerm a))) ++ raw rest

def pairs {A : Type u} [OfNat A 0] [Add A] [Mul A] (w : Poly → A) : Products → A
  | [] => 0
  | z::rest => w z.1 * w z.2 + pairs w rest

def upper (f : Mon → Nat) : Poly → Nat
  | [] => 0
  | a::p => max (f a.1) (upper f p)

abbrev Room (r : Rad) (p q : Poly) :=
  upper Mon.k p + upper Mon.k q < r.k ∧ upper Mon.e p + upper Mon.e q < r.e ∧
  upper Mon.c p + upper Mon.c q < r.c ∧ upper Mon.b p + upper Mon.b q < r.b

def roomCheck (r : Rad) (ps : Products) := ps.all (fun z => decide (Room r z.1 z.2))

end N6.KroneckerCheck

namespace N6.KroneckerFastPack
open N6.SparseCheck N6.KroneckerCheck

abbrev Digit := Nat × Int

/-- Offsets here are in units of coefficient slots, not bits. -/

def shifted (bits offset : Nat) (v : Int) : Int := v <<< (bits * offset : Nat)

def weighted (bits : Nat) : List Digit → Int
  | [] => 0
  | a::p => a.2 * place bits a.1 + weighted bits p

def lower (h : Nat) (p : List Digit) : List Digit := p.filter (fun a => decide (a.1 < h))

def upperDigits (h : Nat) (p : List Digit) : List Digit :=
  (p.filter (fun a => decide (h ≤ a.1))).map (fun a => (a.1 - h, a.2))

def aux (bits : Nat) : Nat → List Digit → Int
  | 0, p => weighted bits p
  | _+1, [] => 0
  | _+1, [a] => shifted bits a.1 a.2
  | n+1, a::b::p =>
    let h := 2^n
    aux bits n (lower h (a::b::p)) +
      shifted bits h (aux bits n (upperDigits h (a::b::p)))

def digits (r : Rad) (p : Poly) : List Digit := p.map (fun a => (code r a.1, a.2))

def fastPack (r : Rad) (bits depth : Nat) (p : Poly) : Int := aux bits depth (digits r p)

end N6.KroneckerFastPack

namespace N6.KroneckerSplit
open N6.SparseCheck N6.KroneckerCheck

def eraseB (m : Mon) : Mon := { m with b := 0 }

def slice (i : Nat) : Poly → Poly
  | [] => []
  | a::p => if a.1.b = i then (eraseB a.1,a.2)::slice i p else slice i p

/-- Sum only the coefficient products with B exponents adding to k. -/

def diagonal (p q : Poly) (k : Nat) : Nat → Products
  | 0 => []
  | i+1 => (slice i p, slice (k-i) q) :: diagonal p q k i

def coefficientPairs (k : Nat) : Products → Products
  | [] => []
  | z::ps => diagonal z.1 z.2 k (k+1) ++ coefficientPairs k ps

def degreeBound : Products → Nat
  | [] => 0
  | z::ps => max (upper Mon.b z.1 + upper Mon.b z.2) (degreeBound ps)

end N6.KroneckerSplit

namespace N6.KroneckerSplitBC
open N6.SparseCheck N6.KroneckerCheck

def swapMon (m : Mon) : Mon := ⟨m.t, m.e, m.k, m.b, m.c⟩

def swapPoly (p : Poly) : Poly := p.map (fun a => (swapMon a.1, a.2))

def swapProducts (ps : Products) : Products :=
  ps.map (fun a => (swapPoly a.1, swapPoly a.2))

def swapPoint {R : Type u} (x : Fin 5 → R) : Fin 5 → R := fun i =>
  if i.val = 3 then x 4 else if i.val = 4 then x 3 else x i

end N6.KroneckerSplitBC
