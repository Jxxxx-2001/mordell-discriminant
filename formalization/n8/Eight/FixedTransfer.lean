import Eight.BernsteinSubdivision

namespace MordellEight.FixedTransfer
set_option maxHeartbeats 0

structure ScaleLaws {A : Type} (o : QOps A) : Prop where
  one : ∀ a, o.scale 1 a = a
  mul : ∀ r s a, o.scale r (o.scale s a) = o.scale (r*s) a

theorem ScaleLaws.lift {A : Type} {o : QOps A} (h : ScaleLaws o) :
    ScaleLaws o.lift := by
  constructor
  · intro a; have he : o.scale 1 = id := funext h.one; simp [QOps.lift,he]
  · intro r s a; simp only [QOps.lift,List.map_map]; congr 1; funext x; exact h.mul r s x

theorem rational_scale : ScaleLaws rationalOps := by
  constructor <;> intros <;> simp [rationalOps,mul_assoc]

structure Map12 {A B : Type} (a : QOps A) (b : QOps B) (f : A → B) : Prop where
  zero : f a.zero = b.zero
  add : ∀ x y, f (a.add x y) = b.add (f x) (f y)
  scale : ∀ r, r=1 ∨ r=2 → ∀ x, f (a.scale r x) = b.scale r (f x)

theorem Map12.listAdd {A B : Type} {a : QOps A} {b : QOps B} {f : A → B}
    (h : Map12 a b f) (p q : List A) :
    (a.listAdd p q).map f = b.listAdd (p.map f) (q.map f) := by
  induction p generalizing q with
  | nil => rfl
  | cons x p ih => cases q <;> simp [QOps.listAdd,h.add,ih]

theorem Map12.lift {A B : Type} {a : QOps A} {b : QOps B} {f : A → B}
    (h : Map12 a b f) : Map12 a.lift b.lift (List.map f) := by
  constructor
  · rfl
  · exact h.listAdd
  · intro r hr p; simp only [QOps.lift,List.map_map]
    congr 1; funext x; exact h.scale r hr x

theorem Map12.shift {A B : Type} {a : QOps A} {b : QOps B} {f : A → B}
    (h : Map12 a b f) (p : List A) :
    (a.shift 1 p).map f = b.shift 1 (p.map f) := by
  induction p with
  | nil => rfl
  | cons x p ih =>
    simp only [QOps.shift,h.listAdd,QOps.mulLinear,List.map_cons,List.map_nil,h.zero]
    simp only [List.map_map,Function.comp_def]
    simp_rw [h.scale 1 (Or.inl rfl)]
    simpa only [List.map_map,Function.comp_def] using
      congrArg (fun q => b.listAdd [f x] (b.listAdd (q.map (b.scale 1)) (b.zero::q))) ih

theorem Map12.rescale {A B : Type} {a : QOps A} {b : QOps B} {f : A → B}
    (h : Map12 a b f) (p : List A) :
    (a.rescale 2 p).map f = b.rescale 2 (p.map f) := by
  induction p with
  | nil => rfl
  | cons x p ih =>
    simp only [QOps.rescale,List.map_cons,List.map_map,Function.comp_def]
    simp_rw [h.scale 2 (Or.inr rfl)]
    simpa only [List.map_map,Function.comp_def] using
      congrArg (fun q => f x :: q.map (b.scale 2)) ih

theorem rescale_get {A : Type} {o : QOps A} (h : ScaleLaws o)
    (r : ℚ) (p : List A) (i : ℕ) (hi : i<p.length) :
    (o.rescale r p)[i]'(by simpa [QOps.rescale_length] using hi) = o.scale (r^i) p[i] := by
  induction p generalizing i with
  | nil => simp at hi
  | cons x p ih =>
    cases i with
    | zero => simp [QOps.rescale,h.one]
    | succ i =>
      simp only [QOps.rescale,List.getElem_cons_succ,List.getElem_map,pow_succ]
      rw [ih i (by simpa using hi),h.mul]
      congr 1
      ring

def numerator {A : Type} (o : QOps A) (right : Bool) (p : List A) : List A :=
  if right then o.rescale 2 (o.shift 1 p)
  else (o.rescale 2 (o.shift 1 p.reverse)).reverse

theorem numerator_length {A : Type} (o : QOps A) (right : Bool) (p : List A) :
    (numerator o right p).length=p.length := by
  cases right <;> simp [numerator,QOps.rescale_length,QOps.shift_length]

theorem Map12.numerator {A B : Type} {a : QOps A} {b : QOps B} {f : A → B}
    (h : Map12 a b f) (right : Bool) (p : List A) :
    (numerator a right p).map f=numerator b right (p.map f) := by
  cases right with
  | false =>
    change ((a.rescale 2 (a.shift 1 p.reverse)).reverse).map f =
      (b.rescale 2 (b.shift 1 (p.map f).reverse)).reverse
    rw [List.map_reverse,h.rescale,h.shift,List.map_reverse]
  | true =>
    change (a.rescale 2 (a.shift 1 p)).map f = b.rescale 2 (b.shift 1 (p.map f))
    rw [h.rescale,h.shift]

end MordellEight.FixedTransfer
