-- Adapted from the checked Eight.FixedHalf general semantics.
import N7.Kernel.Bernstein.FixedTransfer

namespace N7.Kernel.FixedTransfer
set_option maxHeartbeats 0

/-- Reverse rescaling clears one common denominator for the whole row. -/
theorem reciprocal_rescale {A : Type} {o : QOps A} (h : ScaleLaws o)
    (n : ℕ) (p : List A) (hp : p.length=n+1) :
    (o.rescale 2 p).reverse.map (o.scale (1/(2^n))) = o.rescale (1/2) p.reverse := by
  apply List.ext_getElem
  · simp [QOps.rescale_length]
  · intro i hi hj
    have hi' : i < n+1 := by simpa [QOps.rescale_length,hp] using hi
    simp only [List.getElem_map,List.getElem_reverse,QOps.rescale_length]
    rw [rescale_get h 2 p (p.length-1-i) (by omega),
      rescale_get h (1/2) p.reverse i (by simpa only [List.length_reverse] using (show i<p.length by omega)),
      List.getElem_reverse,h.mul]
    congr 1
    have he : (2:ℚ)^n=2^(n-i)*2^i := by
      rw [←pow_add]; congr 1; omega
    rw [show p.length-1-i=n-i by omega,he]
    rw [one_div_pow]
    field_simp

theorem numerator_divided {A : Type} {o : QOps A} (h : ScaleLaws o)
    (n : ℕ) (p : List A) (hp : p.length=n+1) (right : Bool) :
    (numerator o right p).map (o.scale (1/(2^n))) =
      if right then o.bernRight p else o.bernLeft p := by
  have hs : (o.shift 1 p).length=n+1 := by simpa [QOps.shift_length] using hp
  have hs' : (o.shift 1 p.reverse).length=n+1 := by simpa [QOps.shift_length] using hp
  cases right with
  | false => exact reciprocal_rescale h n (o.shift 1 p.reverse) hs'
  | true =>
    have hh := congrArg List.reverse (reciprocal_rescale h n (o.shift 1 p) hs)
    simpa [numerator,QOps.bernRight,←List.map_reverse] using hh

def halfInt {A : Type} (o : QOps A) (divide : A → ℕ → A)
    (right : Bool) (p : List A) : List A :=
  (numerator o right p).map (fun a => divide a (p.length-1))

theorem half_transfer {A B : Type} {a : QOps A} {b : QOps B} {f : A → B}
    (h : Map12 a b f) (laws : ScaleLaws b) (divide : A → ℕ → A) (round : B → B)
    (hd : ∀ x n, f (divide x n)=round (b.scale (1/(2^n)) (f x)))
    (right : Bool) (p : List A) :
    (halfInt a divide right p).map f =
      (if right then b.bernRight (p.map f) else b.bernLeft (p.map f)).map round := by
  cases p with
  | nil => cases right <;> rfl
  | cons x p =>
    have hp : (x::p).length=((x::p).length-1)+1 := by simp
    calc
      _ = ((numerator a right (x::p)).map f).map
          (fun z => round (b.scale (1/(2^((x::p).length-1))) z)) := by
        simp only [halfInt,List.map_map,Function.comp_def,hd]
      _ = (numerator b right ((x::p).map f)).map
          (fun z => round (b.scale (1/(2^((x::p).length-1))) z)) := by
        rw [h.numerator]
      _ = ((numerator b right ((x::p).map f)).map
          (b.scale (1/(2^((x::p).length-1))))).map round := by rw [List.map_map]; rfl
      _ = _ := by rw [numerator_divided laws _ _ (by simpa using hp)]

end N7.Kernel.FixedTransfer
