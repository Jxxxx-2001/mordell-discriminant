-- Adapted from the checked Eight.BernsteinSubdivision general semantics.
import N7.Kernel.Bernstein.BernsteinDense
import N7.Kernel.Bernstein.RationalBernstein

namespace N7.Kernel
set_option maxHeartbeats 0

theorem QOps.rescale_length {A : Type} (o : QOps A) (r : ℚ) (p : List A) :
    (o.rescale r p).length=p.length := by
  induction p with
  | nil => rfl
  | cons a p ih => simp [QOps.rescale,ih]

theorem homogeneous_rescale {A : Type} {o : QOps A} {e : A → ℝ} (h : QSound o e)
    (n : ℕ) (r : ℚ) (p : List A) (x y : ℝ) :
    homogeneous e n (o.rescale r p) x y=homogeneous e n p ((r:ℝ)*x) y := by
  induction p generalizing n with
  | nil => rfl
  | cons a p ih =>
    simp only [QOps.rescale,homogeneous,homogeneous_scale h,ih]
    ring

theorem QSound.homLift {A : Type} {o : QOps A} {e : A → ℝ} (h : QSound o e)
    (n : ℕ) (x y : ℝ) : QSound o.lift (fun p => homogeneous e n p x y) :=
  ⟨rfl,fun p q => homogeneous_add h n p q x y,fun r p => homogeneous_scale h n r p x y⟩

/-- Exact midpoint restriction in unnormalized Bernstein coordinates. -/
def QOps.bernLeft {A : Type} (o : QOps A) (p : List A) : List A :=
  o.rescale (1/2) (o.bernstein p)
def QOps.bernRight {A : Type} (o : QOps A) (p : List A) : List A :=
  (o.rescale (1/2) (o.shift 1 p).reverse).reverse

theorem homogeneous_bernLeft {A : Type} {o : QOps A} {e : A → ℝ} (h : QSound o e)
    (n : ℕ) (p : List A) (hp : p.length=n+1) (x y : ℝ) :
    homogeneous e n (o.bernLeft p) x y=homogeneous e n p (x/2) (y+x/2) := by
  rw [QOps.bernLeft,homogeneous_rescale h,QOps.bernstein,
    homogeneous_reverse e n _ (by simpa only [QOps.shift_length,List.length_reverse] using hp),
    homogeneous_shift h n 1 p.reverse (by simpa using hp.le),homogeneous_reverse e n p hp]
  norm_num
  congr 1 <;> ring

theorem homogeneous_bernRight {A : Type} {o : QOps A} {e : A → ℝ} (h : QSound o e)
    (n : ℕ) (p : List A) (hp : p.length=n+1) (x y : ℝ) :
    homogeneous e n (o.bernRight p) x y=homogeneous e n p (x+y/2) (y/2) := by
  rw [QOps.bernRight,homogeneous_reverse e n _
    (by simpa only [QOps.rescale_length,QOps.shift_length,List.length_reverse] using hp),
    homogeneous_rescale h,homogeneous_reverse e n _ (by simpa only [QOps.shift_length] using hp),
    homogeneous_shift h n 1 p hp.le]
  norm_num
  congr 1 <;> ring

theorem bernLeft_identity {A : Type} {o : QOps A} {e : A → ℝ} (h : QSound o e)
    (n : ℕ) (p : List A) (hp : p.length=n+1) (s : ℝ) :
    homogeneous e n (o.bernLeft p) s (1-s)=homogeneous e n p (s/2) (1-s/2) := by
  rw [homogeneous_bernLeft h n p hp]
  congr 1 <;> ring

theorem bernRight_identity {A : Type} {o : QOps A} {e : A → ℝ} (h : QSound o e)
    (n : ℕ) (p : List A) (hp : p.length=n+1) (s : ℝ) :
    homogeneous e n (o.bernRight p) s (1-s)=
      homogeneous e n p ((1+s)/2) (1-(1+s)/2) := by
  rw [homogeneous_bernRight h n p hp]
  congr 1 <;> ring

end N7.Kernel
