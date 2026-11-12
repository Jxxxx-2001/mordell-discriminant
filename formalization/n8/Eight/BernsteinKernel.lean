import Eight.HornerBounds

namespace MordellEight
open Checks
set_option maxHeartbeats 0

/-- Homogeneous evaluation at a fixed total degree. -/
noncomputable def homogeneous {A : Type} (e : A → ℝ) : ℕ → List A → ℝ → ℝ → ℝ
  | _, [], _, _ => 0
  | n, a::p, x, y => e a*y^n+x*homogeneous e (n-1) p x y

theorem homogeneous_add {A : Type} {o : QOps A} {e : A → ℝ} (h : QSound o e)
    (n : ℕ) (p q : List A) (x y : ℝ) :
    homogeneous e n (o.listAdd p q) x y = homogeneous e n p x y+homogeneous e n q x y := by
  induction p generalizing n q with
  | nil => simp [QOps.listAdd,homogeneous]
  | cons a p ih =>
    cases q with
    | nil => simp [QOps.listAdd,homogeneous]
    | cons b q => simp only [QOps.listAdd,homogeneous,h.add,ih]; ring

theorem homogeneous_scale {A : Type} {o : QOps A} {e : A → ℝ} (h : QSound o e)
    (n : ℕ) (r : ℚ) (p : List A) (x y : ℝ) :
    homogeneous e n (p.map (o.scale r)) x y = (r : ℝ)*homogeneous e n p x y := by
  induction p generalizing n with
  | nil => simp [homogeneous]
  | cons a p ih => simp only [List.map_cons,homogeneous,h.scale,ih]; ring

theorem QOps.listAdd_length {A : Type} (o : QOps A) (p q : List A) :
    (o.listAdd p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp [QOps.listAdd]
  | cons a p ih => cases q <;> simp [QOps.listAdd,ih,Nat.succ_max_succ]

theorem QOps.shift_length {A : Type} (o : QOps A) (r : ℚ) (p : List A) :
    (o.shift r p).length = p.length := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [QOps.shift,QOps.listAdd_length,QOps.mulLinear,List.length_cons,
      List.length_nil,List.length_map,ih]
    omega

theorem homogeneous_raise {A : Type} (e : A → ℝ) (n : ℕ) (p : List A)
    (hp : p.length ≤ n+1) (x y : ℝ) :
    homogeneous e (n+1) p x y = y*homogeneous e n p x y := by
  induction n generalizing p with
  | zero =>
    cases p with
    | nil => simp [homogeneous]
    | cons a p =>
      have he : p=[] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hp; omega)
      subst p
      simp [homogeneous]
      ring
  | succ n ih =>
    cases p with
    | nil => simp [homogeneous]
    | cons a p =>
      have hl : p.length ≤ n+1 := by simp only [List.length_cons] at hp; omega
      simp only [homogeneous,Nat.add_sub_cancel,ih p hl]
      rw [pow_succ]
      ring

theorem homogeneous_mulLinear {A : Type} {o : QOps A} {e : A → ℝ} (h : QSound o e)
    (n : ℕ) (r : ℚ) (p : List A) (hp : p.length ≤ n+1) (x y : ℝ) :
    homogeneous e (n+1) (o.mulLinear r p) x y = (x+(r : ℝ)*y)*homogeneous e n p x y := by
  rw [QOps.mulLinear,homogeneous_add h,homogeneous_scale h,homogeneous_raise e n p hp]
  simp only [homogeneous,h.zero,Nat.add_sub_cancel,zero_mul,zero_add]
  ring

theorem homogeneous_shift {A : Type} {o : QOps A} {e : A → ℝ} (h : QSound o e)
    (n : ℕ) (r : ℚ) (p : List A) (hp : p.length ≤ n+1) (x y : ℝ) :
    homogeneous e n (o.shift r p) x y = homogeneous e n p (x+(r : ℝ)*y) y := by
  induction n generalizing p with
  | zero =>
    cases p with
    | nil => rfl
    | cons a p =>
      have he : p=[] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hp; omega)
      subst p
      simp [QOps.shift,QOps.mulLinear,QOps.listAdd,homogeneous,h.add,h.zero]
  | succ n ih =>
    cases p with
    | nil => rfl
    | cons a p =>
      have hl : p.length ≤ n+1 := by simp only [List.length_cons] at hp; omega
      rw [QOps.shift,homogeneous_add h,homogeneous_mulLinear h n r _
        (by simpa only [QOps.shift_length] using hl),ih p hl]
      simp [homogeneous]

theorem homogeneous_append_last {A : Type} (e : A → ℝ) (n : ℕ) (p : List A) (a : A)
    (hp : p.length=n) (x y : ℝ) :
    homogeneous e n (p++[a]) x y = y*homogeneous e (n-1) p x y+e a*x^n := by
  induction n generalizing p with
  | zero => have he := List.length_eq_zero_iff.mp hp; subst p; simp [homogeneous]
  | succ n ih =>
    cases p with
    | nil => simp at hp
    | cons b p =>
      have hl : p.length=n := by simpa using hp
      simp only [List.cons_append,homogeneous,Nat.add_sub_cancel,ih p hl,pow_succ]
      ring

theorem homogeneous_reverse {A : Type} (e : A → ℝ) (n : ℕ) (p : List A)
    (hp : p.length=n+1) (x y : ℝ) :
    homogeneous e n p.reverse x y = homogeneous e n p y x := by
  induction n generalizing p with
  | zero =>
    cases p with
    | nil => simp at hp
    | cons a p =>
      have he : p=[] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hp; omega)
      subst p
      simp [homogeneous]
  | succ n ih =>
    cases p with
    | nil => simp at hp
    | cons a p =>
      have hl : p.length=n+1 := by simpa using hp
      rw [List.reverse_cons,homogeneous_append_last e (n+1) p.reverse a (by simpa using hl)]
      simp only [Nat.add_sub_cancel]
      rw [ih p hl]
      simp [homogeneous]
      ring

theorem homogeneous_one {A : Type} (e : A → ℝ) (n : ℕ) (p : List A) (x : ℝ) :
    homogeneous e n p x 1 = horner e p x := by
  induction p generalizing n with
  | nil => rfl
  | cons a p ih => simp [homogeneous,horner,ih]

/-- Unnormalized Bernstein coordinates, obtained by two reversals and a translation.
These coordinates absorb the positive binomial factors. -/
def QOps.bernstein {A : Type} (o : QOps A) (p : List A) : List A :=
  (o.shift 1 p.reverse).reverse

theorem bernstein_identity {A : Type} {o : QOps A} {e : A → ℝ} (h : QSound o e)
    (n : ℕ) (p : List A) (hp : p.length=n+1) (x : ℝ) :
    homogeneous e n (o.bernstein p) x (1-x) = horner e p x := by
  rw [QOps.bernstein,homogeneous_reverse e n _ (by simpa only [QOps.shift_length,List.length_reverse] using hp),
    homogeneous_shift h n 1 p.reverse (by simpa using hp.le)]
  norm_num
  rw [homogeneous_reverse e n p hp]
  simpa using homogeneous_one e n p x

theorem homogeneous_nonneg {A : Type} (e : A → ℝ) (n : ℕ) (p : List A) (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hc : ∀ a ∈ p,0 ≤ e a) : 0 ≤ homogeneous e n p x y := by
  induction p generalizing n with
  | nil => exact le_rfl
  | cons a p ih =>
    exact add_nonneg (mul_nonneg (hc a (by simp)) (pow_nonneg hy _))
      (mul_nonneg hx (ih (n-1) (fun b hb => hc b (by simp [hb]))))

theorem bernstein_sound {A : Type} {o : QOps A} {e : A → ℝ} (h : QSound o e)
    (p : List A) (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1)
    (hc : ∀ a ∈ o.bernstein p,0 ≤ e a) : 0 ≤ horner e p x := by
  cases p with
  | nil => exact le_rfl
  | cons a p =>
    rw [←bernstein_identity h p.length (a::p) rfl]
    exact homogeneous_nonneg e _ _ x (1-x) hx.1 (by linarith) hc

end MordellEight
