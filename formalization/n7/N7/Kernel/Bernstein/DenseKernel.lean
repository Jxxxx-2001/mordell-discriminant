-- Adapted from the checked Eight.DenseKernel general semantics.
import N7.Kernel.ExactKernel

namespace N7.Kernel
set_option maxHeartbeats 0

/-- Rational linear operations on the three exact coefficient channels. -/
structure QOps (A : Type) where
  zero : A
  add : A → A → A
  scale : ℚ → A → A

def QOps.listAdd {A : Type} (o : QOps A) : List A → List A → List A
  | [], q => q
  | p, [] => p
  | a::p, b::q => o.add a b :: o.listAdd p q

def QOps.lift {A : Type} (o : QOps A) : QOps (List A) :=
  ⟨[],o.listAdd,fun r p => p.map (o.scale r)⟩

noncomputable def horner {A : Type} (e : A → ℝ) : List A → ℝ → ℝ
  | [], _ => 0
  | a::p, x => e a+x*horner e p x

structure QSound {A : Type} (o : QOps A) (e : A → ℝ) : Prop where
  zero : e o.zero = 0
  add : ∀ a b, e (o.add a b) = e a+e b
  scale : ∀ r a, e (o.scale r a) = (r : ℝ)*e a

theorem horner_add {A : Type} {o : QOps A} {e : A → ℝ} (h : QSound o e)
    (p q : List A) (x : ℝ) : horner e (o.listAdd p q) x = horner e p x+horner e q x := by
  induction p generalizing q with
  | nil => simp [QOps.listAdd,horner]
  | cons a p ih =>
    cases q with
    | nil => simp [QOps.listAdd,horner]
    | cons b q => simp only [QOps.listAdd,horner,h.add,ih]; ring

theorem horner_scale {A : Type} {o : QOps A} {e : A → ℝ} (h : QSound o e)
    (r : ℚ) (p : List A) (x : ℝ) :
    horner e (p.map (o.scale r)) x = (r : ℝ)*horner e p x := by
  induction p with
  | nil => simp [horner]
  | cons a p ih => simp only [List.map_cons,horner,h.scale,ih]; ring

theorem QSound.lift {A : Type} {o : QOps A} {e : A → ℝ} (h : QSound o e) (x : ℝ) :
    QSound o.lift (fun p => horner e p x) :=
  ⟨rfl,fun p q => horner_add h p q x,fun r p => horner_scale h r p x⟩

/-- Multiplication by X+r in ascending Horner coefficients. -/
def QOps.mulLinear {A : Type} (o : QOps A) (r : ℚ) (p : List A) : List A :=
  o.listAdd (p.map (o.scale r)) (o.zero::p)

def QOps.shift {A : Type} (o : QOps A) (r : ℚ) : List A → List A
  | [] => []
  | a::p => o.listAdd [a] (o.mulLinear r (o.shift r p))

theorem horner_mulLinear {A : Type} {o : QOps A} {e : A → ℝ} (h : QSound o e)
    (r : ℚ) (p : List A) (x : ℝ) :
    horner e (o.mulLinear r p) x = (x+(r : ℝ))*horner e p x := by
  rw [QOps.mulLinear,horner_add h,horner_scale h]
  simp only [horner,h.zero]
  ring

theorem horner_shift {A : Type} {o : QOps A} {e : A → ℝ} (h : QSound o e)
    (r : ℚ) (p : List A) (x : ℝ) : horner e (o.shift r p) x = horner e p (x+r) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    rw [QOps.shift,horner_add h,horner_mulLinear h,ih]
    simp [horner]

def QOps.monomial {A : Type} (o : QOps A) (n : ℕ) (a : A) : List A :=
  List.replicate n o.zero ++ [a]

theorem horner_monomial {A : Type} {o : QOps A} {e : A → ℝ} (h : QSound o e)
    (n : ℕ) (a : A) (x : ℝ) : horner e (o.monomial n a) x = e a*x^n := by
  induction n with
  | zero => simp [QOps.monomial,horner]
  | succ n ih =>
    simp only [QOps.monomial,List.replicate_succ,List.cons_append,horner,h.zero,zero_add]
    change x*horner e (o.monomial n a) x = _
    rw [ih,pow_succ]
    ring

def coeffOps : QOps KernelCoeff := ⟨0,(·+·),KernelCoeff.scale⟩
theorem coeffSound : QSound coeffOps KernelCoeff.real :=
  ⟨KernelCoeff.real_zero,KernelCoeff.real_add,KernelCoeff.real_scale⟩

abbrev DenseKernel := List (List (List KernelCoeff))
def denseOps : QOps DenseKernel := coeffOps.lift.lift.lift
noncomputable def DenseKernel.real (p : DenseKernel) (u v t : ℝ) : ℝ :=
  horner (fun q => horner (fun r => horner KernelCoeff.real r t) q v) p u

theorem denseSound (u v t : ℝ) : QSound denseOps (fun p => DenseKernel.real p u v t) :=
  ((coeffSound.lift t).lift v).lift u

def KernelTerm.dense (s : KernelTerm) : DenseKernel :=
  coeffOps.lift.lift.monomial s.u (coeffOps.lift.monomial s.v (coeffOps.monomial s.t s.coeff))

theorem KernelTerm.dense_real (s : KernelTerm) (u v t : ℝ) :
    s.dense.real u v t = s.real u v t := by
  unfold KernelTerm.dense DenseKernel.real
  rw [horner_monomial ((coeffSound.lift t).lift v),horner_monomial (coeffSound.lift t),
    horner_monomial coeffSound]
  dsimp [KernelTerm.real]
  ring

def ExactKernel.dense : ExactKernel → DenseKernel
  | [] => []
  | s::p => denseOps.add s.dense (ExactKernel.dense p)

theorem ExactKernel.dense_real (p : ExactKernel) (u v t : ℝ) :
    p.dense.real u v t = p.real u v t := by
  induction p with
  | nil => rfl
  | cons s p ih =>
    change (denseOps.add s.dense (ExactKernel.dense p)).real u v t = _
    rw [(denseSound u v t).add,KernelTerm.dense_real,ih]
    rfl

def DenseKernel.shiftU (r : ℚ) (p : DenseKernel) : DenseKernel := coeffOps.lift.lift.shift r p
def DenseKernel.shiftV (r : ℚ) (p : DenseKernel) : DenseKernel := p.map (coeffOps.lift.shift r)
def DenseKernel.shiftT (r : ℚ) (p : DenseKernel) : DenseKernel :=
  p.map (List.map (coeffOps.shift r))

theorem DenseKernel.shiftU_real (p : DenseKernel) (r : ℚ) (u v t : ℝ) :
    (p.shiftU r).real u v t = p.real (u+r) v t :=
  horner_shift ((coeffSound.lift t).lift v) r p u

theorem horner_map {A B : Type} (f : A → B) (e : B → ℝ) (p : List A) (x : ℝ) :
    horner e (p.map f) x = horner (fun a => e (f a)) p x := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [List.map_cons,horner,ih]

theorem DenseKernel.shiftV_real (p : DenseKernel) (r : ℚ) (u v t : ℝ) :
    (p.shiftV r).real u v t = p.real u (v+r) t := by
  unfold shiftV DenseKernel.real
  rw [horner_map]
  simp_rw [horner_shift (coeffSound.lift t)]

theorem DenseKernel.shiftT_real (p : DenseKernel) (r : ℚ) (u v t : ℝ) :
    (p.shiftT r).real u v t = p.real u v (t+r) := by
  unfold shiftT DenseKernel.real
  rw [horner_map]
  simp_rw [horner_map,horner_shift coeffSound]

def coeffCheck (a b : KernelCoeff) : Bool := decide (a=b)
theorem coeffCheck_sound {a b : KernelCoeff} (h : coeffCheck a b = true) : a=b :=
  of_decide_eq_true h

def listCheck {A : Type} (test : A → A → Bool) : List A → List A → Bool
  | [], [] => true
  | a::p, b::q => test a b && listCheck test p q
  | _, _ => false

theorem listCheck_sound {A : Type} (test : A → A → Bool)
    (hs : ∀ a b, test a b = true → a=b) (p q : List A)
    (h : listCheck test p q = true) : p=q := by
  induction p generalizing q with
  | nil => cases q <;> simp_all [listCheck]
  | cons a p ih =>
    cases q with
    | nil => simp [listCheck] at h
    | cons b q =>
      have hh : test a b = true ∧ listCheck test p q = true := by
        simpa only [listCheck,Bool.and_eq_true] using h
      rw [hs a b hh.1,ih q hh.2]

def denseCheck : DenseKernel → DenseKernel → Bool :=
  listCheck (listCheck (listCheck coeffCheck))

theorem denseCheck_sound {p q : DenseKernel} (h : denseCheck p q = true) : p=q := by
  apply listCheck_sound _ ?_ p q h
  intro a b hab
  apply listCheck_sound _ ?_ a b hab
  intro c d hcd
  exact listCheck_sound coeffCheck (fun _ _ => coeffCheck_sound) c d hcd

end N7.Kernel
