-- Adapted from Eight.DensePadding for three-channel coefficients.
import N7.Kernel.Bernstein.DenseKernel

namespace N7.Kernel
set_option maxHeartbeats 0

/-- Compare ascending coefficient lists, treating missing trailing coefficients as zero. -/
def listPadCheck {A : Type} (test : A → A → Bool) (z : A) : List A → List A → Bool
  | [], q => q.all (test z)
  | a::p, [] => test a z && listPadCheck test z p []
  | a::p, b::q => test a b && listPadCheck test z p q

theorem horner_all_zero {A : Type} (test : A → A → Bool) (z : A) (e : A → ℝ)
    (hs : ∀ a b,test a b=true → e a=e b) (hz : e z=0) (p : List A)
    (h : p.all (test z)=true) (x : ℝ) : horner e p x=0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    have hh : test z a=true ∧ p.all (test z)=true := by
      simpa only [List.all_cons,Bool.and_eq_true] using h
    have ha : e a=0 := (hs z a hh.1).symm.trans hz
    simp only [horner,ha,ih hh.2,mul_zero,add_zero]

theorem listPadCheck_sound {A : Type} (test : A → A → Bool) (z : A) (e : A → ℝ)
    (hs : ∀ a b,test a b=true → e a=e b) (hz : e z=0) (p q : List A)
    (h : listPadCheck test z p q=true) (x : ℝ) : horner e p x=horner e q x := by
  induction p generalizing q with
  | nil => exact (horner_all_zero test z e hs hz q h x).symm
  | cons a p ih =>
    cases q with
    | nil =>
      have hh : test a z=true ∧ listPadCheck test z p []=true := by
        simpa only [listPadCheck,Bool.and_eq_true] using h
      have ha : e a=0 := (hs a z hh.1).trans hz
      simp only [horner,ha,ih [] hh.2,horner,mul_zero,add_zero]
    | cons b q =>
      have hh : test a b=true ∧ listPadCheck test z p q=true := by
        simpa only [listPadCheck,Bool.and_eq_true] using h
      simp only [horner,hs a b hh.1,ih q hh.2]

def densePadCheck (p q : DenseKernel) : Bool :=
  listPadCheck (listPadCheck (listPadCheck coeffCheck 0) []) [] p q

theorem densePadCheck_sound (p q : DenseKernel) (h : densePadCheck p q=true) (u v t : ℝ) :
    p.real u v t=q.real u v t := by
  have hT (a b : List KernelCoeff) (hab : listPadCheck coeffCheck 0 a b=true) :
      horner KernelCoeff.real a t=horner KernelCoeff.real b t :=
    listPadCheck_sound coeffCheck 0 KernelCoeff.real
      (fun a b hab => congrArg KernelCoeff.real (coeffCheck_sound hab))
      KernelCoeff.real_zero a b hab t
  have hV (a b : List (List KernelCoeff))
      (hab : listPadCheck (listPadCheck coeffCheck 0) [] a b=true) :
      horner (fun c => horner KernelCoeff.real c t) a v=
        horner (fun c => horner KernelCoeff.real c t) b v :=
    listPadCheck_sound (listPadCheck coeffCheck 0) [] (fun c => horner KernelCoeff.real c t)
      hT rfl a b hab v
  exact listPadCheck_sound (listPadCheck (listPadCheck coeffCheck 0) []) []
    (fun a => horner (fun b => horner KernelCoeff.real b t) a v) hV rfl p q h u

theorem zero_padding_accepted : densePadCheck [[[0],[]]] []=true := by decide +kernel
theorem nonzero_padding_rejected : densePadCheck [[[⟨0,1,0⟩]]] []=false := by decide +kernel

end N7.Kernel
