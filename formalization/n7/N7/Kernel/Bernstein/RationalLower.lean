-- Adapted from the checked Eight.RationalLower general semantics.
import N7.Kernel.Bernstein.RationalBernstein
import N7.Kernel.Bernstein.CoefficientBounds

namespace N7.Kernel
set_option maxHeartbeats 0

def zipCheck {A B : Type} (test : A → B → Bool) : List A → List B → Bool
  | [],[] => true
  | a::p,b::q => test a b && zipCheck test p q
  | _,_ => false

theorem zipCheck_horner_le {A B : Type} (test : A → B → Bool) (ea : A → ℝ) (eb : B → ℝ)
    (hs : ∀ a b,test a b=true → eb b≤ea a) (p : List A) (q : List B)
    (hc : zipCheck test p q=true) (x : ℝ) (hx : 0≤x) : horner eb q x≤horner ea p x := by
  induction p generalizing q with
  | nil => cases q <;> simp_all [zipCheck,horner]
  | cons a p ih =>
    cases q with
    | nil => simp [zipCheck] at hc
    | cons b q =>
      have h : test a b=true ∧ zipCheck test p q=true := by
        simpa only [zipCheck,Bool.and_eq_true] using hc
      exact add_le_add (hs a b h.1) (mul_le_mul_of_nonneg_left (ih q h.2) hx)

def DenseKernel.lowerCheck (p : DenseKernel) (q : RationalCube) : Bool :=
  zipCheck (zipCheck (zipCheck (fun c r => decide (r≤c.bound.lo)))) p q

/-- Rounding is external data; each rational coefficient must lie below its actual exact coefficient.
The comparison is only used on nonnegative transformed coordinates. -/
theorem DenseKernel.lowerCheck_sound (p : DenseKernel) (q : RationalCube)
    (hc : p.lowerCheck q=true) (u v t : ℝ) (hu : 0≤u) (hv : 0≤v) (ht : 0≤t) :
    q.real u v t≤p.real u v t := by
  apply zipCheck_horner_le _ _ _ ?_ p q hc u hu
  intro a b hab
  apply zipCheck_horner_le _ _ _ ?_ a b hab v hv
  intro c d hcd
  apply zipCheck_horner_le _ _ _ ?_ c d hcd t ht
  intro e r her
  have h : r≤e.bound.lo := of_decide_eq_true her
  have hr : (r:ℝ)≤(e.bound.lo:ℝ) := by exact_mod_cast h
  exact hr.trans e.bound_sound.1

end N7.Kernel
