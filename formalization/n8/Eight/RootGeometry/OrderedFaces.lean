import Eight.RootGeometry.Common

namespace MordellEight.RootGeometry

/-- Rational endpoint test for inclusion after imposing the order x₀ ≤ x₁. -/
def orderedFaceCheck (source target : ClosedBox 3) : Bool := decide
  (target.lo 0 ≤ source.lo 0 ∧
   (source.hi 0 ≤ target.hi 0 ∨ source.hi 1 ≤ target.hi 0) ∧
   (target.lo 1 ≤ source.lo 1 ∨ target.lo 1 ≤ source.lo 0) ∧
   source.hi 1 ≤ target.hi 1 ∧
   target.lo 2 ≤ source.lo 2 ∧ source.hi 2 ≤ target.hi 2)

theorem orderedFace_contains (source target : ClosedBox 3)
    (hc : orderedFaceCheck source target=true)
    {x : Fin 3 → ℝ} (hx : source.Contains x) (hd : CanonicalDomain x) :
    target.Contains x := by
  have hq : target.lo 0 ≤ source.lo 0 ∧
      (source.hi 0 ≤ target.hi 0 ∨ source.hi 1 ≤ target.hi 0) ∧
      (target.lo 1 ≤ source.lo 1 ∨ target.lo 1 ≤ source.lo 0) ∧
      source.hi 1 ≤ target.hi 1 ∧
      target.lo 2 ≤ source.lo 2 ∧ source.hi 2 ≤ target.hi 2 :=
    of_decide_eq_true hc
  have hr : (target.lo 0 : ℝ) ≤ (source.lo 0 : ℝ) ∧
      ((source.hi 0 : ℝ) ≤ (target.hi 0 : ℝ) ∨
       (source.hi 1 : ℝ) ≤ (target.hi 0 : ℝ)) ∧
      ((target.lo 1 : ℝ) ≤ (source.lo 1 : ℝ) ∨
       (target.lo 1 : ℝ) ≤ (source.lo 0 : ℝ)) ∧
      (source.hi 1 : ℝ) ≤ (target.hi 1 : ℝ) ∧
      (target.lo 2 : ℝ) ≤ (source.lo 2 : ℝ) ∧
      (source.hi 2 : ℝ) ≤ (target.hi 2 : ℝ) := by
    exact_mod_cast hq
  rcases hr with ⟨hl0,hh0,hl1,hh1,hl2,hh2⟩
  have upper0 : x 0 ≤ (target.hi 0 : ℝ) := by
    rcases hh0 with h | h
    · exact le_trans (hx 0).2 h
    · exact le_trans hd.2 (le_trans (hx 1).2 h)
  have lower1 : (target.lo 1 : ℝ) ≤ x 1 := by
    rcases hl1 with h | h
    · exact le_trans h (hx 1).1
    · exact le_trans h (le_trans (hx 0).1 hd.2)
  intro i
  fin_cases i
  · exact ⟨le_trans hl0 (hx 0).1,upper0⟩
  · exact ⟨lower1,le_trans (hx 1).2 hh1⟩
  · exact ⟨le_trans hl2 (hx 2).1,le_trans (hx 2).2 hh2⟩

/-- A bound transfers using a kernel-checked endpoint inclusion and canonical ordering. -/
theorem orderedFace_bound (source target : ClosedBox 3)
    (hc : orderedFaceCheck source target=true) (h : BoxMajorant target) :
    BoxMajorant source := by
  intro x hx hd
  exact h x (orderedFace_contains source target hc hx hd) hd

theorem orderedFace10_3 : orderedFaceCheck RootPartition.B10 RootPartition.B3=true := by
  decide +kernel

theorem orderedFace24_17 : orderedFaceCheck RootPartition.B24 RootPartition.B17=true := by
  decide +kernel

theorem bound10_of_bound3 (h : BoxMajorant RootPartition.B3) :
    BoxMajorant RootPartition.B10 :=
  orderedFace_bound RootPartition.B10 RootPartition.B3 orderedFace10_3 h

theorem bound24_of_bound17 (h : BoxMajorant RootPartition.B17) :
    BoxMajorant RootPartition.B24 :=
  orderedFace_bound RootPartition.B24 RootPartition.B17 orderedFace24_17 h

#print axioms bound10_of_bound3
#print axioms bound24_of_bound17
end MordellEight.RootGeometry
